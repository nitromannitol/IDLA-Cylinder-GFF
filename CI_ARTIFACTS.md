# Continuous integration: what runs and what it keeps

There are two workflows. Both run on GitHub-hosted `ubuntu-24.04` runners (4 vCPU, 16 GB
RAM, six hours per job), and both install the pinned Lean toolchain with
[`tools/prefetch_toolchain.py`](tools/prefetch_toolchain.py) before
`leanprover/lean-action` runs: the script downloads the pinned release asset with retries and
exponential backoff, checks its size and SHA-256, and installs it where elan looks, so that a
single network failure does not fail the job.

## CI (`.github/workflows/build.yml`)

Runs on every push to `main` that changes code or build configuration, and on manual
dispatch.

Mathlib's oleans come from its public cache (`lake exe cache get`). Lattice-Probability has no
prebuilt cache; Lake builds the modules of it that this library imports, at the commit pinned in
`lake-manifest.json`. The job restores the most recent build for the same toolchain and manifest
(the project's and Lattice-Probability's build directories), then

- checks the hashes of the frozen statements (`tools/manifest.py check`);
- builds `IdlaCyl` and fails on any warning;
- prints the axiom report of every registered declaration and fails on any axiom other
  than `propext`, `Classical.choice` and `Quot.sound` (`tools/check_axioms.py`), and fails on
  any warning recorded for a module of `IdlaCyl` (`tools/check_warnings.py`);
- builds the comparator audit `IdlaCylAudit` and checks its structure
  (`tools/check_audit.py`): every challenge imports only mathlib, its vocabulary block is
  byte-identical to the solutions' vocabulary, every solution restates its challenge
  verbatim, and the only warnings are the four intentional `sorry`s of the challenges;
- runs the tests of the checks (`tools/tests/`).

**Artifacts.** `build-logs-<sha>`: the logs of the production build and of the audit build.
The build directories are saved to the Actions cache even when a later step fails, so an
interrupted run is resumed by the next one; a cache entry is a build accelerator, not a
verification result.

## Comparator audit (`.github/workflows/comparator.yml`)

Runs on manual dispatch, for all four pairs or for a comma-separated subset: `MaxFluct`
(Theorem 1.1), `GFF` (Theorem 1.3), `Cycle` and `Torus`. One job per pair:

1. **Tools.** It builds [leanprover/comparator](https://github.com/leanprover/comparator),
   [lean4export](https://github.com/leanprover/lean4export),
   [NanoDa](https://github.com/ammkrn/nanoda_lib) and
   [landrun](https://github.com/Zouuup/landrun) from source at the revisions fixed in the
   workflow, with Go and Rust at fixed versions, checks the checked-out revisions, and caches
   the builds under a key over those revisions and the Lean toolchain.
2. **Library.** It restores the build cache written by CI, when present, and otherwise
   compiles the needed Lattice-Probability modules and the library itself.
3. **Pair.** It checks the audit structure, builds the pair's challenge and solution, and runs
   [`scripts/run_comparators.sh`](scripts/run_comparators.sh). The comparator exports both
   modules, checks that the solution's theorem has exactly the challenge's statement and that
   the dependency closure of the statement agrees with the challenge's, checks that only the
   three permitted axioms occur, and replays the proof with the Lean kernel and with NanoDa.
   The job passes only when the comparator exits successfully, prints its success verdict
   exactly once and reports no warning other than the challenge's intentional `sorry`.
4. **Report.** A final job fails unless every pair passed.

**Artifacts.** `comparator-<Pair>-<sha>`: the build log of the pair, the comparator's standard
output and standard error, and its exit status and running time.

## Running the same checks locally

```bash
lake exe cache get
./tools/gate.sh                          # manifest, build, axiom and warning checks
lake build IdlaCylAudit
python3 tools/check_audit.py
./scripts/run_comparators.sh TOOL_ROOT   # TOOL_ROOT: the four tools, built as above
```
