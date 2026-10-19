# Contributing and building

This repository is mainly a finished artifact, the formalization of one paper, but issues and
pull requests are welcome.

## Building locally

```bash
lake exe cache get                 # prebuilt mathlib oleans
lake build                         # Lattice-Probability and IdlaCyl
lake build IdlaCylAudit            # the comparator challenges and solutions
```

The toolchain is pinned in `lean-toolchain` and managed by
[elan](https://github.com/leanprover/elan). The first build compiles Lattice-Probability from
source. The library must build with **no warnings**. The only files that contain a `sorry`
are the four comparator challenges under `IdlaCylAudit/*/Challenge.lean`, each with exactly
one, in its final theorem.

`./tools/gate.sh` runs every check: the frozen-statement hashes, the build, the axiom report
of every registered declaration, the warning census, and the build and structure of the
comparator audit. With `IDLA_LAKE_LOCK` set to a file name it runs under an exclusive `flock`
on that file.

## Frozen statements

The bytes between `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END` in a file of
`IdlaCyl/Frozen/` or `IdlaCyl/External/` are the statement, and their SHA-256 hashes are
recorded in `ledger/manifest.yaml`.

- Never edit a frozen statement. A proof goes after the end marker. A statement that has to
  change is registered again in a new file, and the new manifest row records the statement it
  supersedes; [`ledger/ERRATA.md`](ledger/ERRATA.md) records why.
- A result the paper cites from the literature is a `def … : Prop` in `IdlaCyl/External/`,
  carried into its consumers as an explicit hypothesis until it is proved.
- In Lean every function is total, so check each new statement for junk values: `a / 0 = 0`,
  `sInf ∅ = 0` in `ℕ`, `tsum` of a non-summable family, `Set.ncard` of an infinite set,
  `ENat.toNat ⊤ = 0`, and `Real.sqrt`, `Real.log`, `Real.toNNReal`, `Nat.floor` outside their
  range. A constant that the paper says depends only on certain parameters is chosen before
  everything else.
- Run `python3 tools/manifest.py check` before every commit.

## Conventions for Lean files

- No `sorry`, `admit`, `native_decide`, new `axiom` or `set_option maxHeartbeats` anywhere in
  the library.
- Refer to a result of the paper by its LaTeX label. Line references `tex:N` refer to the
  pinned source `paper/idla-cylinder-gff.tex`, whose hash is recorded in the manifest.
- Add new declarations under `IdlaCyl/`. The pinned dependencies under `.lake/packages/` are
  read-only; extend them from this project rather than editing them.
- The options in `lakefile.lean` (`autoImplicit` off, the unused-variable and simp linters on)
  apply to modules built through Lake; `lake env lean <file>` does not read them, so check a
  file with `lake build <Module>`.
- `lake clean` deletes the compiled dependencies and forces a long rebuild. To rebuild only
  this project, delete its own build output under `.lake/build/lib/lean/IdlaCyl` and run
  `lake build` again.

## Comparators

Each pair under `IdlaCylAudit/` has a mathlib-only `Challenge.lean`, a `Solution.lean` that
proves the same statement from the library, and a `comparator.json` that permits exactly
`propext`, `Classical.choice` and `Quot.sound`. The vocabulary block of every challenge must be
byte-identical to `IdlaCylAudit/SolutionBasic.lean`; `python3 tools/check_audit.py` checks
this. Do not change a challenge without checking it against the paper's statement. Run all
pairs with `scripts/run_comparators.sh TOOL_ROOT`, as described in the README. A missing pair,
a missing tool or a failed kernel check is a failure. Logs are kept under
`.lake/comparator-logs/`.

## Continuous integration

`.github/workflows/build.yml` builds the library, rejects any warning and runs the manifest,
axiom, warning and audit checks. `.github/workflows/comparator.yml` builds the comparator tools
at pinned revisions and runs the four pairs, one job per pair; see
[`CI_ARTIFACTS.md`](CI_ARTIFACTS.md).
