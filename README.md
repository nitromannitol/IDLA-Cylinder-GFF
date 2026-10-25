# Gaussian fluctuations for Internal DLA on cylinders

A machine-checked **Lean 4** formalization of the paper

> Ahmed Bou-Rabee, Vittoria Silvestri and Ariel Yadin,
> [*Gaussian fluctuations for Internal DLA on cylinders*](https://arxiv.org/abs/2604.21142),
> arXiv:2604.21142.

The paper's arXiv source, its figures and the compiled PDF are included under
[`paper/`](paper/). All four main results of the paper are proved: the maximal
fluctuation bound (Theorem 1.1), the Gaussian fluctuations of the occupation field
(Theorem 1.3), and its two examples, the cycle and the torus. The two results the paper
cites from the literature are proved as well: McLeish's martingale central limit theorem
and Silvestri's Proposition 2. Every lemma and proposition that the proofs of the main
results use is proved at the printed strength. The paper's reduction `pr:reduction` holds
as printed but its printed proof has a gap; it is proved here by a different argument,
together with three statements that are stronger than the published one.

The development is built on [mathlib](https://github.com/leanprover-community/mathlib4)
and on the public library
[Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability)
(`LatticeProb`), which contains McLeish's theorem and the concentration inequalities.

[![CI](https://github.com/nitromannitol/IDLA-Cylinder-GFF/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/IDLA-Cylinder-GFF/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/IDLA-Cylinder-GFF/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/IDLA-Cylinder-GFF/actions/workflows/comparator.yml)

## What is proved

Internal DLA on the cylinder `V_N × ℤ` over a finite connected vertex-transitive base `V_N`
on `N` vertices: particles start, one at a time, uniformly on layer `0`, perform the lazy
cylinder walk, and settle at the first site outside the current cluster, which starts as
the half-cylinder `R_0 = {y ≤ 0}`. The four main results are theorems in
[`IdlaCyl/Frozen/`](IdlaCyl/Frozen/), registered with the hash of their statements in
[`ledger/manifest.yaml`](ledger/manifest.yaml).

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 (`th:max_fluct`) | `IdlaCyl.Frozen.max_fluct_v3` | Maximal fluctuations of the cluster around the flat profile. |
| Theorem 1.3 (`th:GFF`) | `IdlaCyl.Frozen.gff_v3` | Gaussian fluctuations of the discrepancy, under the spectral assumption. |
| The cycle (`thm:cycle`) | `IdlaCyl.Frozen.thm_cycle_v3` | Theorem 1.3 on the cycles `ℤ_N`, with explicit limits. |
| The torus (`thm:torus`) | `IdlaCyl.Frozen.thm_torus_v3` | Theorem 1.3 on the tori `(ℤ/n)^d`, with explicit limits. |

**Theorem 1.1 (maximal fluctuations).** For every `ν > 0` and real `m ≥ 1` there is
`C = C(ν, m) > 0`, chosen before the sequence of bases, such that, with
`T^♯ = N √τ_mix (log N)²` and
`Δ_N = C max{log N, √(((T ∧ T^♯)/N)(log N + log₊(T/N)))}`, for all `N` large enough every
integer `1 ≤ T ≤ N^m` satisfies `P(R_{⌊T/N − Δ_N⌋} ⊆ A(T) ⊆ R_{T/N + Δ_N}) ≥ 1 − N^{−ν}`.
Here `τ_mix` is the total-variation mixing time of the lazy walk on `V_N` at threshold `1/4`.

**Theorem 1.3 (Gaussian fluctuations).** For a test function
`φ(x, y) = ∑_{k=2}^K α_k(y) f_k^N(x)` whose coefficients are differentiable near `y₀ > 0`
with bounded derivative there, extended by `ϕ(x, y) = φ(x, y/a_N)`, under Assumption
`a:spectral` for `2 ≤ k ≤ K` and the growth condition `a_N ≫ log N + log₊ a_N`, with
`T = N⌊y₀ a_N⌋` the pairing `(N a_N)^{−1/2} ⟪D_T, ϕ⟫` of the discrepancy with `ϕ` converges
in distribution to `N(0, σ²(φ))`, where `σ²(φ) = ∑_{k=2}^K α_k(y₀)² (1 − e^{−2γ_k y₀})/(2γ_k)`,
including the degenerate case `σ²(φ) = 0`.

**The cycle and the torus.** For the cycle `ℤ_N` with `a_N = N`, and for the torus
`(ℤ/n)^d` with `N = n^d` and `a_N = n`, the same convergence holds for every orthonormal
eigenbasis of the lazy walk (the paper's Fourier basis is one of them), with
`γ_k = √2 π ⌊k/2⌋` on the cycle and `γ_k = π √(2/d) √r_k` on the torus, where `r_k` is the
`k`-th smallest squared norm of a vector of `ℤ^d` counted with multiplicity; the latter is
proved to equal the printed limit of `a_N √(2(1 − λ_k(N)))`.

**Supporting results.** Every lemma and proposition of the paper that these proofs use is
proved at the printed strength, each as a registered theorem of `IdlaCyl/Frozen/`:
`pr:apriori`, `le:martingale`, `pr:hextension`, `pr:exchange`, `le:replace`,
`clm:Q on Ec`, `clm:Q-W`, `clm:W to sigma`, `pr:inner`, `lem:M lower tail`, `pr:outer`,
`le:wellspread`, `le:released`, `le:mono-init` and `pr:reduction`.

**Cited results, proved here.** The paper cites two results from the literature. Each is a
proposition in [`IdlaCyl/External/`](IdlaCyl/External/), and each is proved:

- McLeish's martingale central limit theorem (D. L. McLeish, *Dependent central limit
  theorems and invariance principles*, Ann. Probab. 2 (1974), Theorem 2.3),
  `thm:martingale-CLT`, as `IdlaCyl.External.martingale_clt_v2`, proved from
  `LatticeProb.McLeish.tendstoInDistribution_martingale_clt` in
  [`Discharge/McLeish.lean`](IdlaCyl/External/Discharge/McLeish.lean).
- Silvestri's Proposition 2 (V. Silvestri, *Internal DLA on cylinder graphs: fluctuations and
  mixing*, Electron. Commun. Probab. 25 (2020)), as `IdlaCyl.External.silvestri_prop2`, with
  the initial cluster connected as in the source. The encoding is restricted to the paper's
  vertex-transitive bases and adds a cutoff `N₀` on the size of the base; both make it weaker
  than the source (ERRATA E21). It is proved as
  `IdlaCyl.External.silvestri_prop2_proved` in
  [`Discharge/Silvestri.lean`](IdlaCyl/External/Discharge/Silvestri.lean) by a coupling of
  first-passage blocks with maximally coupled horizontal windows
  ([`IdlaCyl/Support/Silvestri/`](IdlaCyl/Support/Silvestri/)).

The concentration inequalities the paper uses (Freedman, Bernstein, Chernoff) are derived
from Lattice-Probability in [`IdlaCyl/External/Discharge/`](IdlaCyl/External/Discharge/).

**The reduction `pr:reduction`, and three stronger statements.** The printed proof of the
reduction iterates a layer-by-layer coupling that cannot go below a fixed multiple of
`T^♯`; this is recorded in [`ledger/ERRATA.md`](ledger/ERRATA.md) (entry E18). The printed
statement is true: `IdlaCyl.Frozen.pr_reduction` proves it, with a size cutoff that is
uniform over all bases, by filling blocks of `H ≍ √τ_mix log N` layers at once with `2NH`
particles stopped at the top of each block. Three further registered statements are
**stronger than the published `pr:reduction`** and are not in the paper. Write
`τ_rel = 1/(1 − λ_2)` for the relaxation time of the lazy base walk.

- `IdlaCyl.Frozen.pr_reduction_quant`: for every base, every `T ≥ 1` and `0 < ε < 1`, with
  `U = max(N, T)` and `H = ⌈4 √τ_rel log(2U²/ε)⌉`, there are deterministic `T' ≥ 1` and
  `k ≥ 0` with `T' ≤ min(T, 6NH − 1)` and `T' + Nk = T`, and a coupling of two IDLA
  processes started from `R_0` such that `A(T + s) = A_*(T' + s) + R_k` for **every**
  `s ≥ 0`, with probability at least `1 − ε`.
- `IdlaCyl.Frozen.pr_reduction_strong`: for `ν > 0`, `m ≥ 1`, `N ≥ 3` and every
  `1 ≤ T ≤ N^m`, the same with failure probability `N^{−(ν+1)}`,
  `T' ≤ min(T, D N √τ_rel log N)` and `T' ≤ √2 D N √τ_mix log N`, where
  `D = 6(4(ν + 2m + 2) + 1)`.
- `IdlaCyl.Frozen.pr_reduction_alpha_strong`: for every `α > 0`, `T' ≤ α T^♯` for all bases
  with `N ≥ max(3, ⌈exp(√2 D/α)⌉)` and every `1 ≤ T ≤ N^m`, again with agreement at every
  later time.

Compared with the printed statement, these hold for every `T ≥ 1` rather than for
`T ≥ T^♯`, give a reduced time a factor `log N` below `T^♯`, have explicit constants and an
explicit cutoff, and couple the whole future of the two processes. Their proof replaces
Silvestri's Proposition 2 by an explicit comparison of first-hit distributions through the
spectral first-hit law, whose total variation is at most `√N e^{−H/√τ_rel}`
([`IdlaCyl/Support/Reduction/Block/`](IdlaCyl/Support/Reduction/Block/)).

## Standing assumptions and scope

1. **The model.** A base is a `IdlaCyl.Base`: a finite, connected, vertex-transitive simple
   graph on at least two vertices, with the lazy simple random walk `P_N` of `tex:230-236`.
   The cylinder walk, its law (mathlib's Ionescu-Tulcea construction), the canonical IDLA
   driving law `IdlaCyl.idlaMeasure` (independent walks started uniformly on layer `0`) and
   the clusters `IdlaCyl.clusterTraj` are defined in [`IdlaCyl/Support/`](IdlaCyl/Support/).
   Sequences of bases are `IdlaCyl.BaseSeq`; the normalising sequence `a_N` and the
   spectral data of Theorem 1.3 are `IdlaCyl.Setup`.
2. **Axioms and incomplete proofs.** The library contains no `sorry`, no `admit`, no
   `native_decide` and no `axiom`. The axiom report of every registered theorem consists of
   exactly `propext`, `Classical.choice` and `Quot.sound`. The main theorems rely on no
   unproved result: the two cited results are proved in this repository or in
   Lattice-Probability.
3. **Quantifiers.** "For every `N` large enough" is a cutoff `N₀` chosen after the constants
   and, in Theorem 1.1, after the sequence of bases, as printed. Probability bounds are stated
   for the complementary event, `P(Eᶜ) ≤ N^{−ν}`. Convergence in distribution is stated
   through the integrals of bounded continuous functions.
4. **Spectral data.** The paper fixes an orthonormal eigenbasis of `P_N`. In Lean it is a
   hypothesis `S : SpectralData B`; the theorems hold for every such choice, and every base
   has one (`IdlaCyl.spectralData_exists`).
5. **The torus.** The tori `(ℤ/n)^d` do not have a base of every size, so the torus theorem
   is indexed by the side length (written `n + 3`) and uses a version of Theorem 1.3 along any
   sequence of bases whose sizes tend to infinity (`IdlaCyl.gff_along_sequence`).
6. **Superseded statements.** A registered statement is never edited. Where a first
   encoding did not state the paper's result, the statement is registered again under a new
   name, in the `V2` and `V3` files of `IdlaCyl/Frozen/`. The `V3` forms of the four main
   theorems are unconditional; the `V2` forms carry the two cited results as hypotheses
   (`CONDITIONAL`). [`ledger/ERRATA.md`](ledger/ERRATA.md) records every difference between a
   first encoding and the paper, and every point where the Lean statement reads the paper in
   a particular way (for `clm:Q-W`, the bound for `N` large, entry E19; for Bernstein's
   inequality, an added measurability hypothesis, entry E17).
7. **Total definitions.** Lean's definitions are total: division by zero, `Real.log 0`,
   `sInf ∅` in `ℕ`, a non-integrable integral and a non-summable series all have conventional
   values. The statements carry the positivity, finiteness and integrability hypotheses that
   rule these values out.

## Guarantees

- **No `sorry`.** The library `IdlaCyl/` contains none. The four comparator
  challenges under [`IdlaCylAudit/`](IdlaCylAudit/) each contain one intentional
  statement-level `sorry`, which the corresponding solution proves.
- **Standard axioms only.** [`tools/check_axioms.py`](tools/check_axioms.py) prints the axiom
  report of every registered declaration and fails on any axiom other than `propext`,
  `Classical.choice` and `Quot.sound`, on `sorryAx`, and on a missing report.
- **Frozen statements.** The bytes between `-- FROZEN-STATEMENT-BEGIN` and
  `-- FROZEN-STATEMENT-END` of each file of `IdlaCyl/Frozen/` and `IdlaCyl/External/` are the
  statement; their SHA-256 hashes, with that of the paper source, are recorded for 41
  registered nodes in [`ledger/manifest.yaml`](ledger/manifest.yaml), and
  `python3 tools/manifest.py check` verifies them.
- **Builds from a clean checkout.** In a fresh clone of this tree, `lake build` runs 9,062 jobs
  (most of them mathlib's prebuilt modules) and reports no warning and no error, and
  `lake build IdlaCylAudit` reports only the four intended `sorry` warnings of the challenges.
  The CI build rejects any warning.
- **Independent check of the statements.** The four main theorems are restated in
  [`IdlaCylAudit/`](IdlaCylAudit/) using mathlib alone, one challenge per theorem. Each
  solution proves its restatement from the library, and
  [leanprover/comparator](https://github.com/leanprover/comparator) checks that the
  statement is proved, with only the three standard axioms, and replays the proof with an
  independent kernel. See [`IdlaCylAudit/README.md`](IdlaCylAudit/README.md).
- **Pinned toolchain and dependencies.** Lean `v4.32.0` and mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997`; Lattice-Probability at the exact commit
  recorded in [`lake-manifest.json`](lake-manifest.json) (see [Building](#building)).
- **The paper is part of the repository.** Every statement refers to the version in
  [`paper/`](paper/), whose source `paper/idla-cylinder-gff.tex` is the arXiv source of
  arXiv:2604.21142, pinned by its SHA-256
  `34a459e11753efc825c7a7b0534bb90598fc94a20f32ce8c7d53135c028e7701`.

## Size

The library `IdlaCyl` contains 391 Lean files with 56,758 physical lines (43,585 lines of code
once comments and blank lines are removed), on top of mathlib and Lattice-Probability. The
comparator audit `IdlaCylAudit` is counted separately: 13 files with 4,401 lines, of which the
four challenges share one 744-line vocabulary block.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches the dependencies.

```bash
lake exe cache get                 # prebuilt mathlib
lake build                         # IdlaCyl, the default target
lake build IdlaCylAudit            # the comparator challenges and solutions
./tools/gate.sh                    # manifest, build, axiom and warning checks
```

Lattice-Probability has no prebuilt cache, so the first build compiles it as well as this
library. It is a public repository, pinned in [`lake-manifest.json`](lake-manifest.json):

- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `fcfd4332bc9051cf5a6bbabe73e334df3bf28e76`.

`import IdlaCyl` loads the model, the four main results, `pr:reduction` and its three
strengthenings. To build the paper, run `latexmk -pdf idla-cylinder-gff.tex` in
[`paper/`](paper/).

## Running the comparators

Each comparator pair has a configuration `IdlaCylAudit/<Pair>/comparator.json` that permits
exactly `propext`, `Classical.choice` and `Quot.sound`. The comparator checks that the
solution proves the challenge statement, compares their dependency closures, and replays
the proof with the Lean kernel and with NanoDa.

```bash
./scripts/run_comparators.sh TOOL_ROOT
```

`TOOL_ROOT` holds the builds of leanprover/comparator, lean4export, NanoDa and landrun at the
revisions recorded in [`.github/workflows/comparator.yml`](.github/workflows/comparator.yml).
The [comparator workflow](.github/workflows/comparator.yml) builds these tools and runs all
four pairs on GitHub-hosted runners; see [`CI_ARTIFACTS.md`](CI_ARTIFACTS.md).

There are two continuous-integration workflows: **CI** builds the library and runs the
manifest, axiom and warning checks; **Comparator audit** checks the four challenge/solution
pairs. CI runs on pushes to `main` that change code or build configuration. Both workflows
can be started manually from the
[Actions page](https://github.com/nitromannitol/IDLA-Cylinder-GFF/actions). See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
IdlaCyl.lean          the root module, importing the main theorems and the reduction
IdlaCyl/
  Frozen/             the paper's statements, each quoting the lines of the paper it states
  External/           the two cited results and the concentration inequalities, as
                      propositions, and Discharge/, their proofs
  Definitions/        the paper's quantities used in the statements (T^♯, Δ_N, the test
                      functions, the limiting variance)
  Support/            the model and the proofs: base graph, cylinder walk, IDLA, discrepancy,
                      spectrum, first hit, the inner and outer bounds (Outer/), the replacement
                      lemma (Replace/), the Gaussian limit (Gff/, GffSeq/), the cycle and torus
                      spectra (Cycle/, Torus/), Silvestri's Proposition 2 (Silvestri/) and the
                      reduction (Reduction/, Reduction/Block/)
IdlaCylAudit/         the mathlib-only restatements, their solutions and the bridge
ledger/               manifest.yaml (statement hashes) and ERRATA.md
paper/                the paper: arXiv source, bibliography, figures, PDF
tools/                the manifest, axiom and warning checks and the gate script
scripts/              the comparator runner
.github/workflows/    build and comparator workflows
```

## How this was built

The Lean code was written with AI assistance, using models from Anthropic (Claude) and OpenAI
(GPT) and, for auxiliary proof search, from DeepSeek and Mistral (Leanstral), under the
direction of the author. The argument behind the block reduction and the stronger reductions
was first written out by an OpenAI GPT model and checked in a separate model review before it
was formalized. Every proof is checked by the Lean kernel. The models and tooling are
disclosed in [`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) standard.

## Authors and citation

The Lean development is by **Ahmed Bou-Rabee**. The paper it formalizes is by Ahmed
Bou-Rabee, Vittoria Silvestri and Ariel Yadin. To cite the formalization, use
[`CITATION.cff`](CITATION.cff).

## License

The Lean development is licensed under the Apache License 2.0; see [`LICENSE`](LICENSE).
The paper in [`paper/`](paper/) is included with its authors' permission; its publication
licence, the arXiv non-exclusive distribution licence, is not set by this software licence.

## Palomar preflight

The manually dispatched [Palomar full preflight](.github/workflows/palomar-preflight.yml)
calls Palomar's complete verifier at a pinned revision. Select the repository-relative
Comparator configuration to check. It records the dispatched commit and runs with
`mode: full` and `execution_profile: palomar-standard-v1`. Resolve the current Lean
minimum, source-module, Challenge-closure, licensing and metadata requirements before
dispatch. A passing preflight is advisory; it is separate from submission, editorial
review and a public registry record.
