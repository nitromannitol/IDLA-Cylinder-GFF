# Gaussian fluctuations for Internal DLA on cylinders

[![CI](https://github.com/nitromannitol/IDLA-Cylinder-GFF/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/nitromannitol/IDLA-Cylinder-GFF/actions/workflows/build.yml)
[![Comparator audit](https://github.com/nitromannitol/IDLA-Cylinder-GFF/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/nitromannitol/IDLA-Cylinder-GFF/actions/workflows/comparator.yml)

A Lean 4 formalization of the paper

> Ahmed Bou-Rabee, Vittoria Silvestri and Ariel Yadin,
> [*Gaussian fluctuations for Internal DLA on cylinders*](https://arxiv.org/abs/2604.21142),
> arXiv:2604.21142.

The four main results of the paper are proved in Lean: the bound on the maximal fluctuations
(Theorem 1.1), the Gaussian fluctuations (Theorem 1.9), and its two examples, the cycle and the
torus (Theorems 1.10 and 1.11). Every numbered result that their proofs use is proved, and so is
every result of other works that the proofs cite. The main theorems therefore hold with no
assumption beyond the hypotheses of the paper. The library has no `sorry` and uses only the standard
axioms.

## The paper

*Internal DLA* is a random growth model. A cluster grows one site at a time: each new particle
starts at a source, performs a random walk, and settles at the first site outside the cluster.

Here the graph is a cylinder `G_N = V_N × ℤ`. The base `V_N` is a finite, connected,
vertex-transitive graph on `N` vertices, such as a cycle or a discrete torus. The walk is lazy: it
makes a vertical step with probability 1/2, and otherwise a step of the lazy simple random walk on
`V_N`. The cluster starts as the half-cylinder `R_0 = {y ≤ 0}`, where `R_k = {(x, y) : y ≤ k}`.
Each particle starts at a uniform site of the layer `V_N × {0}`. After `T` particles the cluster is
`A(T)`, and one expects `A(T)` to be close to `R_{T/N}`.

Let `τ_mix` be the total-variation mixing time of the lazy walk on `V_N`, at threshold 1/4.

**Theorem 1.1 (maximal fluctuations).** For every `ν > 0` and `m ≥ 1` there is a constant `C` with
the following property. Set `T^♯ = N √τ_mix (log N)²` and

    Δ_N = C max{ log N, √( ((T ∧ T^♯)/N) (log N + log₊(T/N)) ) }.

Then for every `N` large enough and every integer `1 ≤ T ≤ N^m`,
`P(R_{⌊T/N − Δ_N⌋} ⊆ A(T) ⊆ R_{T/N + Δ_N}) ≥ 1 − N^{−ν}`.

The paper notes that this gives a shape theorem on the cylinder for every vertex-transitive base.

For the Gaussian fluctuations, let `1 = λ_1(N) > λ_2(N) ≥ … ≥ λ_N(N) ≥ 0` be the eigenvalues of the
lazy walk on `V_N`, with orthonormal eigenfunctions `f_k^N`. Choose `a_N → ∞` so that
`a_N √(2(1 − λ_2(N)))` has a finite positive limit.

**Assumption 1.4 (spectral convergence).** For each `k ≥ 2`, `a_N √(2(1 − λ_k(N)))` converges to a
limit `γ_k ∈ (0, ∞)`.

The *discrepancy* `D_T = 1_{A(T)} − 1_{R_{T/N}}` measures, with sign, how far the cluster is from the
flat profile.

**Theorem 1.9 (Gaussian fluctuations).** Fix `y₀ > 0` and a test function
`φ(x, y) = Σ_{k=2}^K α_k(y) f_k^N(x)`, whose coefficients are differentiable near `y₀` with bounded
derivative there. Let `ϕ(x, y) = φ(x, y/a_N)`. Assume Assumption 1.4 for `2 ≤ k ≤ K`, and
`a_N ≫ log N + log₊ a_N`. Then, with `T = N⌊y₀ a_N⌋`, the pairing `(N a_N)^{−1/2} ⟪D_T, ϕ⟫`
converges in distribution to a centred Gaussian with variance
`σ²(φ) = Σ_{k=2}^K α_k(y₀)² (1 − e^{−2γ_k y₀})/(2γ_k)`.

**Theorems 1.10 and 1.11 (the cycle and the torus).** On the cycle `ℤ_N`, with `a_N = N`, the same
convergence holds with `γ_k = √2 π ⌊k/2⌋`. On the torus `(ℤ/n)^d`, with `N = nᵈ` and `a_N = n`, it
holds with `γ_k` the square roots of the eigenvalues of `−(1/(2d))Δ` on the flat torus, counted with
multiplicity. Here the coefficients `α_k` are differentiable on `ℝ` with bounded derivatives.

## The main theorems in Lean

The main theorems are in [`IdlaCyl/Frozen/`](IdlaCyl/Frozen/). Their only hypotheses are those of
the paper.

| Paper | Lean declaration |
| --- | --- |
| Theorem 1.1 | `IdlaCyl.Frozen.max_fluct_v3` |
| Theorem 1.9 | `IdlaCyl.Frozen.gff_v3` |
| Theorem 1.10 | `IdlaCyl.Frozen.thm_cycle_v3` |
| Theorem 1.11 | `IdlaCyl.Frozen.thm_torus_v3` |

How to read the statements:

- A base is an `IdlaCyl.Base`: a finite, connected, vertex-transitive simple graph on at least two
  vertices. A sequence of bases with `N` vertices is an `IdlaCyl.BaseSeq`. An `IdlaCyl.Setup` adds
  the eigenbases and the sequence `a_N`.
- The law of the process is `IdlaCyl.idlaMeasure`: independent walks started uniformly on layer `0`.
  The cluster after `T` particles is `IdlaCyl.clusterTraj`.
- "For every `N` large enough" is a cutoff `N₀`, chosen after the constants and, in Theorem 1.1,
  after the sequence of bases. Probability bounds are stated for the complementary event.
- Convergence in distribution is stated through the integrals of bounded continuous functions.
- The eigenbasis is a hypothesis `S : SpectralData B`, so the theorems hold for every choice. Every
  base has one (`IdlaCyl.spectralData_exists`). On the cycle and the torus this covers the paper's
  Fourier basis.
- The tori do not have a base of every size, so Theorem 1.11 is indexed by the side length,
  written `n + 3`. It uses a form of Theorem 1.9 along any sequence of bases whose sizes tend to
  infinity (`IdlaCyl.gff_along_sequence`). The limits `γ_k` are written as
  `π √(2/d) √r_k`, where `r_k` is the `k`-th smallest squared norm of a vector of `ℤᵈ`; this is
  proved equal to the printed limit.

## All numbered results

Each row gives the Lean declaration that proves the result. The declarations are in the namespace
`IdlaCyl.Frozen`, except Theorem 4.1, which is in `IdlaCyl.External`. Each result is proved at the
printed strength.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1.1 | `max_fluct_v3` | Maximal fluctuations of `A(T)` around `R_{T/N}`. |
| Theorem 1.9 | `gff_v3` | Gaussian fluctuations of the discrepancy, under Assumption 1.4. |
| Theorem 1.10 | `thm_cycle_v3` | Theorem 1.9 on the cycles `ℤ_N`. |
| Theorem 1.11 | `thm_torus_v3` | Theorem 1.9 on the tori `(ℤ/n)^d`. |
| Proposition 2.1 | `pr_apriori_canonical_v2` | A priori bound on the height of the cluster. |
| Lemma 3.1 | `le_martingale_v2` | Sums of a harmonic function over the added sites form a martingale. |
| Proposition 3.2 | `pr_hextension` | Explicit harmonic extension below a layer, with exponential decay. |
| Proposition 3.3 | `pr_exchange_v2` | Changing one walk changes `A_+(T)` by at most two sites. |
| Lemma 3.4 | `le_replace_v2` | Replacing the test function by its harmonic extension changes the rescaled pairing by `o(1)` in probability. |
| Theorem 4.1 | `martingale_clt_v2_of_latticeProb` | McLeish's martingale central limit theorem, quoted from [McL74, Theorem 2.3]. |
| Lemma 4.2 | `clm_q_on_ec_v3` | The sum `Q_N` of the squared martingale increments has vanishing mean off the good event `E`. |
| Lemma 4.3 | `clm_q_w_v3` | On `E`, `Q_N` differs by at most `C Δ_N/a_N` from the same sum `W_N` over the flat profile. |
| Lemma 4.4 | `clm_w_to_sigma_v2` | `W_N → σ²(φ)`. |
| Proposition 5.1 | `pr_inner_stopped` | The inner bound: for `T ≥ K₀ N log N`, `A(T) ⊇ R_h` with `h = ⌊T/N − ℓ_*⌋`, outside probability `N^{−(ν+1)}`. |
| Lemma 5.3 | `lem_m_lower_tail_v2` | `P(M_ζ(T) ≤ −ℓ) ≤ exp(−ℓ²N/(4T))`. |
| Proposition 5.4 | `pr_outer_v2` | The outer bound: for `T ≥ K′ N log N`, `A(T) ⊆ R_{T/N + C′ℓ_*}`, outside probability `N^{−(ν+1)}`. |
| Lemma 5.5 | `le_wellspread_v3` | Outside probability `N^{−(ν+1)}`, no column holds more than `C₂ℓ_*` frozen particles. |
| Lemma 5.6 | `le_released_v3` | A balanced release of `m` particles per column stays below height `C₃m`, outside probability `N^{−(ν+2)}`. |
| Lemma 5.7 | `le_mono_init_v2` | IDLA driven by the same walks is monotone in the initial cluster. |
| Proposition 5.8 | `pr_reduction` | For `T^♯ ≤ T ≤ N^m`, `A(T)` is coupled with a shifted copy of `A_*(T′)`, `T′ ≤ T^♯`, outside probability `N^{−(ν+1)}`. |

The proofs also use results of other works that the paper cites without a number. Each is proved,
in the namespace `IdlaCyl.External`:

| Result | Lean declaration |
| --- | --- |
| Silvestri, Proposition 2 [Sil20] | `silvestri_prop2_proved` |
| Freedman's martingale inequality | `freedman_of_latticeProb` |
| Bernstein's inequality | `bernstein_of_latticeProb` |
| A Chernoff bound | `chernoff_of_latticeProb` |

McLeish's theorem and the three inequalities are derived from
[Lattice-Probability](https://github.com/nitromannitol/Lattice-Probability) in
[`IdlaCyl/External/Discharge/`](IdlaCyl/External/Discharge/).

## Stronger forms of Proposition 5.8

Three registered statements are stronger than Proposition 5.8 and are not in the paper. Write
`τ_rel = 1/(1 − λ_2)` for the relaxation time of the lazy walk on the base.

- `IdlaCyl.Frozen.pr_reduction_quant`: for every base, every `T ≥ 1` and `0 < ε < 1`, with
  `U = max(N, T)` and `H = ⌈4 √τ_rel log(2U²/ε)⌉`, there are `T′ ≤ min(T, 6NH − 1)` and `k` with
  `T′ + Nk = T`, and a coupling under which, with probability at least `1 − ε`, `A(T + s)` is
  `A_*(T′ + s)` shifted up by `k` layers for every `s ≥ 0`.
- `IdlaCyl.Frozen.pr_reduction_strong`: for `ν > 0`, `m ≥ 1`, `N ≥ 3` and `1 ≤ T ≤ N^m`, the same
  with failure probability `N^{−(ν+1)}`, `T′ ≤ D N √τ_rel log N` and `T′ ≤ √2 D N √τ_mix log N`,
  where `D = 6(4(ν + 2m + 2) + 1)`.
- `IdlaCyl.Frozen.pr_reduction_alpha_strong`: for every `α > 0`, `T′ ≤ α T^♯` for all bases with
  `N ≥ max(3, ⌈exp(√2 D/α)⌉)` and every `1 ≤ T ≤ N^m`.

Compared with Proposition 5.8, these hold for every `T ≥ 1`, give a reduced time a factor `log N`
below `T^♯`, have explicit constants and cutoffs, and couple the whole future of the two processes.

## Corrections

The Lean statements follow the arXiv source of the paper,
[`paper/idla-cylinder-gff.tex`](paper/idla-cylinder-gff.tex). No numbered result needed a change.
[`ledger/ERRATA.md`](ledger/ERRATA.md) records every difference between a Lean statement and the
paper, and every place where a printed proof was not followed. It has seven entries:

- E1 and E2 fix conventions: the law of the walks, and the exit site.
- E15 and E17 state Bernstein's inequality with a factor 2 and for measurable indicators, and a
  Chernoff bound with exponent `−δ²np/4`. Free constants of the lemmas that use them absorb the
  changes.
- E19 reads Lemma 4.3 as a bound for `N` beyond a threshold, which is how the paper uses it.
- E18 records a gap in the printed proof of Proposition 5.8. The layer-by-layer reduction cannot
  bring the reduced time below a fixed multiple of `T^♯`. The statement is true, and it is proved by
  filling blocks of about `√τ_mix log N` layers at once.

The formalization also found an error in a cited work. A step of the proof of Proposition 2 of
Silvestri [Sil20] bounds the total time to reach a level, but the coupling needs a lower bound on
the number of horizontal steps. The proof here bounds that number directly, and the conclusion is
unchanged (entry E21).

## Scope

- **Silvestri's Proposition 2** is stated for the paper's vertex-transitive bases and with a cutoff
  on the size of the base, which makes it weaker than the source. The initial cluster is connected,
  as in the source.
- **Registered statements are never edited.** A statement that had to change was registered again
  under a new name, in the `V2` and `V3` files of `IdlaCyl/Frozen/`. The main theorems are the `V3`
  forms. Each statement lies between `-- FROZEN-STATEMENT-BEGIN` and `-- FROZEN-STATEMENT-END`, and
  [`ledger/manifest.yaml`](ledger/manifest.yaml) records the SHA-256 hashes of the 40 registered
  statements and of the paper source.
- **Total definitions.** Lean gives conventional values to division by zero, `Real.log 0`, `sInf ∅`
  in `ℕ`, non-integrable integrals and non-summable series. The statements carry the positivity,
  finiteness and integrability hypotheses that rule these values out.

## Checking the proofs

- **No `sorry`.** The library has none, and no `admit`, `native_decide` or `axiom`. Each of the four
  comparator challenges under [`IdlaCylAudit/`](IdlaCylAudit/) has one intentional `sorry` at the
  statement, which the matching solution proves.
- **Standard axioms only.** [`tools/check_axioms.py`](tools/check_axioms.py) prints the axioms of
  every registered declaration. It fails on any axiom other than `propext`, `Classical.choice` and
  `Quot.sound`, and on a missing report.
- **No warnings.** The build of the library has none, and CI fails on any warning.
- **Independent check of the statements.** Each main theorem is restated in a `Challenge.lean` that
  imports mathlib alone and rebuilds the model from mathlib's primitives. The matching
  `Solution.lean` proves it from the library. [leanprover/comparator](https://github.com/leanprover/comparator)
  checks that the two statements agree, that only the standard axioms are used, and replays the
  proof with the Lean kernel and with NanoDa. See [`IdlaCylAudit/README.md`](IdlaCylAudit/README.md).
- **Pinned statements.** `python3 tools/manifest.py check` verifies the hashes of the registered
  statements and of the paper source.
- **Continuous integration.** The **CI** workflow checks the hashes, builds the library and the
  comparator pairs, and runs the axiom and warning checks. It runs on pushes to `main` that change
  code or build configuration. The **Comparator audit** workflow runs the four comparators when it is
  started from the [Actions page](https://github.com/nitromannitol/IDLA-Cylinder-GFF/actions). See
  [`CI_ARTIFACTS.md`](CI_ARTIFACTS.md).

The library `IdlaCyl` contains 390 Lean files with 56,628 lines, built on mathlib and
Lattice-Probability.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches the dependencies.

```bash
lake exe cache get                 # prebuilt mathlib
lake build                         # IdlaCyl, the default target
lake build IdlaCylAudit            # the comparator challenges and solutions
./tools/gate.sh                    # manifest, build, axiom and warning checks
```

The toolchain is Lean `v4.32.0`. Lattice-Probability has no prebuilt cache, so the first build
compiles it as well as this library. The dependencies are public repositories, pinned in
[`lake-manifest.json`](lake-manifest.json):

- mathlib at `81a5d257c8e410db227a6665ed08f64fea08e997`;
- Lattice-Probability: `https://github.com/nitromannitol/Lattice-Probability` at
  `fcfd4332bc9051cf5a6bbabe73e334df3bf28e76`.

`import IdlaCyl` loads the model, the four main results, Proposition 5.8 and its three stronger
forms. To build the paper, run `latexmk -pdf idla-cylinder-gff.tex` in [`paper/`](paper/).

## Running the comparators

Each comparator pair has a configuration `IdlaCylAudit/<Pair>/comparator.json` that permits
exactly `propext`, `Classical.choice` and `Quot.sound`.

```bash
./scripts/run_comparators.sh TOOL_ROOT
```

`TOOL_ROOT` holds the builds of leanprover/comparator, lean4export, NanoDa and landrun at the
revisions recorded in [`.github/workflows/comparator.yml`](.github/workflows/comparator.yml). See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
IdlaCyl.lean          the root module, importing the main theorems and the reduction
IdlaCyl/
  Frozen/             the paper's statements, each quoting the lines of the paper it states
  External/           the cited results and the concentration inequalities, as
                      propositions, and Discharge/, their proofs
  Definitions/        the paper's quantities used in the statements (T^♯, Δ_N, the test
                      functions, the limiting variance)
  Support/            the model and the proofs
IdlaCylAudit/         the mathlib-only restatements, their solutions and the bridge
ledger/               manifest.yaml (statement hashes) and ERRATA.md
paper/                the paper: arXiv source, bibliography, figures, PDF
tools/                the manifest, axiom and warning checks and the gate script
scripts/              the comparator runner
.github/workflows/    build and comparator workflows
```

## References

- [McL74] D. L. McLeish, Dependent central limit theorems and invariance principles,
  *Annals of Probability* **2** (1974), 620–628.
- [Sil20] V. Silvestri, Internal DLA on cylinder graphs: fluctuations and mixing, *Electronic
  Communications in Probability* **25** (2020).

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
