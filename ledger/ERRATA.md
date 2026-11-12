# Errata

This file records every difference between a Lean statement and the paper, and every point
where the printed proof was not followed. A frozen statement is never edited: a statement that
had to change was registered again under a new name (the `V2` and `V3` files of
`IdlaCyl/Frozen/`), and its manifest row in `ledger/manifest.yaml` records the statement it
supersedes.

## E1 — the first main statements were phrased over an ad hoc driver law

* **Statements:** the first encodings of `th:max_fluct` and `th:GFF`.
* **Issue:** both quantified over a type `Driver` and measured with `driverLaw`, a process
  with two uniform choices per step, rather than the law of independent walks of the paper.
* **Resolution:** the canonical model (`Support/Canonical.lean`, `Support/CanonicalIdla.lean`)
  defines the walk law through mathlib's Ionescu-Tulcea construction and the IDLA law
  `idlaMeasure` as the product of independent walks started uniformly on layer `0`. Every
  main statement (`max_fluct_v3`, `gff_v3`, `thm_cycle_v3`, `thm_torus_v3`) is stated over
  `idlaMeasure` and `clusterTraj`.

## E2 — an exit site with a junk value

* **Issue:** the first exit site read `ENat.toNat ⊤ = 0` on a trajectory that never leaves the
  cluster, and so returned the walk's starting point; any claim that the exit site lies above
  level `0` was then provable on that branch.
* **Resolution:** the exit time `exitTime'` is `ℕ∞`-valued and the exit site `exitSite'` is
  used only where the exit is almost surely finite (`Support/Exit.lean`).

## E15 — Bernstein's inequality carries the factor 2

The first encoding of `ext-bernstein` bounded the deviation probability by
`exp(−ε²/(2(∑ p + ε/3)))`. Bernstein's inequality as proved in Lattice-Probability
(`LatticeProb.bernstein`) gives `2 · exp(−(ε²/2)/(B² + Mε/3))` with `B² = ∑ ∫(X_i − p_i)²`, and
for indicators `B² = ∑ p_i(1 − p_i) ≤ ∑ p_i`. The factor `2` cannot be removed from that
theorem, and its consumer `le:released` has a free constant `K₁` that absorbs it, so
`External.Bernstein` states the factor `2`:
`≤ ofReal (2 * Real.exp (-(ε ^ 2 / 2) / (∑ i, p i + ε / 3)))`.

**Chernoff's constant.** `External.Chernoff` has the exponent `−δ²np/4`. It follows from
`LatticeProb.bernstein_one_sided` with `Y_i = p − X_i`, `t = δnp`, `B² ≤ np` and `M = 1`,
which give the exponent `−(δ²np/2)/(1 + δ/3)`, and `(1/2)/(1 + δ/3) ≥ 1/4` for `δ ≤ 3`; the
consumer's free constant absorbs the change from `−δ²np/2`.

## E17 — Bernstein's inequality needs a measurability hypothesis

`External.Bernstein` (`IdlaCyl/External/Basic.lean`) states the deviation bound for
`{0,1}`-valued `X_i` with `iIndepFun X P` and `∫ ω, X i ω ∂P = p i`, without assuming that the
`X_i` are measurable. `ProbabilityTheory.iIndepFun` is a statement about the σ-algebras
`(mβ i).comap (X i)` only and does not make `X_i` measurable. A `{0,1}`-valued function that is
not almost everywhere strongly measurable has Bochner integral `0`, so the hypothesis
`∫ X_i = p_i` holds with `p_i = 0` while `X_i` is arbitrary; a Bernstein set gives a
counterexample, written out in the header of `IdlaCyl/External/Discharge/Bernstein.lean`. As
stated, `External.Bernstein` is therefore false, and no proof uses it. The paper's `X_i`
(`tex:1314-1320`) are indicators of measurable events, and the form with the hypothesis
`∀ i, Measurable (X i)` is proved as `bernstein_of_latticeProb_of_measurable` and is the one
used. `External.Chernoff` is not affected: there `p` is a single constant, `p = 0` gives an
empty event and `p ≠ 0` forces integrability.

## E18 — the printed proof of `pr:reduction` has a gap; the printed statement is true

* **Printed:** `pr:reduction` (`tex:1445-1449`), proved at `tex:1451-1452` as "Step 1 of the
  proof of" Silvestri's Theorem 4, gives a coupling of `A(T)` with a shifted `A(T')`,
  `T' + Nk = T`, `T' ≤ α T^♯` with `α ≤ 1`; `th:max_fluct` (`tex:268-280`) uses it for
  `T > T^♯`.
* **The gap:** the claim that "α may be made as small as desired" fails for the layer-by-layer
  reduction, whose reduced time has a floor of order `ab · T^♯`, and the cited Step 1 compares
  `A(T)` with a process of size `T + Nβ`, so it does not supply the coupling as stated.
* **The printed statement is true.** `Frozen.pr_reduction` proves it, with a size cutoff that
  is uniform over all bases (`Reduction.block_pr_reduction`, `Support/Reduction/Block/`). The
  argument differs from the printed one: it fills blocks of `H = ⌈B √τ_mix log N⌉` layers with
  `M = 2NH` particles stopped at the top of each block (the block filling follows from the
  stopped inner bound, `stopped_block_fill`), compares the deep and the shallow paused particles
  with canonical growth through Silvestri's Proposition 2, grows the buffer block from particles
  already counted, and iterates `t ↦ t − NH ⌊t/M⌋` until `t < 6NH`, which is below `T^♯` once
  `log N ≥ 6(B + 1)`.
* **Three stronger statements.** Three further registered statements, not in the paper,
  strengthen `pr:reduction`: `pr_reduction_quant` (every base and every `T ≥ 1`, `T' < 6NH` with
  `H = ⌈4 √τ_rel log(2U²/ε)⌉`, `U = max(N, T)`, failure probability at most `ε`),
  `pr_reduction_strong` (`1 ≤ T ≤ N^m`, `T' ≤ D N √τ_rel log N` and `T' ≤ √2 D N √τ_mix log N`,
  `D = 6(4(ν + 2m + 2) + 1)`, failure probability at most `N^{−(ν+1)}`, cutoff only `N ≥ 3`) and
  `pr_reduction_alpha_strong` (`T' ≤ α T^♯` for every `α > 0` once `N ≥ max(3, ⌈exp(√2 D/α)⌉)`).
  All three couple the two processes at every later time `T + s`, `T' + s`. Their comparisons
  use an explicit coupling of first-hit distributions (the spectral first-hit law, with total
  variation at most `√N e^{−H/√τ_rel}`) in place of Silvestri's Proposition 2, so no size
  cutoff is needed.
* **Theorem 1.1** is proved through a finite-coefficient form of the reduction,
  `pr_reduction_alpha`, which suffices because the constant `C` absorbs `√α`
  (`max_fluct_of_reduction`, `Support/MaxFluctOfReduction.lean`).

## E19 — the reading of `clm:Q-W`

The claim sits in an asymptotic argument whose event `E` is
  itself defined only "for `N` large enough" (`tex:910`), its standing assumptions (`a:spectral`,
  the growth condition) are limits in `N`, and it is used only as `N → ∞`. `clm_q_w_v3` reads
  it this way: the inequality holds for `N` beyond a threshold that depends on the setup, with
  a constant chosen from `K`, `α`, `y₀` before the setup. This formalization does not claim that
  the inequality fails at some `N`.

## E21 — Silvestri's Proposition 2: connectedness of the initial cluster, and a step of its proof

* **Source:** V. Silvestri, *Internal DLA on cylinder graphs: fluctuations and mixing*,
  Electron. Commun. Probab. 25 (2020), paper 61. Proposition 2 concerns "two IDLA processes
  with starting configurations A(0) = A′(0)", and IDLA is defined (Definition 2) from "any
  connected subset of V containing the rectangle R₀ and finitely many sites above level 0".
* **Encoding:** `External.silvestri_prop2` assumes that the initial cluster is connected in the
  cylinder graph (`SeedConnected`, `Support/CylGraph.lean`), as in the source. Its other
  departures from the source (vertex-transitive bases only, an added size cutoff `N₀`) weaken
  it. The reduction supplies connectedness (`Support/Reduction/SeedGrowth.lean`): the deep
  comparison applies the proposition to an exact rectangle (`seedConnected_R`); the shallow
  comparison applies it to seeds grown by IDLA from a rectangle with walkers started on its top
  layer, which are connected almost surely because each exit site is adjacent to the seed
  (`exitSite'_adj`, `layerGrowthLaw_not_seedConnected`); translation preserves connectedness
  (`seedConnected_image_vshift`).
* **A step of the printed proof.** The proof bounds the probability that the coupling fails
  by `P(τ_n^Y < 3γ′ τ_N log N) + P(X ≠ X′)`, a bound on the total time to reach level `n`; but
  the bridges are run over the number `s` of horizontal steps up to that time, and a long total
  time does not by itself give many horizontal steps. The proof here bounds `s` from below
  directly: fewer than `m` horizontal steps among the first `4m` steps has probability at most
  `e^{−m/2}` (Hoeffding), and a climb of `h` levels within `4m` steps has probability at most
  `e^{−h²/(4m)}` (`IdlaCyl/Support/Silvestri/TailBounds.lean`). The per-attempt failure bound and
  the conclusion of the proposition are unchanged.
* **Proof:** `External.silvestri_prop2_proved` (`External/Discharge/Silvestri.lean`) proves the
  proposition as encoded. For each pair of walkers it runs a ladder of first-passage blocks to
  the levels `h, 2h, …`, `h = ⌈13 √τ log N⌉`, with independent vertical parts, maximally coupled
  horizontal windows given the numbers of horizontal steps, and one shared continuation once
  the block ends agree; each attempt fails with probability at most `N^{−3}` (`holdFail`). The
  proof uses neither the connectedness of the initial cluster nor the bound on the total time.
