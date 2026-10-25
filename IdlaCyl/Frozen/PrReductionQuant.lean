module

/-
A strengthening of Proposition `pr:reduction` (tex:1446-1449): the quantitative reduction.

This is an additional statement, stronger than the published `pr:reduction`. It is not in the paper
and it does not replace the printed node `Frozen.pr_reduction` (`PrReduction.lean`).

For a base with `N ≥ 2` vertices, an integer `T ≥ 1` and `0 < ε < 1`, put `U = max(N, T)`,
`ρ = √τ_rel`, where `τ_rel = 1/(1 - λ_2)` is the relaxation time of the lazy base kernel, and
`H = ⌈4 ρ log(2U²/ε)⌉`. There are deterministic integers `T' ≥ 1` and `k ≥ 0` with
`T' ≤ min(T, 6NH - 1)` and `T' + Nk = T`, and a coupling of two IDLA processes started from `R_0`,
such that `A(T + s) = A_*(T' + s) + R_k` holds for every `s ≥ 0` simultaneously with probability
at least `1 - ε`.

Compared with the printed statement: there is no size cutoff and no polynomial range (every base
and every `T ≥ 1`); the reduced time is of order `N √τ_rel log(U/ε)` instead of `T^♯`; the
probability bound is explicit; and the two processes agree at every later addition, not only at
time `T`.

Encoding, as in `PrReduction.lean`: a coupling is a measure on pairs of walk sequences whose two
marginals are the canonical IDLA driving law `idlaMeasure B` (walks started uniformly on layer 0 from
`A(0) = R_0`); the clusters are `clusterTraj B ω t`, and `A_*(t) + R_k` is
`Reduction.shiftCluster B k`. `τ_rel` is `S.relaxTime` for a diagonalisation `S : SpectralData B`
of the base kernel (`tex:301-311`); every base has one (`spectralData_exists`). `T' ≤ 6NH - 1` is
written `T' < 6 (N H)`, and `U` is the natural number `max N T`.

Proved in `Support/Reduction/Block/` (`Reduction.pr_reduction_quant_proof`): blocks of `H` layers are
filled by `2NH` particles stopped at the top of each block, and the two release lists of each round
are compared by an explicit coupling of first-hit distributions (the spectral first-hit law, with
total variation at most `√N e^{-H/√τ_rel}`) in place of Silvestri's Proposition 2.
-/
public import IdlaCyl.Support.Reduction.Block.QuantFinal

@[expose] public section

namespace IdlaCyl.Frozen

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem pr_reduction_quant (B : Base) (S : SpectralData B) (T : ℕ) (hT : 1 ≤ T)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ T' k : ℕ, 1 ≤ T' ∧ T' ≤ T ∧
      T' < 6 * (B.card * ⌈4 * Real.sqrt S.relaxTime *
        Real.log (2 * ((max B.card T : ℕ) : ℝ) ^ 2 / ε)⌉₊) ∧
      T' + B.card * k = T ∧
      ∃ μ : Measure (TrajSeq B × TrajSeq B),
        μ.map (Prod.fst : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
        μ.map (Prod.snd : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
        ENNReal.ofReal (1 - ε) ≤
          μ {p | ∀ s : ℕ, clusterTraj B p.1 (T + s) =
            Reduction.shiftCluster B k (clusterTraj B p.2 (T' + s))}
-- FROZEN-STATEMENT-END
:=
  Reduction.pr_reduction_quant_proof B S T hT ε hε hε1
