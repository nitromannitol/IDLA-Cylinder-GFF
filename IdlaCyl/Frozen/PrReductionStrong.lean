/-
A strengthening of Proposition `pr:reduction` (tex:1446-1449): the reduction in the polynomial range,
with explicit constants.

This is an additional statement, stronger than the published `pr:reduction`. It is not in the paper
and it does not replace the printed node `Frozen.pr_reduction` (`PrReduction.lean`).

Fix `ν > 0` and real `m ≥ 1`, and put `D = 6 (4 (ν + 2m + 2) + 1)` and `C = √2 D`. For every base
with `N ≥ 3` vertices and every integer `T` with `1 ≤ T ≤ N^m` there are integers `T' ≥ 1` and
`k ≥ 0` with `T' + Nk = T`,
  `T' ≤ min(T, D N √τ_rel log N)`  and  `T' ≤ C N √τ_mix log N`,
and a coupling of two IDLA processes started from `R_0` such that `A(T + s) = A_*(T' + s) + R_k`
holds for every `s ≥ 0` simultaneously with probability at least `1 - N^{-(ν+1)}`.

Compared with the printed statement: every `1 ≤ T ≤ N^m` (not only `T ≥ T^♯`); the reduced time is
at most `C N √τ_mix log N`, a factor `log N` below `T^♯ = N √τ_mix (log N)²`; the constants are
explicit and there is no unspecified size cutoff (only `N ≥ 3`); and the two processes agree at
every later addition, not only at time `T`.

Encoding: as in `PrReductionQuant.lean`; `τ_rel` is `S.relaxTime` for a diagonalisation
`S : SpectralData B`, `τ_mix` is `mixingTime B` (`tex:269`), and `N^m` is the real power.
Proved as `Reduction.pr_reduction_strong_proof` (`Support/Reduction/Block/QuantFinal.lean`).
-/
import IdlaCyl.Support.Reduction.Block.QuantFinal

namespace IdlaCyl.Frozen

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem pr_reduction_strong (ν : ℝ) (hν : 0 < ν) (m : ℝ) (hm : 1 ≤ m) (B : Base)
    (hN : 3 ≤ B.card) (S : SpectralData B) (T : ℕ) (hT : 1 ≤ T)
    (hTm : (T : ℝ) ≤ (B.card : ℝ) ^ m) :
    ∃ T' k : ℕ, 1 ≤ T' ∧ T' ≤ T ∧
      (T' : ℝ) ≤ 6 * (4 * (ν + 2 * m + 2) + 1) * B.card * Real.sqrt S.relaxTime *
        Real.log B.card ∧
      (T' : ℝ) ≤ Real.sqrt 2 * (6 * (4 * (ν + 2 * m + 2) + 1)) * B.card *
        Real.sqrt (mixingTime B) * Real.log B.card ∧
      T' + B.card * k = T ∧
      ∃ μ : Measure (TrajSeq B × TrajSeq B),
        μ.map (Prod.fst : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
        μ.map (Prod.snd : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
        ENNReal.ofReal (1 - (B.card : ℝ) ^ (-(ν + 1))) ≤
          μ {p | ∀ s : ℕ, clusterTraj B p.1 (T + s) =
            Reduction.shiftCluster B k (clusterTraj B p.2 (T' + s))}
-- FROZEN-STATEMENT-END
:=
  Reduction.pr_reduction_strong_proof ν hν m hm B hN S T hT hTm
