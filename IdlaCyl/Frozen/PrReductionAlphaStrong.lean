module

/-
A strengthening of Proposition `pr:reduction` (tex:1446-1449): an arbitrary coefficient `α > 0` in
`T' ≤ α T^♯`, with an explicit size cutoff.

This is an additional statement, stronger than the published `pr:reduction`. It is not in the paper
and it does not replace the printed node `Frozen.pr_reduction` (`PrReduction.lean`).

Fix `ν > 0`, real `m ≥ 1` and `α > 0`, and put `C = √2 · 6 (4 (ν + 2m + 2) + 1)` and
`N₀ = max(3, ⌈exp(C/α)⌉)`. For every base with `N ≥ N₀` vertices and every integer `T` with
`1 ≤ T ≤ N^m` there are integers `T' ≥ 1` and `k ≥ 0` with `T' ≤ α T^♯` and `T' + Nk = T`, and a
coupling of two IDLA processes started from `R_0` such that `A(T + s) = A_*(T' + s) + R_k` holds for
every `s ≥ 0` simultaneously with probability at least `1 - N^{-(ν+1)}`.

With `α = 1` and `T ≥ T^♯` this contains the printed statement. It is stronger in four ways: every
coefficient `α > 0`; every `1 ≤ T ≤ N^m`; an explicit cutoff `N₀(ν, m, α)` that is uniform over
bases; and agreement at every later addition.

Encoding: as in `PrReduction.lean`; `T^♯ = N √τ_mix (log N)²` is `Defs.sharp B`.
Proved as `Reduction.pr_reduction_alpha_strong_proof` (`Support/Reduction/Block/QuantFinal.lean`).
-/
public import IdlaCyl.Support.Reduction.Block.QuantFinal

@[expose] public section

namespace IdlaCyl.Frozen

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem pr_reduction_alpha_strong (ν : ℝ) (hν : 0 < ν) (m : ℝ) (hm : 1 ≤ m) (α : ℝ)
    (hα : 0 < α) (B : Base)
    (hN : max 3 ⌈Real.exp (Real.sqrt 2 * (6 * (4 * (ν + 2 * m + 2) + 1)) / α)⌉₊ ≤ B.card)
    (T : ℕ) (hT : 1 ≤ T) (hTm : (T : ℝ) ≤ (B.card : ℝ) ^ m) :
    ∃ T' k : ℕ, 1 ≤ T' ∧ (T' : ℝ) ≤ α * Defs.sharp B ∧ T' + B.card * k = T ∧
      ∃ μ : Measure (TrajSeq B × TrajSeq B),
        μ.map (Prod.fst : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
        μ.map (Prod.snd : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
        ENNReal.ofReal (1 - (B.card : ℝ) ^ (-(ν + 1))) ≤
          μ {p | ∀ s : ℕ, clusterTraj B p.1 (T + s) =
            Reduction.shiftCluster B k (clusterTraj B p.2 (T' + s))}
-- FROZEN-STATEMENT-END
:=
  Reduction.pr_reduction_alpha_strong_proof ν hν m hm α hα B hN T hT hTm
