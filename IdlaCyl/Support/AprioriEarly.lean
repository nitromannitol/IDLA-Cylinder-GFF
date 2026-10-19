/-
The canonical `pr:apriori` early outer tail (`paper/idla-cylinder-gff.tex:561-566`),
part (a), on the `TrajSeq`/`idlaMeasure` carrier.

The reduction is the layer-union tail of `Support/CanonicalApriori.lean` with
`h = β log N`, together with the binomial estimate `μ_{m+1}(T) ≤ N^{-m} C(T,m+1)`
(`IdlaCyl.layerMean_le_binom`, `Support/LayerRecurrence.lean`).  The remaining
analytic step is the evaluation of the resulting binomial tail sum
`∑_{m > β log N} N^{-(m-1)} C(T,m) ≤ N^{-(β-1)}`, which is
`apriori_tail_le` below.

Everything is on the canonical carrier; no `Driver`/`driverLaw`/`cluster`.
-/
import IdlaCyl.Support.CanonicalApriori
import Mathlib.Analysis.SpecialFunctions.Stirling

namespace IdlaCyl

open MeasureTheory
open scoped ENNReal BigOperators

/-- **The reduction of part (a)** (`tex:561-566`): the layer-union tail bound at
`h = β log N`, with each layer mass replaced by its binomial estimate. -/
theorem idlaMeasure_apriori_le (B : Base) (hrec : External.LazyRwRecurrent)
    (T : ℕ) (β : ℝ) (hβ : 0 < β) (hN : 1 ≤ B.card) :
    idlaMeasure B {ω : TrajSeq B |
        ¬ (clusterTraj B ω T ⊆ R B (β * Real.log (B.card : ℝ)))}
      ≤ ∑' m : ℤ, (if β * Real.log (B.card : ℝ) < m then
          ENNReal.ofReal ((1 / (B.card : ℝ)) ^ (m - 1).toNat
            * (Nat.choose T ((m - 1).toNat + 1) : ℝ)) else 0) :=
  idlaMeasure_not_subset_le_tsum_binom B hrec T (β * Real.log (B.card : ℝ))
    (mul_nonneg hβ.le (Real.log_nonneg (by exact_mod_cast hN)))

/-- **`pr:apriori`(a), reduced to the binomial tail sum.**

The one remaining input is the explicit analytic evaluation of the binomial
tail at `h = β log N`: for `C > 0`, `β > max 1 (e² C)`, there is `N₀` with, for
all `N ≥ N₀` and all `T` with `(T:ℝ) ≤ C N log N`,

  `∑_{m > β log N} N^{-(m-1)} C(T, m) ≤ N^{-(β-1)}`   (`apriori_tail`).

The proof of that display (the paper's `tex:618-620`) is: bound
`C(T,m) ≤ T^m/m!`, use Stirling's lower bound `m! ≥ (m/e)^m`
(`Stirling.le_factorial_stirling`) to get `N^{-(m-1)} C(T,m) ≤ N (eT/(Nm))^m`,
and then `T ≤ C N log N`, `m ≥ β log N` and `β > e² C` give
`≤ N (eC/β)^m` with `eC/β < e^{-1}`.  Summing the geometric series
`∑_{m ≥ β log N} N (eC/β)^m ≤ 2 N (eC/β)^{β log N}` and using the strict slack
`log(eC/β) < -1` (so `(eC/β)^{β log N} ≤ N^{-β} N^{-βδ}` for some `δ > 0`)
absorbs the factor `2` for `N` large, giving `N^{1-β} = N^{-(β-1)}`. -/
theorem apriori_early_of_tail (hrec : External.LazyRwRecurrent) (C : ℝ) (hC : 0 < C)
    (β : ℝ) (hβ : max 1 (Real.exp 2 * C) < β)
    (htail : ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ T : ℕ,
      (T : ℝ) ≤ C * (N : ℝ) * Real.log (N : ℝ) →
        ∑' m : ℤ, (if β * Real.log (N : ℝ) < m then
            ENNReal.ofReal ((1 / (N : ℝ)) ^ (m - 1).toNat
              * (Nat.choose T ((m - 1).toNat + 1) : ℝ)) else 0)
          ≤ ENNReal.ofReal ((N : ℝ) ^ (-(β - 1)))) :
    ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card → ∀ T : ℕ,
      (T : ℝ) ≤ C * (B.card : ℝ) * Real.log (B.card : ℝ) →
        idlaMeasure B {ω : TrajSeq B |
            ¬ (clusterTraj B ω T ⊆ R B (β * Real.log (B.card : ℝ)))}
          ≤ ENNReal.ofReal ((B.card : ℝ) ^ (-(β - 1))) := by
  obtain ⟨N₀, hN₀⟩ := htail
  have _hC : 0 < C := hC
  refine ⟨max N₀ 1, fun B hB T hT => ?_⟩
  have hcard : 1 ≤ B.card := le_trans (le_max_right _ _) hB
  have hβpos : 0 < β := lt_trans zero_lt_one (lt_of_le_of_lt (le_max_left _ _) hβ)
  exact (idlaMeasure_apriori_le B hrec T β hβpos hcard).trans
    (hN₀ B.card (le_trans (le_max_left _ _) hB) T hT)

end IdlaCyl
