/-
The cited martingale central limit theorem as an explicit hypothesis carrier,
in the real Mathlib API.

`thm:martingale-CLT` (`tex:882-892`) is McLeish's theorem, imported from the
literature and carried here as a `def … : Prop` — never as an axiom or a
`theorem`.  The frozen `IdlaCyl.External.thm_martingale_clt` predates the API and
takes four *uninterpreted* predicates (`IsMartingaleDiffArray`,
`TendstoInProbability`, `TendstoInDistribution`, `Normal`), which makes it a
refutable schema.  This carrier instead uses Mathlib's actual
`Martingale`, `TendstoInMeasure`, `TendstoInDistribution` and `gaussianReal`, so
a downstream consumer cannot satisfy it by instantiating the notions with
`fun _ _ => False`, and it can be discharged (or refuted) honestly.
-/
import IdlaCyl.Support.Martingale
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real

namespace IdlaCyl

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal NNReal

/-- **`thm:martingale-CLT`** (`tex:882-892`, McLeish 1974, Hall–Heyde
Theorem 3.2): a martingale difference array with uniformly bounded maximum
square, vanishing maximum increment, and quadratic variation converging to
`σ² > 0` has sums converging in distribution to `N(0, σ²)`. -/
def MartingaleCLT : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : ℕ → Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (𝒳 : ℕ → ℕ → Ω → ℝ) (tn : ℕ → ℕ) (htn : ∀ n, 0 < tn n) (σsq : ℝ≥0),
    0 < σsq →
    (∀ n, Martingale (fun k => ∑ j ∈ Finset.range k, 𝒳 n j) (ℱ n) P) →
    (∃ C : ℝ, ∀ n, ∫ ω,
      (Finset.range (tn n)).sup' (Finset.nonempty_range_iff.mpr (htn n).ne')
        (fun k => 𝒳 n k ω ^ 2) ∂P ≤ C) →
    TendstoInMeasure P
      (fun n ω => (Finset.range (tn n)).sup' (Finset.nonempty_range_iff.mpr (htn n).ne')
        (fun k => |𝒳 n k ω|)) atTop (fun _ => 0) →
    TendstoInMeasure P
      (fun n ω => ∑ k ∈ Finset.range (tn n), 𝒳 n k ω ^ 2) atTop (fun _ => (σsq : ℝ)) →
    TendstoInDistribution
      (fun n ω => ∑ k ∈ Finset.range (tn n), 𝒳 n k ω) atTop (id : ℝ → ℝ)
      (fun _ => P) (gaussianReal 0 σsq)

end IdlaCyl
