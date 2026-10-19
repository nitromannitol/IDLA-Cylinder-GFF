import IdlaCyl.Support.Replace.FiniteDependence
import IdlaCyl.Support.Replace.CoordinateCost

/-!
Efron–Stein on an infinite independent product in its literal resampling form
(`tex:828-848`). The finite-prefix condition expresses dependence on the
first `T` trajectories, without restricting the support of their laws.
-/

namespace ProbabilityTheory.ProductEfronStein

open MeasureTheory
open scoped BigOperators

universe u
variable {α : Type u} [MeasurableSpace α]

omit [MeasurableSpace α] in
/-- Prefix restriction commutes with replacement of a consumed coordinate. -/
theorem take_update (n : ℕ) (ω : ℕ → α) (i : Fin n) (x : α) :
    take n (Function.update ω (i : ℕ) x) = replace n i x (take n ω) := by
  induction n generalizing ω with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [take_succ, take_succ]
      change (x, take n (fun j => Function.update ω 0 x (j + 1))) =
        (x, take n (fun j => ω (j + 1)))
      congr 1
    · rw [take_succ, take_succ]
      change (Function.update ω ((j : ℕ) + 1) x 0,
        take n (fun k => Function.update ω ((j : ℕ) + 1) x (k + 1))) =
        (ω 0, replace n j x (take n (fun k => ω (k + 1))))
      rw [Function.update_of_ne (show (0 : ℕ) ≠ (j : ℕ) + 1 by omega)]
      congr 1
      rw [← ih (fun k => ω (k + 1)) j]
      apply congrArg (take n)
      funext k
      by_cases hk : k = (j : ℕ)
      · subst k
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hk,
          Function.update_of_ne (show k + 1 ≠ (j : ℕ) + 1 by omega)]

/-- The finite-product coordinate cost equals independent replacement under
the original infinite product whenever the observable has finite dependence. -/
theorem coordinateCost_finiteDependence (μ : ℕ → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (n : ℕ) (tail : ℕ → α) (f : (ℕ → α) → ℝ) (hf : Measurable f)
    (hdep : ∀ ω ω', (∀ j, j < n → ω j = ω' j) → f ω = f ω') (i : Fin n) :
    coordinateCost μ n (fun z => f (extend n z tail)) i =
      ∫ ω, ∫ x, (f ω - f (Function.update ω (i : ℕ) x)) ^ 2 ∂μ i
        ∂Measure.infinitePi μ := by
  let g : Space α n → ℝ := fun z => f (extend n z tail)
  have hg : Measurable g := hf.comp (measurable_extend n tail)
  have hrepr (ω : ℕ → α) : f ω = g (take n ω) :=
    hdep _ _ (fun j hj => (extend_take_eq n ω tail j hj).symm)
  have hd : Measurable (fun z : Space α n × α =>
      (g z.1 - g (replace n i z.2 z.1)) ^ 2) :=
    ((hg.comp measurable_fst).sub (hg.comp (measurable_replace n i))).pow_const 2
  have hm : Measurable (fun z => ∫ x, (g z - g (replace n i x z)) ^ 2 ∂μ i) :=
    hd.stronglyMeasurable.integral_prod_right'.measurable
  have hp := measurePreserving_take μ n
  calc
    _ = ∫ ω, ∫ x, (g (take n ω) - g (replace n i x (take n ω))) ^ 2 ∂μ i
        ∂Measure.infinitePi μ := by
      unfold coordinateCost
      rw [← hp.map_eq, integral_map hp.aemeasurable hm.aestronglyMeasurable]
    _ = _ := by
      apply integral_congr_ae
      refine .of_forall fun ω => ?_
      apply integral_congr_ae
      refine .of_forall fun x => ?_
      change (g (take n ω) - g (replace n i x (take n ω))) ^ 2 =
        (f ω - f (Function.update ω (i : ℕ) x)) ^ 2
      rw [hrepr ω, hrepr (Function.update ω (i : ℕ) x), take_update]

/-- Efron–Stein for an arbitrary infinite independent product, in the usual
sum of independent one-coordinate replacement costs. -/
theorem efron_stein_infinitePi_update (μ : ℕ → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (n : ℕ) (tail : ℕ → α) (f : (ℕ → α) → ℝ) (hf : Measurable f)
    (hdep : ∀ ω ω', (∀ j, j < n → ω j = ω' j) → f ω = f ω')
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ ω, |f ω| ≤ C) :
    variance f (Measure.infinitePi μ) ≤
      (∑ i : Fin n, ∫ ω, ∫ x, (f ω - f (Function.update ω (i : ℕ) x)) ^ 2
        ∂μ i ∂Measure.infinitePi μ) / 2 := by
  have h := efron_stein_finiteDependence μ n tail f hf hdep C hC hbound
  rw [cost_eq_sum_coordinateCost μ n (fun z => f (extend n z tail))
    (hf.comp (measurable_extend n tail)) C hC
    (fun z => hbound (extend n z tail))] at h
  simpa only [coordinateCost_finiteDependence μ n tail f hf hdep] using h

end ProbabilityTheory.ProductEfronStein
