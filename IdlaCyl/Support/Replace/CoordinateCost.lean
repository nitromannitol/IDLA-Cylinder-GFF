module

public import IdlaCyl.Support.Replace.ProductEfronStein

@[expose] public section

/-!
The coordinate-sum form of the resampling cost in Efron–Stein
(`tex:828-848`). Each summand integrates against the full product law.
-/

namespace ProbabilityTheory.ProductEfronStein

open MeasureTheory
open scoped BigOperators

universe u
variable {α : Type u} [MeasurableSpace α]

/-- Replace a labelled coordinate of a finite product. -/
def replace : (n : ℕ) → Fin n → α → Space α n → Space α n
  | 0, i, _, _ => Fin.elim0 i
  | n + 1, i, x, z => Fin.cases (x, z.2) (fun j => (z.1, replace n j x z.2)) i

/-- Finite-product coordinate replacement is jointly measurable. -/
theorem measurable_replace (n : ℕ) (i : Fin n) :
    Measurable (fun z : Space α n × α => replace n i z.2 z.1) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact measurable_snd.prodMk (measurable_snd.comp measurable_fst)
    · exact (measurable_fst.comp measurable_fst).prodMk
        ((ih j).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

/-- Mean squared change under resampling a labelled coordinate. -/
noncomputable def coordinateCost (μ : ℕ → Measure α) (n : ℕ)
    (f : Space α n → ℝ) (i : Fin n) : ℝ :=
  ∫ z, ∫ x, (f z - f (replace n i x z)) ^ 2 ∂μ i ∂law μ n

private theorem coordinateCost_measurable {β : Type*} [MeasurableSpace β]
    (μ : ℕ → Measure α) [∀ i, IsProbabilityMeasure (μ i)] (n : ℕ)
    (f : β × Space α n → ℝ) (hf : Measurable f) (i : Fin n) :
    Measurable (fun b => coordinateCost μ n (fun z => f (b, z)) i) := by
  have hr : Measurable (fun z : (β × Space α n) × α =>
      replace n i z.2 z.1.2) :=
    (measurable_replace n i).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hd : Measurable (fun z : (β × Space α n) × α =>
      (f z.1 - f (z.1.1, replace n i z.2 z.1.2)) ^ 2) :=
    ((hf.comp measurable_fst).sub (hf.comp ((measurable_fst.comp measurable_fst).prodMk hr))).pow_const 2
  exact (hd.stronglyMeasurable.integral_prod_right' (ν := μ i)
    |>.integral_prod_right' (ν := law μ n)).measurable

private theorem difference_sq_abs_le (s t C : ℝ) (hC : 0 ≤ C)
    (hs : |s| ≤ C) (ht : |t| ≤ C) : |(s - t) ^ 2| ≤ 4 * C ^ 2 := by
  rw [abs_of_nonneg (sq_nonneg _)]
  have hb := (abs_sub s t).trans (add_le_add hs ht)
  have hh := (sq_le_sq₀ (abs_nonneg (s - t)) (show 0 ≤ C + C by linarith)).mpr hb
  rw [sq_abs] at hh
  nlinarith only [hh]

private theorem integral_abs_le {β : Type*} [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] (f : β → ℝ) (C : ℝ)
    (hf : ∀ z, |f z| ≤ C) : |∫ z, f z ∂ν| ≤ C := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := ν) (f := f) (C := C)
      (.of_forall fun z => by simpa only [Real.norm_eq_abs] using hf z)

private theorem coordinateCost_abs_le (μ : ℕ → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (n : ℕ) (f : Space α n → ℝ) (i : Fin n) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ z, |f z| ≤ C) : |coordinateCost μ n f i| ≤ 4 * C ^ 2 :=
  integral_abs_le (law μ n) _ _ fun z => integral_abs_le (μ i) _ _ fun x =>
    difference_sq_abs_le _ _ C hC (hbound z) (hbound (replace n i x z))

private theorem integrable_coordinateIntegrand (μ : ℕ → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)] (n : ℕ) (f : Space α n → ℝ) (hf : Measurable f)
    (i : Fin n) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ z, |f z| ≤ C) :
    Integrable (fun z => ∫ x, (f z - f (replace n i x z)) ^ 2 ∂μ i) (law μ n) := by
  have hm : Measurable (fun z : Space α n × α =>
      (f z.1 - f (replace n i z.2 z.1)) ^ 2) :=
    ((hf.comp measurable_fst).sub (hf.comp (measurable_replace n i))).pow_const 2
  refine Integrable.of_bound
    (hm.stronglyMeasurable.integral_prod_right' (ν := μ i)).aestronglyMeasurable
    (4 * C ^ 2) (.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact integral_abs_le (μ i) _ _ fun x =>
    difference_sq_abs_le _ _ C hC (hbound z) (hbound (replace n i x z))

/-- The recursive resampling cost is precisely the sum of the unconditional
mean squared changes in each coordinate. -/
theorem cost_eq_sum_coordinateCost (μ : ℕ → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (n : ℕ) (f : Space α n → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ z, |f z| ≤ C) :
    cost μ n f = ∑ i : Fin n, coordinateCost μ n f i := by
  induction n generalizing μ with
  | zero => simp only [cost, Fin.sum_univ_zero]
  | succ n ih =>
    let μtail := fun i => μ (i + 1)
    have hfirst : coordinateCost μ (n + 1) f 0 =
        ∫ y, ∫ x, ∫ x', (f (x, y) - f (x', y)) ^ 2 ∂μ 0 ∂μ 0 ∂law μtail n := by
      have hi := integrable_coordinateIntegrand μ (n + 1) f hf 0 C hC hbound
      change Integrable (fun z : α × Space α n =>
        ∫ x', (f z - f (x', z.2)) ^ 2 ∂μ 0) ((μ 0).prod (law μtail n)) at hi
      change (∫ z : α × Space α n, ∫ x', (f z - f (x', z.2)) ^ 2 ∂μ 0
        ∂(μ 0).prod (law μtail n)) = _
      exact integral_prod_symm _ hi
    have htail (i : Fin n) : coordinateCost μ (n + 1) f i.succ =
        ∫ x, coordinateCost μtail n (fun y => f (x, y)) i ∂μ 0 := by
      have hi := integrable_coordinateIntegrand μ (n + 1) f hf i.succ C hC hbound
      change Integrable (fun z : α × Space α n =>
        ∫ x', (f z - f (z.1, replace n i x' z.2)) ^ 2 ∂μtail i)
        ((μ 0).prod (law μtail n)) at hi
      change (∫ z : α × Space α n,
        ∫ x', (f z - f (z.1, replace n i x' z.2)) ^ 2 ∂μtail i
        ∂(μ 0).prod (law μtail n)) = _
      exact integral_prod _ hi
    have hslices (x : α) : Measurable (fun y => f (x, y)) :=
      hf.comp (measurable_const.prodMk measurable_id)
    have htailcost (x : α) : cost μtail n (fun y => f (x, y)) =
        ∑ i : Fin n, coordinateCost μtail n (fun y => f (x, y)) i :=
      ih μtail _ (hslices x) (fun y => hbound (x, y))
    have hint (i : Fin n) : Integrable
        (fun x => coordinateCost μtail n (fun y => f (x, y)) i) (μ 0) := by
      have hm := coordinateCost_measurable μtail n f hf i
      exact Integrable.of_bound hm.aestronglyMeasurable (4 * C ^ 2)
        (.of_forall fun x => by
          simpa only [Real.norm_eq_abs] using
            coordinateCost_abs_le μtail n (fun y => f (x, y)) i C hC (fun y => hbound (x, y)))
    rw [Fin.sum_univ_succ, hfirst]
    change _ + (∫ x, cost μtail n (fun y => f (x, y)) ∂μ 0) = _
    congr 1
    simp_rw [htailcost]
    rw [integral_finsetSum _ (fun i _ => hint i)]
    exact Finset.sum_congr rfl fun i _ => (htail i).symm

/-- Efron–Stein in the coordinate-sum form for arbitrary probability laws. -/
theorem efron_stein_coordinateCost (μ : ℕ → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (n : ℕ) (f : Space α n → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ z, |f z| ≤ C) :
    variance f (law μ n) ≤ (∑ i : Fin n, coordinateCost μ n f i) / 2 := by
  rw [← cost_eq_sum_coordinateCost μ n f hf C hC hbound]
  exact efron_stein μ n f hf C hC hbound

end ProbabilityTheory.ProductEfronStein
