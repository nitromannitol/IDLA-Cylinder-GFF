import IdlaCyl.Support.Replace.Variance

/-!
Efron–Stein for products of arbitrary probability measures (`tex:828-848`).
The coordinate spaces need not be finite or countable. The recursive product
and resampling cost make induction on the number of coordinates explicit.
-/

namespace ProbabilityTheory.ProductEfronStein

open MeasureTheory

universe u

/-- Right-associated finite products of an arbitrary measurable coordinate space. -/
abbrev Space (α : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => α × Space α n

instance spaceMeasurableSpace (α : Type u) [MeasurableSpace α] (n : ℕ) :
    MeasurableSpace (Space α n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSpace PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (MeasurableSpace (α × Space α n))

variable {α : Type u} [MeasurableSpace α]

/-- The product law of the first `n` coordinates, allowing different laws. -/
noncomputable def law (μ : ℕ → Measure α) : (n : ℕ) → Measure (Space α n)
  | 0 => Measure.dirac PUnit.unit
  | n + 1 => (μ 0).prod (law (fun i => μ (i + 1)) n)

instance law_isProbability (μ : ℕ → Measure α) [∀ i, IsProbabilityMeasure (μ i)] (n : ℕ) :
    IsProbabilityMeasure (law μ n) := by
  induction n generalizing μ with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac PUnit.unit))
  | succ n ih =>
    letI := ih (fun i => μ (i + 1))
    exact inferInstanceAs (IsProbabilityMeasure ((μ 0).prod (law (fun i => μ (i + 1)) n)))

/-- The sum of the mean squared changes under independent resampling of each
coordinate. The first summand resamples the first coordinate and the second
recurses over the remaining coordinates. -/
noncomputable def cost (μ : ℕ → Measure α) : (n : ℕ) → (Space α n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, f =>
    (∫ y, ∫ x, ∫ x', (f (x, y) - f (x', y)) ^ 2 ∂μ 0 ∂μ 0
      ∂law (fun i => μ (i + 1)) n) +
    ∫ x, cost (fun i => μ (i + 1)) n (fun y => f (x, y)) ∂μ 0

private theorem cost_measurable {β : Type u} [MeasurableSpace β]
    (μ : ℕ → Measure α) [∀ i, IsProbabilityMeasure (μ i)] (n : ℕ)
    (f : β × Space α n → ℝ) (hf : Measurable f) :
    Measurable (fun b => cost μ n (fun z => f (b, z))) := by
  induction n generalizing β μ with
  | zero => exact measurable_const
  | succ n ih =>
    have hdiff : Measurable (fun z : ((β × Space α n) × α) × α =>
        (f (z.1.1.1, (z.1.2, z.1.1.2)) -
          f (z.1.1.1, (z.2, z.1.1.2))) ^ 2) := by fun_prop
    have hfirst := hdiff.stronglyMeasurable.integral_prod_right'
      (ν := μ 0) |>.integral_prod_right' (ν := μ 0)
        |>.integral_prod_right' (ν := law (fun i => μ (i + 1)) n)
    have htail : Measurable (fun z : (β × α) × Space α n =>
        f (z.1.1, (z.1.2, z.2))) := by fun_prop
    have hsecond := (ih (fun i => μ (i + 1)) _ htail).stronglyMeasurable.integral_prod_right'
      (ν := μ 0)
    exact hfirst.measurable.add hsecond.measurable

private theorem cost_abs_le (μ : ℕ → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (n : ℕ) (f : Space α n → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ z, |f z| ≤ C) : |cost μ n f| ≤ 4 * n * C ^ 2 := by
  induction n generalizing μ with
  | zero => simp only [cost, Nat.cast_zero, mul_zero, zero_mul, abs_zero, le_refl]
  | succ n ih =>
    have hdiff (x x' : α) (y : Space α n) :
        |(f (x, y) - f (x', y)) ^ 2| ≤ 4 * C ^ 2 := by
      have hb := (abs_sub _ _).trans (add_le_add (hf (x, y)) (hf (x', y)))
      rw [abs_of_nonneg (sq_nonneg _)]
      have hs := (sq_le_sq₀ (abs_nonneg (f (x, y) - f (x', y)))
        (show 0 ≤ C + C by linarith)).mpr hb
      rw [sq_abs] at hs
      nlinarith only [hs]
    have havg {δ : Type u} [MeasurableSpace δ] (η : Measure δ) [IsProbabilityMeasure η]
        (g : δ → ℝ) (D : ℝ) (hg : ∀ z, |g z| ≤ D) : |∫ z, g z ∂η| ≤ D := by
      simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
        norm_integral_le_of_norm_le_const (μ := η) (f := g) (C := D)
          (.of_forall fun z => by simpa only [Real.norm_eq_abs] using hg z)
    have hfirst : |∫ y, ∫ x, ∫ x', (f (x, y) - f (x', y)) ^ 2 ∂μ 0 ∂μ 0
        ∂law (fun i => μ (i + 1)) n| ≤ 4 * C ^ 2 :=
      havg (law (fun i => μ (i + 1)) n) _ _ fun y =>
        havg (μ 0) _ _ fun x => havg (μ 0) _ _ fun x' => hdiff x x' y
    have hsecond : |∫ x, cost (fun i => μ (i + 1)) n (fun y => f (x, y)) ∂μ 0|
        ≤ 4 * n * C ^ 2 := havg (μ 0) _ _ fun x => ih _ _ (fun y => hf (x, y))
    calc
      |cost μ (n + 1) f| ≤ _ := abs_add_le _ _
      _ ≤ 4 * C ^ 2 + 4 * n * C ^ 2 := add_le_add hfirst hsecond
      _ = 4 * (n + 1 : ℕ) * C ^ 2 := by push_cast; ring

/-- Twice the variance is bounded by the total independent-resampling cost.
Every coordinate has an arbitrary probability law; only the function is bounded. -/
theorem efron_stein_twice (μ : ℕ → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (n : ℕ) (f : Space α n → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ z, |f z| ≤ C) :
    2 * variance f (law μ n) ≤ cost μ n f := by
  induction n generalizing μ with
  | zero =>
    change 2 * variance f (Measure.dirac PUnit.unit) ≤ 0
    rw [variance_dirac]
    norm_num
  | succ n ih =>
    let ν := law (fun i => μ (i + 1)) n
    have hvar := variance_prod_le (μ := μ 0) (ν := ν) f hf C hbound
    have hslice (x : α) : Measurable (fun y => f (x, y)) :=
      hf.comp (measurable_const.prodMk measurable_id)
    have hcostm : Measurable (fun x => cost (fun i => μ (i + 1)) n
        (fun y => f (x, y))) := cost_measurable _ _ f hf
    have hcostint : Integrable (fun x => cost (fun i => μ (i + 1)) n
        (fun y => f (x, y))) (μ 0) :=
      (MemLp.of_bound (p := 1) hcostm.aestronglyMeasurable (4 * n * C ^ 2)
        (.of_forall fun x => by
          simpa only [Real.norm_eq_abs] using
            cost_abs_le _ n _ C hC (fun y => hbound (x, y)))).integrable le_rfl
    have hvm : Measurable (fun x => variance (fun y => f (x, y)) ν) := by
      have heq (x : α) := variance_eq_sub (μ := ν) (MemLp.of_bound (p := 2)
        (hslice x).aestronglyMeasurable C (.of_forall fun y => by
          simpa only [Real.norm_eq_abs] using hbound (x, y)))
      simp_rw [heq]
      simp only [Pi.pow_apply]
      exact (hf.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable.sub
        (hf.stronglyMeasurable.integral_prod_right'.measurable.pow_const 2)
    have hvbd (x : α) : |variance (fun y => f (x, y)) ν| ≤ C ^ 2 := by
      rw [abs_of_nonneg (variance_nonneg _ _)]
      refine (variance_le_expectation_sq (hslice x).aestronglyMeasurable).trans ?_
      have hsint : Integrable (fun y => f (x, y) ^ 2) ν :=
        (MemLp.of_bound (p := 2) (hslice x).aestronglyMeasurable C
          (.of_forall fun y => by
            simpa only [Real.norm_eq_abs] using hbound (x, y))).integrable_sq
      have hsq (y : Space α n) : f (x, y) ^ 2 ≤ C ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hbound (x, y))
      simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, Pi.pow_apply] using
        integral_mono hsint (integrable_const (C ^ 2)) hsq
    have hvint : Integrable (fun x => variance (fun y => f (x, y)) ν) (μ 0) :=
      (MemLp.of_bound (p := 1) hvm.aestronglyMeasurable (C ^ 2)
        (.of_forall fun x => by simpa only [Real.norm_eq_abs] using hvbd x)).integrable le_rfl
    have hind : 2 * (∫ x, variance (fun y => f (x, y)) ν ∂μ 0) ≤
        ∫ x, cost (fun i => μ (i + 1)) n (fun y => f (x, y)) ∂μ 0 := by
      rw [← integral_const_mul]
      exact integral_mono (hvint.const_mul 2) hcostint fun x =>
        ih _ _ (hslice x) (fun y => hbound (x, y))
    have hid : (∫ y, ∫ x, ∫ x', (f (x, y) - f (x', y)) ^ 2 ∂μ 0 ∂μ 0 ∂ν) =
        2 * ∫ y, variance (fun x => f (x, y)) (μ 0) ∂ν := by
      have hiid (y : Space α n) :
          (∫ x, ∫ x', (f (x, y) - f (x', y)) ^ 2 ∂μ 0 ∂μ 0) =
            2 * variance (fun x => f (x, y)) (μ 0) :=
        iid_difference (μ := μ 0) (fun x => f (x, y))
          (hf.comp (measurable_id.prodMk measurable_const)) C (fun x => hbound (x, y))
      simp_rw [hiid]
      exact integral_const_mul _ _
    change 2 * variance f ((μ 0).prod ν) ≤ _
    change _ ≤ (∫ y, ∫ x, ∫ x', (f (x, y) - f (x', y)) ^ 2 ∂μ 0 ∂μ 0 ∂ν) + _
    rw [hid]
    linarith

/-- Efron–Stein with the usual factor `1/2`, including the empty product. -/
theorem efron_stein (μ : ℕ → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (n : ℕ) (f : Space α n → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ z, |f z| ≤ C) :
    variance f (law μ n) ≤ cost μ n f / 2 := by
  have h := efron_stein_twice μ n f hf C hC hbound
  linarith

end ProbabilityTheory.ProductEfronStein
