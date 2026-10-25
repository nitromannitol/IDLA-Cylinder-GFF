module

public import Mathlib

@[expose] public section

/-!
Variance identities for arbitrary probability measures, used in the
Efron–Stein step of the replacement lemma (`tex:828-848`).
-/

namespace ProbabilityTheory.ProductEfronStein

open MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

private theorem bounded_memLp {f : α → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable C (.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using hC x)

private theorem bounded_integrable {f : α → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  (bounded_memLp hf hC).integrable (by norm_num)

private theorem abs_integral_le {f : α → ℝ} {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    |∫ x, f x ∂μ| ≤ C := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := C)
      (.of_forall fun x => by simpa only [Real.norm_eq_abs] using hC x)

/-- Jensen's square inequality, with an explicit square-integrability guard. -/
theorem integral_sq_le (f : α → ℝ) (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  have h := variance_nonneg f μ
  rw [variance_eq_sub hf] at h
  exact sub_nonneg.mp h

/-- The independent-copy formula for variance, for a bounded measurable variable. -/
theorem iid_difference (f : α → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) :
    (∫ x, ∫ x', (f x - f x') ^ 2 ∂μ ∂μ) = 2 * variance f μ := by
  have hlp := bounded_memLp (μ := μ) hf hC
  have hi := hlp.integrable (by norm_num)
  have hs := hlp.integrable_sq
  have heq (x : α) :
      (∫ x', (f x - f x') ^ 2 ∂μ) =
        f x ^ 2 - 2 * f x * (∫ x', f x' ∂μ) + ∫ x', f x' ^ 2 ∂μ := by
    simp_rw [sub_sq]
    have hlin : Integrable (fun x' => 2 * f x * f x') μ := hi.const_mul (2 * f x)
    have hquad : Integrable (fun x' => f x ^ 2 - 2 * f x * f x') μ :=
      (integrable_const _).sub hlin
    rw [integral_add hquad hs, integral_sub (integrable_const (f x ^ 2)) hlin]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, integral_const_mul]
  simp_rw [heq]
  have hlin : Integrable (fun x => 2 * f x * ∫ x', f x' ∂μ) μ :=
    (hi.const_mul 2).mul_const _
  have hquad : Integrable (fun x => f x ^ 2 - 2 * f x * ∫ x', f x' ∂μ) μ := hs.sub hlin
  rw [integral_add hquad (integrable_const (∫ x', f x' ^ 2 ∂μ)),
    integral_sub hs hlin, variance_eq_sub hlp]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
    integral_mul_const, integral_const_mul, Pi.pow_apply]
  ring

/-- Law of total variance for a bounded measurable function on a product space. -/
theorem variance_prod (f : α × β → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ z, |f z| ≤ C) :
    variance f (μ.prod ν) =
      (∫ x, variance (fun y => f (x, y)) ν ∂μ) +
        variance (fun x => ∫ y, f (x, y) ∂ν) μ := by
  have hlp := bounded_memLp (μ := μ.prod ν) hf hC
  have hm : Measurable (fun x => ∫ y, f (x, y) ∂ν) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  have hmlp := bounded_memLp (μ := μ) hm (fun x => abs_integral_le (fun y => hC (x, y)))
  have hsq : Integrable (fun x => ∫ y, f (x, y) ^ 2 ∂ν) μ :=
    hlp.integrable_sq.integral_prod_left
  have hslice (x : α) : MemLp (fun y => f (x, y)) 2 ν := bounded_memLp (μ := ν)
    (hf.comp (measurable_const.prodMk measurable_id)) (fun y => hC (x, y))
  simp_rw [variance_eq_sub (hslice _)]
  simp only [Pi.pow_apply]
  rw [integral_sub hsq hmlp.integrable_sq, variance_eq_sub hlp, variance_eq_sub hmlp]
  simp only [Pi.pow_apply]
  rw [integral_prod _ hlp.integrable_sq, integral_prod _ (hlp.integrable (by norm_num))]
  ring

/-- Averaging one independent coordinate can only decrease the variance
in the other coordinate. -/
theorem variance_integral_le (f : α × β → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ z, |f z| ≤ C) :
    variance (fun x => ∫ y, f (x, y) ∂ν) μ ≤
      ∫ y, variance (fun x => f (x, y)) μ ∂ν := by
  have hi := bounded_integrable (μ := μ.prod ν) hf hC
  have hm : Measurable (fun x => ∫ y, f (x, y) ∂ν) :=
    hf.stronglyMeasurable.integral_prod_right'.measurable
  have hn : Measurable (fun y => ∫ x, f (x, y) ∂μ) :=
    hf.stronglyMeasurable.integral_prod_left'.measurable
  have hnint := bounded_integrable (μ := ν) hn
    (fun y => abs_integral_le (fun x => hC (x, y)))
  have hmlp := bounded_memLp (μ := μ) hm
    (fun x => abs_integral_le (fun y => hC (x, y)))
  have hcent : Measurable (fun z : α × β => f z - ∫ x, f (x, z.2) ∂μ) :=
    hf.sub (hn.comp measurable_snd)
  have hcbd (z : α × β) : |f z - ∫ x, f (x, z.2) ∂μ| ≤ C + C :=
    (abs_sub _ _).trans (add_le_add (hC z) (abs_integral_le (fun x => hC (x, z.2))))
  have hclp := bounded_memLp (μ := μ.prod ν) hcent hcbd
  have heq (x : α) :
      (∫ y, (f (x, y) - ∫ x', f (x', y) ∂μ) ∂ν) =
        (∫ y, f (x, y) ∂ν) - ∫ x', ∫ y, f (x', y) ∂ν ∂μ := by
    have hsliceint : Integrable (fun y => f (x, y)) ν :=
      bounded_integrable (hf.comp (measurable_const.prodMk measurable_id)) (fun y => hC (x, y))
    rw [integral_sub hsliceint hnint, integral_integral_swap (μ := μ) (ν := ν) (f := fun x y => f (x, y)) hi]
  rw [variance_eq_integral hm.aemeasurable]
  calc
    _ ≤ ∫ x, ∫ y, (f (x, y) - ∫ x', f (x', y) ∂μ) ^ 2 ∂ν ∂μ := by
      apply integral_mono (hmlp.sub (memLp_const _)).integrable_sq hclp.integrable_sq.integral_prod_left
      intro x
      change ((∫ y, f (x, y) ∂ν) - ∫ x', ∫ y, f (x', y) ∂ν ∂μ) ^ 2 ≤
        ∫ y, (f (x, y) - ∫ x', f (x', y) ∂μ) ^ 2 ∂ν
      rw [← heq x]
      exact integral_sq_le _ (bounded_memLp
        (hcent.comp (measurable_const.prodMk measurable_id)) (fun y => hcbd (x, y)))
    _ = ∫ y, ∫ x, (f (x, y) - ∫ x', f (x', y) ∂μ) ^ 2 ∂μ ∂ν :=
      integral_integral_swap hclp.integrable_sq
    _ = ∫ y, variance (fun x => f (x, y)) μ ∂ν := by
      apply integral_congr_ae
      exact .of_forall fun y => (variance_eq_integral
        ((hf.comp (measurable_id.prodMk measurable_const)).aemeasurable)).symm

/-- Tensorization of variance on a product of two arbitrary probability spaces. -/
theorem variance_prod_le (f : α × β → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ z, |f z| ≤ C) :
    variance f (μ.prod ν) ≤
      (∫ x, variance (fun y => f (x, y)) ν ∂μ) +
        ∫ y, variance (fun x => f (x, y)) μ ∂ν := by
  rw [variance_prod (μ := μ) (ν := ν) f hf C hC]
  exact add_le_add le_rfl (variance_integral_le (μ := μ) (ν := ν) f hf C hC)

end ProbabilityTheory.ProductEfronStein
