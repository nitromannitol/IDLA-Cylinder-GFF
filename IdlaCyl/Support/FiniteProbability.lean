module

public import Mathlib

@[expose] public section

set_option autoImplicit false

/-!
# Finite probability from weighted sums

All probability identities here are proved directly from nonnegative weights
summing to one. In particular, neither conditional expectation nor a variance
inequality is a field of the input structure. The separate stochastic-model
construction for infinite cylinder trajectories is NOT asserted by this file.
-/

namespace IdlaCyl

open scoped BigOperators
noncomputable section

structure FiniteLaw (α : Type*) [Fintype α] where
  weight : α → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

namespace FiniteLaw

variable {α β : Type*} [Fintype α] [Fintype β]

def expect (μ : FiniteLaw α) (f : α → ℝ) : ℝ := ∑ x, μ.weight x * f x

def variance (μ : FiniteLaw α) (f : α → ℝ) : ℝ :=
  μ.expect (fun x => f x ^ 2) - (μ.expect f) ^ 2

theorem expect_congr (μ : FiniteLaw α) {f g : α → ℝ}
    (h : ∀ x, f x = g x) : μ.expect f = μ.expect g := by
  unfold expect
  exact Finset.sum_congr rfl (fun x _ => congrArg (μ.weight x * ·) (h x))

theorem expect_mono (μ : FiniteLaw α) {f g : α → ℝ}
    (h : ∀ x, f x ≤ g x) : μ.expect f ≤ μ.expect g := by
  unfold expect
  exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonneg x))

theorem expect_nonneg (μ : FiniteLaw α) {f : α → ℝ}
    (h : ∀ x, 0 ≤ f x) : 0 ≤ μ.expect f := by
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x) (h x))

@[simp] theorem expect_const (μ : FiniteLaw α) (c : ℝ) :
    μ.expect (fun _ => c) = c := by
  unfold expect
  rw [← Finset.sum_mul, μ.total, one_mul]

@[simp] theorem expect_add (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.expect (fun x => f x + g x) = μ.expect f + μ.expect g := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

@[simp] theorem expect_sub (μ : FiniteLaw α) (f g : α → ℝ) :
    μ.expect (fun x => f x - g x) = μ.expect f - μ.expect g := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem expect_const_mul (μ : FiniteLaw α) (c : ℝ) (f : α → ℝ) :
    μ.expect (fun x => c * f x) = c * μ.expect f := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

@[simp] theorem expect_mul_const (μ : FiniteLaw α) (f : α → ℝ) (c : ℝ) :
    μ.expect (fun x => f x * c) = μ.expect f * c := by
  unfold expect
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The variance identity is derived, rather than used as an assumption. -/
theorem expect_centered_sq (μ : FiniteLaw α) (f : α → ℝ) :
    μ.expect (fun x => (f x - μ.expect f) ^ 2) = μ.variance f := by
  have h : (fun x => (f x - μ.expect f) ^ 2) =
      (fun x => f x ^ 2 - (2 * μ.expect f) * f x + (μ.expect f) ^ 2) := by
    funext x
    ring
  rw [h, expect_add, expect_sub, expect_const_mul, expect_const]
  unfold variance
  ring

theorem variance_nonneg (μ : FiniteLaw α) (f : α → ℝ) :
    0 ≤ μ.variance f := by
  rw [← expect_centered_sq]
  exact μ.expect_nonneg (fun x => sq_nonneg _)

/-- Jensen for the square, proved from a nonnegative finite sum of squares. -/
theorem expect_sq_le (μ : FiniteLaw α) (f : α → ℝ) :
    (μ.expect f) ^ 2 ≤ μ.expect (fun x => f x ^ 2) := by
  have h := μ.variance_nonneg f
  unfold variance at h
  linarith

theorem expect_comm (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α → β → ℝ) :
    μ.expect (fun x => ν.expect (f x)) =
      ν.expect (fun y => μ.expect (fun x => f x y)) := by
  simp only [expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- Independent product, constructed from the two marginal weights. -/
def prod (μ : FiniteLaw α) (ν : FiniteLaw β) : FiniteLaw (α × β) where
  weight z := μ.weight z.1 * ν.weight z.2
  nonneg z := mul_nonneg (μ.nonneg z.1) (ν.nonneg z.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ν.total, mul_one, μ.total]

@[simp] theorem expect_prod (μ : FiniteLaw α) (ν : FiniteLaw β)
    (f : α × β → ℝ) :
    (μ.prod ν).expect f = μ.expect (fun x => ν.expect (fun y => f (x, y))) := by
  simp only [expect, prod, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Exact independent-copy identity, including zero variance. -/
theorem iid_difference_eq (μ : FiniteLaw α) (f : α → ℝ) :
    μ.expect (fun x => μ.expect (fun y => (f x - f y) ^ 2)) =
      2 * μ.variance f := by
  have inner (x : α) :
      μ.expect (fun y => (f x - f y) ^ 2) =
        f x ^ 2 - (2 * μ.expect f) * f x + μ.expect (fun y => f y ^ 2) := by
    calc
      μ.expect (fun y => (f x - f y) ^ 2) =
          μ.expect (fun y => f x ^ 2 - (2 * f x) * f y + f y ^ 2) := by
        apply μ.expect_congr
        intro y
        ring
      _ = _ := by
        rw [expect_add, expect_sub, expect_const, expect_const_mul]
        ring
  calc
    μ.expect (fun x => μ.expect (fun y => (f x - f y) ^ 2)) =
        μ.expect (fun x => f x ^ 2 - (2 * μ.expect f) * f x +
          μ.expect (fun y => f y ^ 2)) := μ.expect_congr inner
    _ = 2 * μ.variance f := by
      rw [expect_add, expect_sub, expect_const_mul, expect_const]
      unfold variance
      ring

/-- Law of total variance on a product, with no conditional-expectation API. -/
theorem variance_prod (μ : FiniteLaw α) (ν : FiniteLaw β) (f : α → β → ℝ) :
    (μ.prod ν).variance (fun z => f z.1 z.2) =
      μ.expect (fun x => ν.variance (f x)) +
        μ.variance (fun x => ν.expect (f x)) := by
  simp only [variance, expect_prod, expect_sub]
  ring

/-- Averaging an independent coordinate can only decrease variance. -/
theorem variance_expect_le (μ : FiniteLaw α) (ν : FiniteLaw β)
    (f : α → β → ℝ) :
    μ.variance (fun x => ν.expect (f x)) ≤
      ν.expect (fun y => μ.variance (fun x => f x y)) := by
  have h : μ.expect (fun x => μ.expect (fun x' =>
      (ν.expect (f x) - ν.expect (f x')) ^ 2)) ≤
      μ.expect (fun x => μ.expect (fun x' =>
        ν.expect (fun y => (f x y - f x' y) ^ 2))) := by
    apply μ.expect_mono
    intro x
    apply μ.expect_mono
    intro x'
    rw [← ν.expect_sub]
    exact ν.expect_sq_le (fun y => f x y - f x' y)
  have rearrange : μ.expect (fun x => μ.expect (fun x' =>
      ν.expect (fun y => (f x y - f x' y) ^ 2))) =
      ν.expect (fun y => μ.expect (fun x => μ.expect (fun x' =>
        (f x y - f x' y) ^ 2))) := by
    calc
      _ = μ.expect (fun x => ν.expect (fun y => μ.expect (fun x' =>
          (f x y - f x' y) ^ 2))) := by
        apply μ.expect_congr
        intro x
        exact μ.expect_comm ν _
      _ = _ := μ.expect_comm ν _
  rw [rearrange, iid_difference_eq] at h
  simp_rw [iid_difference_eq] at h
  rw [expect_const_mul] at h
  linarith

end FiniteLaw
end
end IdlaCyl

namespace IdlaCyl

open MeasureTheory

/-- The `FiniteLaw` of a probability measure on a finite measurable space with
measurable singletons.  This is the adapter that lets the finite concentration
machinery consume `Measure`-based statements. -/
noncomputable def FiniteLaw.ofMeasure {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ] : FiniteLaw α where
  weight x := μ.real {x}
  nonneg _ := measureReal_nonneg
  total := by
    have h : (∑ x, μ.real {x}) = ∫ x, (1 : ℝ) ∂μ := by
      rw [MeasureTheory.integral_fintype (μ := μ) (f := fun _ : α => (1 : ℝ))
        (integrable_const 1)]
      simp [smul_eq_mul]
    rw [h, integral_const, probReal_univ, smul_eq_mul, one_mul]

theorem FiniteLaw.expect_ofMeasure {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) :
    (FiniteLaw.ofMeasure μ).expect f = ∫ x, f x ∂μ := by
  have hint : Integrable f μ := by
    refine Integrable.mono' (integrable_const (∑ x, |f x|))
      (measurable_of_countable f).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun y _ => abs_nonneg (f y)) (Finset.mem_univ x)
  rw [FiniteLaw.expect, MeasureTheory.integral_fintype (μ := μ) (f := f) hint]
  simp [FiniteLaw.ofMeasure, smul_eq_mul]

end IdlaCyl
