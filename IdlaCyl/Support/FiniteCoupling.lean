module

public import IdlaCyl.Support.FiniteLawOperations

@[expose] public section

set_option autoImplicit false

/-!
# Explicit maximal coupling of two finite laws

The construction places their common mass on the diagonal and couples the two
remaining masses by a product. Its marginals and exact mismatch probability are
proved from finite sums. No coupling theorem is an input.
-/
namespace IdlaCyl
open scoped BigOperators
noncomputable section
namespace FiniteLaw
variable {S : Type*} [Fintype S] [DecidableEq S]

def common (μ ν : FiniteLaw S) (x : S) : ℝ := min (μ.weight x) (ν.weight x)
def residual (μ ν : FiniteLaw S) (x : S) : ℝ := μ.weight x - μ.common ν x
def deficit (μ ν : FiniteLaw S) : ℝ := ∑ x, μ.residual ν x

omit [DecidableEq S] in
theorem common_nonneg (μ ν : FiniteLaw S) (x : S) : 0 ≤ μ.common ν x :=
  le_min (μ.nonneg x) (ν.nonneg x)

omit [DecidableEq S] in
theorem common_comm (μ ν : FiniteLaw S) (x : S) : μ.common ν x = ν.common μ x :=
  min_comm _ _

omit [DecidableEq S] in
theorem residual_nonneg (μ ν : FiniteLaw S) (x : S) : 0 ≤ μ.residual ν x :=
  sub_nonneg.mpr (min_le_left _ _)

omit [DecidableEq S] in
theorem deficit_nonneg (μ ν : FiniteLaw S) : 0 ≤ μ.deficit ν :=
  Finset.sum_nonneg (fun x _ => μ.residual_nonneg ν x)

omit [DecidableEq S] in
theorem deficit_eq (μ ν : FiniteLaw S) :
    μ.deficit ν = 1 - ∑ x, μ.common ν x := by
  simp only [deficit, residual, Finset.sum_sub_distrib, μ.total]

omit [DecidableEq S] in
theorem deficit_comm (μ ν : FiniteLaw S) : μ.deficit ν = ν.deficit μ := by
  simp only [deficit_eq, common, min_comm]

omit [DecidableEq S] in
theorem residual_le_deficit (μ ν : FiniteLaw S) (x : S) :
    μ.residual ν x ≤ μ.deficit ν :=
  Finset.single_le_sum (fun y _ => μ.residual_nonneg ν y) (Finset.mem_univ x)

omit [DecidableEq S] in
theorem residual_zero_of_deficit_zero (μ ν : FiniteLaw S)
    (h : μ.deficit ν = 0) (x : S) : μ.residual ν x = 0 := by
  have hu := μ.residual_le_deficit ν x
  have hl := μ.residual_nonneg ν x
  linarith

omit [DecidableEq S] in
theorem residual_product_zero (μ ν : FiniteLaw S) (x : S) :
    μ.residual ν x * ν.residual μ x = 0 := by
  by_cases h : μ.weight x ≤ ν.weight x
  · simp [residual, common, min_eq_left h]
  · have hh := le_of_lt (lt_of_not_ge h)
    simp [residual, common, min_eq_right hh, min_eq_left hh]

def couplingWeight (μ ν : FiniteLaw S) (x y : S) : ℝ :=
  (if x = y then μ.common ν x else 0) +
    μ.residual ν x * ν.residual μ y / μ.deficit ν

theorem couplingWeight_nonneg (μ ν : FiniteLaw S) (x y : S) :
    0 ≤ μ.couplingWeight ν x y := by
  unfold couplingWeight
  apply add_nonneg
  · split_ifs
    · exact μ.common_nonneg ν x
    · exact le_rfl
  · exact div_nonneg (mul_nonneg (μ.residual_nonneg ν x)
      (ν.residual_nonneg μ y)) (μ.deficit_nonneg ν)

omit [DecidableEq S] in
theorem residual_div_identity (μ ν : FiniteLaw S) (x : S) :
    μ.residual ν x * μ.deficit ν / μ.deficit ν = μ.residual ν x := by
  by_cases hd : μ.deficit ν = 0
  · rw [μ.residual_zero_of_deficit_zero ν hd x]
    simp
  · exact mul_div_cancel_right₀ _ hd

theorem couplingWeight_row (μ ν : FiniteLaw S) (x : S) :
    (∑ y, μ.couplingWeight ν x y) = μ.weight x := by
  unfold couplingWeight
  rw [Finset.sum_add_distrib]
  have hc : (∑ y, if x = y then μ.common ν x else 0) = μ.common ν x := by simp
  have hr : (∑ y, μ.residual ν x * ν.residual μ y / μ.deficit ν) =
      μ.residual ν x * μ.deficit ν / μ.deficit ν := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
    change _ * ν.deficit μ / _ = _
    rw [deficit_comm ν μ]
  rw [hc, hr, residual_div_identity]
  dsimp [residual]
  ring

theorem couplingWeight_swap (μ ν : FiniteLaw S) (x y : S) :
    μ.couplingWeight ν x y = ν.couplingWeight μ y x := by
  unfold couplingWeight
  rw [deficit_comm ν μ]
  have hc : (if x = y then μ.common ν x else 0) =
      (if y = x then ν.common μ y else 0) := by
    by_cases h : x = y
    · subst y
      simp only [common_comm]
    · simp [h, Ne.symm h]
  rw [hc, mul_comm (μ.residual ν x)]

theorem couplingWeight_column (μ ν : FiniteLaw S) (y : S) :
    (∑ x, μ.couplingWeight ν x y) = ν.weight y := by
  simp only [couplingWeight_swap μ ν]
  exact ν.couplingWeight_row μ y

/-- A concrete joint law with the desired marginals. -/
def maximalCoupling (μ ν : FiniteLaw S) : FiniteLaw (S × S) where
  weight z := μ.couplingWeight ν z.1 z.2
  nonneg z := μ.couplingWeight_nonneg ν z.1 z.2
  total := by
    rw [Fintype.sum_prod_type]
    simp only [couplingWeight_row, μ.total]

theorem coupling_diagonal (μ ν : FiniteLaw S) (x : S) :
    (μ.maximalCoupling ν).weight (x,x) = μ.common ν x := by
  change μ.couplingWeight ν x x = _
  simp only [couplingWeight, residual_product_zero, zero_div, add_zero, ↓reduceIte]

theorem coupling_first_expect (μ ν : FiniteLaw S) (f : S → ℝ) :
    (μ.maximalCoupling ν).expect (fun z => f z.1) = μ.expect f := by
  unfold expect
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  change (∑ y, μ.couplingWeight ν x y * f x) = _
  rw [← Finset.sum_mul, couplingWeight_row]

theorem coupling_second_expect (μ ν : FiniteLaw S) (f : S → ℝ) :
    (μ.maximalCoupling ν).expect (fun z => f z.2) = ν.expect f := by
  unfold expect
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  change (∑ x, μ.couplingWeight ν x y * f y) = _
  rw [← Finset.sum_mul, couplingWeight_column]

theorem coupling_agreement (μ ν : FiniteLaw S) :
    (μ.maximalCoupling ν).event (fun z => z.1 = z.2) = 1 - μ.deficit ν := by
  classical
  have hsum : (μ.maximalCoupling ν).event (fun z => z.1 = z.2) =
      ∑ x, μ.common ν x := by
    unfold event expect
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_eq_single x]
    · simp [coupling_diagonal]
    · intro y _ hyx
      dsimp only
      rw [if_neg (Ne.symm hyx), mul_zero]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  rw [hsum, deficit_eq]
  ring

omit [DecidableEq S] in
theorem absolute_difference (μ ν : FiniteLaw S) (x : S) :
    |μ.weight x - ν.weight x| = μ.residual ν x + ν.residual μ x := by
  by_cases h : μ.weight x ≤ ν.weight x
  · simp only [abs_of_nonpos (sub_nonpos.mpr h), residual, common,
      min_eq_left h, min_eq_right h]
    ring
  · have hh := le_of_lt (lt_of_not_ge h)
    simp only [abs_of_nonneg (sub_nonneg.mpr hh), residual, common,
      min_eq_right hh, min_eq_left hh]
    ring

omit [DecidableEq S] in
theorem deficit_half_l1 (μ ν : FiniteLaw S) :
    μ.deficit ν = (∑ x, |μ.weight x - ν.weight x|) / 2 := by
  simp only [absolute_difference, Finset.sum_add_distrib]
  change μ.deficit ν = (μ.deficit ν + ν.deficit μ) / 2
  rw [deficit_comm ν μ]
  ring

end FiniteLaw
end
end IdlaCyl
