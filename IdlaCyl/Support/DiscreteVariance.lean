module

/-
Exact discrete variance factors for the Gaussian limit (`tex:1040-1058`).

These are the finite geometric-sum calculations and the elementary identities
for the limiting covariance `σ²(φ)`: the per-mode diagonal factor
`varianceDiagonal γ y = (1 - e^{-2γy})/(2γ)` (`tex:1051`), the half-line Green
kernel whose diagonal it is, and the finite spectral variance over the modes
`c i`.

The sequence limit `q_k^N → γ_k` and the passage `W_N → σ²(φ)` are separate
nodes; only the finite algebra is here.  All sums are finite; `varianceDiagonal`
has the branch `γ = 0` where Lean reads `x/0 = 0`, so every consumer carries
`0 < γ`.
-/
public import Mathlib

@[expose] public section

namespace IdlaCyl

open scoped BigOperators

/-- Telescoping without division, valid even at `r = 1` and `h = 0`. -/
theorem geometric_sum_mul (r : ℝ) (h : ℕ) :
    (∑ j ∈ Finset.range h, r ^ j) * (1 - r) = 1 - r ^ h := by
  induction h with
  | zero => simp
  | succ h ih =>
      rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
      ring

theorem geometric_sum_eq (r : ℝ) (hr : r ≠ 1) (h : ℕ) :
    (∑ j ∈ Finset.range h, r ^ j) = (1 - r ^ h) / (1 - r) := by
  have hden : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  apply (eq_div_iff hden).mpr
  exact geometric_sum_mul r h

/-- Exponential specialization, proved by induction rather than reindexing. -/
theorem exp_nat_mul (t : ℝ) (n : ℕ) : Real.exp (t * (n : ℝ)) = Real.exp t ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, mul_add, mul_one, Real.exp_add, ih, pow_succ]

/-- The exact per-mode factor before passing to the limit (`tex:1051`). -/
noncomputable def discreteVarianceFactor (q a : ℝ) (h : ℕ) : ℝ :=
  (∑ j ∈ Finset.range h, Real.exp ((-2 * q / a) * (j : ℝ))) / a

/-- Exact factor in the rectangular quadratic variation, after reversing
heights. -/
theorem discreteVarianceFactor_eq (q a : ℝ) (h : ℕ)
    (hr : Real.exp (-2 * q / a) ≠ 1) :
    discreteVarianceFactor q a h =
      (1 - Real.exp ((-2 * q / a) * (h : ℝ))) /
        (a * (1 - Real.exp (-2 * q / a))) := by
  unfold discreteVarianceFactor
  simp_rw [exp_nat_mul]
  rw [geometric_sum_eq _ hr]
  rw [div_div, mul_comm (1 - Real.exp (-2 * q / a)) a]

/-- The diagonal factor `(1 - e^{-2γy})/(2γ)` (`tex:1051`); at `γ = 0` Lean reads
`x/0 = 0`, so consumers carry `0 < γ`. -/
noncomputable def varianceDiagonal (γ y : ℝ) : ℝ :=
  (1 - Real.exp (-2 * γ * y)) / (2 * γ)

theorem varianceDiagonal_zero (γ : ℝ) : varianceDiagonal γ 0 = 0 := by
  simp [varianceDiagonal]

theorem varianceDiagonal_nonneg (γ y : ℝ) (hγ : 0 < γ) (hy : 0 ≤ y) :
    0 ≤ varianceDiagonal γ y := by
  have hprod : 0 ≤ γ * y := mul_nonneg (le_of_lt hγ) hy
  have ht : -2 * γ * y ≤ 0 := by nlinarith [hprod]
  have he : Real.exp (-2 * γ * y) ≤ 1 := by
    calc
      Real.exp (-2 * γ * y) ≤ Real.exp 0 := Real.exp_le_exp.mpr ht
      _ = 1 := Real.exp_zero
  unfold varianceDiagonal
  exact div_nonneg (sub_nonneg.mpr he) (by linarith)

theorem varianceDiagonal_pos (γ y : ℝ) (hγ : 0 < γ) (hy : 0 < y) :
    0 < varianceDiagonal γ y := by
  have ht : -2 * γ * y < 0 := by nlinarith [mul_pos hγ hy]
  have he : Real.exp (-2 * γ * y) < 1 := by
    calc
      Real.exp (-2 * γ * y) < Real.exp 0 := Real.exp_lt_exp.mpr ht
      _ = 1 := Real.exp_zero
  unfold varianceDiagonal
  exact div_pos (sub_pos.mpr he) (by linarith)

theorem varianceDiagonal_le (γ y : ℝ) (hγ : 0 < γ) :
    varianceDiagonal γ y ≤ 1 / (2 * γ) := by
  unfold varianceDiagonal
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ 2 * γ)
  have he := Real.exp_pos (-2 * γ * y)
  linarith

/-- The half-line Dirichlet Green kernel at a positive spectral rate. -/
noncomputable def halfLineGreen (γ x y : ℝ) : ℝ :=
  (Real.exp (-γ * |x - y|) - Real.exp (-γ * (x + y))) / (2 * γ)

theorem halfLineGreen_diagonal (γ y : ℝ) :
    halfLineGreen γ y y = varianceDiagonal γ y := by
  unfold halfLineGreen varianceDiagonal
  simp only [sub_self, abs_zero, mul_zero, Real.exp_zero]
  rw [show -γ * (y + y) = -2 * γ * y by ring]

/-- Finite spectral variance over the modes `c i`, allowing the degenerate
normal limit (`tex:407`, `tex:1071-1074`). -/
noncomputable def spectralVariance {I : Type*} [Fintype I]
    (c γ : I → ℝ) (y : ℝ) : ℝ := ∑ i, c i ^ 2 * varianceDiagonal (γ i) y

theorem spectralVariance_nonneg {I : Type*} [Fintype I]
    (c γ : I → ℝ) (y : ℝ) (hγ : ∀ i, 0 < γ i) (hy : 0 ≤ y) :
    0 ≤ spectralVariance c γ y := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (sq_nonneg (c i)) (varianceDiagonal_nonneg _ _ (hγ i) hy)

end IdlaCyl
