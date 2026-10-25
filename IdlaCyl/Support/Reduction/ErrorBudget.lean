module

/-
Numerical error budget for the finite-coefficient reduction.
Source: paper/idla-cylinder-gff.tex, tex:1445-1453; consumer tex:1136.

These are scalar inequalities for a finite union bound. They do not supply
couplings or assert any stochastic event estimate.
-/
public import Mathlib

@[expose] public section

namespace IdlaCyl.Reduction

open scoped BigOperators

/-- Two additional powers of N absorb the four error contributions at N≥2. -/
theorem final_error_budget (N ν : ℝ) (hN : 2 ≤ N) :
    4 * N ^ (-(ν + 3)) ≤ N ^ (-(ν + 1)) := by
  have hNpos : 0 < N := by linarith
  have hpow : 4 ≤ N ^ (2 : ℕ) := by nlinarith
  have he : -(ν + 1) = (2 : ℝ) + -(ν + 3) := by ring
  rw [he, Real.rpow_add hNpos, Real.rpow_two]
  exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hNpos.le _)

/-- Layer-filling errors and two comparison errors fit one uniform round allowance. -/
theorem round_error_budget (N ν r L : ℝ) (hN : 0 < N)
    (hL : L ≤ 2 * N ^ (r - 1)) :
    L * N ^ (-(ν + 2 * r + 1)) + 2 * N ^ (-(ν + r + 2)) ≤
      4 * N ^ (-(ν + r + 2)) := by
  have hprod : N ^ (r - 1) * N ^ (-(ν + 2 * r + 1)) =
      N ^ (-(ν + r + 2)) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  calc
    _ ≤ (2 * N ^ (r - 1)) * N ^ (-(ν + 2 * r + 1)) +
        2 * N ^ (-(ν + r + 2)) :=
      add_le_add
        (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg hN.le _)) le_rfl
    _ = 4 * N ^ (-(ν + r + 2)) := by rw [mul_assoc, hprod]; ring

/-- A finite sum of valid round allowances has the target failure budget. -/
theorem summed_error_budget (N ν r : ℝ) (R : ℕ) (e : Fin R → ℝ)
    (hN : 2 ≤ N) (hR : (R : ℝ) ≤ N ^ (r - 1))
    (he : ∀ i, e i ≤ 4 * N ^ (-(ν + r + 2))) :
    ∑ i, e i ≤ N ^ (-(ν + 1)) := by
  have hNpos : 0 < N := by linarith
  have hprod : N ^ (r - 1) * N ^ (-(ν + r + 2)) = N ^ (-(ν + 3)) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  calc
    _ ≤ ∑ _i : Fin R, 4 * N ^ (-(ν + r + 2)) :=
      Finset.sum_le_sum (fun i _ => he i)
    _ = (R : ℝ) * (4 * N ^ (-(ν + r + 2))) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ N ^ (r - 1) * (4 * N ^ (-(ν + r + 2))) :=
      mul_le_mul_of_nonneg_right hR (by positivity)
    _ = 4 * N ^ (-(ν + 3)) := by rw [mul_left_comm, hprod]
    _ ≤ N ^ (-(ν + 1)) := final_error_budget N ν hN

/-- The round allowance is attained in a concrete nonzero-buffer numerical example. -/
example : (4 : ℝ) * 2 ^ (-(1 + 2 * 2 + 1 : ℝ)) + 2 * 2 ^ (-(1 + 2 + 2 : ℝ)) ≤
    4 * 2 ^ (-(1 + 2 + 2 : ℝ)) := by
  apply round_error_budget 2 1 2 4 (by norm_num)
  norm_num [Real.rpow_one]

/-- A positive confidence parameter at a legitimate base size. -/
example : (4 : ℝ) * 2 ^ (-(1 + 3 : ℝ)) ≤ 2 ^ (-(1 + 1 : ℝ)) :=
  final_error_budget 2 1 (by norm_num)

end IdlaCyl.Reduction
