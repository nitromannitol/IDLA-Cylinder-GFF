/-
Quadratic-form inputs for the spectral decomposition of the lazy base kernel.

`paper/idla-cylinder-gff.tex:301-311` (`tex:301-311`): the eigenvalues of `P_N`
satisfy `1 = λ_1 > λ_2 ≥ ⋯ ≥ λ_N ≥ 0`, "where strict inequality `λ_2(N) < 1`
comes from irreducibility and the lower bound `λ_N(N) ≥ 0` comes from
laziness".  This file proves the three quadratic-form facts behind that line,
for the quadratic form `v ↦ ∑ x, ∑ x', v x * P x x' * v x'`:

* `P_quadratic_nonneg`: it is nonnegative (laziness, `λ_N ≥ 0`);
* `P_quadratic_le`: it is at most `∑ x, v x ^ 2` (eigenvalues `≤ 1`);
* `P_fixed_const`: a `P`-fixed vector is constant (irreducibility, `λ_2 < 1`).

They are inputs to the obligation `IdlaCyl.spectralData_exists`.
-/
import IdlaCyl.Support.Base

namespace IdlaCyl.Obligation

open IdlaCyl

section Generic

variable {V : Type} [Fintype V]

/-- Expanding `∑∑ K x x' * (v x + c * v x') ^ 2` for a kernel `K` with all row
and column sums equal to `1` and a sign `c` with `c ^ 2 = 1`. -/
theorem P_quadratic_expand (K : V → V → ℝ) (hr : ∀ x, ∑ x', K x x' = 1)
    (hc : ∀ x', ∑ x, K x x' = 1) (v : V → ℝ) (c : ℝ) (hc2 : c ^ 2 = 1) :
    ∑ x, ∑ x', K x x' * (v x + c * v x') ^ 2
      = 2 * ∑ x, v x ^ 2 + 2 * c * ∑ x, ∑ x', v x * K x x' * v x' := by
  have hterm : ∀ x x', K x x' * (v x + c * v x') ^ 2
      = K x x' * v x ^ 2 + 2 * c * (v x * K x x' * v x') + K x x' * v x' ^ 2 := by
    intro x x'
    linear_combination (K x x' * v x' ^ 2) * hc2
  have hA : ∑ x, ∑ x', K x x' * v x ^ 2 = ∑ x, v x ^ 2 := by
    simp_rw [← Finset.sum_mul, hr, one_mul]
  have hC : ∑ x, ∑ x', K x x' * v x' ^ 2 = ∑ x, v x ^ 2 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hc, one_mul]
  have hB : ∑ x, ∑ x', 2 * c * (v x * K x x' * v x')
      = 2 * c * ∑ x, ∑ x', v x * K x x' * v x' := by
    simp_rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => hterm x x']
  simp only [Finset.sum_add_distrib]
  rw [hA, hB, hC]
  ring

end Generic

/-- Column sums of the base kernel are `1`, by symmetry. -/
theorem P_quadratic_col_sum (B : Base) (x' : B.V) : ∑ x, B.P x x' = 1 := by
  calc ∑ x, B.P x x' = ∑ x, B.P x' x := Finset.sum_congr rfl fun x _ => B.P_symm x x'
    _ = 1 := B.P_row_sum x'

/-- The Dirichlet identity for the base kernel. -/
theorem P_quadratic_dirichlet (B : Base) (v : B.V → ℝ) :
    ∑ x, ∑ x', B.P x x' * (v x - v x') ^ 2
      = 2 * (∑ x, v x ^ 2 - ∑ x, ∑ x', v x * B.P x x' * v x') := by
  have h := P_quadratic_expand B.P B.P_row_sum (P_quadratic_col_sum B) v (-1) (by norm_num)
  have e : ∀ x x', B.P x x' * (v x - v x') ^ 2 = B.P x x' * (v x + (-1) * v x') ^ 2 := by
    intro x x'
    ring
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => e x x', h]
  ring

theorem P_quadratic_le (B : Base) (v : B.V → ℝ) :
    ∑ x, ∑ x', v x * B.P x x' * v x' ≤ ∑ x, v x ^ 2 := by
  have h := P_quadratic_dirichlet B v
  have hnn : 0 ≤ ∑ x, ∑ x', B.P x x' * (v x - v x') ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun x' _ =>
      mul_nonneg (B.P_nonneg x x') (sq_nonneg _)
  linarith

/-- The base kernel is lazy: `P x x = 1/2`. -/
theorem P_quadratic_diag (B : Base) (x : B.V) : B.P x x = 1 / 2 := by
  simp [Base.P]

/-- The kernel `R x x' = 2 * P x x' - 1_{x = x'}`, which is nonnegative by
laziness and has all row and column sums `1`. -/
noncomputable def P_quadratic_R (B : Base) (x x' : B.V) : ℝ :=
  2 * B.P x x' - if x = x' then 1 else 0

theorem P_quadratic_R_nonneg (B : Base) (x x' : B.V) : 0 ≤ P_quadratic_R B x x' := by
  unfold P_quadratic_R
  by_cases h : x = x'
  · subst h
    rw [P_quadratic_diag]
    norm_num
  · simp [h, B.P_nonneg x x']

theorem P_quadratic_R_row_sum (B : Base) (x : B.V) : ∑ x', P_quadratic_R B x x' = 1 := by
  unfold P_quadratic_R
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, B.P_row_sum, Finset.sum_ite_eq]
  norm_num

theorem P_quadratic_R_col_sum (B : Base) (x' : B.V) : ∑ x, P_quadratic_R B x x' = 1 := by
  unfold P_quadratic_R
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, P_quadratic_col_sum, Finset.sum_ite_eq']
  norm_num

/-- The quadratic form of `R` in terms of that of `P`. -/
theorem P_quadratic_R_form (B : Base) (v : B.V → ℝ) :
    ∑ x, ∑ x', v x * P_quadratic_R B x x' * v x'
      = 2 * ∑ x, ∑ x', v x * B.P x x' * v x' - ∑ x, v x ^ 2 := by
  have e : ∀ x x', v x * P_quadratic_R B x x' * v x'
      = 2 * (v x * B.P x x' * v x') - (if x = x' then v x * v x' else 0) := by
    intro x x'
    unfold P_quadratic_R
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => e x x']
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  simp [sq]

theorem P_quadratic_nonneg (B : Base) (v : B.V → ℝ) :
    0 ≤ ∑ x, ∑ x', v x * B.P x x' * v x' := by
  have h := P_quadratic_expand (P_quadratic_R B) (P_quadratic_R_row_sum B)
    (P_quadratic_R_col_sum B) v 1 (by norm_num)
  have hnn : 0 ≤ ∑ x, ∑ x', P_quadratic_R B x x' * (v x + 1 * v x') ^ 2 :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun x' _ =>
      mul_nonneg (P_quadratic_R_nonneg B x x') (sq_nonneg _)
  rw [h, P_quadratic_R_form] at hnn
  linarith

/-- If `v` is `P`-fixed, the Dirichlet sum vanishes termwise. -/
theorem P_fixed_const_zero (B : Base) (v : B.V → ℝ)
    (hv : ∀ x, ∑ x', B.P x x' * v x' = v x) (x x' : B.V) :
    B.P x x' * (v x - v x') ^ 2 = 0 := by
  have hQ : ∑ x, ∑ x', v x * B.P x x' * v x' = ∑ x, v x ^ 2 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    calc ∑ x', v x * B.P x x' * v x' = v x * ∑ x', B.P x x' * v x' := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x' _ => by ring
      _ = v x ^ 2 := by rw [hv x]; ring
  have h := P_quadratic_dirichlet B v
  rw [hQ, sub_self, mul_zero] at h
  have hnn : ∀ a b, 0 ≤ B.P a b * (v a - v b) ^ 2 := fun a b =>
    mul_nonneg (B.P_nonneg a b) (sq_nonneg _)
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => hnn a b).mp h x (Finset.mem_univ x)
  exact (Finset.sum_eq_zero_iff_of_nonneg fun b _ => hnn x b).mp h1 x' (Finset.mem_univ x')

theorem P_fixed_const (B : Base) (v : B.V → ℝ)
    (hv : ∀ x, ∑ x', B.P x x' * v x' = v x) (x y : B.V) : v x = v y := by
  have hadj : ∀ a b, B.graph.Adj a b → v a = v b := by
    intro a b hab
    have h0 := P_fixed_const_zero B v hv a b
    have hP : B.P a b = 1 / (2 * (B.deg : ℝ)) := by simp [Base.P, hab]
    have hd : (0 : ℝ) < B.deg := Nat.cast_pos.mpr B.deg_pos
    have hPpos : B.P a b ≠ 0 := by rw [hP]; positivity
    have hsq : (v a - v b) ^ 2 = 0 := (mul_eq_zero.mp h0).resolve_left hPpos
    have : v a - v b = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hsq
    linarith
  obtain ⟨w⟩ := B.connected.preconnected x y
  induction w with
  | nil => rfl
  | cons h p ih => exact (hadj _ _ h).trans ih

end IdlaCyl.Obligation
