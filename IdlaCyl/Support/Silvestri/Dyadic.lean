module

public import IdlaCyl.External.SilvestriProp2
public import LatticeProb.Prob.FiniteChainPairTV
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic

@[expose] public section

/-!
# Dyadic decay of the base-chain total variation

The base chain `B.P` of a quasi-regular base `B` is a finite Markov chain. This file
identifies Silvestri's pairwise total variation `silvestriTV` with the pairwise total
variation `pairTV` of `LatticeProb` for the same kernel, and derives dyadic decay from the
threshold-one-half mixing time `silvestriMixingTime`:

* `silvestriTV B s x y ≤ (1 / 2) ^ (s / silvestriMixingTime B)` for every time `s`;
* `tvToUniform B s x ≤ (1 / 2) ^ (s / silvestriMixingTime B)`, the distance from the
  `s`-step law to the uniform law, by averaging the pairwise bound over the uniform law.

The only input beyond Mathlib and `LatticeProb` is `silvestriMixingTime_spec`.
-/

namespace IdlaCyl.Silvestri

open IdlaCyl.External LatticeProb.FiniteChain

/-- The `t`-step powers of the base kernel are the `kpow` powers of `B.P`. -/
theorem basePow_eq_kpow (B : Base) (t : ℕ) (x y : B.V) :
    basePow B t x y = kpow B.P t x y := by
  induction t generalizing x y with
  | zero => simp [basePow, kpow]
  | succ t ih => simp only [basePow, kpow, ih]

/-- Silvestri's pairwise total variation of the base chain is the `pairTV` of `B.P`. -/
theorem silvestriTV_eq_pairTV (B : Base) (t : ℕ) (x y : B.V) :
    silvestriTV B t x y = pairTV B.P t x y := by
  simp only [silvestriTV, pairTV, basePow_eq_kpow]

/-- Dyadic decay of the pairwise total variation of the base chain: after `s` steps,
the distance between any two starting points is at most `(1/2) ^ (s / τ)`, where `τ` is
the threshold-one-half mixing time. -/
theorem silvestriTV_le_dyadic (B : Base) (s : ℕ) (x y : B.V) :
    silvestriTV B s x y ≤ (1 / 2 : ℝ) ^ (s / silvestriMixingTime B) := by
  have hτ : ∀ x y, pairTV B.P (silvestriMixingTime B) x y ≤ 1 / 2 := fun x y => by
    rw [← silvestriTV_eq_pairTV]
    exact silvestriMixingTime_spec B x y
  have hk := pairTV_mul_le B.P B.P_nonneg B.P_row_sum hτ (s / silvestriMixingTime B)
  have hr := pairTV_le_one B.P B.P_nonneg B.P_row_sum (s % silvestriMixingTime B)
  have h := pairTV_add_le B.P B.P_nonneg B.P_row_sum hk hr x y
  rw [Nat.div_add_mod' s (silvestriMixingTime B), mul_one] at h
  rw [silvestriTV_eq_pairTV]
  exact h

/-- Column sums of the `t`-step kernel are one. This uses the symmetry of `B.P`. -/
theorem sum_basePow_col (B : Base) (t : ℕ) (z : B.V) : ∑ x, basePow B t x z = 1 := by
  induction t generalizing z with
  | zero => simp [basePow]
  | succ t ih =>
    simp only [basePow]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, ih, one_mul]
    rw [Finset.sum_congr rfl fun w _ => B.P_symm w z]
    exact B.P_row_sum z

/-- Averaging the `t`-step rows over the uniform law gives the uniform law. -/
theorem basePow_uniform_stat (B : Base) (t : ℕ) (z : B.V) :
    ∑ x, (1 / (B.card : ℝ)) * basePow B t x z = 1 / (B.card : ℝ) := by
  rw [← Finset.mul_sum, sum_basePow_col, mul_one]

/-- Dyadic decay of the distance from the `s`-step law to the uniform law. The uniform law
is the average of the rows, so the distance is at most the average of the pairwise distances
from `x`, and each of those is at most `(1/2) ^ (s / τ)`. -/
theorem tvToUniform_le_dyadic (B : Base) (s : ℕ) (x : B.V) :
    tvToUniform B s x ≤ (1 / 2 : ℝ) ^ (s / silvestriMixingTime B) := by
  have hN : (B.card : ℝ) ≠ 0 := by
    have h2 : 2 ≤ B.card := B.nontrivial
    exact_mod_cast (show B.card ≠ 0 by omega)
  have hpos : (0 : ℝ) < 1 / (B.card : ℝ) := by
    apply one_div_pos.mpr
    exact lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hN)
  have hsum1 : ∑ y : B.V, (1 / (B.card : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_one_div_cancel hN
  have hdev : ∀ x', basePow B s x x' - 1 / (B.card : ℝ)
      = ∑ y, (1 / (B.card : ℝ)) * (basePow B s x x' - basePow B s y x') := by
    intro x'
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [basePow_uniform_stat, ← Finset.sum_mul, hsum1, one_mul]
  have hinner : ∀ x', |basePow B s x x' - 1 / (B.card : ℝ)|
      ≤ ∑ y, (1 / (B.card : ℝ)) * |basePow B s x x' - basePow B s y x'| := by
    intro x'
    rw [hdev x']
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun y _ => ?_))
    rw [abs_mul, abs_of_pos hpos]
  unfold tvToUniform
  calc (1 / 2 : ℝ) * ∑ x', |basePow B s x x' - 1 / (B.card : ℝ)|
      ≤ (1 / 2 : ℝ) * ∑ x', ∑ y, (1 / (B.card : ℝ)) * |basePow B s x x' - basePow B s y x'| :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x' _ => hinner x') (by norm_num)
    _ = ∑ y, (1 / (B.card : ℝ)) * silvestriTV B s x y := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        unfold silvestriTV
        rw [← Finset.mul_sum]
        ring
    _ ≤ ∑ y, (1 / (B.card : ℝ)) * (1 / 2 : ℝ) ^ (s / silvestriMixingTime B) :=
        Finset.sum_le_sum fun y _ =>
          mul_le_mul_of_nonneg_left (silvestriTV_le_dyadic B s x y) hpos.le
    _ = (1 / 2 : ℝ) ^ (s / silvestriMixingTime B) := by
        rw [← Finset.sum_mul, hsum1, one_mul]

end IdlaCyl.Silvestri
