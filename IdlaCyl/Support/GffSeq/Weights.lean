module

/-
Source: paper/idla-cylinder-gff.tex, tex:970-998.
Scalar estimates for a refinement of the paper's height layers: the first
height is ceil(L a_N), and subsequent layers have consecutive integer heights.
-/
public import IdlaCyl.Support.QOnEc.Weights
public import IdlaCyl.Support.QOnEc.Mass
public import IdlaCyl.Support.GffSeq.Mass
public import IdlaCyl.Support.Torus.Sequence

@[expose] public section

namespace IdlaCyl.GffSeq.QOnEc

open IdlaCyl.Defs Filter
open scoped Topology BigOperators

/-- A fixed multiple of the scale is the first height in the refined layers. -/
noncomputable def cutHeight (U : SequenceSetup) (L : ℝ) (N : ℕ) : ℕ := ⌈L * U.a N⌉₊

/-- The first height is above the fixed multiple of the scale. -/
theorem le_cutHeight (U : SequenceSetup) (L : ℝ) (N : ℕ) :
    L * U.a N ≤ (cutHeight U L N : ℝ) := Nat.le_ceil _

/-- The first height is positive when its multiple is positive. -/
theorem cutHeight_pos (U : SequenceSetup) (L : ℝ) (hL : 0 < L) (N : ℕ) :
    1 ≤ cutHeight U L N := by
  have hp := (mul_pos hL (U.a_pos N)).trans_le (le_cutHeight U L N)
  have : 0 < cutHeight U L N := Nat.cast_pos.mp hp
  omega

/-- The first height divided by the scale is bounded by `L+1` once `a_N ≥ 1`. -/
theorem cutHeight_div_le (U : SequenceSetup) (L : ℝ) (hL : 0 < L) (N : ℕ)
    (ha : 1 ≤ U.a N) : (cutHeight U L N : ℝ) / U.a N ≤ L + 1 := by
  apply (div_le_iff₀ (U.a_pos N)).mpr
  have hc := Nat.ceil_lt_add_one (mul_pos hL (U.a_pos N)).le
  change (cutHeight U L N : ℝ) < L * U.a N + 1 at hc
  nlinarith

/-- The first height tends to infinity. -/
theorem cutHeight_tendsto (U : SequenceSetup) (L : ℝ) (hL : 0 < L) :
    Tendsto (fun N => (cutHeight U L N : ℝ)) atTop atTop := by
  exact tendsto_atTop_mono (le_cutHeight U L)
    (U.a_tendsto.const_mul_atTop hL)

/-- The height weight is bounded at the first layer. -/
theorem first_weight_le (U : SequenceSetup) (L : ℝ) (hL : 0 < L)
    (A b : ℝ) (hA : 0 ≤ A) (hb : 0 ≤ b) (N : ℕ) (ha : 1 ≤ U.a N) :
    A * ((cutHeight U L N : ℝ) / U.a N) *
        Real.exp (b * ((cutHeight U L N : ℝ) / U.a N)) ≤
      A * (L + 1) * Real.exp (b * (L + 1)) := by
  have hr := cutHeight_div_le U L hL N ha
  exact mul_le_mul (mul_le_mul_of_nonneg_left hr hA)
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr hb))
    (Real.exp_nonneg _) (mul_nonneg hA (by linarith))

end IdlaCyl.GffSeq.QOnEc
