module

/-
Source: paper/idla-cylinder-gff.tex, tex:970-998.
Scalar estimates for a refinement of the paper's height layers: the first
height is ceil(L a_N), and subsequent layers have consecutive integer heights.
-/
public import IdlaCyl.Support.QOnEc.Mass

@[expose] public section

namespace IdlaCyl.QOnEc

open IdlaCyl.Defs Filter
open scoped Topology BigOperators

/-- A fixed multiple of the scale is the first height in the refined layers. -/
noncomputable def cutHeight (U : Setup) (L : ℝ) (N : ℕ) : ℕ := ⌈L * U.a N⌉₊

/-- The first height is above the fixed multiple of the scale. -/
theorem le_cutHeight (U : Setup) (L : ℝ) (N : ℕ) :
    L * U.a N ≤ (cutHeight U L N : ℝ) := Nat.le_ceil _

/-- The first height is positive when its multiple is positive. -/
theorem cutHeight_pos (U : Setup) (L : ℝ) (hL : 0 < L) (N : ℕ) :
    1 ≤ cutHeight U L N := by
  have hp := (mul_pos hL (U.a_pos N)).trans_le (le_cutHeight U L N)
  have : 0 < cutHeight U L N := Nat.cast_pos.mp hp
  omega

/-- The first height divided by the scale is bounded by `L+1` once `a_N ≥ 1`. -/
theorem cutHeight_div_le (U : Setup) (L : ℝ) (hL : 0 < L) (N : ℕ)
    (ha : 1 ≤ U.a N) : (cutHeight U L N : ℝ) / U.a N ≤ L + 1 := by
  apply (div_le_iff₀ (U.a_pos N)).mpr
  have hc := Nat.ceil_lt_add_one (mul_pos hL (U.a_pos N)).le
  change (cutHeight U L N : ℝ) < L * U.a N + 1 at hc
  nlinarith

/-- The first height tends to infinity. -/
theorem cutHeight_tendsto (U : Setup) (L : ℝ) (hL : 0 < L) :
    Tendsto (fun N => (cutHeight U L N : ℝ)) atTop atTop := by
  exact tendsto_atTop_mono (le_cutHeight U L)
    (U.a_tendsto.const_mul_atTop hL)

/-- The height weight is bounded at the first layer. -/
theorem first_weight_le (U : Setup) (L : ℝ) (hL : 0 < L)
    (A b : ℝ) (hA : 0 ≤ A) (hb : 0 ≤ b) (N : ℕ) (ha : 1 ≤ U.a N) :
    A * ((cutHeight U L N : ℝ) / U.a N) *
        Real.exp (b * ((cutHeight U L N : ℝ) / U.a N)) ≤
      A * (L + 1) * Real.exp (b * (L + 1)) := by
  have hr := cutHeight_div_le U L hL N ha
  exact mul_le_mul (mul_le_mul_of_nonneg_left hr hA)
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr hb))
    (Real.exp_nonneg _) (mul_nonneg hA (by linarith))

/-- For large scale, the height-dependent weight grows slower than `exp(h/2)`. -/
theorem weight_le_exp (A b a h : ℝ) (hA : 0 ≤ A)
    (ha : 1 ≤ a) (hab : 4 * b ≤ a) (hh : 0 ≤ h) :
    A * (h / a) * Real.exp (b * (h / a)) ≤ 4 * A * Real.exp (h / 2) := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hdiv : h / a ≤ h := (div_le_iff₀ ha0).mpr (by nlinarith)
  have hbdiv : b * (h / a) ≤ h / 4 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ ha0).mpr
    nlinarith
  have hlinear : h ≤ 4 * Real.exp (h / 4) := by
    have he := Real.add_one_le_exp (h / 4)
    linarith
  calc A * (h / a) * Real.exp (b * (h / a)) ≤
        A * h * Real.exp (h / 4) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hdiv hA)
        (Real.exp_le_exp.mpr hbdiv) (Real.exp_nonneg _) (mul_nonneg hA hh)
    _ ≤ A * (4 * Real.exp (h / 4)) * Real.exp (h / 4) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlinear hA) (Real.exp_nonneg _)
    _ = 4 * A * (Real.exp (h / 4) * Real.exp (h / 4)) := by ring
    _ = 4 * A * Real.exp (h / 2) := by rw [← Real.exp_add]; congr 2; ring

/-- The weighted tail of a consecutive layer has a geometric bound. -/
theorem weight_tail_le (A b a h : ℝ) (hA : 0 ≤ A)
    (ha : 1 ≤ a) (hab : 4 * b ≤ a) (hh : 0 ≤ h) :
    (A * ((h + 1) / a) * Real.exp (b * ((h + 1) / a))) * Real.exp (-h) ≤
      (4 * A * Real.exp (1 / 2)) * Real.exp (-h / 2) := by
  calc _ ≤ (4 * A * Real.exp ((h + 1) / 2)) * Real.exp (-h) :=
      mul_le_mul_of_nonneg_right (weight_le_exp A b a (h + 1) hA ha hab (by linarith))
        (Real.exp_nonneg _)
    _ = 4 * A * (Real.exp ((h + 1) / 2) * Real.exp (-h)) := by ring
    _ = _ := by
      rw [← Real.exp_add, show (h + 1) / 2 + -h = 1 / 2 + -h / 2 by ring,
        Real.exp_add]
      ring

/-- The sum over all finite consecutive layers has a bound independent of
the observation time and number of layers. -/
theorem sum_exp_layers_le (H T : ℕ) :
    (∑ j ∈ Finset.range T, Real.exp (-((H + j : ℕ) : ℝ) / 2)) ≤
      Real.exp (-(H : ℝ) / 2) / (1 - Real.exp (-(1 : ℝ) / 2)) := by
  let r := Real.exp (-(1 : ℝ) / 2)
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hsum : (∑ j ∈ Finset.range T, r ^ j) ≤ 1 / (1 - r) := by
    apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
    have he := geom_sum_mul_neg r T
    nlinarith [pow_nonneg hr0 T]
  have heq : ∀ j : ℕ, Real.exp (-((H + j : ℕ) : ℝ) / 2) =
      Real.exp (-(H : ℝ) / 2) * r ^ j := by
    intro j
    rw [← Real.exp_nat_mul]
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [heq]
  rw [← Finset.mul_sum]
  calc Real.exp (-(H : ℝ) / 2) * (∑ j ∈ Finset.range T, r ^ j) ≤
        Real.exp (-(H : ℝ) / 2) * (1 / (1 - r)) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _)
    _ = Real.exp (-(H : ℝ) / 2) / (1 - Real.exp (-(1 : ℝ) / 2)) := by
      dsimp [r]
      ring

end IdlaCyl.QOnEc
