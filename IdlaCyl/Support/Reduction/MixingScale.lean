/-
Positivity of the mixing time and the ceiling form of the terminal scale bound.

The mixing time is the smallest `t ≥ 0` with `max_x ‖P_N^t(x,·) - π_N‖_TV ≤ 1/4`
(`paper/idla-cylinder-gff.tex:269`), defined in `IdlaCyl.mixingTime`.  The
threshold is `T^♯ = N √τ_mix (log N)²` (`paper/idla-cylinder-gff.tex:273`),
defined in `IdlaCyl.Defs.sharp`.  The terminal time satisfies `T' < 3βM ≤ α T^♯`
with `α = 3(a+1)(b+1)`, and the rounded scale bound below is the integer form of
the factor `3(a+1)(b+1)`.
-/
import IdlaCyl.Definitions.ShapeEvent
import IdlaCyl.Support.Obligation.MixingContraction
import IdlaCyl.Support.Obligation.BasePowPos

namespace IdlaCyl.Reduction

open MeasureTheory ProbabilityTheory

/-- At time zero the total variation distance from any starting point to the uniform law
is at least `1/2`.  The row `P^0(x,·)` is the point mass at `x`, and every coordinate of
`P^0(x,·) - π_N` has absolute value at least `1/N`. -/
theorem mixingScale_tvToUniform_zero_ge (B : Base) (x : B.V) :
    1 / 2 ≤ tvToUniform B 0 x := by
  have hN : (2 : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast B.nontrivial
  have hterm : ∀ x' : B.V, 1 / (B.card : ℝ) ≤ |basePow B 0 x x' - 1 / (B.card : ℝ)| := by
    intro x'
    by_cases hx : x = x'
    · subst hx
      have h1 : basePow B 0 x x = 1 := by simp [basePow]
      rw [h1]
      have h2 : 1 / (B.card : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hN
      have h3 : 1 / (B.card : ℝ) ≤ 1 - 1 / (B.card : ℝ) := by linarith
      exact le_trans h3 (le_abs_self _)
    · have h1 : basePow B 0 x x' = 0 := by simp [basePow, hx]
      rw [h1, zero_sub, abs_neg]
      exact le_abs_self _
  have hcard : (B.card : ℝ) = (Fintype.card B.V : ℝ) := rfl
  have hne : (B.card : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hsum : ∑ x' : B.V, 1 / (B.card : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hcard]
    field_simp
  unfold tvToUniform
  have hle := Finset.sum_le_sum (fun x' (_ : x' ∈ Finset.univ) => hterm x')
  rw [hsum] at hle
  linarith

/-- The total variation mixing time is positive: at time zero the distance to uniform is
at least `1/2 > 1/4`, so `0` is not in the defining set of `IdlaCyl.mixingTime`. -/
theorem manuscript_mixing_pos (B : Base) : 0 < mixingTime B := by
  have hmem : ∀ x : B.V, tvToUniform B (mixingTime B) x ≤ 1 / 4 := by
    unfold mixingTime
    exact Nat.sInf_mem (Obligation.mixingTime_spec_of_pos B (Obligation.basePow_pos_uniform B))
  rcases Nat.eq_zero_or_pos (mixingTime B) with h0 | h
  · have hx := hmem B.pt
    rw [h0] at hx
    have hlow := mixingScale_tvToUniform_zero_ge B B.pt
    linarith
  · exact h

/-- The rounded terminal scale is at most `3(a+1)(b+1)` times the threshold `T^♯`.  Each
ceiling is at most its argument plus one, and the argument is at least one, so each
ceiling is at most a multiple of `√τ_mix log N` or of `N log N` with a factor `(b+1)` or
`(a+1)`.  The product is then `3(a+1)(b+1) N √τ_mix (log N)²`, which is `3(a+1)(b+1) T^♯`. -/
theorem rounded_scale (B : Base) (a b : ℝ)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hlog : 1 ≤ Real.log (B.card : ℝ)) :
    ((3 * (⌈b * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ)⌉₊) *
      (⌈a * (B.card : ℝ) * Real.log (B.card : ℝ)⌉₊) : ℕ) : ℝ) ≤
      (3 * (a + 1) * (b + 1)) * Defs.sharp B := by
  have hN : (2 : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast B.nontrivial
  have hτ : (1 : ℝ) ≤ (mixingTime B : ℝ) :=
    Nat.one_le_cast.mpr (manuscript_mixing_pos B)
  have hs : 1 ≤ Real.sqrt (mixingTime B) := Real.one_le_sqrt.mpr hτ
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  set N := (B.card : ℝ) with hNdef
  set L := Real.log N with hLdef
  set s := Real.sqrt (mixingTime B) with hsdef
  have hN0 : 0 ≤ N := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hsL : 1 ≤ s * L := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hlog)]
  have hNL : 1 ≤ N * L := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) (sub_nonneg.mpr hlog)]
  have hx1 : 0 ≤ b * s * L := mul_nonneg (mul_nonneg hb0 hs0) hL0
  have hx2 : 0 ≤ a * N * L := mul_nonneg (mul_nonneg ha0 hN0) hL0
  have hceil1 : (⌈b * s * L⌉₊ : ℝ) ≤ (b + 1) * s * L := by
    have h := Nat.ceil_lt_add_one hx1
    nlinarith
  have hceil2 : (⌈a * N * L⌉₊ : ℝ) ≤ (a + 1) * N * L := by
    have h := Nat.ceil_lt_add_one hx2
    nlinarith
  have hF1 : (0 : ℝ) ≤ (⌈b * s * L⌉₊ : ℝ) := Nat.cast_nonneg _
  have hF2 : (0 : ℝ) ≤ (⌈a * N * L⌉₊ : ℝ) := Nat.cast_nonneg _
  have key : 3 * (⌈b * s * L⌉₊ : ℝ) * (⌈a * N * L⌉₊ : ℝ) ≤
      3 * (a + 1) * (b + 1) * (N * s * L ^ 2) := by
    calc 3 * (⌈b * s * L⌉₊ : ℝ) * (⌈a * N * L⌉₊ : ℝ)
        ≤ 3 * ((b + 1) * s * L) * ((a + 1) * N * L) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hceil1 (by norm_num))
            hceil2 hF2 (by linarith [le_trans hF1 hceil1])
      _ = 3 * (a + 1) * (b + 1) * (N * s * L ^ 2) := by ring
  rw [show Defs.sharp B = N * s * L ^ 2 from rfl]
  exact_mod_cast key

end IdlaCyl.Reduction
