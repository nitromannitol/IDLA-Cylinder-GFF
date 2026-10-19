/-
The cycle scaling limit and its strict positivity. Source: tex:479-484,
`paper/idla-cylinder-gff.tex`: `γ_k = √2 π ⌊k/2⌋`, with `a_N = N`.
-/
import IdlaCyl.Support.Cycle.Ordering

namespace IdlaCyl
open Filter
open scoped Topology

namespace CycleSpectrum

lemma mul_sinc (x : ℝ) : x * Real.sinc x = Real.sin x := by
  by_cases hx : x = 0
  · simp only [hx, zero_mul, Real.sin_zero]
  · rw [Real.sinc_of_ne_zero hx]
    field_simp

lemma scaled_value (N j : ℕ) (hN : 0 < N) :
    (N : ℝ) * Real.sqrt (2 * (1 - value N j)) =
      Real.sqrt 2 * |Real.pi * j * Real.sinc (Real.pi * j / N)| := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hcos : Real.cos (2 * Real.pi * j / N) =
      1 - 2 * Real.sin (Real.pi * j / N) ^ 2 := by
    rw [show 2 * Real.pi * j / N = 2 * (Real.pi * j / N) by ring,
      Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * j / N)]
  have hrad : 2 * (1 - value N j) = 2 * Real.sin (Real.pi * j / N) ^ 2 := by
    unfold value
    rw [hcos]
    ring
  have hsin : (N : ℝ) * Real.sin (Real.pi * j / N) =
      Real.pi * j * Real.sinc (Real.pi * j / N) := by
    rw [← mul_sinc (Real.pi * j / N)]
    field_simp
  rw [hrad, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq_eq_abs]
  calc (N : ℝ) * (Real.sqrt 2 * |Real.sin (Real.pi * j / N)|) =
      Real.sqrt 2 * |(N : ℝ) * Real.sin (Real.pi * j / N)| := by
        rw [abs_mul, abs_of_pos hNr]
        ring
       _ = _ := by rw [hsin]

/-- The numerical cycle eigenvalue formula has the claimed scaling limit. -/
theorem value_limit (j : ℕ) :
    Tendsto (fun n : ℕ => ((n + 3 : ℕ) : ℝ) *
      Real.sqrt (2 * (1 - value (n + 3) j))) atTop
      (𝓝 (Real.sqrt 2 * Real.pi * j)) := by
  have hN : Tendsto (fun n : ℕ => ((n + 3 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hx : Tendsto (fun n : ℕ => Real.pi * j / ((n + 3 : ℕ) : ℝ)) atTop (𝓝 0) :=
    hN.const_div_atTop (Real.pi * j)
  have hsinc := Real.continuous_sinc.continuousAt.tendsto.comp hx
  have hlim := (hsinc.const_mul (Real.pi * j)).abs.const_mul (Real.sqrt 2)
  have hval : (fun n : ℕ => ((n + 3 : ℕ) : ℝ) *
      Real.sqrt (2 * (1 - value (n + 3) j))) =
      (fun n : ℕ => Real.sqrt 2 * |Real.pi * j * Real.sinc (Real.pi * j / ((n + 3 : ℕ) : ℝ))|) := by
    funext n
    exact scaled_value (n + 3) j (by omega)
  rw [hval]
  simpa only [Function.comp_apply, Real.sinc_zero, mul_one,
    abs_of_nonneg (mul_nonneg Real.pi_pos.le (Nat.cast_nonneg j)), mul_assoc] using hlim

end CycleSpectrum

/-- The cycle spectral limit for every supplied lawful eigenbasis, together
with the strict positivity required by the spectral assumption (`tex:482-483`). -/
theorem cycle_gammaLimit (S : (n : ℕ) → SpectralData (cycleSeq n))
    (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ => ((n + 3 : ℕ) : ℝ) *
      Real.sqrt (2 * (1 - (S n).lam k))) atTop
      (𝓝 (Real.sqrt 2 * Real.pi * (k / 2 : ℕ))) ∧
      0 < Real.sqrt 2 * Real.pi * (k / 2 : ℕ) := by
  constructor
  · apply (CycleSpectrum.value_limit (k / 2)).congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    rw [cycle_lam_eq (n + 3) (by omega) (S n) k (by omega) (by omega)]
    rfl
  · have hj : (0 : ℝ) < (k / 2 : ℕ) := Nat.cast_pos.mpr (by omega)
    exact mul_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) Real.pi_pos) hj

end IdlaCyl
