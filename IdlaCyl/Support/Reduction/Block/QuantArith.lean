import IdlaCyl.Definitions.ShapeEvent
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
Explicit constants of the quantitative reduction for cylinder IDLA.

Pure real and natural arithmetic. Let `U = max N T`, `ρ ≥ 1`, `a = 2 U² / ε` with
`0 < ε < 1`, and let the block height be `H = ⌈4 ρ log a⌉₊`. The file proves:

* the block tail `N H e^{-H/4}` and the stopping tail `T √N e^{-H/ρ}` are at most
  `ε / (2 U)`, and the summed block errors `∑ (ℓ_i + 3) ε / (2 U)` are at most `ε`;
* with `ε = N^{-(ν+1)}` and `1 ≤ T ≤ N^m`, one has `log a ≤ (ν + 2 m + 2) log N` and
  `H ≤ (4 (ν + 2 m + 2) + 1) ρ log N`, so that `6 N H ≤ D N ρ log N` with
  `D = 6 (4 (ν + 2 m + 2) + 1)`, and `6 N H ≤ C N √τ log N` with `C = √2 D` when
  `ρ ≤ √2 √τ`;
* for `α > 0` and `N` at least `⌈exp (C / α)⌉₊`, `C N √τ log N ≤ α N √τ (log N)²`,
  and in particular `C N √τ log N ≤ α · Defs.sharp B` for the base `B`, with
  `N = B.card` and `τ = mixingTime B`.
-/

namespace IdlaCyl.Reduction

/-- The block tail at the height `H = ⌈4 ρ log (2 U² / ε)⌉₊`: `U e^{-H/4} ≤ ε / (2 U)`. -/
theorem block_exp_le (U H : ℕ) (ρ ε : ℝ) (hU : 1 ≤ U) (hρ : 1 ≤ ρ) (hε : 0 < ε)
    (hε1 : ε < 1) (hH : H = ⌈4 * ρ * Real.log (2 * (U : ℝ) ^ 2 / ε)⌉₊) :
    (U : ℝ) * Real.exp (-(H : ℝ) / 4) ≤ ε / (2 * U) := by
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hU0 : (0 : ℝ) < U := by linarith
  have hUne : (U : ℝ) ≠ 0 := hU0.ne'
  have hεne : ε ≠ 0 := hε.ne'
  set a : ℝ := 2 * (U : ℝ) ^ 2 / ε with ha_def
  have ha_eps : a * ε = 2 * (U : ℝ) ^ 2 := by
    rw [ha_def]
    field_simp
  have ha1 : 1 ≤ a := by
    nlinarith [mul_nonneg (sq_nonneg (U : ℝ)) (by linarith : (0 : ℝ) ≤ 2)]
  have ha0 : 0 < a := by linarith
  have hlog0 : 0 ≤ Real.log a := Real.log_nonneg ha1
  have hHx : 4 * ρ * Real.log a ≤ (H : ℝ) := by
    rw [hH]
    exact Nat.le_ceil _
  have hH4 : Real.log a ≤ (H : ℝ) / 4 := by nlinarith
  have hexp : Real.exp (-(H : ℝ) / 4) ≤ a⁻¹ := by
    have h := Real.exp_le_exp.mpr (show -(H : ℝ) / 4 ≤ -Real.log a by linarith)
    rwa [Real.exp_neg, Real.exp_log ha0] at h
  have hfin : (U : ℝ) * a⁻¹ = ε / (2 * U) := by
    rw [ha_def]
    field_simp
  calc (U : ℝ) * Real.exp (-(H : ℝ) / 4) ≤ (U : ℝ) * a⁻¹ :=
        mul_le_mul_of_nonneg_left hexp hU0.le
    _ = ε / (2 * U) := hfin

/-- The block tail once a step runs: `N H e^{-H/4} ≤ ε / (2 U)` when `N H ≤ U`. -/
theorem block_mass_le (N H U : ℕ) (ρ ε : ℝ) (hU : 1 ≤ U) (hρ : 1 ≤ ρ) (hε : 0 < ε)
    (hε1 : ε < 1) (hNH : N * H ≤ U)
    (hH : H = ⌈4 * ρ * Real.log (2 * (U : ℝ) ^ 2 / ε)⌉₊) :
    (N : ℝ) * H * Real.exp (-(H : ℝ) / 4) ≤ ε / (2 * U) := by
  have hnat : (N : ℝ) * H ≤ U := by exact_mod_cast hNH
  calc (N : ℝ) * H * Real.exp (-(H : ℝ) / 4)
      ≤ (U : ℝ) * Real.exp (-(H : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hnat (Real.exp_nonneg _)
    _ ≤ ε / (2 * U) := block_exp_le U H ρ ε hU hρ hε hε1 hH

/-- The stopping tail: `T √N e^{-H/ρ} ≤ ε / (2 U)` when `N ≤ U` and `T ≤ U`. -/
theorem stop_exp_le (N T U H : ℕ) (ρ ε : ℝ) (hN : 2 ≤ N) (hNU : N ≤ U) (hTU : T ≤ U)
    (hρ : 1 ≤ ρ) (hε : 0 < ε) (hε1 : ε < 1)
    (hH : H = ⌈4 * ρ * Real.log (2 * (U : ℝ) ^ 2 / ε)⌉₊) :
    (T : ℝ) * (Real.sqrt N * Real.exp (-(H : ℝ) / ρ)) ≤ ε / (2 * U) := by
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast (show 1 ≤ U by omega)
  have hU0 : (0 : ℝ) < U := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNU' : (N : ℝ) ≤ U := by exact_mod_cast hNU
  have hTU' : (T : ℝ) ≤ U := by exact_mod_cast hTU
  have hρ0 : 0 < ρ := by linarith
  set a : ℝ := 2 * (U : ℝ) ^ 2 / ε with ha_def
  have ha_eps : a * ε = 2 * (U : ℝ) ^ 2 := by
    rw [ha_def]
    field_simp
  have haU : (U : ℝ) ≤ a := by
    nlinarith [mul_nonneg (le_of_lt (show 0 < a by nlinarith)) (sub_nonneg.mpr hε1.le),
      mul_le_mul_of_nonneg_left hU1 hU0.le]
  have ha1 : 1 ≤ a := le_trans hU1 haU
  have ha0 : 0 < a := by linarith
  have hsN : Real.sqrt N ≤ a := by
    have h1 : Real.sqrt N ≤ N :=
      (Real.sqrt_le_sqrt (by nlinarith : (N : ℝ) ≤ (N : ℝ) ^ 2)).trans
        (Real.sqrt_sq hN0).le
    linarith
  have hlog4 : 4 * Real.log a ≤ (H : ℝ) / ρ := by
    rw [le_div_iff₀ hρ0]
    have h4 : 4 * ρ * Real.log a ≤ (H : ℝ) := by
      rw [hH]
      exact Nat.le_ceil _
    nlinarith
  have hexp : Real.exp (-(H : ℝ) / ρ) * a ^ 4 ≤ 1 := by
    have h1 : Real.exp (-(H : ℝ) / ρ) ≤ Real.exp (-(4 * Real.log a)) :=
      Real.exp_le_exp.mpr (by rw [neg_div]; linarith)
    have h4 : Real.exp (4 * Real.log a) = a ^ 4 := by
      rw [show 4 * Real.log a = Real.log a + Real.log a + Real.log a + Real.log a by ring,
        Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log ha0]
      ring
    have h2 : Real.exp (-(4 * Real.log a)) * a ^ 4 = 1 := by
      rw [Real.exp_neg, h4]
      exact inv_mul_cancel₀ (pow_pos ha0 4).ne'
    calc Real.exp (-(H : ℝ) / ρ) * a ^ 4
        ≤ Real.exp (-(4 * Real.log a)) * a ^ 4 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 1 := h2
  have hE0 : 0 ≤ Real.exp (-(H : ℝ) / ρ) := (Real.exp_pos _).le
  have h5 : Real.exp (-(H : ℝ) / ρ) * a ^ 2 ≤ 1 := by
    have ha2 : a ^ 2 ≤ a ^ 4 := pow_le_pow_right₀ ha1 (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left ha2 hE0) hexp
  have hTs : (T : ℝ) * Real.sqrt N ≤ U * a :=
    mul_le_mul hTU' hsN (Real.sqrt_nonneg _) hU0.le
  have h6 : (U : ℝ) * a * Real.exp (-(H : ℝ) / ρ) * a ≤ U := by
    have := mul_le_mul_of_nonneg_left h5 hU0.le
    nlinarith
  have hfin : ε / (2 * U) = U / a := by
    rw [div_eq_div_iff (by positivity) ha0.ne']
    linear_combination ha_eps
  rw [hfin, le_div_iff₀ ha0]
  calc (T : ℝ) * (Real.sqrt N * Real.exp (-(H : ℝ) / ρ)) * a
      = (T : ℝ) * Real.sqrt N * Real.exp (-(H : ℝ) / ρ) * a := by ring
    _ ≤ (U * a) * Real.exp (-(H : ℝ) / ρ) * a :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hTs hE0) ha0.le
    _ ≤ U := h6

/-- The summed block errors: with `ℓ i ≥ 3` and `∑ ℓ i ≤ T / (N H)`, one has
`∑ (ℓ i + 3) · (ε / (2 U)) ≤ ε`. -/
theorem block_sum_le {R : ℕ} (ℓ : Fin R → ℕ) (T N H U : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hU : 1 ≤ U) (hTU : T ≤ U) (hℓ : ∀ i, 3 ≤ ℓ i) (hsum : ∑ i, ℓ i ≤ T / (N * H)) :
    ∑ i, ((ℓ i : ℝ) + 3) * (ε / (2 * U)) ≤ ε := by
  have hS : ∑ i, ℓ i ≤ U := (hsum.trans (Nat.div_le_self _ _)).trans hTU
  have hS' : ∑ i, (ℓ i : ℝ) ≤ U := by exact_mod_cast hS
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hU0 : (0 : ℝ) < 2 * U := by linarith
  have h3 : ∑ _i : Fin R, (3 : ℝ) ≤ ∑ i, (ℓ i : ℝ) :=
    Finset.sum_le_sum fun i _ => by exact_mod_cast hℓ i
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  have hsum2 : ∑ i, ((ℓ i : ℝ) + 3) ≤ 2 * U := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  rw [← Finset.sum_mul]
  calc (∑ i, ((ℓ i : ℝ) + 3)) * (ε / (2 * U))
      ≤ (2 * U) * (ε / (2 * U)) :=
        mul_le_mul_of_nonneg_right hsum2 (div_nonneg hε hU0.le)
    _ = ε := by field_simp

/-- Bound (29) on the logarithm: for `N ≥ 3`, `m ≥ 1`, `1 ≤ T ≤ N^m`, `U = max N T` and
`ε = N^{-(ν+1)}`, one has `log (2 U² / ε) ≤ (ν + 2 m + 2) log N`. -/
theorem log_a_le (N T U : ℕ) (ν m : ℝ) (hN : 3 ≤ N) (hm : 1 ≤ m)
    (hT : (T : ℝ) ≤ (N : ℝ) ^ m) (hU : U = max N T) (ε : ℝ)
    (hε : ε = (N : ℝ) ^ (-(ν + 1))) :
    Real.log (2 * (U : ℝ) ^ 2 / ε) ≤ (ν + 2 * m + 2) * Real.log N := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hNm : (N : ℝ) ≤ (N : ℝ) ^ m := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ N by linarith) hm
    rwa [Real.rpow_one] at h
  have hUle : (U : ℝ) ≤ (N : ℝ) ^ m := by
    rw [hU, Nat.cast_max]
    exact max_le hNm hT
  have hNU : (N : ℝ) ≤ U := by
    rw [hU, Nat.cast_max]
    exact le_max_left _ _
  have hUpos : (0 : ℝ) < U := by linarith
  have hlogU : Real.log U ≤ m * Real.log N := by
    have h := Real.log_le_log hUpos hUle
    rwa [Real.log_rpow hNpos] at h
  have hlog2 : Real.log 2 ≤ Real.log N :=
    Real.log_le_log (by norm_num) (by linarith)
  have hεpos : 0 < ε := by
    rw [hε]
    positivity
  have hlogε : Real.log ε = -(ν + 1) * Real.log N := by
    rw [hε, Real.log_rpow hNpos]
  rw [Real.log_div (mul_ne_zero two_ne_zero (pow_ne_zero 2 hUpos.ne')) hεpos.ne',
    Real.log_mul two_ne_zero (pow_ne_zero 2 hUpos.ne'), Real.log_pow, hlogε]
  push_cast
  linarith

/-- Bound (29) on the block height: with `ρ ≥ 1`, `N ≥ 3`, `1 ≤ U`, `0 < ε < 1` and
`H = ⌈4 ρ log (2 U² / ε)⌉₊`, the logarithm bound `log (2U²/ε) ≤ (ν + 2m + 2) log N`
gives `H ≤ (4 (ν + 2 m + 2) + 1) ρ log N`. -/
theorem H_le_log (N U H : ℕ) (ρ ν m ε : ℝ) (hN : 3 ≤ N) (hU : 1 ≤ U) (hρ : 1 ≤ ρ)
    (hε : 0 < ε) (hε1 : ε < 1)
    (hH : H = ⌈4 * ρ * Real.log (2 * (U : ℝ) ^ 2 / ε)⌉₊)
    (hlog : Real.log (2 * (U : ℝ) ^ 2 / ε) ≤ (ν + 2 * m + 2) * Real.log N) :
    (H : ℝ) ≤ (4 * (ν + 2 * m + 2) + 1) * ρ * Real.log N := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hU1 : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hU0 : (0 : ℝ) < U := by linarith
  set a : ℝ := 2 * (U : ℝ) ^ 2 / ε with ha_def
  have ha_eps : a * ε = 2 * (U : ℝ) ^ 2 := by
    rw [ha_def]
    field_simp
  have ha1 : 1 ≤ a := by
    rw [ha_def, le_div_iff₀ hε]
    nlinarith
  have hlog0 : 0 ≤ Real.log a := Real.log_nonneg ha1
  have hH' : (H : ℝ) < 4 * ρ * Real.log a + 1 := by
    rw [hH]
    exact Nat.ceil_lt_add_one (mul_nonneg (by linarith) hlog0)
  have hlogN1 : 1 ≤ Real.log N := by
    have he : Real.exp 1 ≤ N := by
      have h := Real.exp_one_lt_d9
      norm_num at h
      linarith
    have h := Real.log_le_log (Real.exp_pos 1) he
    rwa [Real.log_exp] at h
  have hρlog : 1 ≤ ρ * Real.log N := by nlinarith
  have h4 : 4 * ρ * Real.log a ≤ 4 * ρ * ((ν + 2 * m + 2) * Real.log N) :=
    mul_le_mul_of_nonneg_left hlog (by linarith)
  nlinarith

/-- The constant `D_{ν,m} = 6 (4 (ν + 2 m + 2) + 1)` of (4). -/
noncomputable def quantD (ν m : ℝ) : ℝ := 6 * (4 * (ν + 2 * m + 2) + 1)

/-- The constant `C_{ν,m} = √2 D_{ν,m}` of (4). -/
noncomputable def quantC (ν m : ℝ) : ℝ := Real.sqrt 2 * quantD ν m

/-- Bound (4), first form: `6 N H ≤ D_{ν,m} N ρ log N` when `H ≤ (4 (ν + 2 m + 2) + 1) ρ log N`. -/
theorem six_NH_le_quantD (N H : ℕ) (ρ ν m : ℝ)
    (hH : (H : ℝ) ≤ (4 * (ν + 2 * m + 2) + 1) * ρ * Real.log N) :
    6 * ((N : ℝ) * H) ≤ quantD ν m * N * ρ * Real.log N := by
  have h := mul_le_mul_of_nonneg_left hH (by positivity : (0 : ℝ) ≤ 6 * N)
  unfold quantD
  linarith

/-- Bound (5): `6 N H ≤ C_{ν,m} N √τ log N` when `ρ ≤ √2 √τ`, `ν, m ≥ 0` and `N ≥ 3`. -/
theorem six_NH_le_quantC (N H : ℕ) (ρ τ ν m : ℝ) (hν : 0 ≤ ν) (hm : 0 ≤ m) (hN : 3 ≤ N)
    (hH : (H : ℝ) ≤ (4 * (ν + 2 * m + 2) + 1) * ρ * Real.log N)
    (hρτ : ρ ≤ Real.sqrt 2 * Real.sqrt τ) :
    6 * ((N : ℝ) * H) ≤ quantC ν m * N * Real.sqrt τ * Real.log N := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hD : 0 ≤ quantD ν m := by
    unfold quantD
    linarith
  have hDN : 0 ≤ quantD ν m * N * Real.log N :=
    mul_nonneg (mul_nonneg hD (Nat.cast_nonneg N)) hlog
  have h1 := six_NH_le_quantD N H ρ ν m hH
  have h2 := mul_le_mul_of_nonneg_left hρτ hDN
  calc 6 * ((N : ℝ) * H) ≤ quantD ν m * N * ρ * Real.log N := h1
    _ = quantD ν m * N * Real.log N * ρ := by ring
    _ ≤ quantD ν m * N * Real.log N * (Real.sqrt 2 * Real.sqrt τ) := h2
    _ = quantC ν m * N * Real.sqrt τ * Real.log N := by
        unfold quantC
        ring

/-- Bound (6): for `α > 0` and `N ≥ max 3 ⌈exp (C / α)⌉₊`,
`C N √τ log N ≤ α (N √τ (log N)²)`. -/
theorem C_mul_le_alpha (N : ℕ) (τ C α : ℝ) (hα : 0 < α) (hN : 3 ≤ N)
    (hNC : ⌈Real.exp (C / α)⌉₊ ≤ N) :
    C * N * Real.sqrt τ * Real.log N ≤ α * (N * Real.sqrt τ * (Real.log N) ^ 2) := by
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hexpN : Real.exp (C / α) ≤ N :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hNC)
  have hlogN : C / α ≤ Real.log N := by
    have h := Real.log_le_log (Real.exp_pos _) hexpN
    rwa [Real.log_exp] at h
  have hC : C ≤ α * Real.log N := by
    rw [div_le_iff₀ hα] at hlogN
    linarith
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hK : 0 ≤ N * Real.sqrt τ * Real.log N :=
    mul_nonneg (mul_nonneg hNpos.le (Real.sqrt_nonneg _)) hlog0
  have h := mul_le_mul_of_nonneg_right hC hK
  calc C * N * Real.sqrt τ * Real.log N
      = C * (N * Real.sqrt τ * Real.log N) := by ring
    _ ≤ α * Real.log N * (N * Real.sqrt τ * Real.log N) := h
    _ = α * (N * Real.sqrt τ * (Real.log N) ^ 2) := by ring

/-- Bound (6) against the sharp threshold: for a base `B` with `N = B.card` and
`τ = mixingTime B`, `C N √τ log N ≤ α · Defs.sharp B` once `N ≥ max 3 ⌈exp (C / α)⌉₊`. -/
theorem C_mul_le_sharp (B : Base) (C α : ℝ) (hα : 0 < α) (hN : 3 ≤ B.card)
    (hNC : ⌈Real.exp (C / α)⌉₊ ≤ B.card) :
    C * (B.card : ℝ) * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ)
      ≤ α * Defs.sharp B := by
  unfold Defs.sharp
  exact C_mul_le_alpha B.card (mixingTime B : ℝ) C α hα hN hNC

end IdlaCyl.Reduction
