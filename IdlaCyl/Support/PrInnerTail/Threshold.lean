import IdlaCyl.Support.PrInnerTail.SlabUnion

/-!
# Threshold arithmetic of `pr:inner`

The arithmetic that closes the second inequality of `pr:inner`
(`paper/idla-cylinder-gff.tex:1221-1234`), with no probability:

* `L_T = log N + log₊(T/N)` and `T ≤ e^{L_T}` (`e^{L_T} = max{N, T}`);
* the slab `V_N × {1, …, h}` has `N · h⁺` sites, at most `T` when `h ≤ T/N`;
* `T · e^{-(ν+4) L_T} ≤ N^{-(ν+1)}` for `N ≥ 1`, `T ≥ 0`, `ν ≥ -3` (`tex:1231`);
* `ℓ_*² N / (4T) = (C²/4) L_T` for `ℓ_* = C √((T/N) L_T)`, so the condition
  `4(ν+4) ≤ C²` gives `(ν+4) L_T ≤ ℓ_*² N / (4T)` (`tex:1223`);
* for `N ≥ 256 C⁴ + 1` and `T ≥ 16 C² N log N`, `ℓ_* ≤ T/(2N)` (`tex:1225`).
-/

namespace IdlaCyl.PrInnerTail

/-- The logarithmic height `L_T = log N + log₊(T/N)` (`tex:1221`), with `log₊ x = max (log x) 0`
as in `tex:270`. -/
noncomputable def logTerm (N T : ℝ) : ℝ := Real.log N + max (Real.log (T / N)) 0

/-- `L_T ≥ log N ≥ 0` for `N ≥ 1`, because `log₊ ≥ 0` (`tex:1221`). -/
theorem logTerm_nonneg (N T : ℝ) (hN : 1 ≤ N) : 0 ≤ logTerm N T := by
  have h1 : 0 ≤ Real.log N := Real.log_nonneg hN
  have h2 : 0 ≤ max (Real.log (T / N)) 0 := le_max_right _ _
  unfold logTerm
  linarith

/-- `T ≤ e^{L_T}` for `N > 0` and `T ≥ 0`, since `e^{L_T} = max{N, T}` (`tex:1231`). -/
theorem le_exp_logTerm (N T : ℝ) (hN : 0 < N) (hT : 0 ≤ T) :
    T ≤ Real.exp (logTerm N T) := by
  rcases hT.eq_or_lt with h0 | hpos
  · rw [← h0]
    exact (Real.exp_pos _).le
  · have hq : 0 < T / N := div_pos hpos hN
    have hmax : Real.log (T / N) ≤ max (Real.log (T / N)) 0 := le_max_left _ _
    have hexp : T / N ≤ Real.exp (max (Real.log (T / N)) 0) :=
      (Real.exp_log hq).symm.le.trans (Real.exp_le_exp.mpr hmax)
    calc T = N * (T / N) := by field_simp
      _ ≤ N * Real.exp (max (Real.log (T / N)) 0) := mul_le_mul_of_nonneg_left hexp hN.le
      _ = Real.exp (logTerm N T) := by
        rw [logTerm, Real.exp_add, Real.exp_log hN]

/-- The closing arithmetic of `pr:inner` (`tex:1231`): for `N ≥ 1`, `T ≥ 0` and `ν ≥ -3`,
`T · e^{-(ν+4) L_T} ≤ N^{-(ν+1)}`. The proof uses `T ≤ e^{L_T}`, which turns the left side into
`e^{-(ν+3) L_T}`; `L_T ≥ log N` with `ν + 3 ≥ 0` bounds that by `N^{-(ν+3)}`; and `N ≥ 1` gives
`N^{-(ν+3)} ≤ N^{-(ν+1)}`. -/
theorem mul_exp_neg_logTerm_le (N T ν : ℝ) (hN : 1 ≤ N) (hT : 0 ≤ T) (hν : -3 ≤ ν) :
    T * Real.exp (-(ν + 4) * logTerm N T) ≤ N ^ (-(ν + 1)) := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  have hL : Real.log N ≤ logTerm N T := by
    unfold logTerm
    linarith [le_max_right (Real.log (T / N)) 0]
  have hstep1 : T * Real.exp (-(ν + 4) * logTerm N T)
      ≤ Real.exp (logTerm N T) * Real.exp (-(ν + 4) * logTerm N T) :=
    mul_le_mul_of_nonneg_right (le_exp_logTerm N T hN0 hT) (Real.exp_pos _).le
  have hstep2 : Real.exp (logTerm N T) * Real.exp (-(ν + 4) * logTerm N T)
      = Real.exp (-(ν + 3) * logTerm N T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hstep3 : Real.exp (-(ν + 3) * logTerm N T) ≤ Real.exp (-(ν + 3) * Real.log N) :=
    Real.exp_le_exp.mpr
      (by linarith [mul_le_mul_of_nonneg_left hL (by linarith : (0 : ℝ) ≤ ν + 3)])
  have hstep4 : Real.exp (-(ν + 3) * Real.log N) = N ^ (-(ν + 3)) := by
    rw [Real.rpow_def_of_pos hN0]
    congr 1
    ring
  have hstep5 : N ^ (-(ν + 3)) ≤ N ^ (-(ν + 1)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  linarith [hstep1, hstep2, hstep3, hstep4, hstep5]

/-- The lower-tail exponent at `ℓ_* = C √((T/N) L_T)` (`tex:1223`): `ℓ_*² N / (4T) = (C²/4) L_T`
for `N ≥ 1` and `T > 0`. -/
theorem ell_star_sq_mul_div (N T C : ℝ) (hN : 1 ≤ N) (hT : 0 < T) :
    (C * Real.sqrt (T / N * logTerm N T)) ^ 2 * N / (4 * T) = C ^ 2 / 4 * logTerm N T := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  have hNne : N ≠ 0 := hN0.ne'
  have hTne : T ≠ 0 := hT.ne'
  have hL : 0 ≤ logTerm N T := logTerm_nonneg N T hN
  rw [mul_pow, Real.sq_sqrt (mul_nonneg (div_nonneg hT.le hN0.le) hL)]
  field_simp

/-- The exponent condition (i) of `tex:1223-1234`: if `4(ν + 4) ≤ C²`, then
`(ν + 4) L_T ≤ ℓ_*² N / (4T)` for `ℓ_* = C √((T/N) L_T)`. -/
theorem ell_star_exponent_ge (N T C ν : ℝ) (hN : 1 ≤ N) (hT : 0 < T)
    (hC : 4 * (ν + 4) ≤ C ^ 2) :
    (ν + 4) * logTerm N T ≤ (C * Real.sqrt (T / N * logTerm N T)) ^ 2 * N / (4 * T) := by
  rw [ell_star_sq_mul_div N T C hN hT]
  have hC' : ν + 4 ≤ C ^ 2 / 4 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hC' (logTerm_nonneg N T hN)]

/-- The slab `V_N × {1, …, h}` has `N · h⁺` sites, where `h⁺ = max h 0` (`tex:1231`). -/
theorem card_slab (B : Base) (h : ℤ) : (slab B h).card = B.card * h.toNat := by
  rw [slab, Finset.card_product, Finset.card_univ, Int.card_Icc, add_sub_cancel_right]
  rfl

/-- The slab has at most `T` sites when `h ≤ T / N` (`tex:1231`, `N h ≤ T`). -/
theorem card_slab_le (B : Base) (h : ℤ) (T : ℕ) (hT : (h : ℝ) ≤ (T : ℝ) / B.card) :
    ((slab B h).card : ℝ) ≤ T := by
  rw [card_slab]
  have hN : (0 : ℝ) < B.card := by
    have h2 : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
    linarith
  rcases le_or_gt h 0 with h0 | h0
  · rw [Int.toNat_of_nonpos h0]
    simp
  · have hcast : ((h.toNat : ℕ) : ℝ) = (h : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h0.le
    rw [Nat.cast_mul, hcast, mul_comm]
    exact (le_div_iff₀ hN).mp hT

/-- The core inequality of `tex:1225`: for `N ≥ 256 C⁴ + 1` and `v ≥ 16 C² log N`, the bound
`4 C² L ≤ v` holds, where `L = log N + log₊ v`. If `v ≤ N` then `log₊ v ≤ log N`, so
`4 C² L ≤ 8 C² log N ≤ v`. If `N ≤ v` then `log v ≤ 2 √v` and `√v ≥ 16 C²`, so
`4 C² L ≤ 8 C² log v ≤ 16 C² √v ≤ v`. -/
theorem four_sq_mul_le (N v C : ℝ) (hC : 0 ≤ C) (hN : 256 * C ^ 4 + 1 ≤ N)
    (hv : 16 * C ^ 2 * Real.log N ≤ v) :
    4 * C ^ 2 * (Real.log N + max (Real.log v) 0) ≤ v := by
  have hN1 : 1 ≤ N := by nlinarith [pow_nonneg hC 4]
  have hN0 : 0 < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  have hv0 : 0 ≤ v := le_trans (mul_nonneg (mul_nonneg (by norm_num) hC2) hlogN) hv
  rcases le_total v N with hvN | hvN
  · have hlogv : Real.log v ≤ Real.log N := by
      rcases hv0.eq_or_lt with h0 | hpos
      · rw [← h0, Real.log_zero]
        exact hlogN
      · exact Real.log_le_log hpos hvN
    have hmax : max (Real.log v) 0 ≤ Real.log N := max_le hlogv hlogN
    nlinarith [mul_le_mul_of_nonneg_left hmax (by positivity : (0 : ℝ) ≤ 4 * C ^ 2),
      mul_nonneg hC2 hlogN]
  · have hpos : 0 < v := lt_of_lt_of_le hN0 hvN
    have hlogNv : Real.log N ≤ Real.log v := Real.log_le_log hN0 hvN
    have hmaxv : max (Real.log v) 0 = Real.log v := max_eq_left (le_trans hlogN hlogNv)
    have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hpos
    have hlogv2 : Real.log v ≤ 2 * Real.sqrt v := by
      have h1 : Real.log (Real.sqrt v) ≤ Real.sqrt v - 1 := Real.log_le_sub_one_of_pos hs
      have h2 : Real.log (Real.sqrt v) = Real.log v / 2 := Real.log_sqrt hv0
      linarith
    have hs16 : 16 * C ^ 2 ≤ Real.sqrt v := by
      have h1 : Real.sqrt ((16 * C ^ 2) ^ 2) ≤ Real.sqrt v :=
        Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_sq (by positivity)] at h1
    have h8 : 8 * C ^ 2 * Real.log v ≤ 8 * C ^ 2 * (2 * Real.sqrt v) :=
      mul_le_mul_of_nonneg_left hlogv2 (by positivity)
    have h16 : 16 * C ^ 2 * Real.sqrt v ≤ Real.sqrt v * Real.sqrt v :=
      mul_le_mul_of_nonneg_right hs16 hs.le
    have hsq : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv0
    rw [hmaxv]
    nlinarith [mul_le_mul_of_nonneg_left hlogNv (by positivity : (0 : ℝ) ≤ 4 * C ^ 2)]

/-- The threshold condition `ℓ_* ≤ T/(2N)` (`tex:1225`): for `C ≥ 0`, `N ≥ 256 C⁴ + 1` and
`T ≥ 16 C² N log N` (that is, `T ≥ K_0 N log N` with `K_0 = 16 C²`, `tex:1223`),
`C √((T/N) L_T) ≤ T / (2N)`. The proof squares the inequality and applies `four_sq_mul_le`
with `v = T/N`. -/
theorem ell_star_le_half (N T C : ℝ) (hC : 0 ≤ C) (hN : 256 * C ^ 4 + 1 ≤ N)
    (hT : 16 * C ^ 2 * N * Real.log N ≤ T) :
    C * Real.sqrt (T / N * logTerm N T) ≤ T / (2 * N) := by
  have hN1 : 1 ≤ N := by nlinarith [pow_nonneg hC 4]
  have hN0 : 0 < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hv : 16 * C ^ 2 * Real.log N ≤ T / N := by
    rw [le_div_iff₀ hN0]
    linarith
  have hv0 : 0 ≤ T / N := le_trans (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg C)) hlogN) hv
  have hT0 : 0 ≤ T := by
    have h16 : 0 ≤ 16 * C ^ 2 * N * Real.log N :=
      mul_nonneg (mul_nonneg (by positivity) hN0.le) hlogN
    exact le_trans h16 hT
  have hcore : 4 * C ^ 2 * logTerm N T ≤ T / N := four_sq_mul_le N (T / N) C hC hN hv
  have hL : 0 ≤ logTerm N T := logTerm_nonneg N T hN1
  have hkey : C ^ 2 * (T / N * logTerm N T) ≤ (T / (2 * N)) ^ 2 := by
    have h2N : T / (2 * N) = T / N / 2 := by ring
    rw [h2N]
    nlinarith [mul_nonneg hv0 (sub_nonneg.mpr hcore)]
  calc C * Real.sqrt (T / N * logTerm N T)
      = Real.sqrt (C ^ 2 * (T / N * logTerm N T)) := by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]
    _ ≤ Real.sqrt ((T / (2 * N)) ^ 2) := Real.sqrt_le_sqrt hkey
    _ = T / (2 * N) := Real.sqrt_sq (div_nonneg hT0 (by linarith))

end IdlaCyl.PrInnerTail
