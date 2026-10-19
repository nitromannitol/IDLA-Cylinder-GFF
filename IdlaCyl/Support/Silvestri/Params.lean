import IdlaCyl.External.SilvestriProp2
import Mathlib

/-!
# Constants and the per-attempt failure budget for Silvestri's Proposition 2

For a base `B` with `N = B.card` vertices, let `τ` be Silvestri's pairwise mixing
time, `ℓ = log N` and `r = √τ · ℓ`. This file defines the ladder spacing
`h = ⌈13 r⌉₊`, the holding threshold `m = ⌈10 τ ℓ⌉₊`, the attempt count
`K = ⌈(μ + γ)/3⌉₊` and the rectangle constant `b = 14 K`. It proves:

* `1 ≤ τ`, and `0 < h`, `0 < m` for `2 ≤ N`;
* `h ≤ 14 r` and hence `K h ≤ 14 K r` for `6 ≤ N`, so the ladder levels lie in
  the rectangle of size `b r`;
* the per-attempt failure budget `2 (e^{-h²/(4m)} + e^{-m/2}) + 2 · 2^{-⌊m/τ⌋} ≤ N^{-3}`
  for `6 ≤ N`.
-/

namespace IdlaCyl.Silvestri

noncomputable section

/-- The ladder spacing `h = ⌈13 √τ log N⌉₊`. -/
def ladderStep (B : Base) : ℕ :=
  ⌈13 * (Real.sqrt (External.silvestriMixingTime B : ℝ) * Real.log (B.card : ℝ))⌉₊

/-- The holding threshold `m = ⌈10 τ log N⌉₊`. -/
def holdLen (B : Base) : ℕ :=
  ⌈10 * ((External.silvestriMixingTime B : ℝ) * Real.log (B.card : ℝ))⌉₊

/-- The attempt count `K = ⌈(μ + γ) / 3⌉₊`. -/
def attempts (μ : ℕ) (γ : ℝ) : ℕ :=
  ⌈((μ : ℝ) + γ) / 3⌉₊

/-- The rectangle constant `b = 14 K`, with `K = attempts μ γ`. -/
def bConst (μ : ℕ) (γ : ℝ) : ℝ :=
  14 * (attempts μ γ : ℝ)

/-- Silvestri's pairwise mixing time is at least one on a base with two vertices.
The defining set is nonempty by `External.silvestriMixing_nonempty`. -/
theorem tau_pos (B : Base) : 1 ≤ External.silvestriMixingTime B := by
  by_contra h
  have h0 : External.silvestriMixingTime B = 0 := by omega
  obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card
    (show 1 < Fintype.card B.V by have := B.nontrivial; omega)
  have h1 : External.silvestriTV B 0 x y ≤ 1 / 2 := by
    have := External.silvestriMixingTime_spec B x y
    rwa [h0] at this
  have e1 : basePow B 0 x x - basePow B 0 y x = 1 := by
    simp [basePow, Ne.symm hxy]
  have e2 : basePow B 0 x y - basePow B 0 y y = -1 := by
    simp [basePow, hxy]
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun z => |basePow B 0 x z - basePow B 0 y z|)
    (Finset.subset_univ ({x, y} : Finset B.V)) (fun z _ _ => abs_nonneg _)
  simp only [Finset.sum_pair hxy] at hle
  rw [e1, e2] at hle
  unfold External.silvestriTV at h1
  norm_num at hle
  linarith

/-- On a base with two vertices, the ladder spacing is positive. -/
theorem ladderStep_pos (B : Base) (hN : 2 ≤ B.card) : 0 < ladderStep B := by
  have hτ : (1 : ℝ) ≤ (External.silvestriMixingTime B : ℝ) := by
    exact_mod_cast tau_pos B
  have hlog : 0 < Real.log (B.card : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B.card by omega))
  have hs : 0 < Real.sqrt (External.silvestriMixingTime B : ℝ) :=
    Real.sqrt_pos.mpr (by linarith)
  unfold ladderStep
  apply Nat.ceil_pos.mpr
  exact mul_pos (by norm_num) (mul_pos hs hlog)

/-- On a base with two vertices, the holding threshold is positive. -/
theorem holdLen_pos (B : Base) (hN : 2 ≤ B.card) : 0 < holdLen B := by
  have hτ : (1 : ℝ) ≤ (External.silvestriMixingTime B : ℝ) := by
    exact_mod_cast tau_pos B
  have hlog : 0 < Real.log (B.card : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < B.card by omega))
  unfold holdLen
  apply Nat.ceil_pos.mpr
  exact mul_pos (by norm_num) (mul_pos (by linarith) hlog)

/-- For `6 ≤ N`, `log N ≥ 1`, since `exp 1 < 6`. -/
theorem one_le_log_card (B : Base) (hN : 6 ≤ B.card) :
    1 ≤ Real.log (B.card : ℝ) := by
  have h6 : (6 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hN
  have he : Real.exp 1 ≤ (B.card : ℝ) := by
    have := Real.exp_one_lt_d9
    norm_num at this
    linarith
  have := Real.log_le_log (Real.exp_pos 1) he
  rwa [Real.log_exp] at this

/-- For `6 ≤ N`, the spacing satisfies `h ≤ 14 r`, where `r = √τ log N ≥ 1`. -/
theorem ladderStep_le (B : Base) (hN : 6 ≤ B.card) :
    (ladderStep B : ℝ) ≤ 14 * (Real.sqrt (External.silvestriMixingTime B : ℝ) * Real.log (B.card : ℝ)) := by
  have hτ : (1 : ℝ) ≤ (External.silvestriMixingTime B : ℝ) := by
    exact_mod_cast tau_pos B
  have hl := one_le_log_card B hN
  have hs : 1 ≤ Real.sqrt (External.silvestriMixingTime B : ℝ) := by
    have := Real.sqrt_le_sqrt hτ
    rwa [Real.sqrt_one] at this
  have hr : 1 ≤ Real.sqrt (External.silvestriMixingTime B : ℝ) * Real.log (B.card : ℝ) := by
    nlinarith
  have hnn : (0 : ℝ) ≤ 13 * (Real.sqrt (External.silvestriMixingTime B : ℝ) * Real.log (B.card : ℝ)) := by
    linarith
  unfold ladderStep
  have := Nat.ceil_lt_add_one hnn
  linarith

/-- The ladder levels `K h` fit in the rectangle of size `14 K r`. -/
theorem ladder_le (B : Base) (hN : 6 ≤ B.card) (K : ℕ) :
    (K * ladderStep B : ℝ) ≤
      14 * K * (Real.sqrt (External.silvestriMixingTime B : ℝ) * Real.log (B.card : ℝ)) := by
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have := mul_le_mul_of_nonneg_left (ladderStep_le B hN) hK
  linarith

/-- Real-variable core of the budget. With `N = exp L ≥ 6`, the two exponential
terms and the dyadic term are each bounded by a fixed multiple of `exp (-3 L)`:
`2 · 5/12 + 2 · 1/36 + 1/54 = 49/54 < 1` bounds the sum by `exp (-3 L)`. -/
theorem budget_core (N L t h m : ℝ) (k : ℕ) (hN : 6 ≤ N) (hLN : Real.exp L = N)
    (ht : 1 ≤ t) (hL1 : 1 ≤ L) (hm_lo : 10 * (t * L) ≤ m) (hm_hi : m ≤ 11 * (t * L))
    (hh : 169 * (t * L ^ 2) ≤ h ^ 2) (hkL : 10 * L < (k : ℝ) + 1) :
    2 * (Real.exp (-h ^ 2 / (4 * m)) + Real.exp (-m / 2)) + 2 * (1 / 2 : ℝ) ^ k
      ≤ Real.exp (L * -3) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hTL : 1 ≤ t * L := one_le_mul_of_one_le_of_one_le ht hL1
  have hm10 : 10 * L ≤ m := by
    nlinarith [mul_le_mul_of_nonneg_right ht (by linarith : (0 : ℝ) ≤ L)]
  have hmpos : 0 < 4 * m := by linarith
  have hLlog : Real.log N = L := by rw [← hLN, Real.log_exp]
  have hs : Real.exp (L / 2) * Real.exp (L / 2) = N := by
    rw [← Real.exp_add, add_halves, hLN]
  have hs_pos : 0 < Real.exp (L / 2) := Real.exp_pos _
  have hs_ge : 12 / 5 ≤ Real.exp (L / 2) := by nlinarith
  have hA : Real.exp (-h ^ 2 / (4 * m)) ≤ Real.exp (L * -3) * (5 / 12) := by
    have h1 : -h ^ 2 / (4 * m) ≤ L * -3 + -(L / 2) := by
      rw [div_le_iff₀ hmpos]
      nlinarith [mul_le_mul_of_nonneg_left hm_hi (by linarith : (0 : ℝ) ≤ L),
        mul_nonneg (by linarith : (0 : ℝ) ≤ t) (sq_nonneg L)]
    have h2 : Real.exp (-(L / 2)) ≤ 5 / 12 := by
      rw [Real.exp_neg, ← one_div, div_le_iff₀ hs_pos]
      linarith
    calc Real.exp (-h ^ 2 / (4 * m)) ≤ Real.exp (L * -3 + -(L / 2)) := Real.exp_le_exp.mpr h1
      _ = Real.exp (L * -3) * Real.exp (-(L / 2)) := Real.exp_add _ _
      _ ≤ Real.exp (L * -3) * (5 / 12) := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  have hB : Real.exp (-m / 2) ≤ Real.exp (L * -3) * (1 / 36) := by
    have e2 : Real.exp (L * -2) = (N * N)⁻¹ := by
      rw [← hLN, ← Real.exp_add, ← Real.exp_neg]
      congr 1
      ring
    have h2 : Real.exp (L * -2) ≤ 1 / 36 := by
      rw [e2, inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
    have h1 : -m / 2 ≤ L * -3 + L * -2 := by linarith
    calc Real.exp (-m / 2) ≤ Real.exp (L * -3 + L * -2) := Real.exp_le_exp.mpr h1
      _ = Real.exp (L * -3) * Real.exp (L * -2) := Real.exp_add _ _
      _ ≤ Real.exp (L * -3) * (1 / 36) := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  have hP : Real.exp (L * -3) * (N * N * N) = 1 := by
    have e3 : Real.exp (L * -3) = (N * N * N)⁻¹ := by
      rw [← hLN, ← Real.exp_add, ← Real.exp_add, ← Real.exp_neg]
      congr 1
      ring
    rw [e3, inv_mul_cancel₀ (mul_pos (mul_pos hN0 hN0) hN0).ne']
  have hPN : Real.exp (L * -3) * N ^ 6 = N ^ 3 := by
    calc Real.exp (L * -3) * N ^ 6 = (Real.exp (L * -3) * (N * N * N)) * (N * N * N) := by ring
      _ = N ^ 3 := by rw [hP, one_mul]; ring
  have hN3 : 216 ≤ N ^ 3 := by nlinarith
  have hD : 2 * (1 / 2 : ℝ) ^ k ≤ Real.exp (L * -3) / 54 := by
    have hpow : N ^ 6 ≤ (2 : ℝ) ^ (k + 1) := by
      rw [← Real.log_le_log_iff (pow_pos hN0 6) (pow_pos (by norm_num : (0 : ℝ) < 2) _),
        Real.log_pow, Real.log_pow, hLlog]
      have h2 := Real.log_two_gt_d9
      norm_num at h2
      push_cast
      nlinarith [mul_lt_mul_of_pos_right hkL (by linarith : (0 : ℝ) < Real.log 2),
        mul_le_mul_of_nonneg_left h2.le (by linarith : (0 : ℝ) ≤ L)]
    have hC : (1 / 2 : ℝ) ^ k ≤ 2 / N ^ 6 := by
      have e : (1 / 2 : ℝ) ^ k = 2 * (1 / (2 : ℝ) ^ (k + 1)) := by
        rw [pow_succ, one_div_pow]
        ring
      rw [e, show (2 : ℝ) / N ^ 6 = 2 * (1 / N ^ 6) by ring]
      exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (pow_pos hN0 6) hpow) (by norm_num)
    have hC2 : 2 * (1 / 2 : ℝ) ^ k ≤ 4 / N ^ 6 := by
      rw [show (4 : ℝ) / N ^ 6 = 2 * (2 / N ^ 6) by ring]
      exact mul_le_mul_of_nonneg_left hC (by norm_num)
    refine hC2.trans ?_
    rw [div_le_iff₀ (pow_pos hN0 6)]
    linarith
  linarith [Real.exp_pos (L * -3)]

/-- The per-attempt failure budget: for `6 ≤ N`,
`2 (e^{-h²/(4m)} + e^{-m/2}) + 2 · 2^{-⌊m/τ⌋} ≤ N^{-3}`. -/
theorem attempt_budget_le (B : Base) (hN : 6 ≤ B.card) :
    2 * (Real.exp (-(ladderStep B : ℝ) ^ 2 / (4 * holdLen B))
        + Real.exp (-(holdLen B : ℝ) / 2))
      + 2 * (1 / 2 : ℝ) ^ (holdLen B / External.silvestriMixingTime B)
      ≤ (B.card : ℝ) ^ (-(3 : ℝ)) := by
  have hN0 : (0 : ℝ) < B.card := by exact_mod_cast (show 0 < B.card by omega)
  have hN6 : (6 : ℝ) ≤ B.card := by exact_mod_cast hN
  have hτ1 : (1 : ℝ) ≤ (External.silvestriMixingTime B : ℝ) := by exact_mod_cast tau_pos B
  have hτN : 0 < External.silvestriMixingTime B := by have := tau_pos B; omega
  have hL1 := one_le_log_card B hN
  have hTL : 1 ≤ (External.silvestriMixingTime B : ℝ) * Real.log (B.card : ℝ) :=
    one_le_mul_of_one_le_of_one_le hτ1 hL1
  have hm_lo : 10 * ((External.silvestriMixingTime B : ℝ) * Real.log (B.card : ℝ))
      ≤ (holdLen B : ℝ) := by
    unfold holdLen
    exact Nat.le_ceil _
  have hm_hi : (holdLen B : ℝ) ≤ 11 * ((External.silvestriMixingTime B : ℝ) * Real.log (B.card : ℝ)) := by
    unfold holdLen
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 10 * ((External.silvestriMixingTime B : ℝ) *
      Real.log (B.card : ℝ)) by linarith)
    linarith
  have hh : 169 * ((External.silvestriMixingTime B : ℝ) * Real.log (B.card : ℝ) ^ 2)
      ≤ (ladderStep B : ℝ) ^ 2 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ (External.silvestriMixingTime B : ℝ) by linarith)
    have hnn : (0 : ℝ) ≤ 13 * (Real.sqrt (External.silvestriMixingTime B : ℝ) *
        Real.log (B.card : ℝ)) :=
      mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) (by linarith))
    have h13 : 13 * (Real.sqrt (External.silvestriMixingTime B : ℝ) *
        Real.log (B.card : ℝ)) ≤ (ladderStep B : ℝ) := by
      unfold ladderStep
      exact Nat.le_ceil _
    have hsq := pow_le_pow_left₀ hnn h13 2
    calc 169 * ((External.silvestriMixingTime B : ℝ) * Real.log (B.card : ℝ) ^ 2)
        = (13 * (Real.sqrt (External.silvestriMixingTime B : ℝ) * Real.log (B.card : ℝ))) ^ 2 := by
          rw [mul_pow, mul_pow, hs]
          ring
      _ ≤ (ladderStep B : ℝ) ^ 2 := hsq
  have hdiv := Nat.div_add_mod (holdLen B) (External.silvestriMixingTime B)
  have hmod := Nat.mod_lt (holdLen B) hτN
  have hdivR : (External.silvestriMixingTime B : ℝ) *
      ((holdLen B / External.silvestriMixingTime B : ℕ) : ℝ) +
      ((holdLen B % External.silvestriMixingTime B : ℕ) : ℝ) = (holdLen B : ℝ) := by
    exact_mod_cast hdiv
  have hmodR : ((holdLen B % External.silvestriMixingTime B : ℕ) : ℝ) <
      (External.silvestriMixingTime B : ℝ) := by
    exact_mod_cast hmod
  have hkL : 10 * Real.log (B.card : ℝ) <
      ((holdLen B / External.silvestriMixingTime B : ℕ) : ℝ) + 1 := by
    have h1 : (External.silvestriMixingTime B : ℝ) * (10 * Real.log (B.card : ℝ)) <
        (External.silvestriMixingTime B : ℝ) *
          (((holdLen B / External.silvestriMixingTime B : ℕ) : ℝ) + 1) := by
      nlinarith
    exact lt_of_mul_lt_mul_left h1 (by linarith)
  rw [Real.rpow_def_of_pos hN0]
  exact budget_core (B.card : ℝ) (Real.log (B.card : ℝ)) (External.silvestriMixingTime B : ℝ)
    (ladderStep B : ℝ) (holdLen B : ℝ) (holdLen B / External.silvestriMixingTime B) hN6
    (Real.exp_log hN0) hτ1 hL1 hm_lo hm_hi hh hkL

end

end IdlaCyl.Silvestri
