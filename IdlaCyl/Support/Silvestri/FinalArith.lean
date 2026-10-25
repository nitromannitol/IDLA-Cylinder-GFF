module

public import IdlaCyl.Support.Silvestri.Params
public import Mathlib

@[expose] public section

/-!
# Arithmetic of the final proof of Silvestri's Proposition 2

For a base `B` with `N = B.card` vertices, `holdFail B` is the per-attempt failure
budget of `Params.lean`: the left side of `attempt_budget_le`, which is at most `N^{-3}`
once `6 ≤ N`. For `m : ℕ` and `γ > 0`, the attempt count `attempts m γ` is at least `1`
and satisfies `m + γ ≤ 3 · attempts m γ`.

The file proves:

* `holdFail` is nonnegative and at most `N^{-3}` for `6 ≤ N`;
* the attempt count bounds: `1 ≤ attempts m γ` and `m + γ ≤ 3 · attempts m γ`;
* the union bound `T · holdFail^K ≤ N^{-γ}` when `T ≤ N^m` and `m + γ ≤ 3K`;
* the conversion of that bound to `ENNReal`, giving
  `ENNReal.ofReal (1 - N^{-γ}) ≤ 1 - T · ENNReal.ofReal (holdFail^K)`;
* the ladder inclusion `R (K · h) ⊆ R (14 K √τ log N)` for `6 ≤ N`, where `h = ladderStep`.
-/

namespace IdlaCyl.Silvestri

noncomputable section

/-- The per-attempt failure budget of the ladder, the left side of `attempt_budget_le`:
`2 (e^{-h²/(4m)} + e^{-m/2}) + 2 · 2^{-⌊m/τ⌋}`, where `h = ladderStep B`, `m = holdLen B`
and `τ = silvestriMixingTime B`. -/
def holdFail (B : Base) : ℝ :=
  2 * (Real.exp (-(ladderStep B : ℝ) ^ 2 / (4 * holdLen B))
      + Real.exp (-(holdLen B : ℝ) / 2))
    + 2 * (1 / 2 : ℝ) ^ (holdLen B / External.silvestriMixingTime B)

/-- The per-attempt failure budget is nonnegative. -/
theorem holdFail_nonneg (B : Base) : 0 ≤ holdFail B := by
  unfold holdFail
  positivity

/-- For `6 ≤ N`, the per-attempt failure budget is at most `N^{-3}`. -/
theorem holdFail_le (B : Base) (hN : 6 ≤ B.card) :
    holdFail B ≤ (B.card : ℝ) ^ (-(3 : ℝ)) :=
  attempt_budget_le B hN

/-- The attempt count `attempts m γ` is at least one when `γ > 0`, and
`m + γ ≤ 3 · attempts m γ`. -/
theorem attempts_spec (m : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    1 ≤ attempts m γ ∧ (m : ℝ) + γ ≤ 3 * attempts m γ := by
  constructor
  · unfold attempts
    have hpos : (0 : ℝ) < ((m : ℝ) + γ) / 3 := by
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    exact Nat.ceil_pos.mpr hpos
  · have := Nat.le_ceil (((m : ℝ) + γ) / 3)
    unfold attempts
    linarith

/-- The `K`-fold product of the per-attempt budget is at most `N^{-3K}`. -/
theorem holdFail_pow_le (B : Base) (hN : 6 ≤ B.card) (K : ℕ) :
    holdFail B ^ K ≤ (B.card : ℝ) ^ (-(3 * (K : ℝ))) := by
  have hN0 : (0 : ℝ) < B.card := by exact_mod_cast (show 0 < B.card by omega)
  have hq0 : 0 ≤ holdFail B := holdFail_nonneg B
  have h1 : holdFail B ^ K ≤ ((B.card : ℝ) ^ (-(3 : ℝ))) ^ K :=
    pow_le_pow_left₀ hq0 (holdFail_le B hN) K
  have h2 : ((B.card : ℝ) ^ (-(3 : ℝ))) ^ K = (B.card : ℝ) ^ (-(3 * (K : ℝ))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    congr 1
    ring
  rw [← h2]
  exact h1

/-- Union bound for the attempts: `T · holdFail^K ≤ N^{-γ}` when `T ≤ N^m` and
`m + γ ≤ 3K`, for `6 ≤ N`. -/
theorem total_fail_le (B : Base) (T m K : ℕ) (γ : ℝ) (hN : 6 ≤ B.card)
    (hTm : T ≤ B.card ^ m) (hK : (m : ℝ) + γ ≤ 3 * K) :
    (T : ℝ) * holdFail B ^ K ≤ (B.card : ℝ) ^ (-γ) := by
  have hN0 : (0 : ℝ) < B.card := by exact_mod_cast (show 0 < B.card by omega)
  have hN1 : (1 : ℝ) ≤ B.card := by exact_mod_cast (show 1 ≤ B.card by omega)
  have hq0 : 0 ≤ holdFail B := holdFail_nonneg B
  have hT : (T : ℝ) ≤ (B.card : ℝ) ^ (m : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast hTm
  calc (T : ℝ) * holdFail B ^ K
      ≤ (B.card : ℝ) ^ (m : ℝ) * (B.card : ℝ) ^ (-(3 * (K : ℝ))) :=
        mul_le_mul hT (holdFail_pow_le B hN K) (pow_nonneg hq0 K)
          (Real.rpow_nonneg hN0.le _)
    _ = (B.card : ℝ) ^ ((m : ℝ) + -(3 * (K : ℝ))) := by
        rw [Real.rpow_add hN0]
    _ ≤ (B.card : ℝ) ^ (-γ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

/-- Conversion of the union bound to `ENNReal`: if `T · q ≤ N^{-γ}` and `q ≥ 0`, then
`ENNReal.ofReal (1 - N^{-γ}) ≤ 1 - T · ENNReal.ofReal q`. -/
theorem ofReal_one_sub_le_budget (N γ q : ℝ) (T : ℕ) (hq : 0 ≤ q)
    (hT : (T : ℝ) * q ≤ N ^ (-γ)) :
    ENNReal.ofReal (1 - N ^ (-γ)) ≤ 1 - (T : ENNReal) * ENNReal.ofReal q := by
  have hx : 0 ≤ N ^ (-γ) := le_trans (mul_nonneg (Nat.cast_nonneg T) hq) hT
  have hmul : (T : ENNReal) * ENNReal.ofReal q ≤ ENNReal.ofReal (N ^ (-γ)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg T)]
    exact ENNReal.ofReal_le_ofReal hT
  rw [ENNReal.ofReal_sub 1 hx, ENNReal.ofReal_one]
  exact tsub_le_tsub_left hmul 1

/-- For `0 < γ`, `6 ≤ N` and `T ≤ N^m`, the lower bound `1 - N^{-γ}` is at most
`1 - T · holdFail^{attempts m γ}`, the form in which the union bound over `T` walkers
is stated in `ENNReal`. -/
theorem fail_mul_le (B : Base) (m T : ℕ) (γ : ℝ) (hγ : 0 < γ) (hN : 6 ≤ B.card)
    (hTm : T ≤ B.card ^ m) :
    ENNReal.ofReal (1 - (B.card : ℝ) ^ (-γ))
      ≤ 1 - (T : ENNReal) * ENNReal.ofReal (holdFail B ^ attempts m γ) := by
  obtain ⟨_, h2⟩ := attempts_spec m γ hγ
  exact ofReal_one_sub_le_budget (B.card : ℝ) γ (holdFail B ^ attempts m γ) T
    (pow_nonneg (holdFail_nonneg B) _) (total_fail_le B T m (attempts m γ) γ hN hTm h2)

/-- The ladder levels `K · ladderStep B` lie in the half-cylinder of height
`14 K √τ log N`, for `6 ≤ N`. The right side is the rectangle of the frozen statement
with `b = 14 K`. -/
theorem ladder_rect (B : Base) (hN : 6 ≤ B.card) (K : ℕ) :
    R B ((K : ℝ) * ladderStep B) ⊆
      R B (14 * (K : ℝ) * Real.sqrt (External.silvestriMixingTime B) * Real.log (B.card : ℝ)) := by
  apply R_mono
  have h := ladder_le B hN K
  calc (K : ℝ) * ladderStep B
      ≤ 14 * (K : ℝ) * (Real.sqrt (External.silvestriMixingTime B) * Real.log (B.card : ℝ)) := h
    _ = 14 * (K : ℝ) * Real.sqrt (External.silvestriMixingTime B) * Real.log (B.card : ℝ) := by
        ring

end

end IdlaCyl.Silvestri
