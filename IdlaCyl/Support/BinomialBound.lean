import Mathlib

set_option autoImplicit false

/-!
# The deterministic binomial induction in Section 2

`mu m t` denotes the expected occupation of layer m+1 at time t.
This file proves the implication from the one-step recurrence to the exact
binomial estimate. Establishing that recurrence for the random walk, and the
probabilistic outer tail, remain distinct obligations.
-/

namespace IdlaCyl

/-- A comparison principle for the occupation recurrence, including t = 0. -/
theorem binomial_recurrence_bound (mu : ℕ → ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hzero : ∀ m, mu m 0 ≤ 0)
    (hbase : ∀ t, mu 0 t ≤ (t : ℝ))
    (hstep : ∀ m t, mu (m + 1) (t + 1) ≤ mu (m + 1) t + c * mu m t) :
    ∀ m t, mu m t ≤ c ^ m * (Nat.choose t (m + 1) : ℝ) := by
  intro m t
  induction t generalizing m with
  | zero =>
      simpa using hzero m
  | succ t ih =>
      cases m with
      | zero =>
          simpa using hbase (t + 1)
      | succ m =>
          have h1 := ih (m + 1)
          have h2 := mul_le_mul_of_nonneg_left (ih m) hc
          have hp :
              (Nat.choose (t + 1) (m + 2) : ℝ) =
                (Nat.choose t (m + 1) : ℝ) + (Nat.choose t (m + 2) : ℝ) := by
            exact_mod_cast Nat.choose_succ_succ t (m + 1)
          calc
            mu (m + 1) (t + 1) ≤ mu (m + 1) t + c * mu m t := hstep m t
            _ ≤ c ^ (m + 1) * (Nat.choose t (m + 2) : ℝ) +
                c * (c ^ m * (Nat.choose t (m + 1) : ℝ)) := add_le_add h1 h2
            _ = c ^ (m + 1) * (Nat.choose (t + 1) (m + 2) : ℝ) := by
              rw [hp, pow_succ]
              ring

/-- Paper normalization: c = 1 / N, and layer index is m+1. -/
theorem cylinder_binomial_recurrence (mu : ℕ → ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    (hzero : ∀ m, mu m 0 ≤ 0)
    (hbase : ∀ t, mu 0 t ≤ (t : ℝ))
    (hstep : ∀ m t, mu (m + 1) (t + 1) ≤
      mu (m + 1) t + (1 / (N : ℝ)) * mu m t) :
    ∀ m t, mu m t ≤ (1 / (N : ℝ)) ^ m * (Nat.choose t (m + 1) : ℝ) := by
  apply binomial_recurrence_bound mu (1 / (N : ℝ))
  · positivity
  · exact hzero
  · exact hbase
  · exact hstep

/-- Above time t, the recurrence bound is zero, without an asymptotic estimate. -/
theorem recurrence_zero_above_time (mu : ℕ → ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hzero : ∀ m, mu m 0 ≤ 0) (hbase : ∀ t, mu 0 t ≤ (t : ℝ))
    (hstep : ∀ m t, mu (m + 1) (t + 1) ≤ mu (m + 1) t + c * mu m t)
    (hnonneg : ∀ m t, 0 ≤ mu m t) {m t : ℕ} (ht : t < m + 1) :
    mu m t = 0 := by
  have hb := binomial_recurrence_bound mu c hc hzero hbase hstep m t
  rw [Nat.choose_eq_zero_of_lt ht, Nat.cast_zero, mul_zero] at hb
  exact le_antisymm hb (hnonneg m t)

end IdlaCyl
