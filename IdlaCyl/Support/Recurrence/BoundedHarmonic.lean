import IdlaCyl.Support.Base

/-!
# Bounded harmonic functions on a half-line

The deterministic core of the discharge of `IdlaCyl.External.LazyRwRecurrent`
(`tex:600-604`): a function `g : ℤ → ℝ` with values in `[0, 1]` on `(-∞, k]`,
harmonic for the symmetric walk at every point of `(-∞, k)`, and vanishing at
`k`, vanishes identically on `(-∞, k]`.

The proof shows `g (k - m) = m * g (k - 1)` by two-step induction, so boundedness
forces `g (k - 1) = 0`.
-/

namespace IdlaCyl.Recurrence

/-- Linear growth away from the boundary: `g (k - m) = m * g (k - 1)`. -/
theorem bounded_harmonic_halfline_linear (g : ℤ → ℝ) (k : ℤ) (hk : g k = 0)
    (hh : ∀ y < k, 2 * g y = g (y + 1) + g (y - 1)) :
    ∀ m : ℕ, g (k - m) = m * g (k - 1) := by
  intro m
  induction m using Nat.twoStepInduction with
  | zero => simpa using hk
  | one => simp
  | more m ih0 ih1 =>
    have h := hh (k - ((m + 1 : ℕ) : ℤ)) (by omega)
    have e1 : k - ((m + 1 : ℕ) : ℤ) + 1 = k - (m : ℤ) := by push_cast; ring
    have e2 : k - ((m + 1 : ℕ) : ℤ) - 1 = k - ((m + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2] at h
    push_cast at h ih0 ih1 ⊢
    linarith

theorem bounded_harmonic_halfline (g : ℤ → ℝ) (k : ℤ) (hk : g k = 0)
    (hb : ∀ y ≤ k, 0 ≤ g y ∧ g y ≤ 1)
    (hh : ∀ y < k, 2 * g y = g (y + 1) + g (y - 1)) :
    ∀ y ≤ k, g y = 0 := by
  have hlin := bounded_harmonic_halfline_linear g k hk hh
  have h1 : g (k - 1) = 0 := by
    have hnn : 0 ≤ g (k - 1) := (hb (k - 1) (by omega)).1
    by_contra hne
    have hpos : 0 < g (k - 1) := lt_of_le_of_ne hnn (Ne.symm hne)
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / g (k - 1))
    have hm' : 1 < (m : ℝ) * g (k - 1) := by
      rwa [div_lt_iff₀ hpos] at hm
    have hle := (hb (k - m) (by omega)).2
    rw [hlin m] at hle
    linarith
  intro y hy
  have hnat : ((k - y).toNat : ℤ) = k - y := Int.toNat_of_nonneg (by omega)
  have hy' : y = k - ((k - y).toNat : ℕ) := by omega
  rw [hy', hlin, h1, mul_zero]

end IdlaCyl.Recurrence
