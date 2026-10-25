module

public import IdlaCyl.Support.DiscreteVariance

@[expose] public section

set_option autoImplicit false

/-!
# A single-cutoff exponential-moment estimate

The inputs are explicit finite height masses and pointwise tail bounds. The
result is finite algebra, not an assumed uniform-integrability conclusion.
Its application to actual IDLA is proved in the accompanying mathematical note;
that probability-model application is not yet a Lean theorem.
-/

namespace IdlaCyl

open scoped BigOperators

theorem geometric_sum_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (∑ j ∈ Finset.range n, r ^ j) ≤ 1 / (1 - r) := by
  apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
  rw [geometric_sum_mul]
  have h := pow_nonneg hr n
  linarith

/-- The contribution of all heights beyond one cutoff is a geometric tail. -/
theorem weighted_geometric_tail_le (p q : ℕ → ℝ) (C D r s : ℝ) (L n : ℕ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrs : r * s < 1)
    (hp0 : ∀ j, 0 ≤ p (L + 1 + j))
    (hp : ∀ j, p (L + 1 + j) ≤ C * r ^ (L + 1 + j))
    (hq : ∀ j, q (L + 1 + j) ≤ D * s ^ (L + 1 + j)) :
    (∑ j ∈ Finset.range n, p (L + 1 + j) * q (L + 1 + j)) ≤
      C * D * (r * s) ^ (L + 1) / (1 - r * s) := by
  have hfactor : 0 ≤ C * D * (r * s) ^ (L + 1) :=
    mul_nonneg (mul_nonneg hC hD) (pow_nonneg (mul_nonneg hr hs) _)
  calc
    (∑ j ∈ Finset.range n, p (L + 1 + j) * q (L + 1 + j)) ≤
        ∑ j ∈ Finset.range n,
          (C * r ^ (L + 1 + j)) * (D * s ^ (L + 1 + j)) := by
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ p (L + 1 + j) * (D * s ^ (L + 1 + j)) :=
          mul_le_mul_of_nonneg_left (hq j) (hp0 j)
        _ ≤ _ := mul_le_mul_of_nonneg_right (hp j)
          (mul_nonneg hD (pow_nonneg hs _))
    _ = (C * D * (r * s) ^ (L + 1)) *
        (∑ j ∈ Finset.range n, (r * s) ^ j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [pow_add, mul_pow]
      ring
    _ ≤ (C * D * (r * s) ^ (L + 1)) * (1 / (1 - r * s)) :=
      mul_le_mul_of_nonneg_left (geometric_sum_le (r * s) (mul_nonneg hr hs) hrs n)
        hfactor
    _ = _ := by ring

/-- Low heights only cost a deterministic bound times the bad-event mass. -/
theorem low_height_bad_mass_le (p q : ℕ → ℝ) (B δ : ℝ) (L : ℕ)
    (hB : 0 ≤ B) (hp : ∀ j ≤ L, 0 ≤ p j)
    (hq : ∀ j ≤ L, q j ≤ B)
    (hmass : (∑ j ∈ Finset.range (L + 1), p j) ≤ δ) :
    (∑ j ∈ Finset.range (L + 1), p j * q j) ≤ B * δ := by
  calc
    (∑ j ∈ Finset.range (L + 1), p j * q j) ≤
        ∑ j ∈ Finset.range (L + 1), p j * B := by
      apply Finset.sum_le_sum
      intro j hj
      have hjL : j ≤ L := by have := Finset.mem_range.mp hj; omega
      exact mul_le_mul_of_nonneg_left (hq j hjL) (hp j hjL)
    _ = B * (∑ j ∈ Finset.range (L + 1), p j) := by
      rw [← Finset.sum_mul, mul_comm]
    _ ≤ B * δ := mul_le_mul_of_nonneg_left hmass hB

/-- Single-cutoff replacement for a hierarchy of bad-height events. -/
theorem single_cutoff_moment_bound (p q : ℕ → ℝ)
    (B δ C D r s : ℝ) (L n : ℕ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r * s < 1)
    (hp0 : ∀ j, 0 ≤ p j)
    (hlow : ∀ j ≤ L, q j ≤ B)
    (hmass : (∑ j ∈ Finset.range (L + 1), p j) ≤ δ)
    (hptail : ∀ j, p (L + 1 + j) ≤ C * r ^ (L + 1 + j))
    (hqtail : ∀ j, q (L + 1 + j) ≤ D * s ^ (L + 1 + j)) :
    (∑ j ∈ Finset.range (L + 1), p j * q j) +
      (∑ j ∈ Finset.range n, p (L + 1 + j) * q (L + 1 + j)) ≤
        B * δ + C * D * (r * s) ^ (L + 1) / (1 - r * s) := by
  exact add_le_add
    (low_height_bad_mass_le p q B δ L hB (fun j _ => hp0 j) hlow hmass)
    (weighted_geometric_tail_le p q C D r s L n hC hD hr hs hrs
      (fun j => hp0 _) hptail hqtail)

end IdlaCyl
