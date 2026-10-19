import IdlaCyl.Support.WeightedStability

set_option autoImplicit false

/-!
# The layer-averaging algebra in the Efron--Stein step

Here `r y` is a nonnegative inclusion weight that is constant over a horizontal
layer. Establishing that constancy from a random trajectory law and a
transitive group action is not assumed silently: it is a separate outstanding
probabilistic/symmetry obligation. This module is only the deterministic
weighted-sum inequality used after that obligation is established.
-/

namespace IdlaCyl

open scoped BigOperators

/-- Layerwise L² control removes the otherwise spurious factor |V|. -/
theorem layer_weighted_energy_le {V Y : Type*} [Fintype V]
    (s : Finset Y) (r : Y → ℝ) (f : V → Y → ℝ) (L B : ℝ)
    (hr : ∀ y ∈ s, 0 ≤ r y) (hL : 0 ≤ L)
    (hlayer : ∀ y ∈ s, (∑ x, f x y ^ 2) ≤ (Fintype.card V : ℝ) * L)
    (hmass : (∑ y ∈ s, r y * (Fintype.card V : ℝ)) ≤ B) :
    (∑ y ∈ s, ∑ x, r y * f x y ^ 2) ≤ B * L := by
  calc
    (∑ y ∈ s, ∑ x, r y * f x y ^ 2) =
        ∑ y ∈ s, r y * (∑ x, f x y ^ 2) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ y ∈ s, r y * ((Fintype.card V : ℝ) * L) := by
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_left (hlayer y hy) (hr y hy)
    _ = (∑ y ∈ s, r y * (Fintype.card V : ℝ)) * L := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ ≤ B * L := mul_le_mul_of_nonneg_right hmass hL

/-- A changed set of expected size at most two contributes at most 2 L. -/
theorem two_site_layer_energy_le {V Y : Type*} [Fintype V]
    (s : Finset Y) (r : Y → ℝ) (f : V → Y → ℝ) (L : ℝ)
    (hr : ∀ y ∈ s, 0 ≤ r y) (hL : 0 ≤ L)
    (hlayer : ∀ y ∈ s, (∑ x, f x y ^ 2) ≤ (Fintype.card V : ℝ) * L)
    (hmass : (∑ y ∈ s, r y * (Fintype.card V : ℝ)) ≤ 2) :
    (∑ y ∈ s, ∑ x, r y * f x y ^ 2) ≤ 2 * L := by
  exact layer_weighted_energy_le s r f L 2 hr hL hlayer hmass

end IdlaCyl
