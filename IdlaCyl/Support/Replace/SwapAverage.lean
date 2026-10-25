module

public import IdlaCyl.Support.Replace.SwapLayer
public import IdlaCyl.Support.LeReplaceInputs

@[expose] public section

/-!
Layer averaging for the canonical resampled difference (`tex:836-848`).
The mass bound is `2`, from the trajectory exchange theorem, independently
of the number of particles or the slab thickness.
-/

namespace IdlaCyl.Replace

attribute [local instance] Classical.propDecidable

open MeasureTheory
open scoped BigOperators

variable (B : Base)

/-- Square mass of a resampled difference in a fixed finite slab. -/
noncomputable def swapSlabMass (T j : ℕ) (Y : Finset ℤ) (f : Site B → ℝ)
    (z : TrajSeq B × (ℕ → Site B)) : ℝ :=
  ∑ y ∈ Y, ∑ x : B.V, if (x, y) ∈ swapSites B T j z then f (x, y) ^ 2 else 0

private theorem integrable_swapOccupation (T j : ℕ) (p : Site B) (c : ℝ) :
    Integrable (fun z : TrajSeq B × (ℕ → Site B) =>
      if p ∈ swapSites B T j z then c else 0) (swapLaw B) :=
  by
    have hi : Integrable
        ({z : TrajSeq B × (ℕ → Site B) | p ∈ swapSites B T j z}.indicator (fun _ => c))
        (swapLaw B) := (integrable_const c).indicator (measurableSet_mem_swapSites B T j p)
    apply hi.congr
    refine .of_forall fun z => ?_
    by_cases h : p ∈ swapSites B T j z <;> simp [h]

/-- The slab square mass is integrable under the independent-resampling law. -/
theorem integrable_swapSlabMass (T j : ℕ) (Y : Finset ℤ) (f : Site B → ℝ) :
    Integrable (swapSlabMass B T j Y f) (swapLaw B) :=
  integrable_finsetSum _ fun y _ => integrable_finsetSum _ fun x _ =>
    integrable_swapOccupation B T j (x, y) (f (x, y) ^ 2)

/-- Expected square mass equals the layer mean squares weighted by the
horizontal-constant site probabilities. -/
theorem integral_swapSlabMass (T j : ℕ) (Y : Finset ℤ) (f : Site B → ℝ) (x₀ : B.V) :
    (∫ z, swapSlabMass B T j Y f z ∂swapLaw B) =
      ∑ y ∈ Y, (swapLaw B).real {z | (x₀, y) ∈ swapSites B T j z} *
        ((B.card : ℝ) * layerMeanSquare B f y) := by
  unfold swapSlabMass
  rw [integral_finsetSum _ (fun y _ => integrable_finsetSum _ (fun x _ =>
    integrable_swapOccupation B T j (x, y) (f (x, y) ^ 2)))]
  apply Finset.sum_congr rfl
  intro y _
  rw [card_mul_layerMeanSquare, Finset.mul_sum,
    integral_finsetSum _ (fun x _ => integrable_swapOccupation B T j (x, y) (f (x, y) ^ 2))]
  apply Finset.sum_congr rfl
  intro x _
  have heq : (fun z : TrajSeq B × (ℕ → Site B) =>
      if (x, y) ∈ swapSites B T j z then f (x, y) ^ 2 else 0) =
      {z : TrajSeq B × (ℕ → Site B) | (x, y) ∈ swapSites B T j z}.indicator
        (fun _ => f (x, y) ^ 2) := by
    funext z
    by_cases h : (x, y) ∈ swapSites B T j z <;> simp [h]
  rw [heq]
  rw [integral_indicator_const _ (measurableSet_mem_swapSites B T j (x, y)), smul_eq_mul,
    swapSites_layer_constancy B T j x x₀ y]

/-- The number of resampled-difference sites in any finite slab is at most two. -/
theorem swapSlabMass_one_le_two (T j : ℕ) (Y : Finset ℤ)
    (z : TrajSeq B × (ℕ → Site B)) :
    swapSlabMass B T j Y (fun _ => 1) z ≤ 2 := by
  classical
  let Q : Finset (Site B) := Finset.univ.product Y
  have he : swapSlabMass B T j Y (fun _ => 1) z =
      ((Q ∩ swapSites B T j z).card : ℝ) := by
    unfold swapSlabMass
    rw [Finset.sum_comm, ← Finset.sum_product (Finset.univ : Finset B.V) Y
      (fun p : Site B => if p ∈ swapSites B T j z then (1 : ℝ) ^ 2 else 0)]
    change (∑ p ∈ Q, if p ∈ swapSites B T j z then (1 : ℝ) ^ 2 else 0) = _
    simp only [one_pow, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [he]
  exact_mod_cast (Finset.card_le_card (Finset.inter_subset_right :
    Q ∩ swapSites B T j z ⊆ swapSites B T j z)).trans (swapSites_card_le_two B T j z)

/-- The total expected layer weight in any finite slab is at most two. -/
theorem swapSites_slab_mass_le_two (T j : ℕ) (Y : Finset ℤ) (x₀ : B.V) :
    (∑ y ∈ Y, (B.card : ℝ) *
      (swapLaw B).real {z | (x₀, y) ∈ swapSites B T j z}) ≤ 2 := by
  have he := integral_swapSlabMass B T j Y (fun _ => 1) x₀
  have hcard (y : ℤ) : (B.card : ℝ) * layerMeanSquare B (fun _ => 1) y = B.card := by
    rw [card_mul_layerMeanSquare]
    simp only [one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rfl
  simp_rw [hcard, mul_comm _ (B.card : ℝ)] at he
  rw [← he]
  have hi := integrable_swapSlabMass B T j Y (fun _ => 1)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
    integral_mono hi (integrable_const (2 : ℝ)) (swapSlabMass_one_le_two B T j Y)

/-- The canonical `eq:layeravg` estimate: at most twice the maximal layer
mean square, using the resampled difference rather than the whole cluster. -/
theorem integral_swapSlabMass_le (T j : ℕ) (Y : Finset ℤ) (f : Site B → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ y ∈ Y, layerMeanSquare B f y ≤ M) :
    (∫ z, swapSlabMass B T j Y f z ∂swapLaw B) ≤ 2 * M := by
  rw [integral_swapSlabMass B T j Y f B.pt]
  calc
    _ ≤ ∑ y ∈ Y, ((B.card : ℝ) *
        (swapLaw B).real {z | (B.pt, y) ∈ swapSites B T j z}) * M := by
      apply Finset.sum_le_sum
      intro y hy
      calc
        _ = ((B.card : ℝ) *
            (swapLaw B).real {z | (B.pt, y) ∈ swapSites B T j z}) *
            layerMeanSquare B f y := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hbound y hy)
          (mul_nonneg (Nat.cast_nonneg _) (ENNReal.toReal_nonneg))
    _ = (∑ y ∈ Y, (B.card : ℝ) *
        (swapLaw B).real {z | (B.pt, y) ∈ swapSites B T j z}) * M := by
      rw [Finset.sum_mul]
    _ ≤ 2 * M := mul_le_mul_of_nonneg_right (swapSites_slab_mass_le_two B T j Y B.pt) hM

end IdlaCyl.Replace
