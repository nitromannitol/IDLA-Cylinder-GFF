/-
The stationary release-layer identity for any finite amount of ordinary growth.
Source: paper/idla-cylinder-gff.tex, tex:246-265,595-610,1440-1453.
All actual occupied sites are retained, including sites above L.
-/
import IdlaCyl.Support.Reduction.EntranceTail
import IdlaCyl.Support.Reduction.BufferGrowth

namespace IdlaCyl.Reduction

open MeasureTheory

/-- The initial rectangle persists under the actual finite-cluster growth law. -/
theorem layerGrowthLaw_ae_filled (B : Base) (F : ResumeFinite B) (h L : ℤ)
    (hF : R B (L : ℝ) ⊆ resumeSeed B F) (n : ℕ) :
    ∀ᵐ G ∂layerGrowthLaw B F h n, G ∈ filled B L := by
  apply (ae_map_iff (measurable_resumeGrow B F n).aemeasurable
    (Set.to_countable _).measurableSet).mpr
  exact Filter.Eventually.of_forall (fun ω => hF.trans (seed_subset_growth B F ω n))

/-- Releasing from any lower stationary layer gives exactly the same finite growth law. -/
theorem below_layer_release_growth (B : Base) (F : ResumeFinite B)
    (h L : ℤ) (hhL : h ≤ L) (hF : R B (L : ℝ) ⊆ resumeSeed B F)
    (n : ℕ) : layerGrowthLaw B F h n = layerGrowthLaw B F L n := by
  induction n with
  | zero => rw [layerGrowthLaw_zero, layerGrowthLaw_zero]
  | succ n ih =>
      rw [layerGrowthLaw_succ, layerGrowthLaw_succ, ih]
      apply Measure.bind_congr_right
      filter_upwards [layerGrowthLaw_ae_filled B F L L hF n] with G hG
      exact below_layer_release_step B G h L hhL hG

end IdlaCyl.Reduction
