/-
Canonical block filling from an exact rectangle.
Source: paper/idla-cylinder-gff.tex, tex:1227-1251 (block filling),
tex:246-265,595-610,1440-1453 (canonical growth).
The release layer is moved to `L`, the shifted growth is pulled back to the flat growth,
and the flat cluster is compared with the stopped cluster of `stopped_block_fill_ge`.
-/
import IdlaCyl.Support.Reduction.Block.BlockFill
import IdlaCyl.Support.Reduction.LayerRelease
import IdlaCyl.Support.Reduction.ShiftLaws
import IdlaCyl.Support.Reduction.DrivingLift

/-!
# Canonical block filling from an exact rectangle

Canonical growth from the shifted empty seed `shiftFinite B L (resumeEmpty B)`, released on a
layer `h ≤ L`, fills the rectangle of height `L + H` except on an event of probability at most
`N H e^{-H/8}`, once `2 N H` additions have been made, where `N = B.card`.  The release layer
moves up to `L` without changing the law, the shifted growth is the shift of the flat growth,
and the flat cluster contains the stopped cluster of `stopped_block_fill_ge`.
-/

namespace IdlaCyl.Reduction

open MeasureTheory
open scoped ENNReal

variable (B : Base)

/-- Shifting a finite cluster by `L` fills the rectangle of height `L + H` exactly when the
unshifted cluster fills the rectangle of height `H`. -/
theorem mem_filled_shiftFinite (L H : ℕ) (F : ResumeFinite B) :
    shiftFinite B L F ∈ filled B ((L : ℤ) + (H : ℤ)) ↔ F ∈ filled B (H : ℤ) := by
  have hR : R B ((((L : ℤ) + (H : ℤ)) : ℤ) : ℝ) = outerShift B (L : ℤ) '' R B (H : ℝ) := by
    rw [outerShift_image_R]
    congr 1
    push_cast
    ring
  unfold filled
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, hR, resumeSeed_shiftFinite,
    Set.image_subset_image_iff (outerShift B (L : ℤ)).injective, Int.cast_natCast]

/-- Growth from the shifted empty seed, observed on the rectangle of height `L + H`, has the
failure probability of the flat growth observed on the rectangle of height `H`. -/
theorem layerGrowthLaw_shiftFinite_filled_compl (L H : ℕ) (n : ℕ) :
    layerGrowthLaw B (shiftFinite B L (resumeEmpty B)) (L : ℤ) n
        (filled B ((L : ℤ) + (H : ℤ)))ᶜ =
      idlaMeasure B {ω : TrajSeq B | ¬ R B (H : ℝ) ⊆ clusterTraj B ω n} := by
  have hshift : layerGrowthLaw B (shiftFinite B L (resumeEmpty B)) (L : ℤ) n =
      (flatClusterLaw B n).map (shiftFinite B L) := by
    have h := layerGrowthLaw_map_shiftFinite B L (resumeEmpty B) 0 n
    rw [zero_add] at h
    exact h.symm
  have hset : shiftFinite B L ⁻¹' (filled B ((L : ℤ) + (H : ℤ)))ᶜ =
      {G : ResumeFinite B | G ∉ filled B (H : ℤ)} := by
    ext G
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq, mem_filled_shiftFinite]
  rw [hshift, Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet,
    hset, flatClusterLaw_eq_map,
    Measure.map_apply (measurable_resumeGrow B (resumeEmpty B) n) (Set.to_countable _).measurableSet]
  congr 1
  ext ω
  simp only [Set.mem_preimage, Set.mem_setOf_eq, filled, resumeSeed_grow, resumeSeed_empty,
    clusterTraj, Int.cast_natCast]

/-- **Canonical block filling** (`tex:1227-1251`).  Canonical additions from the shifted empty
seed, released on any layer `h ≤ L`, fill the rectangle of height `L + H` except on an event of
probability at most `N H e^{-H/8}`, once `2 N H ≤ n` additions have been made. -/
theorem canonical_block_fill (L : ℕ) (h : ℤ) (hh : h ≤ L) (H : ℕ) (hH : 1 ≤ H) (n : ℕ)
    (hn : 2 * B.card * H ≤ n) :
    layerGrowthLaw B (shiftFinite B L (resumeEmpty B)) h n (filled B ((L : ℤ) + H))ᶜ ≤
      ENNReal.ofReal ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8)) := by
  have hF : R B ((L : ℤ) : ℝ) ⊆ resumeSeed B (shiftFinite B L (resumeEmpty B)) := by
    rw [resumeSeed_shiftFinite_empty, Int.cast_natCast]
  rw [below_layer_release_growth B (shiftFinite B L (resumeEmpty B)) h (L : ℤ) hh hF n,
    layerGrowthLaw_shiftFinite_filled_compl B L H n]
  refine (measure_mono_ae ?_).trans (stopped_block_fill_ge B H hH n hn)
  filter_upwards [idlaMeasure_ae_stopped_hyp B] with ω hω
  intro hnot hmem
  exact hnot (hmem.trans (stoppedCluster_subset_clusterTraj B (H : ℤ) ω hω.2.2.2 n))

end IdlaCyl.Reduction
