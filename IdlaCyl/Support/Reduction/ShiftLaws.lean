/-
Translation of the actual uniform canonical growth law.
Source: paper/idla-cylinder-gff.tex, tex:246-265,1440-1453;
The entire finite extension is shifted.
-/
import IdlaCyl.Support.Reduction.ShiftFinite

namespace IdlaCyl.Reduction

open MeasureTheory

/-- A uniform layer translated vertically is the uniform law on the translated layer. -/
theorem layerLawAt_map_shift (B : Base) (h k : ℤ) :
    (layerLawAt B h).map (outerShift B k) = layerLawAt B (h + k) := by
  unfold layerLawAt
  rw [Measure.map_sum (measurable_of_countable (outerShift B k)).aemeasurable]
  simp only [Measure.map_smul, Measure.map_dirac' (measurable_of_countable (outerShift B k))]
  rfl

/-- Translating a whole stationary walk translates its starting layer. -/
theorem walkLawUniformAt_map_shift (B : Base) (h k : ℤ) :
    (walkLawUniformAt B h).map (outerShiftPath B k) = walkLawUniformAt B (h + k) := by
  rw [walkLawUniformAt_eq_bind, walkLawUniformAt_eq_bind,
    resume_map_bind _ _ _ (measurable_of_countable _) (measurable_outerShiftPath B k)]
  simp_rw [walkPathLaw_map_outerShift]
  rw [← resume_bind_map _ _ _ (measurable_of_countable _) (measurable_of_countable _),
    layerLawAt_map_shift]

/-- Simultaneous translation preserves independence of the entire driving family. -/
theorem layerDrivingLaw_map_shift (B : Base) (h k : ℤ) :
    (layerDrivingLaw B h).map (outerShiftTraj B k) = layerDrivingLaw B (h + k) := by
  unfold layerDrivingLaw outerShiftTraj
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => walkLawUniformAt B h)
    (fun _ => measurable_outerShiftPath B k)]
  simp only [walkLawUniformAt_map_shift]

/-- Canonical finite growth commutes with upward translation pathwise. -/
theorem resumeGrow_shiftFinite (B : Base) (L : ℕ) (F : ResumeFinite B)
    (ω : TrajSeq B) (n : ℕ) :
    resumeGrow B (shiftFinite B L F) (outerShiftTraj B (L : ℤ) ω) n =
      shiftFinite B L (resumeGrow B F ω n) := by
  apply resumeSeed_injective B
  rw [resumeSeed_grow, resumeSeed_shiftFinite, resumeSeed_shiftFinite,
    resumeSeed_grow, clusterFrom_outerShift]

/-- The shifted canonical growth marginal is exactly growth from the shifted seed. -/
theorem layerGrowthLaw_map_shiftFinite (B : Base) (L : ℕ) (F : ResumeFinite B)
    (h : ℤ) (n : ℕ) :
    (layerGrowthLaw B F h n).map (shiftFinite B L) =
      layerGrowthLaw B (shiftFinite B L F) (h + (L : ℤ)) n := by
  unfold layerGrowthLaw
  rw [Measure.map_map (measurable_of_countable _) (measurable_resumeGrow B F n),
    ← layerDrivingLaw_map_shift B h (L : ℤ),
    Measure.map_map (measurable_resumeGrow B (shiftFinite B L F) n)
      (measurable_outerShiftTraj B (L : ℤ))]
  congr 1
  funext ω
  exact (resumeGrow_shiftFinite B L F ω n).symm

end IdlaCyl.Reduction
