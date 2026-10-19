/-
Literal layer-by-layer freezing kernels for the reduction.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396,1440-1453.
Every duplicate coupon adds one mobile copy to the queue.
The remaining count records walks whose starting vertices are still hidden.
-/
import IdlaCyl.Support.Reduction.LayerRelease
import IdlaCyl.Support.Outer.ResumePaused

attribute [local instance] Classical.propDecidable

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Settle the first arrival to an empty site and retain each later arrival as a mobile copy. -/
noncomputable def freezeCoupon (B : Base) (s : ResumeState B) (z : Site B) : ResumeState B :=
  if z ∈ resumeSeed B s.1 then (s.1, s.2 ++ [z])
  else (resumeInsert B s.1 z, s.2)

/-- Stop a new independent uniform-zero release at its first entrance to j. -/
noncomputable def freezeLayerStep (B : Base) (j : ℤ) (s : ResumeState B) :
    Measure (ResumeState B) :=
  (walkLawUniform B).map (fun X => freezeCoupon B s (firstHitSite B j X))

instance freezeLayerStep_isProbability (B : Base) (j : ℤ) (s : ResumeState B) :
    IsProbabilityMeasure (freezeLayerStep B j s) :=
  Measure.isProbabilityMeasure_map ((measurable_of_countable (freezeCoupon B s)).comp
    (measurable_firstHitSite B j)).aemeasurable

/-- Exactly M fresh releases are used for a layer, even after that layer has filled. -/
noncomputable def freezeBatch (B : Base) (j : ℤ) : ℕ → ResumeState B →
    Measure (ResumeState B)
  | 0, s => Measure.dirac s
  | M + 1, s => (freezeLayerStep B j s).bind (freezeBatch B j M)

instance freezeBatch_isProbability (B : Base) (j : ℤ) (M : ℕ) (s : ResumeState B) :
    IsProbabilityMeasure (freezeBatch B j M s) := by
  induction M generalizing s with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac s))
  | succ M ih =>
      apply isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
      exact Filter.Eventually.of_forall (fun t => ih t)

/-- Abort before the next batch if the previous layer failed; do not release later starts. -/
noncomputable def layeredPause (B : Base) (M : ℕ) : ℕ → ℕ →
    ResumeState B → ℕ → Measure (ResumeState B × ℕ)
  | 0, _, s, r => Measure.dirac (s, r)
  | n + 1, j, s, r =>
      if R B (j : ℝ) ⊆ resumeSeed B s.1 then
        (freezeBatch B (j + 1 : ℕ) M s).bind
          (fun s' => layeredPause B M n (j + 1) s' (r - M))
      else Measure.dirac (s, r)

instance layeredPause_isProbability (B : Base) (M n j : ℕ) (s : ResumeState B) (r : ℕ) :
    IsProbabilityMeasure (layeredPause B M n j s r) := by
  induction n generalizing j s r with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (s, r)))
  | succ n ih =>
      unfold layeredPause
      split_ifs
      · apply isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
        exact Filter.Eventually.of_forall (fun t => ih (j + 1) t (r - M))
      · infer_instance

/-- Complete every mobile copy, then release every still-hidden uniform start. -/
noncomputable def finishUniform (B : Base) (s : ResumeState B) (r : ℕ) :
    Measure (ResumeFinite B) :=
  (resumeRun B s.1 s.2).bind (fun F => layerGrowthLaw B F 0 r)

instance finishUniform_isProbability (B : Base) (s : ResumeState B) (r : ℕ) :
    IsProbabilityMeasure (finishUniform B s r) := by
  unfold finishUniform
  apply isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
  exact Filter.Eventually.of_forall (fun _ => inferInstance)

/-- Freezing never removes any actually occupied site. -/
theorem freezeCoupon_seed_mono (B : Base) (s : ResumeState B) (z : Site B) :
    resumeSeed B s.1 ⊆ resumeSeed B (freezeCoupon B s z).1 := by
  unfold freezeCoupon
  split_ifs
  · exact Set.Subset.rfl
  · rw [resumeSeed_insert]
    exact Set.subset_union_left

/-- Every arrival site is occupied after its freezing update. -/
theorem freezeCoupon_mem (B : Base) (s : ResumeState B) (z : Site B) :
    z ∈ resumeSeed B (freezeCoupon B s z).1 := by
  unfold freezeCoupon
  split_ifs with hz
  · exact hz
  · rw [resumeSeed_insert]
    exact Or.inr rfl

/-- Every frozen mobile copy is located at an occupied site. -/
theorem freezeCoupon_queue_occupied (B : Base) (s : ResumeState B)
    (hs : ∀ z ∈ s.2, z ∈ resumeSeed B s.1) (z : Site B) :
    ∀ w ∈ (freezeCoupon B s z).2, w ∈ resumeSeed B (freezeCoupon B s z).1 := by
  intro w hw
  by_cases hz : z ∈ resumeSeed B s.1
  · simp only [freezeCoupon, if_pos hz] at hw ⊢
    rcases List.mem_append.mp hw with hw | hw
    · exact hs w hw
    · exact (List.mem_singleton.mp hw) ▸ hz
  · simp only [freezeCoupon, if_neg hz] at hw ⊢
    rw [resumeSeed_insert]
    exact Or.inl (hs w hw)

end IdlaCyl.Reduction
