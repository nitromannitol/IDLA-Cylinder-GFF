module

/-
Finite prescribed-release queues: order invariance and adding missing particles.
Source: paper/idla-cylinder-gff.tex, tex:1391-1396.
All order comparisons are equalities of the constructed fresh-walk laws.
-/
public import IdlaCyl.Support.Outer.ResumeGrowth
public import Mathlib.Data.List.Perm.Subperm

@[expose] public section

attribute [local instance] Classical.propDecidable
namespace IdlaCyl
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

/-- Every permutation of a finite prescribed queue has the same completion law. -/
theorem outerRun_perm (B : Base) {L M : List (Site B)} (hLM : L.Perm M)
    (F : ResumeFinite B) : resumeRun B F L = resumeRun B F M := by
  induction hLM generalizing F with
  | nil => rfl
  | cons p h ih =>
      change (resumeStep B p F).bind _ = (resumeStep B p F).bind _
      congr 1
      funext G
      exact ih G
  | swap p q L =>
      change (resumeStep B q F).bind (fun G =>
        (resumeStep B p G).bind (fun H => resumeRun B H L)) = _
      rw [← Measure.bind_bind (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable, resumeStep_commute,
        Measure.bind_bind (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable]
      rfl
  | trans _ _ ih₁ ih₂ => exact (ih₁ F).trans (ih₂ F)

/-- An upward event already true of the seed remains true after any fresh queue. -/
theorem outerRun_upward_one (B : Base) (S : Set (ResumeFinite B))
    (hup : ∀ F G, resumeSeed B F ⊆ resumeSeed B G → F ∈ S → G ∈ S)
    (F : ResumeFinite B) (hF : F ∈ S) (L : List (Site B)) :
    resumeRun B F L S = 1 := by
  induction L generalizing F with
  | nil => exact Measure.dirac_apply_of_mem hF
  | cons p L ih =>
      change ((resumeStep B p F).bind (fun G => resumeRun B G L)) S = 1
      rw [Measure.bind_apply (Set.to_countable S).measurableSet
        (measurable_of_countable _).aemeasurable]
      have hpoint (X : ℕ → Site B) :
          resumeRun B (resumeInsert B F (exitSite' B (resumeSeed B F) X)) L S = 1 := by
        apply ih
        apply hup F _ _ hF
        rw [resumeSeed_insert]
        exact Set.subset_union_left
      change (∫⁻ G, resumeRun B G L S ∂(walkPathLaw B p).map
        (fun X => resumeInsert B F (exitSite' B (resumeSeed B F) X))) = 1
      rw [lintegral_map (measurable_of_countable _)
        (measurable_resumeStep_output B F)]
      simp only [hpoint, lintegral_const, measure_univ, mul_one]

/-- Appending fresh releases can only increase the probability of an upward event. -/
theorem outerRun_append_le (B : Base) (S : Set (ResumeFinite B))
    (hup : ∀ F G, resumeSeed B F ⊆ resumeSeed B G → F ∈ S → G ∈ S)
    (F : ResumeFinite B) (L M : List (Site B)) :
    resumeRun B F L S ≤ resumeRun B F (L ++ M) S := by
  rw [resumeRun_append, Measure.bind_apply (Set.to_countable S).measurableSet
    (measurable_of_countable _).aemeasurable]
  calc
    _ = ∫⁻ G, S.indicator (fun _ => (1 : ℝ≥0∞)) G ∂resumeRun B F L := by
      exact (lintegral_indicator_one (Set.to_countable S).measurableSet).symm
    _ ≤ _ := lintegral_mono (fun G => by
      by_cases hG : G ∈ S
      · rw [Set.indicator_of_mem hG, outerRun_upward_one B S hup G hG M]
      · rw [Set.indicator_of_notMem hG]
        exact bot_le)

/-- Multiset domination is derived from finite order invariance and extra releases. -/
theorem outerRun_subperm_le (B : Base) (S : Set (ResumeFinite B))
    (hup : ∀ F G, resumeSeed B F ⊆ resumeSeed B G → F ∈ S → G ∈ S)
    (F : ResumeFinite B) {L M : List (Site B)} (hLM : L.Subperm M) :
    resumeRun B F L S ≤ resumeRun B F M S := by
  obtain ⟨K, hK, hL⟩ := List.subperm_iff.mp hLM
  obtain ⟨D, hD⟩ := List.Sublist.exists_perm_append hL
  have heq : resumeRun B F M = resumeRun B F (L ++ D) :=
    outerRun_perm B (hK.symm.trans hD) F
  rw [heq]
  exact outerRun_append_le B S hup F L D

example (p q : Site PrInnerTail.K2) :
    resumeRun PrInnerTail.K2 (resumeEmpty PrInnerTail.K2) [p, q] =
      resumeRun PrInnerTail.K2 (resumeEmpty PrInnerTail.K2) [q, p] :=
  outerRun_perm PrInnerTail.K2 (List.Perm.swap q p []) _

example : resumeRun PrInnerTail.K2 (resumeEmpty PrInnerTail.K2) [] Set.univ = 1 :=
  measure_univ

end
end IdlaCyl
