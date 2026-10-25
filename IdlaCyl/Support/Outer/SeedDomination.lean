module

/-
Seed monotonicity for fresh prescribed finite queues, with recurrence discharged.
Source: paper/idla-cylinder-gff.tex, tex:1400-1427.
-/
public import IdlaCyl.Support.Outer.QueueDomination

@[expose] public section

attribute [local instance] Classical.propDecidable
namespace IdlaCyl
open MeasureTheory ProbabilityTheory
noncomputable section

/-- Extend a finite prescribed queue; the extension is ignored by finite growth. -/
def outerQueueStart (B : Base) (L : List (Site B)) (j : ℕ) : Site B :=
  if hj : j < L.length then L[j] else (B.pt, 0)

theorem outerQueueStart_ofFn (B : Base) (L : List (Site B)) :
    List.ofFn (fun i : Fin L.length => outerQueueStart B L i) = L := by
  simp only [outerQueueStart, dif_pos (Fin.isLt _)]
  exact List.ofFn_getElem

/-- Every prescribed trajectory visits every height, simultaneously over all labels. -/
theorem outerPrescribed_ae_hits (B : Base) (start : ℕ → Site B) :
    ∀ᵐ ω ∂prescribedMeasure B start, ∀ j : ℕ, ∀ a : ℤ, ∃ n, (ω j n).2 = a := by
  apply ae_all_iff.mpr
  intro j
  have hwalk : ∀ᵐ X ∂walkPathLaw B (start j), ∀ a : ℤ, ∃ n, (X n).2 = a :=
    ae_all_iff.mpr (fun a => ae_exists_ver_eq External.lazyRwRecurrent_holds B (start j) a)
  rw [← Measure.infinitePi_map_eval (fun j => walkPathLaw B (start j)) j] at hwalk
  exact ae_of_ae_map (measurable_pi_apply j).aemeasurable hwalk

/-- Finite exit from every evolving finite extension is proved from recurrence. -/
theorem outerPrescribed_ae_exit (B : Base) (F : ResumeFinite B) (start : ℕ → Site B) :
    ∀ᵐ ω ∂prescribedMeasure B start, ∀ j,
      exitTime' B (clusterFrom B (resumeSeed B F) ω j) (ω j) ≠ ⊤ := by
  filter_upwards [outerPrescribed_ae_hits B start] with ω hω
  intro j
  rw [← resumeSeed_grow]
  simpa only [resumeSeed, Int.cast_zero] using
    outer_exit_ne_top_of_hits B 0 (resumeGrow B F ω j).val (ω j) (hω j)

/-- The seed monotonicity induction uses only exits from the larger evolving seed. -/
theorem outerCluster_seed_mono (B : Base) {A C : Set (Site B)} (hAC : A ⊆ C)
    (ω : TrajSeq B) (n : ℕ)
    (hfinite : ∀ j < n, exitTime' B (clusterFrom B C ω j) (ω j) ≠ ⊤) :
    clusterFrom B A ω n ⊆ clusterFrom B C ω n := by
  induction n with
  | zero => exact hAC
  | succ n ih =>
      rw [clusterFrom_succ, clusterFrom_succ]
      have hn := ih (fun j hj => hfinite j (by omega))
      exact Set.union_subset (hn.trans Set.subset_union_left)
        (Set.singleton_subset_iff.mpr (exitSite'_mem_of_subset B hn (hfinite n (by omega))))

/-- A larger seed increases every upward-event probability for the same finite queue. -/
theorem outerRun_seed_le (B : Base) (S : Set (ResumeFinite B))
    (hup : ∀ F G, resumeSeed B F ⊆ resumeSeed B G → F ∈ S → G ∈ S)
    (F G : ResumeFinite B) (hFG : resumeSeed B F ⊆ resumeSeed B G)
    (L : List (Site B)) : resumeRun B F L S ≤ resumeRun B G L S := by
  have hF := prescribedMeasure_map_resumeGrow B F (outerQueueStart B L) L.length
  have hG := prescribedMeasure_map_resumeGrow B G (outerQueueStart B L) L.length
  rw [outerQueueStart_ofFn] at hF hG
  rw [← hF, ← hG, Measure.map_apply (measurable_resumeGrow B F L.length)
    (Set.to_countable S).measurableSet, Measure.map_apply (measurable_resumeGrow B G L.length)
      (Set.to_countable S).measurableSet]
  apply measure_mono_ae
  filter_upwards [outerPrescribed_ae_exit B G (outerQueueStart B L)] with ω hω
  intro hmem
  apply hup _ _ _ hmem
  rw [resumeSeed_grow, resumeSeed_grow]
  exact outerCluster_seed_mono B hFG ω L.length (fun j _ => hω j)

/-- Height failure is an upward measurable event on the actual finite state space. -/
def outerHeightEvent (B : Base) (r : ℝ) : Set (ResumeFinite B) :=
  {F | ¬ resumeSeed B F ⊆ R B r}

theorem outerHeightEvent_upward (B : Base) (r : ℝ) (F G : ResumeFinite B)
    (hFG : resumeSeed B F ⊆ resumeSeed B G) (hF : F ∈ outerHeightEvent B r) :
    G ∈ outerHeightEvent B r := fun hG => hF (hFG.trans hG)

example : resumeRun PrInnerTail.K2 (resumeEmpty PrInnerTail.K2) []
    (outerHeightEvent PrInnerTail.K2 0) = 0 := by
  change (Measure.dirac _) _ = 0
  rw [Measure.dirac_apply' _ (Set.to_countable _).measurableSet]
  simp only [outerHeightEvent, Set.mem_setOf_eq, resumeSeed_empty, Set.Subset.refl,
    not_true_eq_false, Set.indicator_of_notMem, not_false_eq_true]

end
end IdlaCyl
