module

/-
Stopped continuation at the actual adaptive first-stage pause times.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396.
Both the chronological paused state and the whole current stopped record are
retained. The fresh continuation is sampled at that record's actual exit.
-/
public import IdlaCyl.Support.Outer.ResumePaused
public import IdlaCyl.Support.Outer.ResumeStopped

@[expose] public section

attribute [local instance] Classical.propDecidable

namespace IdlaCyl
open MeasureTheory ProbabilityTheory
noncomputable section

/-- Uniform starts preserve the complete stopped-record continuation factorization. -/
theorem walkLawUniform_map_resumeRecord_tail (B : Base) (S : Set (Site B))
    (h : ℤ) (hS : S ⊆ R B ((h : ℝ) - 1)) :
    (walkLawUniform B).map (fun X => (resumeRecord B S X, resumeTail B S X)) =
      (walkLawUniform B).bind (resumeRecordKernel B S) := by
  have hj := (measurable_resumeRecord B S).prodMk (measurable_resumeTail B S)
  unfold walkLawUniform
  rw [walkLawUniformAt_eq_bind,
    resume_map_bind _ _ _ (measurable_of_countable _) hj,
    Measure.bind_bind (measurable_of_countable _).aemeasurable
      (resumeRecordKernel B S).measurable.aemeasurable]
  exact Measure.bind_congr_right (Filter.Eventually.of_forall
    (fun p => walkPathLaw_map_resumeRecord_tail B p S h hS))

/-- The actual next stopped record and tail, jointly with the current paused state. -/
theorem idlaMeasure_map_adaptive_resumeRecord_tail (B : Base) (h : ℤ)
    (hh : 1 ≤ h) (T : ℕ) :
    (idlaMeasure B).map (fun ω =>
      (resumePauseGrow B h ω T,
        (resumeRecord B (resumeSeed B (resumePauseGrow B h ω T).1) (ω T),
          resumeTail B (resumeSeed B (resumePauseGrow B h ω T).1) (ω T)))) =
      ((idlaMeasure B).map (fun ω => resumePauseGrow B h ω T)).bind
        (fun s => ((walkLawUniform B).bind (resumeRecordKernel B (resumeSeed B s.1))).map
          (fun r => (s, r))) := by
  let π := (idlaMeasure B).map (fun ω => resumePauseGrow B h ω T)
  let f := fun sX : ResumeState B × (ℕ → Site B) =>
    (sX.1, (resumeRecord B (resumeSeed B sX.1.1) sX.2,
      resumeTail B (resumeSeed B sX.1.1) sX.2))
  have hf : Measurable f := by
    apply measurable_from_prod_countable_right
    intro s
    exact measurable_const.prodMk
      ((measurable_resumeRecord B (resumeSeed B s.1)).prodMk
        (measurable_resumeTail B (resumeSeed B s.1)))
  have hj := IndepFun.map_prod_eq_prod_map_map
    (measurable_resumePauseGrow B h T).aemeasurable (measurable_pi_apply T).aemeasurable
    (resume_indep_past B (fun _ => walkLawUniform B) T _ (measurable_resumePauseGrow B h T)
      (fun ω η hω => resumePauseGrow_congr B h ω η T hω))
  rw [Measure.infinitePi_map_eval] at hj
  change (idlaMeasure B).map (fun ω => (resumePauseGrow B h ω T, ω T)) =
    ((idlaMeasure B).map (fun ω => resumePauseGrow B h ω T)).prod (walkLawUniform B) at hj
  have hcap : ∀ᵐ s ∂π, resumeSeed B s.1 ⊆ R B ((h : ℝ) - 1) := by
    exact (ae_map_iff (measurable_resumePauseGrow B h T).aemeasurable
      ((Set.to_countable _).measurableSet)).mpr
        (Filter.Eventually.of_forall (fun ω => resumePauseGrow_below B h hh ω T))
  calc
    _ = ((idlaMeasure B).map (fun ω => (resumePauseGrow B h ω T, ω T))).map f :=
      (Measure.map_map hf ((measurable_resumePauseGrow B h T).prodMk
        (measurable_pi_apply T))).symm
    _ = (π.prod (walkLawUniform B)).map f := by rw [hj]
    _ = π.bind (fun s => (walkLawUniform B).map (fun X => f (s, X))) :=
      resume_prod_map _ _ _ hf
    _ = _ := by
      apply Measure.bind_congr_right
      filter_upwards [hcap] with s hs
      have hm := (measurable_resumeRecord B (resumeSeed B s.1)).prodMk
        (measurable_resumeTail B (resumeSeed B s.1))
      calc
        _ = ((walkLawUniform B).map (fun X =>
            (resumeRecord B (resumeSeed B s.1) X, resumeTail B (resumeSeed B s.1) X))).map
              (fun r => (s, r)) :=
          (Measure.map_map (measurable_prodMk_left (x := s)) hm).symm
        _ = _ := by rw [walkLawUniform_map_resumeRecord_tail B _ h hs]


example : (walkLawUniform PrInnerTail.K2).map
      (fun X => (resumeRecord PrInnerTail.K2 (R PrInnerTail.K2 0) X,
        resumeTail PrInnerTail.K2 (R PrInnerTail.K2 0) X)) =
    (walkLawUniform PrInnerTail.K2).bind
      (resumeRecordKernel PrInnerTail.K2 (R PrInnerTail.K2 0)) :=
  walkLawUniform_map_resumeRecord_tail PrInnerTail.K2 _ 1 (by
    intro z hz
    simpa only [Int.cast_one, sub_self] using hz)

end
end IdlaCyl
