module

/-
Fresh resumption has the ordinary IDLA cluster law.
Source: paper/idla-cylinder-gff.tex, tex:1385-1400.
The chronological queue is completed with the literal conditional fresh law.
The comparison is an induction of commuting release kernels, with the actual
paused state and all output maps explicitly identified.
-/
public import IdlaCyl.Support.Outer.ResumeFinish
public import IdlaCyl.Support.Outer.ResumeAdaptive
public import IdlaCyl.Support.Outer.ResumeZero

@[expose] public section

attribute [local instance] Classical.propDecidable

namespace IdlaCyl
open MeasureTheory ProbabilityTheory
noncomputable section

/-- The literal fresh experiment is the measurable completion kernel of the actual paused state. -/
theorem resumeLaw_map_clusterCode (B : Base) (h : ℤ) (hh : 1 ≤ h) (T : ℕ) :
    (resumeLaw B h T).map
        (fun p => clusterCode B (resumedCluster B h T p.1 p.2)) =
      (((idlaMeasure B).map (fun ω => resumePauseGrow B h ω T)).bind
        (fun s => resumeRun B s.1 s.2)).map
          (fun G => clusterCode B (resumeSeed B G)) := by
  let out := fun p : TrajSeq B × TrajSeq B =>
    clusterCode B (resumedCluster B h T p.1 p.2)
  let code := fun G : ResumeFinite B => clusterCode B (resumeSeed B G)
  have hout : Measurable out := measurable_clusterCode_resumedCluster B h T
  have hcode : Measurable code := (resumeCode_measurableEmbedding B).measurable
  have hpoint (ω : TrajSeq B) :
      ((prescribedMeasure B (pausedStart B h T ω)).map (fun η => (ω, η))).map out =
        (resumeRun B (resumePauseGrow B h ω T).1 (resumePauseGrow B h ω T).2).map code := by
    rw [Measure.map_map hout measurable_prodMk_left]
    have hrun := resumeRun_clusterFrom_law B (resumePauseGrow B h ω T).1
      (pausedStart B h T ω) (pauseList B h T ω).length
    rw [← resumeQueue_eq_ofFn_pausedStart,
      ← (resumePauseGrow_seed_queue B h hh ω T).2,
      (resumePauseGrow_seed_queue B h hh ω T).1] at hrun
    exact hrun.symm
  calc
    _ = (idlaMeasure B).bind (fun ω =>
        ((prescribedMeasure B (pausedStart B h T ω)).map (fun η => (ω, η))).map out) :=
      resume_map_bind _ _ out (measurable_resume_kernel B h T) hout
    _ = (idlaMeasure B).bind (fun ω =>
        (resumeRun B (resumePauseGrow B h ω T).1 (resumePauseGrow B h ω T).2).map code) :=
      Measure.bind_congr_right (Filter.Eventually.of_forall hpoint)
    _ = _ := by
      rw [resume_map_bind _ _ code (measurable_of_countable _) hcode,
        resume_bind_map _ _ _ (measurable_resumePauseGrow B h T) (measurable_of_countable _)]

/-- The exact task-7 contract, with no supplied law, coupling, stabilization, or Markov property. -/
theorem resumedCluster_law (B : Base) (h : ℤ) (hh : 1 ≤ h) (T : ℕ) :
  IsProbabilityMeasure (resumeLaw B h T) ∧
  (resumeLaw B h T).map Prod.fst = idlaMeasure B ∧
  Measurable (fun p : TrajSeq B × TrajSeq B =>
    clusterCode B (resumedCluster B h T p.1 p.2)) ∧
  Measurable (fun ω : TrajSeq B => clusterCode B (clusterTraj B ω T)) ∧
  (resumeLaw B h T).map
      (fun p => clusterCode B (resumedCluster B h T p.1 p.2)) =
    (idlaMeasure B).map (fun ω => clusterCode B (clusterTraj B ω T)) := by
  refine ⟨inferInstance, resumeLaw_map_fst B h T,
    measurable_clusterCode_resumedCluster B h T, measurable_clusterCode_clusterTraj B T, ?_⟩
  rw [resumeLaw_map_clusterCode B h hh T, resumePauseGrow_finish_law B h hh T,
    Measure.map_map (resumeCode_measurableEmbedding B).measurable
      (measurable_resumeGrow B (resumeEmpty B) T)]
  congr 1
  funext ω
  change clusterCode B (resumeSeed B (resumeGrow B (resumeEmpty B) ω T)) =
    clusterCode B (clusterTraj B ω T)
  rw [resumeSeed_grow, resumeSeed_empty]
  rfl

example : (resumeLaw PrInnerTail.K2 2 0).map
      (fun p => clusterCode PrInnerTail.K2 (resumedCluster PrInnerTail.K2 2 0 p.1 p.2)) =
    (idlaMeasure PrInnerTail.K2).map
      (fun ω => clusterCode PrInnerTail.K2 (clusterTraj PrInnerTail.K2 ω 0)) :=
  (resumedCluster_law PrInnerTail.K2 2 (by norm_num) 0).2.2.2.2

example : (resumeLaw PrInnerTail.K2 2 4).map
      (fun p => clusterCode PrInnerTail.K2 (resumedCluster PrInnerTail.K2 2 4 p.1 p.2)) =
    (idlaMeasure PrInnerTail.K2).map
      (fun ω => clusterCode PrInnerTail.K2 (clusterTraj PrInnerTail.K2 ω 4)) :=
  (resumedCluster_law PrInnerTail.K2 2 (by norm_num) 4).2.2.2.2

end
end IdlaCyl
