/-
The complete time-zero fresh-resumption law.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396.
-/
import IdlaCyl.Support.Outer.ResumeMeasurable

attribute [local instance] Classical.propDecidable

namespace IdlaCyl
open MeasureTheory ProbabilityTheory
noncomputable section

theorem resumedCluster_zero (B : Base) (h : ℤ) (hh : 1 ≤ h)
    (ω η : TrajSeq B) : resumedCluster B h 0 ω η = R B 0 := by
  change clusterFrom B (pausedCluster B h ω 0) η 0 = _
  exact pausedCluster_zero B h hh ω

/-- At time zero every clause of the exact task-7 target holds. -/
theorem resumedCluster_law_zero (B : Base) (h : ℤ) (hh : 1 ≤ h) :
    IsProbabilityMeasure (resumeLaw B h 0) ∧
    (resumeLaw B h 0).map Prod.fst = idlaMeasure B ∧
    Measurable (fun p : TrajSeq B × TrajSeq B =>
      clusterCode B (resumedCluster B h 0 p.1 p.2)) ∧
    Measurable (fun ω : TrajSeq B => clusterCode B (clusterTraj B ω 0)) ∧
    (resumeLaw B h 0).map
        (fun p => clusterCode B (resumedCluster B h 0 p.1 p.2)) =
      (idlaMeasure B).map (fun ω => clusterCode B (clusterTraj B ω 0)) := by
  refine ⟨inferInstance, resumeLaw_map_fst B h 0,
    measurable_clusterCode_resumedCluster B h 0, measurable_clusterCode_clusterTraj B 0, ?_⟩
  have hres : (fun p : TrajSeq B × TrajSeq B =>
      clusterCode B (resumedCluster B h 0 p.1 p.2)) = fun _ => clusterCode B (R B 0) := by
    funext p
    rw [resumedCluster_zero B h hh]
  change _ = (idlaMeasure B).map (fun _ => clusterCode B (R B 0))
  rw [hres]
  simp only [Measure.map_const, measure_univ, one_smul]

example : (resumeLaw PrInnerTail.K2 2 0).map
      (fun p => clusterCode PrInnerTail.K2 (resumedCluster PrInnerTail.K2 2 0 p.1 p.2)) =
    (idlaMeasure PrInnerTail.K2).map
      (fun ω => clusterCode PrInnerTail.K2 (clusterTraj PrInnerTail.K2 ω 0)) :=
  (resumedCluster_law_zero PrInnerTail.K2 2 (by norm_num)).2.2.2.2

end
end IdlaCyl
