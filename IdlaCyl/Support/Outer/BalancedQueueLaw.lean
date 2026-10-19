/-
The literal balanced product law realizes the prescribed queue, including translation.
Source: paper/idla-cylinder-gff.tex, tex:1331-1337,1427-1431.
-/
import IdlaCyl.Support.Outer.BalancedQueue
import IdlaCyl.Support.Outer.Translation

attribute [local instance] Classical.propDecidable
namespace IdlaCyl
open MeasureTheory ProbabilityTheory
noncomputable section

/-- Extract the finite balanced coordinates from a prescribed infinite stream. -/
def outerBalancedExtract (B : Base) (m : ℕ) (ω : TrajSeq B) : BalancedDriver B m :=
  fun i => ω ((balancedIndex B m).symm i).val

theorem measurable_outerBalancedExtract (B : Base) (m : ℕ) :
    Measurable (outerBalancedExtract B m) :=
  measurable_pi_iff.mpr (fun i => measurable_pi_apply ((balancedIndex B m).symm i).val)

/-- The extracted family has the actual independent balanced product law. -/
theorem outerPrescribed_map_balancedExtract (B : Base) (m : ℕ) :
    (prescribedMeasure B (outerQueueStart B (outerBalancedQueue B 0 m))).map
      (outerBalancedExtract B m) = balancedLaw B m := by
  have hinj : Function.Injective (fun i : B.V × Fin m => ((balancedIndex B m).symm i).val) := by
    intro i j hij
    exact (balancedIndex B m).symm.injective (Fin.ext hij)
  have hi : iIndepFun (fun i (ω : TrajSeq B) =>
      ω ((balancedIndex B m).symm i).val)
      (prescribedMeasure B (outerQueueStart B (outerBalancedQueue B 0 m))) :=
    iIndepFun.precomp hinj (iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id))
  rw [show outerBalancedExtract B m = (fun ω i => ω ((balancedIndex B m).symm i).val) from rfl,
    hi.map_fun_eq_pi_map (fun i => (measurable_pi_apply _).aemeasurable)]
  simp only [prescribedMeasure, Measure.infinitePi_map_eval]
  congr 1
  funext i
  have hj := ((balancedIndex B m).symm i).isLt
  simp only [outerQueueStart, outerBalancedQueue, List.length_ofFn, dif_pos hj,
    List.getElem_ofFn]
  change walkPathLaw B (((balancedIndex B m) ((balancedIndex B m).symm i)).1, 0) = _
  rw [Equiv.apply_symm_apply]

/-- Reconstructing the balanced stream recovers every coordinate actually released. -/
theorem outerBalancedExtract_prefix (B : Base) (m : ℕ) (ω : TrajSeq B)
    (j : ℕ) (hj : j < B.card * m) :
    balancedTrajSeq B m (outerBalancedExtract B m ω) j = ω j := by
  rw [balancedTrajSeq_apply B m _ j hj]
  simp only [outerBalancedExtract, Equiv.symm_apply_apply]

/-- The fresh product family, shifted to h, has the finite prescribed-queue law. -/
theorem outerBalancedQueue_law (B : Base) (h : ℤ) (m : ℕ) (F : ResumeFinite B) :
    (balancedLaw B m).map (fun η =>
      resumeGrow B F (outerShiftTraj B h (balancedTrajSeq B m η)) (B.card * m)) =
        resumeRun B F (outerBalancedQueue B h m) := by
  let start := outerQueueStart B (outerBalancedQueue B 0 m)
  have hm : Measurable (fun η =>
      resumeGrow B F (outerShiftTraj B h (balancedTrajSeq B m η)) (B.card * m)) :=
    (measurable_resumeGrow B F _).comp
      ((measurable_outerShiftTraj B h).comp (measurable_balancedTrajSeq B m))
  rw [← outerPrescribed_map_balancedExtract B m,
    Measure.map_map hm (measurable_outerBalancedExtract B m)]
  have heq : (fun ω => resumeGrow B F
      (outerShiftTraj B h (balancedTrajSeq B m (outerBalancedExtract B m ω))) (B.card * m)) =
      (fun ω => resumeGrow B F (outerShiftTraj B h ω) (B.card * m)) := by
    funext ω
    apply resumeGrow_congr
    intro j hj
    exact congrArg (outerShiftPath B h) (outerBalancedExtract_prefix B m ω j hj)
  change (prescribedMeasure B start).map (fun ω => resumeGrow B F
    (outerShiftTraj B h (balancedTrajSeq B m (outerBalancedExtract B m ω))) (B.card * m)) = _
  rw [heq]
  change (prescribedMeasure B start).map
    ((fun ω => resumeGrow B F ω (B.card * m)) ∘ outerShiftTraj B h) = _
  rw [← Measure.map_map (measurable_resumeGrow B F _) (measurable_outerShiftTraj B h),
    prescribedMeasure_map_outerShift, prescribedMeasure_map_resumeGrow]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp only [start, outerQueueStart, outerBalancedQueue, List.length_ofFn,
    dif_pos i.isLt, List.getElem_ofFn, outerShift, Equiv.coe_fn_mk, zero_add]

example : (balancedLaw PrInnerTail.K2 0).map (fun η =>
    resumeGrow PrInnerTail.K2 (resumeEmpty PrInnerTail.K2)
      (outerShiftTraj PrInnerTail.K2 2 (balancedTrajSeq PrInnerTail.K2 0 η)) 0) =
        resumeRun PrInnerTail.K2 (resumeEmpty PrInnerTail.K2)
          (outerBalancedQueue PrInnerTail.K2 2 0) :=
  outerBalancedQueue_law PrInnerTail.K2 2 0 _

end
end IdlaCyl
