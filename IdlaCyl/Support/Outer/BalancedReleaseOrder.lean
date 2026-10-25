module

/-
Order invariance in law of the balanced release (`le:released`, "in any order").
Source: paper/idla-cylinder-gff.tex, tex:1331-1337 (the cluster Ã^{(m)} releases exactly m
particles from each site of V_N × {0}, in any order) and tex:1346.

For an enumeration `σ` of the N*m labelled releases, `balancedClusterOf B m σ` reads the
trajectories in the order `σ`. Its law is the law of `balancedCluster` (the enumeration
`balancedIndex`): the finite product law sends the order-`σ` release to the same
prescribed-start resume run, and `resumeRun_perm` makes that run depend only on the multiset of
starts, which is the same for every enumeration (`balanced_start_count`).

Proof route: the copy of `outerPrescribed_map_balancedExtract` and `outerBalancedQueue_law`
with `balancedIndex` replaced by `σ` (the existing lemmas are the case `σ = balancedIndex`), the
copy of `outerFlatBalanced_grow` and `outerFlatBalanced_height_law`, then `Equiv.Perm.ofFn_comp_perm`
and `resumeRun_perm`.
-/
public import IdlaCyl.Support.Outer.BalancedRelease
public import IdlaCyl.Support.Outer.LeReleasedV2Assembly
public import IdlaCyl.Support.Outer.FlatBalanced

@[expose] public section

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- The balanced stream read along an arbitrary enumeration `σ`; the extension after N*m is
ignored, as in `balancedTrajSeq`. -/
def balancedTrajSeqOf (B : Base) (m : ℕ) (σ : Fin (B.card * m) ≃ B.V × Fin m)
    (ω : BalancedDriver B m) : TrajSeq B :=
  fun j => if hj : j < B.card * m then
    ω (σ ⟨j, hj⟩) else fun _ => (B.pt, 0)

/-- The balanced cluster with the releases taken in the order `σ`. -/
def balancedClusterOf (B : Base) (m : ℕ) (σ : Fin (B.card * m) ≃ B.V × Fin m)
    (ω : BalancedDriver B m) : Set (Site B) :=
  clusterTraj B (balancedTrajSeqOf B m σ ω) (B.card * m)

/-- The enumeration `balancedIndex` recovers the balanced cluster. -/
theorem balancedClusterOf_balancedIndex (B : Base) (m : ℕ) :
    balancedClusterOf B m (balancedIndex B m) = balancedCluster B m := rfl

/-- Measurability of the order-`σ` stream into the canonical trajectory space. -/
theorem measurable_balancedTrajSeqOf (B : Base) (m : ℕ) (σ : Fin (B.card * m) ≃ B.V × Fin m) :
    Measurable (balancedTrajSeqOf B m σ) := by
  apply measurable_pi_iff.mpr
  intro j
  unfold balancedTrajSeqOf
  split_ifs with hj
  · exact measurable_pi_apply (σ ⟨j, hj⟩)
  · exact measurable_const

/-- Extract the finite coordinates of an infinite stream, indexed by labels, along `σ`. -/
def balancedExtractOf (B : Base) (m : ℕ) (σ : Fin (B.card * m) ≃ B.V × Fin m)
    (ω : TrajSeq B) : BalancedDriver B m :=
  fun i => ω ((σ.symm i).val)

theorem measurable_balancedExtractOf (B : Base) (m : ℕ) (σ : Fin (B.card * m) ≃ B.V × Fin m) :
    Measurable (balancedExtractOf B m σ) :=
  measurable_pi_iff.mpr (fun i => measurable_pi_apply ((σ.symm i).val))

/-- The prescribed release queue read along `σ`, released at height `h`. -/
def balancedQueueOf (B : Base) (h : ℤ) (m : ℕ) (σ : Fin (B.card * m) ≃ B.V × Fin m) :
    List (Site B) :=
  List.ofFn (fun i : Fin (B.card * m) => ((σ i).1, h))

/-- The extracted family along `σ` has the actual independent balanced product law. -/
theorem balancedExtractOf_map (B : Base) (m : ℕ) (σ : Fin (B.card * m) ≃ B.V × Fin m) :
    (prescribedMeasure B (outerQueueStart B (balancedQueueOf B 0 m σ))).map
      (balancedExtractOf B m σ) = balancedLaw B m := by
  have hinj : Function.Injective (fun i : B.V × Fin m => (σ.symm i).val) := by
    intro i j hij
    exact σ.symm.injective (Fin.ext hij)
  have hi : iIndepFun (fun i (ω : TrajSeq B) => ω (σ.symm i).val)
      (prescribedMeasure B (outerQueueStart B (balancedQueueOf B 0 m σ))) :=
    iIndepFun.precomp hinj (iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id))
  rw [show balancedExtractOf B m σ = (fun ω i => ω (σ.symm i).val) from rfl,
    hi.map_fun_eq_pi_map (fun i => (measurable_pi_apply _).aemeasurable)]
  simp only [prescribedMeasure, Measure.infinitePi_map_eval]
  congr 1
  funext i
  have hj := (σ.symm i).isLt
  simp only [outerQueueStart, balancedQueueOf, List.length_ofFn, dif_pos hj,
    List.getElem_ofFn]
  change walkPathLaw B ((σ (σ.symm i)).1, 0) = _
  rw [Equiv.apply_symm_apply]

/-- Reading the order-`σ` stream of the extracted family recovers every coordinate released. -/
theorem balancedExtractOf_prefix (B : Base) (m : ℕ) (σ : Fin (B.card * m) ≃ B.V × Fin m)
    (ω : TrajSeq B) (j : ℕ) (hj : j < B.card * m) :
    balancedTrajSeqOf B m σ (balancedExtractOf B m σ ω) j = ω j := by
  simp only [balancedTrajSeqOf, dif_pos hj, balancedExtractOf, Equiv.symm_apply_apply]

/-- The fresh product family read along `σ`, shifted to `h`, has the prescribed-queue law. -/
theorem balancedLaw_map_resumeGrow_of (B : Base) (h : ℤ) (m : ℕ)
    (σ : Fin (B.card * m) ≃ B.V × Fin m) (F : ResumeFinite B) :
    (balancedLaw B m).map (fun η =>
      resumeGrow B F (outerShiftTraj B h (balancedTrajSeqOf B m σ η)) (B.card * m)) =
        resumeRun B F (balancedQueueOf B h m σ) := by
  let start := outerQueueStart B (balancedQueueOf B 0 m σ)
  have hm : Measurable (fun η =>
      resumeGrow B F (outerShiftTraj B h (balancedTrajSeqOf B m σ η)) (B.card * m)) :=
    (measurable_resumeGrow B F _).comp
      ((measurable_outerShiftTraj B h).comp (measurable_balancedTrajSeqOf B m σ))
  rw [← balancedExtractOf_map B m σ,
    Measure.map_map hm (measurable_balancedExtractOf B m σ)]
  have heq : (fun ω => resumeGrow B F
      (outerShiftTraj B h (balancedTrajSeqOf B m σ (balancedExtractOf B m σ ω))) (B.card * m)) =
      (fun ω => resumeGrow B F (outerShiftTraj B h ω) (B.card * m)) := by
    funext ω
    apply resumeGrow_congr
    intro j hj
    exact congrArg (outerShiftPath B h) (balancedExtractOf_prefix B m σ ω j hj)
  change (prescribedMeasure B start).map (fun ω => resumeGrow B F
    (outerShiftTraj B h (balancedTrajSeqOf B m σ (balancedExtractOf B m σ ω))) (B.card * m)) = _
  rw [heq]
  change (prescribedMeasure B start).map
    ((fun ω => resumeGrow B F ω (B.card * m)) ∘ outerShiftTraj B h) = _
  rw [← Measure.map_map (measurable_resumeGrow B F _) (measurable_outerShiftTraj B h),
    prescribedMeasure_map_outerShift, prescribedMeasure_map_resumeGrow]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp only [start, outerQueueStart, balancedQueueOf, List.length_ofFn,
    dif_pos i.isLt, List.getElem_ofFn, outerShift, Equiv.coe_fn_mk, zero_add]

/-- Under the order-`σ` product law, the enlarged output is the translated order-`σ` cluster. -/
theorem balancedFlatGrow_of (B : Base) (h : ℤ) (hh : 0 ≤ h) (m : ℕ)
    (σ : Fin (B.card * m) ≃ B.V × Fin m) (η : BalancedDriver B m) :
    resumeSeed B (resumeGrow B (outerFlatSeed B h)
      (outerShiftTraj B h (balancedTrajSeqOf B m σ η)) (B.card * m)) =
        outerShift B h '' balancedClusterOf B m σ η := by
  rw [resumeSeed_grow, outerFlatSeed_eq B h hh]
  have hR : R B (h : ℝ) = outerShift B h '' R B 0 := by
    rw [outerShift_image_R, zero_add]
  rw [hR, clusterFrom_outerShift]
  rfl

/-- The height law of the order-`σ` balanced release, at the flat seed of height `h`. -/
theorem balancedFlatHeight_of (B : Base) (h : ℤ) (hh : 0 ≤ h) (m : ℕ)
    (σ : Fin (B.card * m) ≃ B.V × Fin m) (r : ℝ) :
    resumeRun B (outerFlatSeed B h) (balancedQueueOf B h m σ)
      (outerHeightEvent B ((h : ℝ) + r)) =
        balancedLaw B m {η : BalancedDriver B m | ¬ balancedClusterOf B m σ η ⊆ R B r} := by
  have hm : Measurable (fun η : BalancedDriver B m =>
      resumeGrow B (outerFlatSeed B h)
        (outerShiftTraj B h (balancedTrajSeqOf B m σ η)) (B.card * m)) :=
    (measurable_resumeGrow B _ _).comp
      ((measurable_outerShiftTraj B h).comp (measurable_balancedTrajSeqOf B m σ))
  rw [← balancedLaw_map_resumeGrow_of B h m σ (outerFlatSeed B h),
    Measure.map_apply hm (Set.to_countable _).measurableSet]
  congr 1
  ext η
  change (¬ resumeSeed B (resumeGrow B (outerFlatSeed B h)
    (outerShiftTraj B h (balancedTrajSeqOf B m σ η)) (B.card * m)) ⊆ R B ((h : ℝ) + r)) ↔ _
  rw [balancedFlatGrow_of B h hh m σ η, add_comm (h : ℝ) r, outerShift_subset_R_iff]
  rfl

/-- Every enumeration gives the same prescribed-start queue up to a permutation of its entries:
both are the labels `(x, h)` with `x` ranging over `B.V` exactly `m` times. -/
theorem balancedQueueOf_perm (B : Base) (h : ℤ) (m : ℕ)
    (σ : Fin (B.card * m) ≃ B.V × Fin m) :
    (balancedQueueOf B h m σ).Perm (balancedQueueOf B h m (balancedIndex B m)) := by
  have hfun : balancedQueueOf B h m σ = List.ofFn
      ((fun i : Fin (B.card * m) => ((balancedIndex B m i).1, h)) ∘
        (σ.trans (balancedIndex B m).symm)) := by
    unfold balancedQueueOf
    congr 1
    funext i
    simp only [Function.comp_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [hfun]
  exact Equiv.Perm.ofFn_comp_perm _ _

/-- **Order invariance in law (`le:released`, "in any order").** For every enumeration `σ` of
the N*m releases, the balanced cluster read along `σ` has the same law as the balanced cluster
read along `balancedIndex`, for every target set of the form `R B r`. -/
theorem balancedLaw_cluster_order_invariant (B : Base) (m : ℕ)
    (σ : Fin (B.card * m) ≃ B.V × Fin m) (r : ℝ) :
    balancedLaw B m {ω : BalancedDriver B m | ¬ balancedClusterOf B m σ ω ⊆ R B r} =
      balancedLaw B m {ω : BalancedDriver B m | ¬ balancedCluster B m ω ⊆ R B r} := by
  calc balancedLaw B m {ω : BalancedDriver B m | ¬ balancedClusterOf B m σ ω ⊆ R B r}
      = resumeRun B (outerFlatSeed B 0) (balancedQueueOf B 0 m σ)
          (outerHeightEvent B (((0 : ℤ) : ℝ) + r)) :=
        (balancedFlatHeight_of B 0 le_rfl m σ r).symm
    _ = resumeRun B (outerFlatSeed B 0) (balancedQueueOf B 0 m (balancedIndex B m))
          (outerHeightEvent B (((0 : ℤ) : ℝ) + r)) := by
        rw [resumeRun_perm B (outerFlatSeed B 0) (balancedQueueOf_perm B 0 m σ)]
    _ = balancedLaw B m {ω : BalancedDriver B m | ¬ balancedCluster B m ω ⊆ R B r} :=
        balancedFlatHeight_of B 0 le_rfl m (balancedIndex B m) r

end
end IdlaCyl
