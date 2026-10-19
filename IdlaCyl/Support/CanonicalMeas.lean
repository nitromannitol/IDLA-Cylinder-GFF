/-
Measurability facts of the canonical IDLA cluster.

The recursion `A(t) = A(t-1) ∪ {(X_t, Y_t)}` of `tex:263-265` is taken for granted to be
measurable in the driving trajectories; here it is proved: the
cluster `clusterTraj B ω t` depends only on `ω 0, …, ω (t-1)`, the settling site
`settleSite B ω t` is a measurable function of `ω`, and membership of a fixed site in the
cluster is a measurable event.
-/
import IdlaCyl.Support.CanonicalIdla
import IdlaCyl.Support.Exit

namespace IdlaCyl

open MeasureTheory

/-- The cluster `A(t)` depends only on the first `t` trajectories (`tex:263-265`). -/
theorem clusterTraj_congr (B : Base) {ω ω' : TrajSeq B} {t : ℕ}
    (h : ∀ j < t, ω j = ω' j) : clusterTraj B ω t = clusterTraj B ω' t :=
  clusterFrom_congr B (R B 0) ω ω' h

/-- If the first `t` settling sites of `ω` are `s`, then the cluster is `R_0 ∪ range s`. -/
theorem measurable_settleSite_cluster_eq (B : Base) {t : ℕ} {ω : TrajSeq B}
    {s : Fin t → Site B} (h : ∀ j : Fin t, settleSite B ω j = s j) :
    clusterTraj B ω t = R B 0 ∪ Set.range s := by
  rw [clusterTraj_eq_union]
  congr 1
  ext p
  simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio, Set.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, (h ⟨j, hj⟩).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, j.2, h j⟩

/-- The settling site `(X_t, Y_t)` of `tex:263-265` is a measurable function of the driving
trajectories. -/
theorem measurable_settleSite (B : Base) (t : ℕ) :
    Measurable fun ω : TrajSeq B => settleSite B ω t := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    refine measurable_to_countable' fun q => ?_
    have hset : (fun ω : TrajSeq B => settleSite B ω t) ⁻¹' {q}
        = ⋃ s : Fin t → Site B,
            ({ω : TrajSeq B | ∀ j : Fin t, settleSite B ω j = s j} ∩
              {ω : TrajSeq B | exitSite' B (R B 0 ∪ Set.range s) (ω t) = q}) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_setOf_eq]
      constructor
      · intro hq
        refine ⟨fun j => settleSite B ω j, fun j => rfl, ?_⟩
        rw [← measurable_settleSite_cluster_eq B (s := fun j : Fin t => settleSite B ω j)
          (fun j => rfl)]
        exact hq
      · rintro ⟨s, hs, hq⟩
        have hc := measurable_settleSite_cluster_eq B hs
        show exitSite' B (clusterTraj B ω t) (ω t) = q
        rw [hc]
        exact hq
    rw [hset]
    refine MeasurableSet.iUnion fun s => MeasurableSet.inter ?_ ?_
    · have h1 : {ω : TrajSeq B | ∀ j : Fin t, settleSite B ω j = s j}
          = ⋂ j : Fin t, (fun ω : TrajSeq B => settleSite B ω j) ⁻¹' {s j} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      rw [h1]
      exact MeasurableSet.iInter fun j => ih j j.2 (measurableSet_singleton (s j))
    · exact ((measurable_exitSite' B (R B 0 ∪ Set.range s)).comp (measurable_pi_apply t))
        (measurableSet_singleton q)

/-- Membership of a fixed site in the cluster `A(t)` is a measurable event. -/
theorem measurableSet_mem_clusterTraj (B : Base) (t : ℕ) (p : Site B) :
    MeasurableSet {ω : TrajSeq B | p ∈ clusterTraj B ω t} := by
  have hset : {ω : TrajSeq B | p ∈ clusterTraj B ω t}
      = {ω : TrajSeq B | p ∈ R B 0} ∪
        ⋃ j ∈ Finset.range t, (fun ω : TrajSeq B => settleSite B ω j) ⁻¹' {p} := by
    ext ω
    simp only [clusterTraj_eq_union, Set.mem_setOf_eq, Set.mem_union, Finset.coe_image,
      Finset.coe_range, Set.mem_image, Set.mem_Iio, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_singleton_iff, Finset.mem_range, exists_prop]
  rw [hset]
  refine MeasurableSet.union (MeasurableSet.const _) ?_
  exact MeasurableSet.biUnion (Finset.range t).countable_toSet fun j _ =>
    measurable_settleSite B j (measurableSet_singleton p)

end IdlaCyl
