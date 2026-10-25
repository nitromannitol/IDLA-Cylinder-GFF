module

public import IdlaCyl.Support.Obligation.ExitAeFinite

@[expose] public section

/-!
`|A_+(t)| = t` almost surely (`tex:265`, `tex:340`), where `A_+(t) = A(t) ∩ {y ≥ 1}` is the
part of the cluster strictly above level `0`.

The part above level `0` is finite for every `ω`. Off a null set, the site added at each
stage lies outside the previous cluster and strictly above level `0`, because the flat seed
`R_0` lies in every cluster. So the count rises by one at each stage.
-/

namespace IdlaCyl.Obligation.ClusterPlusCard

open MeasureTheory

variable (B : Base)

/-- The part of the cluster above level `0` lies in the finite box `V_N × [1, t]`. -/
theorem clusterPlus_finite (ω : Driver) (t : ℕ) : (clusterPlus B ω t).Finite := by
  refine (Set.finite_univ.prod (Set.finite_Icc (1 : ℤ) t)).subset ?_
  rintro ⟨x, y⟩ ⟨hc, hy⟩
  have hh : (y : ℝ) ≤ (t : ℝ) := ExitAeFinite.cluster_height B ω t hc
  have hh' : y ≤ (t : ℤ) := by exact_mod_cast hh
  exact ⟨Set.mem_univ _, hy, hh'⟩

/-- Before the first stage the part above level `0` is empty. -/
theorem clusterPlus_zero (ω : Driver) : clusterPlus B ω 0 = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  rintro ⟨x, y⟩ ⟨hc, hy⟩
  have hh : (y : ℝ) ≤ ((0 : ℕ) : ℝ) := ExitAeFinite.cluster_height B ω 0 hc
  have hh' : y ≤ 0 := by exact_mod_cast hh
  have hy' : (1 : ℤ) ≤ y := hy
  omega

/-- The flat seed `R_0` lies in every cluster. -/
theorem seed_subset (ω : Driver) (t : ℕ) : R B 0 ⊆ cluster B ω t := by
  simpa only [cluster_zero] using cluster_mono B ω (Nat.zero_le t)

/-- Off the null set, the site added at a stage is outside the cluster and strictly above
level `0`. -/
theorem newSite_level (ω : Driver) (t : ℕ)
    (hω : exitTime B (cluster B ω t) (stepWalk B (ω t)) ≠ ⊤) :
    1 ≤ (exitSite B (cluster B ω t) (ω t)).2 := by
  by_contra h
  have hp : exitSite B (cluster B ω t) (ω t) ∈ R B 0 := by
    rw [mem_R]
    have h0 : (exitSite B (cluster B ω t) (ω t)).2 ≤ 0 := by omega
    exact_mod_cast h0
  exact (ExitAeFinite.exitSite_outside B (cluster B ω t) (ω t) hω) (seed_subset B ω t hp)

/-- One stage adds exactly the new site to the part above level `0`. -/
theorem clusterPlus_succ (ω : Driver) (t : ℕ)
    (hω : exitTime B (cluster B ω t) (stepWalk B (ω t)) ≠ ⊤) :
    clusterPlus B ω (t + 1) = insert (exitSite B (cluster B ω t) (ω t)) (clusterPlus B ω t) := by
  have hnew := newSite_level B ω t hω
  ext p
  simp only [clusterPlus, cluster_succ, Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_insert_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hp | hp, hp1⟩
    · exact Or.inr ⟨hp, hp1⟩
    · exact Or.inl hp
  · rintro (rfl | ⟨hp, hp1⟩)
    · exact ⟨Or.inr rfl, hnew⟩
    · exact ⟨Or.inl hp, hp1⟩

/-- One stage raises the count above level `0` by exactly one. -/
theorem clusterPlus_ncard_succ (ω : Driver) (t : ℕ)
    (hω : exitTime B (cluster B ω t) (stepWalk B (ω t)) ≠ ⊤) :
    (clusterPlus B ω (t + 1)).ncard = (clusterPlus B ω t).ncard + 1 := by
  have hnot : exitSite B (cluster B ω t) (ω t) ∉ clusterPlus B ω t := by
    intro hm
    exact ExitAeFinite.exitSite_outside B (cluster B ω t) (ω t) hω hm.1
  rw [clusterPlus_succ B ω t hω, Set.ncard_insert_of_notMem hnot (clusterPlus_finite B ω t)]

/-- If every exit is finite, the part above level `0` has `t` sites. -/
theorem clusterPlus_ncard_of (ω : Driver) (t : ℕ)
    (h : ∀ s, exitTime B (cluster B ω s) (stepWalk B (ω s)) ≠ ⊤) :
    (clusterPlus B ω t).ncard = t := by
  induction t with
  | zero => rw [clusterPlus_zero B ω, Set.ncard_empty]
  | succ n ih => rw [clusterPlus_ncard_succ B ω n (h n), ih]

end IdlaCyl.Obligation.ClusterPlusCard

namespace IdlaCyl.Obligation

open MeasureTheory

/-- `|A_+(t)| = t` almost surely (`tex:265`, `tex:340`). The exit events for all stages
hold together off a null set, and on that set the count rises by one at each stage. -/
theorem clusterPlus_ncard_legacy (B : Base) (t : ℕ) :
    ∀ᵐ ω ∂driverLaw, (clusterPlus B ω t).ncard = t := by
  filter_upwards [ae_all_iff.mpr fun s => exit_ae_finite B s] with ω hω
  exact ClusterPlusCard.clusterPlus_ncard_of B ω t hω

/-- Nonvacuity at `t = 0`: the part above level `0` is empty for every `ω`, so the
conclusion is the genuine value `|A_+(0)| = 0`. -/
example (B : Base) : ∀ᵐ ω ∂driverLaw, (clusterPlus B ω 0).ncard = 0 :=
  Filter.Eventually.of_forall fun ω => by
    rw [ClusterPlusCard.clusterPlus_zero B ω, Set.ncard_empty]

/-- Nonvacuity at `t = 1` on any base. -/
example (B : Base) : ∀ᵐ ω ∂driverLaw, (clusterPlus B ω 1).ncard = 1 :=
  clusterPlus_ncard_legacy B 1

/-- The driver law is a probability measure, so the almost-sure statements are not
vacuous: the zero measure would satisfy every one of them. -/
example : IsProbabilityMeasure driverLaw := by
  haveI : IsProbabilityMeasure stepLaw := ⟨by norm_num [stepLaw, Measure.restrict_apply_univ]⟩
  haveI : IsProbabilityMeasure walkDriverLaw := by unfold walkDriverLaw; infer_instance
  haveI : IsProbabilityMeasure stepDriverLaw := by unfold stepDriverLaw; infer_instance
  unfold driverLaw; infer_instance

end IdlaCyl.Obligation
