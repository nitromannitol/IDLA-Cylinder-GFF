module

/-
Measurability of the shape event of the canonical IDLA process.

The event of Theorem 1.1 (`tex:271-280`, the frozen `max_fluct`) is `R_j ⊆ A(t) ⊆ R_k`.
It is a countable intersection of the events `p ∈ A(t)` (for `p ∈ R_j`) and `p ∉ A(t)`
(for `p ∉ R_k`), each measurable by `measurableSet_mem_clusterTraj`; hence it is measurable and
its probability under the canonical law is a genuine probability.
-/
public import IdlaCyl.Support.CanonicalMeas

@[expose] public section

namespace IdlaCyl

/-- The event `R_j ⊆ A(t) ⊆ R_k` of `tex:271-280` is measurable for the canonical process. -/
theorem measurableSet_shapeTraj (B : Base) (t : ℕ) (j k : ℝ) :
    MeasurableSet {ω : TrajSeq B | R B j ⊆ clusterTraj B ω t ∧ clusterTraj B ω t ⊆ R B k} := by
  have hset : {ω : TrajSeq B | R B j ⊆ clusterTraj B ω t ∧ clusterTraj B ω t ⊆ R B k}
      = (⋂ p ∈ R B j, {ω : TrajSeq B | p ∈ clusterTraj B ω t}) ∩
        (⋂ p ∈ (R B k)ᶜ, {ω : TrajSeq B | p ∈ clusterTraj B ω t}ᶜ) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter₂, Set.mem_compl_iff,
      Set.subset_def]
    refine and_congr Iff.rfl ⟨fun h p hp hpc => hp (h p hpc), fun h p hpc => ?_⟩
    by_contra hp
    exact h p hp hpc
  rw [hset]
  exact (MeasurableSet.biInter (Set.to_countable _) fun p _ =>
      measurableSet_mem_clusterTraj B t p).inter
    (MeasurableSet.biInter (Set.to_countable _) fun p _ =>
      (measurableSet_mem_clusterTraj B t p).compl)

end IdlaCyl
