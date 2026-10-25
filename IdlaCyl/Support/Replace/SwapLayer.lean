module

public import IdlaCyl.Support.Replace.SwapBound
public import IdlaCyl.Support.LeReplaceLayerAvg

@[expose] public section

/-!
The resampling pair and its horizontal invariance in the replacement lemma
(`tex:828-841`). Both trajectories and their independent replacement are
transported by the same base automorphism.
-/

namespace IdlaCyl.Replace

open MeasureTheory
open scoped BigOperators

variable (B : Base)

/-- The joint law of the original trajectory family and one fresh trajectory. -/
noncomputable def swapLaw : Measure (TrajSeq B × (ℕ → Site B)) :=
  (idlaMeasure B).prod (walkLawUniform B)

instance swapLaw_isProbability : IsProbabilityMeasure (swapLaw B) :=
  inferInstanceAs (IsProbabilityMeasure ((idlaMeasure B).prod (walkLawUniform B)))

/-- Replace coordinate `j` by the independent trajectory. -/
def swapped (j : ℕ) (z : TrajSeq B × (ℕ → Site B)) : TrajSeq B :=
  Function.update z.1 j z.2

/-- Coordinate replacement is measurable. -/
theorem measurable_swapped (j : ℕ) : Measurable (swapped B j) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i = j
  · subst i
    simpa only [swapped, Function.update_self] using
      (measurable_snd : Measurable (fun z : TrajSeq B × (ℕ → Site B) => z.2))
  · simpa only [swapped, Function.update_of_ne hi, Function.comp_def] using
      (measurable_pi_apply i).comp
        (measurable_fst : Measurable (fun z : TrajSeq B × (ℕ → Site B) => z.1))

/-- The finite symmetric difference produced by resampling one trajectory. -/
noncomputable def swapSites (T j : ℕ) (z : TrajSeq B × (ℕ → Site B)) : Finset (Site B) :=
  symmDiff (clusterPlusFinset B z.1 T) (clusterPlusFinset B (swapped B j z) T)

/-- The resampled symmetric difference has at most two sites, pathwise. -/
theorem swapSites_card_le_two (T j : ℕ) (z : TrajSeq B × (ℕ → Site B)) :
    (swapSites B T j z).card ≤ 2 := by
  classical
  have hshared (i : ℕ) (_ : i < T) (hi : i ≠ j) : z.1 i = swapped B j z i := by
    simp only [swapped, Function.update_of_ne hi]
  have he := CanonicalExchange.clusterPlusTraj_symmDiff_encard_le_two
    B z.1 (swapped B j z) T j hshared
  rw [← coe_clusterPlusFinset B z.1 T, ← coe_clusterPlusFinset B (swapped B j z) T,
    ← Finset.coe_symmDiff, Set.encard_coe_eq_coe_finsetCard] at he
  exact_mod_cast he

/-- Occupation in the positive cluster is a measurable event. -/
theorem measurableSet_mem_clusterPlusFinset (T : ℕ) (p : Site B) :
    MeasurableSet {ω : TrajSeq B | p ∈ clusterPlusFinset B ω T} := by
  by_cases hp : 1 ≤ p.2
  · convert measurableSet_mem_clusterTraj B T p using 1
    ext ω
    exact mem_clusterPlusFinset_iff_cluster B ω T hp
  · have he : {ω : TrajSeq B | p ∈ clusterPlusFinset B ω T} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hp ((mem_clusterPlusFinset_iff B ω T p).mp h).2
    rw [he]
    exact MeasurableSet.empty

/-- Membership in the resampled difference is measurable under the pair law. -/
theorem measurableSet_mem_swapSites (T j : ℕ) (p : Site B) :
    MeasurableSet {z : TrajSeq B × (ℕ → Site B) | p ∈ swapSites B T j z} := by
  classical
  have h₁ := (measurableSet_mem_clusterPlusFinset B T p).preimage
    (measurable_fst : Measurable (fun z : TrajSeq B × (ℕ → Site B) => z.1))
  have h₂ := (measurableSet_mem_clusterPlusFinset B T p).preimage (measurable_swapped B j)
  convert h₁.symmDiff h₂ using 1
  ext z
  simp only [swapSites, Finset.mem_symmDiff, Set.mem_symmDiff,
    Set.mem_preimage, Set.mem_setOf_eq]

/-- Horizontal transport of a resampling pair. -/
noncomputable def transportPair (σ : B.graph ≃g B.graph)
    (z : TrajSeq B × (ℕ → Site B)) : TrajSeq B × (ℕ → Site B) :=
  (transportTraj B σ z.1, walkTransport B σ z.2)

/-- The pair law is invariant under simultaneous horizontal transport. -/
theorem measurePreserving_transportPair (σ : B.graph ≃g B.graph) :
    MeasurePreserving (transportPair B σ) (swapLaw B) (swapLaw B) :=
  (show MeasurePreserving (transportTraj B σ) (idlaMeasure B) (idlaMeasure B) from
    ⟨transportTraj_measurable B σ, idlaMeasure_map_transportTraj B σ⟩).prod
      (show MeasurePreserving (walkTransport B σ) (walkLawUniform B) (walkLawUniform B) from
        ⟨walkTransport_measurable B σ, walkLawUniform_map B σ⟩)

/-- Resampling commutes with simultaneous horizontal transport. -/
theorem swapped_transportPair (σ : B.graph ≃g B.graph) (j : ℕ)
    (z : TrajSeq B × (ℕ → Site B)) :
    swapped B j (transportPair B σ z) = transportTraj B σ (swapped B j z) := by
  funext i
  by_cases hi : i = j
  · subst i
    simp only [swapped, Function.update_self, transportPair, transportTraj]
  · simp only [swapped, Function.update_of_ne hi, transportPair, transportTraj]

private theorem mem_clusterPlusFinset_transport (σ : B.graph ≃g B.graph)
    (ω : TrajSeq B) (T : ℕ) (p : Site B) :
    horIso B σ p ∈ clusterPlusFinset B (transportTraj B σ ω) T ↔
      p ∈ clusterPlusFinset B ω T := by
  change horIso B σ p ∈ (clusterPlusFinset B (transportTraj B σ ω) T : Set (Site B)) ↔
    p ∈ (clusterPlusFinset B ω T : Set (Site B))
  rw [coe_clusterPlusFinset, coe_clusterPlusFinset]
  change (_ ∈ clusterTraj B (transportTraj B σ ω) T ∧ _) ↔
    (p ∈ clusterTraj B ω T ∧ _)
  rw [clusterTraj_horIso]
  constructor
  · rintro ⟨⟨q, hq, he⟩, hy⟩
    have hqp : q = p := (horIso B σ).injective he
    exact ⟨hqp ▸ hq, hy⟩
  · rintro ⟨hp, hy⟩
    exact ⟨⟨p, hp, rfl⟩, hy⟩

/-- The symmetric difference is horizontally equivariant, including trajectories
that never exit a cluster. -/
theorem mem_swapSites_transportPair (σ : B.graph ≃g B.graph) (T j : ℕ)
    (z : TrajSeq B × (ℕ → Site B)) (p : Site B) :
    horIso B σ p ∈ swapSites B T j (transportPair B σ z) ↔ p ∈ swapSites B T j z := by
  classical
  unfold swapSites
  rw [swapped_transportPair]
  change _ ∈ symmDiff (clusterPlusFinset B (transportTraj B σ z.1) T)
    (clusterPlusFinset B (transportTraj B σ (swapped B j z)) T) ↔ _
  simp only [Finset.mem_symmDiff, mem_clusterPlusFinset_transport]

/-- The probability of membership in a resampled difference depends only on
height (`tex:836-841`). -/
theorem swapSites_layer_constancy (T j : ℕ) (x x' : B.V) (y : ℤ) :
    (swapLaw B).real {z | (x, y) ∈ swapSites B T j z} =
      (swapLaw B).real {z | (x', y) ∈ swapSites B T j z} := by
  obtain ⟨σ, hσ⟩ := B.vertexTransitive x x'
  have he : {z | (x, y) ∈ swapSites B T j z} =
      transportPair B σ ⁻¹' {z | (x', y) ∈ swapSites B T j z} := by
    ext z
    have hp : horIso B σ (x, y) = (x', y) := Prod.ext hσ rfl
    simpa only [Set.mem_setOf_eq, Set.mem_preimage, hp] using
      (mem_swapSites_transportPair B σ T j z (x, y)).symm
  unfold Measure.real
  congr 1
  rw [he, ← Measure.map_apply (measurePreserving_transportPair B σ).measurable
    (measurableSet_mem_swapSites B T j (x', y)),
    (measurePreserving_transportPair B σ).map_eq]

end IdlaCyl.Replace
