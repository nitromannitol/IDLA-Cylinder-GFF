/-
Elementary probability interfaces for the cluster couplings.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.
All marginals and equality events are literal; no existence of a reduction
coupling is assumed here.
-/
import IdlaCyl.Support.Reduction.Laws

namespace IdlaCyl.Reduction

open MeasureTheory

/-- A probability first marginal forces the joint measure to be a probability. -/
theorem probability_of_first_marginal {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure (α × β)) (P : Measure α) [IsProbabilityMeasure P]
    (hμ : μ.map Prod.fst = P) : IsProbabilityMeasure μ := by
  haveI : IsProbabilityMeasure (μ.map (Prod.fst : α × β → α)) := by
    rw [hμ]
    infer_instance
  exact Measure.isProbabilityMeasure_of_map Prod.fst

/-- Convert a real success lower bound to a complement upper bound without truncation loss. -/
theorem failure_le_of_success {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (E : Set α) (hE : MeasurableSet E) (ε : ℝ) (hε : 0 ≤ ε)
    (hs : ENNReal.ofReal (1 - ε) ≤ μ E) : μ Eᶜ ≤ ENNReal.ofReal ε := by
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hε).mpr
  have hr := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ E)).mp hs
  have hc := probReal_compl_eq_one_sub (μ := μ) hE
  change μ.real Eᶜ ≤ ε
  rw [hc]
  change 1 - (μ E).toReal ≤ ε
  linarith

/-- The zero vertical translation is literally the identity on occupied sets. -/
theorem outerShift_zero_image (B : Base) (A : Set (Site B)) :
    outerShift B 0 '' A = A := by
  have heq : (outerShift B 0 : Site B → Site B) = id := by
    funext z
    exact Prod.ext rfl (add_zero z.2)
  rw [heq, Set.image_id]

/-- The zero-shift match event is equality of the injective finite cluster codes. -/
theorem mem_matchShift_zero (B : Base) (p : ResumeFinite B × ResumeFinite B) :
    p ∈ matchShift B 0 ↔ p.1 = p.2 := by
  change resumeSeed B p.1 = outerShift B 0 '' resumeSeed B p.2 ↔ _
  rw [outerShift_zero_image]
  exact (resumeSeed_injective B).eq_iff

/-- Both actual finite-cluster laws agree in a diagonal zero-error coupling. -/
theorem clusterCoupling_diagonal (B : Base) (P : Measure (ResumeFinite B))
    [IsProbabilityMeasure P] : ClusterCoupling B P P 0 0 := by
  let μ := P.map (fun F => (F, F))
  have hdiag : Measurable (fun F : ResumeFinite B => (F, F)) :=
    measurable_id.prodMk measurable_id
  refine ⟨μ, ?_, ?_, ?_⟩
  · change (P.map (fun F => (F, F))).map Prod.fst = P
    rw [Measure.map_map measurable_fst hdiag]
    exact Measure.map_id
  · change (P.map (fun F => (F, F))).map Prod.snd = P
    rw [Measure.map_map measurable_snd hdiag]
    exact Measure.map_id
  · change (P.map (fun F => (F, F))) (matchShift B 0)ᶜ ≤ _
    rw [Measure.map_apply hdiag (Set.to_countable _).measurableSet]
    have hempty : (fun F : ResumeFinite B => (F, F)) ⁻¹' (matchShift B 0)ᶜ = ∅ := by
      ext F
      simp only [Set.mem_preimage, Set.mem_compl_iff, mem_matchShift_zero, not_true_eq_false,
        Set.mem_empty_iff_false]
    rw [hempty, measure_empty, ENNReal.ofReal_zero]

/-- Increasing a nonnegative failure allowance preserves a constructed coupling. -/
theorem clusterCoupling_mono (B : Base) (P Q : Measure (ResumeFinite B))
    (k : ℕ) (ε η : ℝ) (hεη : ε ≤ η) (hc : ClusterCoupling B P Q k ε) :
    ClusterCoupling B P Q k η := by
  obtain ⟨μ, hf, hs, he⟩ := hc
  exact ⟨μ, hf, hs, he.trans (ENNReal.ofReal_le_ofReal hεη)⟩

end IdlaCyl.Reduction
