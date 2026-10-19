/-
Countable-space gluing of deterministic reduction rounds.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.
Adjacent joint laws are glued over their actual common marginal. No
independence of round-success events is assumed.
-/
import IdlaCyl.Support.Reduction.CountableLift
import IdlaCyl.Support.Reduction.Target

namespace IdlaCyl.Reduction

open MeasureTheory
open scoped BigOperators

/-- Couple two adjacent edges so that their middle coordinates agree almost surely. -/
theorem glue_edges {C D E : Type*} [MeasurableSpace C] [MeasurableSpace D]
    [MeasurableSpace E] [Countable D] [MeasurableSingletonClass D]
    (μ : Measure (C × D)) (ν : Measure (D × E))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hm : μ.map Prod.snd = ν.map Prod.fst) :
    ∃ τ : Measure ((C × D) × (D × E)), τ.map Prod.fst = μ ∧ τ.map Prod.snd = ν ∧
      ∀ᵐ q ∂τ, q.1.2 = q.2.1 := by
  let P := μ.map (Prod.snd : C × D → D)
  haveI : IsProbabilityMeasure P := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let δ := P.map (fun d => (d, d))
  have hdiag : Measurable (fun d : D => (d, d)) := measurable_id.prodMk measurable_id
  have hδf : δ.map Prod.fst = μ.map Prod.snd := by
    change (P.map (fun d => (d, d))).map Prod.fst = P
    rw [Measure.map_map measurable_fst hdiag]
    exact Measure.map_id
  have hδs : δ.map Prod.snd = ν.map Prod.fst := by
    change (P.map (fun d => (d, d))).map Prod.snd = _
    rw [Measure.map_map measurable_snd hdiag]
    exact (Measure.map_id (μ := P)).trans hm
  obtain ⟨τ, hτf, hτs, hτm⟩ := countable_coupling_lift μ ν Prod.snd Prod.fst
    measurable_snd measurable_fst δ hδf hδs
  refine ⟨τ, hτf, hτs, ?_⟩
  have hδbad : δ {p | p.1 ≠ p.2} = 0 := by
    rw [Measure.map_apply hdiag (Set.to_countable _).measurableSet]
    have he : (fun d : D => (d, d)) ⁻¹' {p | p.1 ≠ p.2} = ∅ := by
      ext d
      simp only [Set.mem_preimage, Set.mem_setOf_eq, ne_eq, not_true_eq_false,
        Set.mem_empty_iff_false]
    rw [he, measure_empty]
  have h := congrArg (fun ρ : Measure (D × D) => ρ {p | p.1 ≠ p.2}) hτm
  rw [Measure.map_apply (measurable_snd.prodMap measurable_fst)
    (Set.to_countable _).measurableSet, hδbad] at h
  exact ae_iff.mpr h

/-- Compose two cluster couplings and add their actual failure allowances. -/
theorem clusterCoupling_comp (B : Base) (P Q R : Measure (ResumeFinite B))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (k l : ℕ) (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hc : ClusterCoupling B P Q k ε) (hd : ClusterCoupling B Q R l η) :
    ClusterCoupling B P R (k + l) (ε + η) := by
  obtain ⟨μ, hμf, hμs, hμe⟩ := hc
  obtain ⟨ν, hνf, hνs, hνe⟩ := hd
  haveI : IsProbabilityMeasure μ := probability_of_first_marginal μ P hμf
  haveI : IsProbabilityMeasure ν := probability_of_first_marginal ν Q hνf
  obtain ⟨τ, hτf, hτs, hmid⟩ := glue_edges μ ν (hμs.trans hνf.symm)
  let out : (ResumeFinite B × ResumeFinite B) × (ResumeFinite B × ResumeFinite B) →
      ResumeFinite B × ResumeFinite B := fun q => (q.1.1, q.2.2)
  have hout : Measurable out := measurable_of_countable _
  refine ⟨τ.map out, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hout]
    have h := Measure.map_map measurable_fst measurable_fst (μ := τ)
    rw [hτf, hμf] at h
    exact h.symm
  · rw [Measure.map_map measurable_snd hout]
    have h := Measure.map_map measurable_snd measurable_snd (μ := τ)
    rw [hτs, hνs] at h
    exact h.symm
  · rw [Measure.map_apply hout (Set.to_countable _).measurableSet]
    have hsub : ∀ᵐ q ∂τ, out q ∉ matchShift B (k + l) →
        q.1 ∉ matchShift B k ∨ q.2 ∉ matchShift B l := by
      filter_upwards [hmid] with q hq
      intro hbad
      by_contra hno
      have ha : q.1 ∈ matchShift B k := by
        by_contra h
        exact hno (Or.inl h)
      have hb : q.2 ∈ matchShift B l := by
        by_contra h
        exact hno (Or.inr h)
      apply hbad
      change resumeSeed B q.1.1 = outerShift B (k + l : ℕ) '' resumeSeed B q.2.2
      change resumeSeed B q.1.1 = outerShift B (k : ℤ) '' resumeSeed B q.1.2 at ha
      change resumeSeed B q.2.1 = outerShift B (l : ℤ) '' resumeSeed B q.2.2 at hb
      rw [hq, hb] at ha
      calc
        _ = outerShift B (k : ℤ) '' (outerShift B (l : ℤ) '' resumeSeed B q.2.2) := ha
        _ = _ := shiftCluster_add B k l (resumeSeed B q.2.2)
    calc
      _ ≤ τ ((Prod.fst ⁻¹' (matchShift B k)ᶜ) ∪ (Prod.snd ⁻¹' (matchShift B l)ᶜ)) :=
        measure_mono_ae hsub
      _ ≤ τ (Prod.fst ⁻¹' (matchShift B k)ᶜ) + τ (Prod.snd ⁻¹' (matchShift B l)ᶜ) :=
        measure_union_le _ _
      _ = μ (matchShift B k)ᶜ + ν (matchShift B l)ᶜ := by
        rw [← Measure.map_apply measurable_fst (Set.to_countable _).measurableSet,
          ← Measure.map_apply measurable_snd (Set.to_countable _).measurableSet, hτf, hτs]
      _ ≤ ENNReal.ofReal ε + ENNReal.ofReal η := add_le_add hμe hνe
      _ = ENNReal.ofReal (ε + η) := (ENNReal.ofReal_add hε hη).symm

/-- Glue a finite deterministic chain of reduction couplings, including the zero-round case. -/
theorem glue_cluster_couplings (B : Base) (R : ℕ)
    (P : Fin (R + 1) → Measure (ResumeFinite B))
    (hP : ∀ i, IsProbabilityMeasure (P i))
    (k : Fin R → ℕ) (ε : Fin R → ℝ)
    (hε : ∀ i, 0 ≤ ε i)
    (hc : ∀ i : Fin R,
      ClusterCoupling B (P i.castSucc) (P i.succ) (k i) (ε i)) :
    ClusterCoupling B (P 0) (P (Fin.last R)) (∑ i, k i) (∑ i, ε i) := by
  induction R with
  | zero =>
      haveI : IsProbabilityMeasure (P 0) := hP 0
      simpa only [Fin.sum_univ_zero, Fin.last_zero] using clusterCoupling_diagonal B (P 0)
  | succ R ih =>
      have hprefix : ClusterCoupling B (P 0) (P (Fin.last R).castSucc)
          (∑ i : Fin R, k i.castSucc) (∑ i : Fin R, ε i.castSucc) := by
        apply ih (fun i => P i.castSucc) (fun i => hP i.castSucc)
          (fun i => k i.castSucc) (fun i => ε i.castSucc) (fun i => hε i.castSucc)
        intro i
        simpa only [Fin.castSucc_succ] using hc i.castSucc
      haveI : IsProbabilityMeasure (P 0) := hP 0
      haveI : IsProbabilityMeasure (P (Fin.last R).castSucc) := hP _
      have hcomp := clusterCoupling_comp B (P 0) (P (Fin.last R).castSucc)
        (P (Fin.last (R + 1))) _ _ _ _
        (Finset.sum_nonneg (fun i _ => hε i.castSucc)) (hε (Fin.last R))
        hprefix (hc (Fin.last R))
      simpa only [Fin.sum_univ_castSucc] using hcomp

end IdlaCyl.Reduction
