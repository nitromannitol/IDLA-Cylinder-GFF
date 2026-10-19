/-
Recover a raw-shift coupling from an equality coupling to translated clusters.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.
-/
import IdlaCyl.Support.Reduction.ShiftFinite
import IdlaCyl.Support.Reduction.CountableLift

namespace IdlaCyl.Reduction

open MeasureTheory

/-- The second translated marginal can be lifted back without changing the failure law. -/
theorem clusterCoupling_unshift_second (B : Base) (L : ℕ)
    (P Q : Measure (ResumeFinite B)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (ε : ℝ) (hc : ClusterCoupling B P (Q.map (shiftFinite B L)) 0 ε) :
    ClusterCoupling B P Q L ε := by
  obtain ⟨ρ, hf, hs, he⟩ := hc
  obtain ⟨η, hηf, hηs, hη⟩ := countable_coupling_lift P Q id (shiftFinite B L)
    measurable_id (measurable_of_countable _) ρ (by simpa only [Measure.map_id] using hf) hs
  refine ⟨η, hηf, hηs, ?_⟩
  have hpre : (Prod.map id (shiftFinite B L)) ⁻¹' (matchShift B 0)ᶜ =
      (matchShift B L)ᶜ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_compl_iff, mem_matchShift_zero]
    apply not_congr
    change p.1 = shiftFinite B L p.2 ↔ p ∈ matchShift B L
    rw [← (resumeSeed_injective B).eq_iff, resumeSeed_shiftFinite]
    rfl
  rw [← hη, Measure.map_apply (measurable_id.prodMap (measurable_of_countable _))
    (Set.to_countable _).measurableSet, hpre] at he
  exact he

end IdlaCyl.Reduction
