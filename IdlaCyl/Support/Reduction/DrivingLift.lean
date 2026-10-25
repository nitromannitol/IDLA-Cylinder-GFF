module

/-
A finite-cluster coupling lifts to the exact full-driving-law reduction header.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.
No stochastic IDLA assertion is assumed beyond the supplied endpoint coupling.
-/
public import IdlaCyl.Support.Reduction.Target
public import IdlaCyl.Support.Reduction.CountableLift

@[expose] public section

namespace IdlaCyl.Reduction

open MeasureTheory

/-- The finite flat-start cluster law is the literal canonical driving-law pushforward. -/
theorem flatClusterLaw_eq_map (B : Base) (n : ℕ) :
    flatClusterLaw B n = (idlaMeasure B).map (fun ω => resumeGrow B (resumeEmpty B) ω n) := rfl

/-- The two shift definitions coincide on actual finite growth, including the infinite seed. -/
theorem matchShift_preimage (B : Base) (T T' k : ℕ) :
    (Prod.map (fun ω => resumeGrow B (resumeEmpty B) ω T)
      (fun ω => resumeGrow B (resumeEmpty B) ω T')) ⁻¹' matchShift B k =
      {p | clusterTraj B p.1 T = shiftCluster B k (clusterTraj B p.2 T')} := by
  ext p
  change resumeSeed B (resumeGrow B (resumeEmpty B) p.1 T) =
      outerShift B (k : ℤ) '' resumeSeed B (resumeGrow B (resumeEmpty B) p.2 T') ↔ _
  rw [resumeSeed_grow, resumeSeed_grow, resumeSeed_empty]
  rfl

/-- Lift an actual endpoint coupling, with its same failure allowance, to whole driving sequences. -/
theorem lift_cluster_coupling (B : Base) (T T' k : ℕ) (ε : ℝ)
    (hc : ClusterCoupling B (flatClusterLaw B T) (flatClusterLaw B T') k ε) :
    ∃ μ : Measure (TrajSeq B × TrajSeq B),
      μ.map Prod.fst = idlaMeasure B ∧ μ.map Prod.snd = idlaMeasure B ∧
      μ {p | clusterTraj B p.1 T =
        shiftCluster B k (clusterTraj B p.2 T')}ᶜ ≤ ENNReal.ofReal ε := by
  obtain ⟨ρ, hρf, hρg, hρe⟩ := hc
  rw [flatClusterLaw_eq_map] at hρf hρg
  obtain ⟨μ, hμf, hμg, hμout⟩ := countable_coupling_lift (idlaMeasure B) (idlaMeasure B)
    (fun ω => resumeGrow B (resumeEmpty B) ω T)
    (fun ω => resumeGrow B (resumeEmpty B) ω T')
    (measurable_resumeGrow B (resumeEmpty B) T)
    (measurable_resumeGrow B (resumeEmpty B) T') ρ hρf hρg
  refine ⟨μ, hμf, hμg, ?_⟩
  rw [← matchShift_preimage B T T' k, ← Set.preimage_compl,
    ← Measure.map_apply
      ((measurable_resumeGrow B (resumeEmpty B) T).prodMap
        (measurable_resumeGrow B (resumeEmpty B) T')) (Set.to_countable _).measurableSet,
    hμout]
  exact hρe

end IdlaCyl.Reduction
