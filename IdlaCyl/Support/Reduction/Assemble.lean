module

/-
Finite-coefficient reduction from Silvestri's Proposition 2.
Source: paper/idla-cylinder-gff.tex, tex:270-282,1119-1136,1440-1453;
Both marginals are the entire canonical driving law.
-/
public import IdlaCyl.Support.Reduction.UniformParameters
public import IdlaCyl.Support.Reduction.DrivingLift

@[expose] public section

namespace IdlaCyl.Reduction

open MeasureTheory

/-- The finite-coefficient reduction uses only the explicit cited input. -/
theorem pr_reduction_alpha_of_silvestri
    (hsil : External.silvestri_prop2) : IdlaCyl.pr_reduction_alpha := by
  intro ν hν m hm
  obtain ⟨α, hα, N₀, hc⟩ := reduced_cluster_coupling hsil ν m hν hm
  refine ⟨α, hα, N₀, ?_⟩
  intro B hN T hlow hhigh
  have hT : 0 < T := by
    have hh := lt_of_lt_of_le (mul_pos hα (reduction_sharp_pos B)) hlow
    exact_mod_cast hh
  obtain ⟨T', k, hT', hscale, hvol, hcouple⟩ := hc B hN T hT hhigh
  obtain ⟨μ, hf, hs, he⟩ := lift_cluster_coupling B T T' k _ hcouple
  haveI : IsProbabilityMeasure μ := coupling_isProbability B μ hf
  refine ⟨T', k, hT', hscale, hvol, μ, hf, hs, ?_⟩
  let E := {p : TrajSeq B × TrajSeq B | clusterTraj B p.1 T =
    shiftCluster B k (clusterTraj B p.2 T')}
  have hE : MeasurableSet E := measurableSet_cluster_eq_shift B T T' k
  have hε : 0 ≤ (B.card : ℝ) ^ (-(ν + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hreal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) he
  rw [ENNReal.toReal_ofReal hε] at hreal
  have hcompl := probReal_compl_eq_one_sub (μ := μ) hE
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ E)).mpr
  change (μ Eᶜ).toReal ≤ _ at hreal
  change (μ Eᶜ).toReal = 1 - (μ E).toReal at hcompl
  linarith

end IdlaCyl.Reduction
