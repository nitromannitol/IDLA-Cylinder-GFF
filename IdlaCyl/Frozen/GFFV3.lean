module

/-
th:GFF without the cited martingale central limit theorem: `gff_v2` applied to
`IdlaCyl.External.martingale_clt_v2_of_latticeProb`, the Lattice-Probability proof of McLeish's
theorem. The statement is the frozen statement of `gff_v2` with the binder `hclt` removed.
-/
public import IdlaCyl.Frozen.GFFV2
public import IdlaCyl.External.Discharge.McLeish

@[expose] public section

namespace IdlaCyl.Frozen

open IdlaCyl IdlaCyl.Defs Filter MeasureTheory ProbabilityTheory
open scoped Topology

-- FROZEN-STATEMENT-BEGIN
theorem gff_v3
    (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    ∀ g : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun N : ℕ => ∫ ω : TrajSeq (U.B N),
        g ((Real.sqrt ((N : ℝ) * U.a N))⁻¹ *
          pairingTraj (U.B N) ω (N * Nat.floor (y₀ * U.a N))
            (testAt (U.B N) (U.S N) (U.a N) K α)) ∂idlaMeasure (U.B N))
        atTop (𝓝 (∫ z : ℝ, g z ∂gaussianReal 0 (Real.toNNReal (variance K α γ y₀))))
-- FROZEN-STATEMENT-END
    := gff_v2 IdlaCyl.External.martingale_clt_v2_of_latticeProb
      U y₀ hy₀ K hK α hα γ hspec hgrowth

end IdlaCyl.Frozen
