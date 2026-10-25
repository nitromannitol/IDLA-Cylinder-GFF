module

public import IdlaCylAudit.SolutionBasic
public import IdlaCylAudit.Support.BridgeSpectral
public import IdlaCyl.Frozen.GFFV3

@[expose] public section

/-!
# Theorem 1.3: Gaussian fluctuations of the occupation field

This file proves `IdlaCylAudit.gff`, the Gaussian fluctuation theorem for the rescaled pairing of
the IDLA discrepancy at time `N ⌊y₀ a_N⌋` with the test function built from the eigenfunctions
`2 ≤ k ≤ K`. The statement is the Mathlib-only challenge of the paper's `th:GFF`. The proof
transports the library theorem `IdlaCyl.Frozen.gff_v3` along the bridges, which identify the
vocabulary of the statement with the library's definitions.
-/

namespace IdlaCylAudit

open IdlaCylAudit.Defs Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- Theorem 1.3 (`th:GFF`). Under the spectral assumption and the growth condition, the rescaled
pairing of the discrepancy with the test function converges in law to a centred Gaussian with
variance `variance K α γ y₀`. -/
theorem gff
    (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    ∀ g : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun N : ℕ => ∫ ω : TrajSeq (U.B N),
        g ((Real.sqrt ((N : ℝ) * U.a N))⁻¹ *
          pairingTraj (U.B N) ω (N * Nat.floor (y₀ * U.a N))
            (testAt (U.B N) (U.S N) (U.a N) K α)) ∂idlaMeasure (U.B N))
        atTop (𝓝 (∫ z : ℝ, g z ∂gaussianReal 0 (Real.toNNReal (variance K α γ y₀)))) := by
  intro g
  have h := IdlaCyl.Frozen.gff_v3 (Bridge.setup U) y₀ hy₀ K hK α
    ((Bridge.regular_iff α K y₀).1 hα) γ
    ((Bridge.spectralAssumption_iff U γ K).1 hspec) ((Bridge.growthCondition_iff U).1 hgrowth) g
  simp only [Bridge.setup_B, Bridge.setup_a, ← Bridge.pairingTraj_eq,
    ← Bridge.idlaMeasure_eq] at h
  exact h

end IdlaCylAudit
