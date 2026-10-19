/-
The torus theorem conditional on the proposed general-index GFF theorem.
Source: tex:398-416,502-520, `paper/idla-cylinder-gff.tex`.
The general-index GFF conclusion is an explicit premise, not an asserted result.
-/
import IdlaCyl.Support.Torus.Setup
import IdlaCyl.Definitions.TestFunction
import IdlaCyl.Support.CanonicalIdla
import IdlaCyl.External.MartingaleCltV2

namespace IdlaCyl
open Defs Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- The proposed general-index GFF theorem, as an explicit proposition.
This definition does not assert that the proposition is true. -/
def GffAlongSequence : Prop :=
  External.martingale_clt_v2 →
  ∀ (U : SequenceSetup) (y₀ : ℝ), 0 < y₀ →
    ∀ (K : ℕ), 2 ≤ K → ∀ (α : ℕ → ℝ → ℝ), regular α K y₀ →
      ∀ (γ : ℕ → ℝ), U.SpectralAssumption γ K → U.GrowthCondition →
        ∀ g : BoundedContinuousFunction ℝ ℝ,
          Tendsto (fun n : ℕ => ∫ ω : TrajSeq (U.B n),
            g ((Real.sqrt (((U.B n).card : ℝ) * U.a n))⁻¹ *
              pairingTraj (U.B n) ω ((U.B n).card * Nat.floor (y₀ * U.a n))
                (testAt (U.B n) (U.S n) (U.a n) K α)) ∂idlaMeasure (U.B n))
            atTop (𝓝 (∫ z : ℝ, g z ∂gaussianReal 0 (Real.toNNReal (variance K α γ y₀))))

/-- The exact torus conclusion, reduced to the general-index GFF theorem.
The additional premise `hgff` is the general-index GFF theorem. -/
theorem thm_torus_of_gff_sequence (hgff : GffAlongSequence)
    (hclt : External.martingale_clt_v2)
    (d : ℕ) (hd : 1 ≤ d) (S : (n : ℕ) → SpectralData (torusSeq d hd n))
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ)
    (hαd : ∀ k ∈ Finset.Icc 2 K, Differentiable ℝ (α k))
    (hαb : ∀ k ∈ Finset.Icc 2 K, ∃ M : ℝ, ∀ y, |deriv (α k) y| ≤ M)
    (y₀ : ℝ) (hy₀ : 0 < y₀) :
    ∀ g : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ ω : TrajSeq (torusSeq d hd n),
        g ((Real.sqrt ((((n + 3) ^ d : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ)))⁻¹ *
          pairingTraj (torusSeq d hd n) ω
            ((n + 3) ^ d * Nat.floor (y₀ * ((n + 3 : ℕ) : ℝ)))
            (testAt (torusSeq d hd n) (S n) ((n + 3 : ℕ) : ℝ) K α))
          ∂idlaMeasure (torusSeq d hd n))
        atTop (𝓝 (∫ z : ℝ, g z ∂gaussianReal 0
          (Real.toNNReal (variance K α (torusGamma d hd) y₀)))) := by
  intro g
  have hreg : regular α K y₀ := by
    intro k hk2 hkK
    have hk : k ∈ Finset.Icc 2 K := Finset.mem_Icc.mpr ⟨hk2, hkK⟩
    obtain ⟨M, hM⟩ := hαb k hk
    exact ⟨Set.univ, Filter.univ_mem, fun y _ => hαd k hk y, M, fun y _ => hM y⟩
  have h := hgff hclt (torusSetupOf d hd S) y₀ hy₀ K hK α hreg (torusGamma d hd)
    (torusSetupOf_spectralAssumption d hd S K) (torusSetupOf_growthCondition d hd S) g
  simp only [torusSetupOf, torusBase_card] at h
  convert h using 1
  funext n
  congr 1

end IdlaCyl
