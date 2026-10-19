import IdlaCylAudit.SolutionBasic
import IdlaCylAudit.Support.BridgeSpectral
import IdlaCylAudit.Support.BridgeExamples
import IdlaCyl.Frozen.ThmCycleV3

/-!
# The cycle example: solution

The Gaussian limit of Theorem 1.3 on the cycles `ℤ_N`, with `a_N = N` and `γ_k = √2 π ⌊k/2⌋`,
for every choice of eigenbases, every `K ≥ 2` and coefficients `α_k` that are differentiable with
bounded derivative. The statement is that of the challenge `IdlaCylAudit.thm_cycle`, whose
vocabulary is a copy of the library's. The proof transports the library theorem
`IdlaCyl.Frozen.thm_cycle_v3` along the identifications of the vocabulary with the library. On the
indexed cycle base these identifications are propositional (by cases on `3 ≤ N`); the remaining
ones are definitional, except for the pairing, which is carried across by its bridge.
-/

namespace IdlaCylAudit

open IdlaCylAudit.Defs Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- The spectral data of the vocabulary on the indexed cycle base at `N`, read as spectral data of
the library's indexed cycle base. -/
noncomputable def spectralAt (N : ℕ) (S : SpectralData (CycleSpectrum.indexedBase N)) :
    IdlaCyl.SpectralData (IdlaCyl.CycleSpectrum.indexedBase N) :=
  (Bridge.indexedBase_eq N) ▸ Bridge.spectralData S

/-- The integral of a library pairing does not change when the library base is replaced by an equal
one, the spectral data being transported along the equality. -/
theorem integral_transport {B₁ B₂ : IdlaCyl.Base} (h : B₁ = B₂) (S : IdlaCyl.SpectralData B₁)
    (g : BoundedContinuousFunction ℝ ℝ) (c a : ℝ) (t K : ℕ) (α : ℕ → ℝ → ℝ) :
    ∫ ω : IdlaCyl.TrajSeq B₁,
        g (c * IdlaCyl.pairingTraj B₁ ω t (IdlaCyl.Defs.testAt B₁ S a K α))
          ∂IdlaCyl.idlaMeasure B₁ =
      ∫ ω : IdlaCyl.TrajSeq B₂,
        g (c * IdlaCyl.pairingTraj B₂ ω t (IdlaCyl.Defs.testAt B₂ (h ▸ S) a K α))
          ∂IdlaCyl.idlaMeasure B₂ := by
  subst h
  rfl

/-- The test function of the vocabulary is the library's, as a function on sites. -/
theorem testFun_eq (B : IdlaCylAudit.Base) (S : SpectralData B) (a : ℝ) (K : ℕ)
    (α : ℕ → ℝ → ℝ) :
    Defs.testAt B S a K α = IdlaCyl.Defs.testAt (Bridge.base B) (Bridge.spectralData S) a K α :=
  funext (Bridge.testAt_eq B S a K α)

/-- The term of the vocabulary's cycle sequence at `N` is the library's term at `N`, with the
spectral data transported by `spectralAt`. -/
theorem term_eq (N : ℕ) (S : SpectralData (CycleSpectrum.indexedBase N))
    (g : BoundedContinuousFunction ℝ ℝ) (c a : ℝ) (t K : ℕ) (α : ℕ → ℝ → ℝ) :
    ∫ ω : TrajSeq (CycleSpectrum.indexedBase N),
        g (c * pairingTraj (CycleSpectrum.indexedBase N) ω t
          (testAt (CycleSpectrum.indexedBase N) S a K α))
          ∂idlaMeasure (CycleSpectrum.indexedBase N) =
      ∫ ω : IdlaCyl.TrajSeq (IdlaCyl.CycleSpectrum.indexedBase N),
        g (c * IdlaCyl.pairingTraj (IdlaCyl.CycleSpectrum.indexedBase N) ω t
          (IdlaCyl.Defs.testAt (IdlaCyl.CycleSpectrum.indexedBase N) (spectralAt N S) a K α))
          ∂IdlaCyl.idlaMeasure (IdlaCyl.CycleSpectrum.indexedBase N) := by
  simp only [Bridge.idlaMeasure_eq, Bridge.pairingTraj_eq, testFun_eq]
  exact integral_transport (Bridge.indexedBase_eq N) (Bridge.spectralData S) g c a t K α

/-- The Gaussian limit of Theorem 1.3 on the cycles `ℤ_N`, with `a_N = N` and
`γ_k = √2 π ⌊k/2⌋`, for every choice of eigenbases, every `K ≥ 2` and coefficients `α_k` that
are differentiable with bounded derivative. -/
theorem thm_cycle
    (S : (N : ℕ) → SpectralData (CycleSpectrum.indexedBase N))
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ)
    (hd : ∀ k ∈ Finset.Icc 2 K, Differentiable ℝ (α k))
    (hb : ∀ k ∈ Finset.Icc 2 K, ∃ M : ℝ, ∀ y, |deriv (α k) y| ≤ M)
    (y₀ : ℝ) (hy₀ : 0 < y₀) :
    ∀ g : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun N : ℕ => ∫ ω : TrajSeq (CycleSpectrum.indexedBase N),
        g ((1 / (N : ℝ)) *
          pairingTraj (CycleSpectrum.indexedBase N) ω (N * Nat.floor (y₀ * (N : ℝ)))
            (testAt (CycleSpectrum.indexedBase N) (S N) (N : ℝ) K α))
          ∂idlaMeasure (CycleSpectrum.indexedBase N))
        atTop (𝓝 (∫ z : ℝ, g z ∂gaussianReal 0
          (Real.toNNReal (variance K α (fun k => Real.sqrt 2 * Real.pi * ((k / 2 : ℕ) : ℝ)) y₀)))) := by
  intro g
  rw [Bridge.variance_eq]
  refine Tendsto.congr (fun N => ?_)
    (IdlaCyl.Frozen.thm_cycle_v3 (fun N => spectralAt N (S N)) K hK α hd hb y₀ hy₀ g)
  exact (term_eq N (S N) g (1 / (N : ℝ)) (N : ℝ) (N * Nat.floor (y₀ * (N : ℝ))) K α).symm

end IdlaCylAudit
