module

public import IdlaCylAudit.SolutionBasic
public import IdlaCylAudit.Support.BridgeSpectral
public import IdlaCylAudit.Support.BridgeExamples
public import IdlaCyl.Frozen.ThmTorusV3

@[expose] public section

/-!
# The torus example: the Gaussian limit

On the discrete tori `(ℤ/N)^d` with side length `N = n + 3`, the cluster discrepancy of the
IDLA process at height `y₀ > 0`, paired with the spectral test function
`∑_{k=2}^K α_k(y/N) f_k` and rescaled by `√(N^d · N)⁻¹`, converges in law to a centred Gaussian
as `n → ∞`. The variance is the sum over the shells `k ≥ 2` of
`α_k(y₀)² (1 - e^{-2 γ_k y₀}) / (2 γ_k)`, where `γ_k = π √(2/d) √(shell k)`.

The proof is the library's theorem `IdlaCyl.Frozen.thm_torus_v3`, transported along the bridges.
The torus base, the driving law, the test function, the variance and the shell enumeration of the
vocabulary are definitionally the library's. The pairing is only propositionally equal to the
library's, through the induction `clusterTraj_eq`, so it is rewritten first.
-/

namespace IdlaCylAudit

/-- The Gaussian limit for the tori `(ℤ/(n+3))^d`, `d ≥ 1`, with the spectral data `S n` of each
torus, the coefficients `α_k` for `2 ≤ k ≤ K` and the height `y₀ > 0`: the rescaled pairing
converges in distribution to a centred Gaussian with the variance `σ²` of `Defs.variance`. -/
theorem thm_torus
    (d : ℕ) (hd : 1 ≤ d)
    (S : (n : ℕ) → IdlaCylAudit.SpectralData (IdlaCylAudit.torusSeq d hd n))
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ)
    (hαd : ∀ k ∈ Finset.Icc 2 K, Differentiable ℝ (α k))
    (hαb : ∀ k ∈ Finset.Icc 2 K, ∃ M : ℝ,
      ∀ y, |deriv (α k) y| ≤ M)
    (y₀ : ℝ) (hy₀ : 0 < y₀) :
    ∀ g : BoundedContinuousFunction ℝ ℝ,
      Filter.Tendsto (fun n : ℕ => ∫ ω : IdlaCylAudit.TrajSeq (IdlaCylAudit.torusSeq d hd n),
        g ((Real.sqrt ((((n + 3) ^ d : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ)))⁻¹ *
          IdlaCylAudit.pairingTraj (IdlaCylAudit.torusSeq d hd n) ω
            ((n + 3) ^ d * Nat.floor (y₀ * ((n + 3 : ℕ) : ℝ)))
            (IdlaCylAudit.Defs.testAt (IdlaCylAudit.torusSeq d hd n) (S n)
              ((n + 3 : ℕ) : ℝ) K α))
          ∂IdlaCylAudit.idlaMeasure (IdlaCylAudit.torusSeq d hd n))
        Filter.atTop
        (nhds (∫ z : ℝ, g z ∂ProbabilityTheory.gaussianReal 0
          (Real.toNNReal (IdlaCylAudit.Defs.variance K α
            (fun k => Real.pi * Real.sqrt (2 / (d : ℝ)) *
              Real.sqrt (IdlaCylAudit.TorusSpectrum.shell d hd k)) y₀)))) := by
  intro g
  simp only [IdlaCylAudit.Bridge.pairingTraj_eq, IdlaCylAudit.Bridge.variance_eq,
    IdlaCylAudit.Bridge.shell_eq]
  exact IdlaCyl.Frozen.thm_torus_v3 d hd (fun n => IdlaCylAudit.Bridge.spectralData (S n))
    K hK α hαd hαb y₀ hy₀ g

end IdlaCylAudit
