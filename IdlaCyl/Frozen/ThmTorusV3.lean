/-
thm:torus without the cited martingale central limit theorem: `thm_torus_v2` applied to
`IdlaCyl.External.martingale_clt_v2_of_latticeProb`, the Lattice-Probability proof of McLeish's
theorem. The statement is the frozen statement of `thm_torus_v2` with the binder `hclt` removed.
-/
import IdlaCyl.Frozen.ThmTorusV2
import IdlaCyl.External.Discharge.McLeish

namespace IdlaCyl.Frozen

open IdlaCyl IdlaCyl.Defs Filter MeasureTheory ProbabilityTheory
open scoped Topology

-- FROZEN-STATEMENT-BEGIN
theorem thm_torus_v3
    (d : ℕ) (hd : 1 ≤ d)
    (S : (n : ℕ) → IdlaCyl.SpectralData (IdlaCyl.torusSeq d hd n))
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ)
    (hαd : ∀ k ∈ Finset.Icc 2 K, Differentiable ℝ (α k))
    (hαb : ∀ k ∈ Finset.Icc 2 K, ∃ M : ℝ,
      ∀ y, |deriv (α k) y| ≤ M)
    (y₀ : ℝ) (hy₀ : 0 < y₀) :
    ∀ g : BoundedContinuousFunction ℝ ℝ,
      Filter.Tendsto (fun n : ℕ => ∫ ω : IdlaCyl.TrajSeq (IdlaCyl.torusSeq d hd n),
        g ((Real.sqrt ((((n + 3) ^ d : ℕ) : ℝ) * ((n + 3 : ℕ) : ℝ)))⁻¹ *
          IdlaCyl.pairingTraj (IdlaCyl.torusSeq d hd n) ω
            ((n + 3) ^ d * Nat.floor (y₀ * ((n + 3 : ℕ) : ℝ)))
            (IdlaCyl.Defs.testAt (IdlaCyl.torusSeq d hd n) (S n)
              ((n + 3 : ℕ) : ℝ) K α))
          ∂IdlaCyl.idlaMeasure (IdlaCyl.torusSeq d hd n))
        Filter.atTop
        (nhds (∫ z : ℝ, g z ∂ProbabilityTheory.gaussianReal 0
          (Real.toNNReal (IdlaCyl.Defs.variance K α
            (fun k => Real.pi * Real.sqrt (2 / (d : ℝ)) *
              Real.sqrt (IdlaCyl.TorusSpectrum.shell d hd k)) y₀))))
-- FROZEN-STATEMENT-END
    := thm_torus_v2 IdlaCyl.External.martingale_clt_v2_of_latticeProb
      d hd S K hK α hαd hαb y₀ hy₀

end IdlaCyl.Frozen
