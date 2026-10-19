/-
thm:cycle without the cited martingale central limit theorem: `thm_cycle_v2` applied to
`IdlaCyl.External.martingale_clt_v2_of_latticeProb`, the Lattice-Probability proof of McLeish's
theorem. The statement is the frozen statement of `thm_cycle_v2` with the binder `hclt` removed.
-/
import IdlaCyl.Frozen.ThmCycleV2
import IdlaCyl.External.Discharge.McLeish

namespace IdlaCyl.Frozen

open IdlaCyl IdlaCyl.Defs Filter MeasureTheory ProbabilityTheory
open scoped Topology

-- FROZEN-STATEMENT-BEGIN
theorem thm_cycle_v3
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
          (Real.toNNReal (variance K α (fun k => Real.sqrt 2 * Real.pi * ((k / 2 : ℕ) : ℝ)) y₀))))
-- FROZEN-STATEMENT-END
    := thm_cycle_v2 IdlaCyl.External.martingale_clt_v2_of_latticeProb
      S K hK α hd hb y₀ hy₀

end IdlaCyl.Frozen
