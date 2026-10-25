module

/-
Source: paper/idla-cylinder-gff.tex, tex:474-498 (the cycle base, eq:fj, a_N = N, and thm:cycle with its
proof "This is Theorem th:GFF applied to V_N = Z_N with a_N = N").
-/
public import IdlaCyl.Frozen.GFFV2
public import IdlaCyl.Support.Cycle.OfGff

@[expose] public section

namespace IdlaCyl.Frozen

open IdlaCyl IdlaCyl.Defs Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- `thm:cycle` (`tex:486-494`):

> \begin{Theorem}\label{thm:cycle}
> Let $\a_2, \ldots, \a_K : \bbR \to \bbR$ be differentiable functions with bounded derivatives, where $K \geq 2$ is an integer independent of $N$, and fix $y_0 > 0$. Let $\phi : \bbZ_N \times \bbR \to \bbR$ be the test function
> 	\[ \phi(x, y) = \sum_{k=2}^K \a_k(y)\, f_k^N(x)\,, \]
> and let $\varphi(x,y) \coloneqq \phi(x, y/a_N)$ on $\bbZ_N \times \bbZ$. Then with $T = N \lfloor y_0 a_N \rfloor$,
> 	\[ \frac{1}{N} \laa D_T,\, \varphi \raa
> 	\Rightarrow \cN\!\left( 0\,, \sum_{k=2}^K \a_k(y_0)^2\, \frac{1 - e^{-2\g_k y_0}}{2 \g_k} \right) \]
> as $N \to \infty$, where $\g_k = \sqrt{2}\,\pi\,\lfloor k/2 \rfloor$.
> \end{Theorem}
> 

For every lawful eigenbasis of the cycle `ℤ_N` (of which `eq:fj` is one), `(1/N)⟨D_T, φ⟩` converges in
distribution to the centred normal law with variance `∑_{k=2}^K α_k(y₀)² (1 - e^{-2γ_k y₀})/(2γ_k)`,
`γ_k = √2 π ⌊k/2⌋`, given the cited martingale central limit theorem. -/
-- FROZEN-STATEMENT-BEGIN
theorem thm_cycle_v2 (hclt : IdlaCyl.External.martingale_clt_v2)
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
  := thm_cycle_of_gff (gff_v2 hclt) S K hK α hd hb y₀ hy₀

end IdlaCyl.Frozen
