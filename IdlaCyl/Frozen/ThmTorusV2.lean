/-
Source: paper/idla-cylinder-gff.tex, tex:502-518 (the torus base Z_n^d, its eigenvalues, γ_k, and thm:torus with its
proof "The conclusion follows from Theorem th:GFF").
-/
import IdlaCyl.Support.GffSeq.Theorem
import IdlaCyl.Support.Torus.OfGff

namespace IdlaCyl.Frozen

open IdlaCyl IdlaCyl.Defs Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- `thm:torus` (`tex:507-514`):

> \begin{Theorem}\label{thm:torus}
> Let $\a_2, \ldots, \a_K : \bbR \to \bbR$ be differentiable functions with bounded derivatives, where $K \geq 2$ is an integer independent of $N$, and fix $y_0 > 0$. Let
> 	\[ \phi(\underline x, y) = \sum_{k=2}^K \a_k(y)\, f_k^N(\underline x) \]
> be the corresponding test function on $\bbZ_n^d \times \bbR$, and let $\varphi(\underline x, y) \coloneqq \phi(\underline x, y/a_N)$ on $\bbZ_n^d \times \bbZ$. Then with $T = N \lfloor y_0 a_N \rfloor$,
> 	\[ \frac{1}{\sqrt{N a_N}} \laa D_T,\, \varphi \raa
> 	\Rightarrow \cN\!\left(0\,, \sum_{k=2}^K \a_k(y_0)^2\, \frac{1 - e^{-2\g_k y_0}}{2\g_k} \right) \]
> as $n \to \infty$, where $\g_k \coloneqq \lim_{n\to\infty} a_N \sqrt{2(1 - \l_k(N))}$.
> \end{Theorem}
> 

For every lawful eigenbasis of the torus `(ℤ/n)^d`, `n = side ≥ 3`, `(N a_N)^{-1/2}⟨D_T, φ⟩` with `N = n^d`, `a_N = n` converges
in distribution to the centred normal law with variance `∑_{k=2}^K α_k(y₀)² (1 - e^{-2γ_k y₀})/(2γ_k)`, where
`γ_k = π √(2/d) √r_k` is the printed limit `a_N √(2(1 - λ_k(N)))` (`TorusSpectrum.gamma_limit`), given the cited martingale central
limit theorem. -/
-- FROZEN-STATEMENT-BEGIN
theorem thm_torus_v2
    (hclt : IdlaCyl.External.martingale_clt_v2)
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
  := thm_torus_of_gff_sequence gff_along_sequence hclt d hd S K hK α hαd hαb y₀ hy₀

end IdlaCyl.Frozen
