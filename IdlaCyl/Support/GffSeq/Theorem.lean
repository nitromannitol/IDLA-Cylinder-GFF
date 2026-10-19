/-
Source: paper/idla-cylinder-gff.tex, tex:398-416; proof tex:869-912,1066-1112.
Theorem 1.3 in the canonical IDLA law, conditional only on the cited McLeish
martingale central limit theorem.
-/
import IdlaCyl.Support.Gff.Limit
import IdlaCyl.Support.GffSeq.Limit
import IdlaCyl.Support.Torus.OfGff

namespace IdlaCyl.GffSeq

open IdlaCyl IdlaCyl.Defs Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- `th:GFF` (`tex:398-416`):

> Fix $y_0 \in (0, \infty)$. Let $\phi = \phi_N : V_N \times \bbR \to \bbR$ be a test function of the form
> 	\[ \phi (x,y) = \sum_{k=2}^K \alpha_k(y) f_k^N(x) \]
> for some finite integer $K \geq 2$ independent of $N$, where each coefficient $\alpha_k$ does not depend on $N$ and is differentiable on a neighbourhood of $y_0$ with bounded derivative there.
> Let $\varphi = \varphi_N : V_N \times \bbZ \to \bbR$ be the extension
> 	\[ \varphi (x,y) \coloneqq \phi \Big( x , \frac{y}{a_N} \Big)\,, \qquad (x,y) \in V_N \times \bbZ\,, \]
> with $a_N$ as in~\eqref{eq:aN}. Assume that Assumption~\ref{a:spectral} holds for each $2 \leq k \leq K$, and that
> 	\[ a_N \gg \log N + \log_+ a_N \qquad \text{as } N \to \infty\,. \]
> Let
> 	\[ \sigma^2(\phi) \coloneqq \sum_{k=2}^K \alpha_k(y_0)^2 \, \frac{1 - e^{-2\g_k y_0}}{2\g_k} \,\geq\, 0\,. \]
> Then, with $T = N \lfloor y_0 a_N \rfloor$,
> 	\begin{equation}\label{eq:thGFF}
> 	 \frac{1}{\sqrt{Na_N}} \laa D_T , \varphi \raa \Rightarrow
> 	\mathcal{N} \big( 0\,,\, \sigma^2(\phi) \big)
> 	\end{equation}
> as $N\to\infty$. 
> 
> Here $\Rightarrow$ denotes convergence in distribution, and $\mathcal{N} (0, \sigma^2)$ denotes a normal distribution with $0$ mean and variance $\sigma^2$.

The normalized discrepancy pairing at `T = N ⌊y₀ a_N⌋` converges to the centered
Gaussian with the printed variance, as tested by every bounded continuous function. -/
theorem gff_v2 (hclt : IdlaCyl.External.martingale_clt_v2)
    (U : SequenceSetup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    ∀ g : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun N : ℕ => ∫ ω : TrajSeq (U.B N),
        g ((Real.sqrt (((U.B N).card : ℝ) * U.a N))⁻¹ *
          pairingTraj (U.B N) ω ((U.B N).card * Nat.floor (y₀ * U.a N))
            (testAt (U.B N) (U.S N) (U.a N) K α)) ∂idlaMeasure (U.B N))
        atTop (𝓝 (∫ z : ℝ, g z ∂gaussianReal 0 (Real.toNNReal (variance K α γ y₀))))
    := by
  intro g
  have hd := Gff.statistic_tendstoInDistribution hclt U y₀ hy₀ K hK α hα γ hspec hgrowth
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hd.tendsto) g
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at ht
  have hmap (N : ℕ) : (∫ z : ℝ, g z ∂(Gff.law U).map (Gff.statistic U K α y₀ N)) =
      ∫ ω : Gff.Space U, g (Gff.statistic U K α y₀ N ω) ∂Gff.law U :=
    integral_map (Gff.measurable_statistic U K α y₀ N).aemeasurable
      g.continuous.measurable.aestronglyMeasurable
  simp_rw [hmap] at ht
  apply ht.congr'
  filter_upwards with N
  have htime : SequenceSetup.time U y₀ N = (U.B N).card * Nat.floor (y₀ * U.a N) := rfl
  dsimp only [Gff.statistic]
  have heval := Gff.integral_eval U N
    (fun ω : TrajSeq (U.B N) => g ((Real.sqrt (((U.B N).card : ℝ) * U.a N))⁻¹ *
      pairingTraj (U.B N) ω (SequenceSetup.time U y₀ N) (testAt (U.B N) (U.S N) (U.a N) K α)))
    (g.continuous.measurable.comp
      (measurable_const.mul (measurable_pairingTraj (U.B N) (SequenceSetup.time U y₀ N) _)))
  simpa only [htime] using heval

end IdlaCyl.GffSeq

namespace IdlaCyl
/-- The GFF theorem along a cofinal row-indexed sequence of bases (tex:398-416). -/
theorem gff_along_sequence : GffAlongSequence := GffSeq.gff_v2
end IdlaCyl
