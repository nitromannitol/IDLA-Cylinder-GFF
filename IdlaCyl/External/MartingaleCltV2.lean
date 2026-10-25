module

/-
Theorem `thm:martingale-CLT` from *Gaussian fluctuations for Internal DLA on cylinders*
(Bou-Rabee, Silvestri, Yadin), `paper/idla-cylinder-gff.tex`, lines 882-892, citing
McLeish (1974), Theorem 2.3:

Let $(X_{k,n})_{k\leq t_n}$ be a martingale difference array with respect to
$(\mathcal{F}_{k,n})_{k\leq t_n}$. Assume that:
(a) $\mathbb{E}\Big(\max_{k\leq t_n} X_{k,n}^2\Big)$ is uniformly bounded in $n$,
(b) $\max_{k\leq t_n} |X_{k,n}| \to 0$ in probability as $n\to\infty$,
(c) $\sum_{k=1}^{t_n} X_{k,n}^2 \to \sigma^2$ in probability as $n\to\infty$, for some
    $\sigma^2 \in (0,\infty)$.
Then, $\sum_{k=1}^{t_n} X_{k,n} \to \mathcal{N}(0,\sigma^2)$ in distribution as $n\to\infty$.

The statement uses Mathlib's `Martingale`, `TendstoInMeasure`, `TendstoInDistribution` and
`gaussianReal`. Row `n` of the array is `k ↦ 𝒳 n k` for `k < t n` (the paper's
`k = 1, …, t_n`, shifted by one); "martingale difference array with respect to
`(ℱ_{k,n})`" is the statement that the partial sums `k ↦ ∑_{j<k} 𝒳 n j` form a martingale
for the filtration `ℱ n`. Clause (a) asks that `max_k X_{k,n}²` be integrable as well as
bounded in mean, since a Bochner integral of a non-integrable function is `0`.
-/
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

namespace IdlaCyl.External

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

-- FROZEN-STATEMENT-BEGIN
/-- `thm:martingale-CLT` (`tex:882-892`; McLeish 1974, Theorem 2.3): a martingale
difference array whose maximal squared increment is integrable and bounded in mean
uniformly in the row, whose maximal increment tends to `0` in probability, and whose
sum of squares tends to `σ² ∈ (0, ∞)` in probability, has row sums converging in
distribution to `N(0, σ²)`. -/
def martingale_clt_v2 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : ℕ → Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (𝒳 : ℕ → ℕ → Ω → ℝ) (t : ℕ → ℕ) (ht : ∀ n, 0 < t n) (σsq : ℝ≥0),
    0 < σsq →
    (∀ n, Martingale (fun k ω => ∑ j ∈ Finset.range k, 𝒳 n j ω) (ℱ n) P) →
    (∀ n, Integrable (fun ω => (Finset.range (t n)).sup'
        (Finset.nonempty_range_iff.mpr (ht n).ne') (fun k => 𝒳 n k ω ^ 2)) P) →
    (∃ C : ℝ, ∀ n, ∫ ω, (Finset.range (t n)).sup'
        (Finset.nonempty_range_iff.mpr (ht n).ne') (fun k => 𝒳 n k ω ^ 2) ∂P ≤ C) →
    TendstoInMeasure P
      (fun n ω => (Finset.range (t n)).sup'
        (Finset.nonempty_range_iff.mpr (ht n).ne') (fun k => |𝒳 n k ω|))
      atTop (fun _ => 0) →
    TendstoInMeasure P
      (fun n ω => ∑ k ∈ Finset.range (t n), 𝒳 n k ω ^ 2) atTop (fun _ => (σsq : ℝ)) →
    TendstoInDistribution
      (fun n ω => ∑ k ∈ Finset.range (t n), 𝒳 n k ω) atTop (id : ℝ → ℝ)
      (fun _ => P) (gaussianReal 0 σsq)
-- FROZEN-STATEMENT-END

end IdlaCyl.External
