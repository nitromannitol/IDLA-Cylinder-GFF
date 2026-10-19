/-
Theorem `thm:martingale-CLT` from *Gaussian fluctuations for Internal DLA on cylinders*
(Bou-Rabee, Silvestri, Yadin), from `paper/idla-cylinder-gff.tex`, lines 883-892
(the statement is cited verbatim below):

Let $(X_{k,n})_{k\leq t_n}$ be a martingale difference array with respect to
$(\mathcal{F}_{k,n})_{k\leq t_n}$. Assume that:
(a) $\mathbb{E}\Big(\max_{k\leq t_n} X_{k,n}^2\Big)$ is uniformly bounded in $n$,
(b) $\max_{k\leq t_n} |X_{k,n}| \to 0$ in probability as $n\to\infty$,
(c) $\sum_{k=1}^{t_n} X_{k,n}^2 \to \sigma^2$ in probability as $n\to\infty$, for some
    $\sigma^2 \in (0,\infty)$.
Then, $\sum_{k=1}^{t_n} X_{k,n} \to \mathcal{N}(0,\sigma^2)$ in distribution as $n\to\infty$.
-/

-- NEEDS: The project API does not contain the following notions, which the cited
-- result requires. They are therefore taken as explicit hypothesis parameters of the
-- statement rather than being defined here:
--   * `IsMartingaleDiffArray`, the property that `(X n k)` is a martingale difference
--     array with respect to the filtration `(𝓕 n k)`;
--   * `TendstoInProbability`, convergence in probability of a sequence of real-valued
--     random variables;
--   * `TendstoInDistribution`, convergence in distribution of a sequence of real-valued
--     random variables to a probability measure on `ℝ`;
--   * `Normal`, the centred normal law, `Normal v` being `N(0, v)`.
-- The paper's array indices `k = 1, …, t_n` are represented by `Fin (t n)`
-- (a harmless reindexing of the sum), and the assumed non-emptiness of the index set is
-- recorded as the hypothesis `ht : ∀ n, 0 < t n` so that the `max` over `k ≤ t_n` is a
-- genuine maximum (`Finset.sup'`) and not a junk value.

import IdlaCyl.Support.Base
import IdlaCyl.Support.Cylinder
import IdlaCyl.Support.Idla
import IdlaCyl.Support.Obligations
import IdlaCyl.Support.Spectral

open MeasureTheory

namespace IdlaCyl.External

-- FROZEN-STATEMENT-BEGIN
def thm_martingale_clt
    (IsMartingaleDiffArray : {Ω : Type} → [MeasurableSpace Ω] → Measure Ω →
      (t : ℕ → ℕ) → ((n : ℕ) → Fin (t n) → Ω → ℝ) →
      ((n : ℕ) → Fin (t n) → MeasurableSpace Ω) → Prop)
    (TendstoInProbability : {Ω : Type} → [MeasurableSpace Ω] → Measure Ω →
      (ℕ → Ω → ℝ) → ℝ → Prop)
    (TendstoInDistribution : {Ω : Type} → [MeasurableSpace Ω] → Measure Ω →
      (ℕ → Ω → ℝ) → Measure ℝ → Prop)
    (Normal : ℝ → Measure ℝ) :
    Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : ℕ → ℕ) (ht : ∀ n, 0 < t n)
    (X : (n : ℕ) → Fin (t n) → Ω → ℝ)
    (𝓕 : (n : ℕ) → Fin (t n) → MeasurableSpace Ω)
    (v : ℝ) (_hv : 0 < v),
    IsMartingaleDiffArray μ t X 𝓕 →
    -- (a) E[max_{k ≤ t_n} X_{k,n}^2] is uniformly bounded in n
    (∃ C : ℝ, ∀ n,
      ∫ ω, (Finset.univ : Finset (Fin (t n))).sup'
            (⟨⟨0, ht n⟩, Finset.mem_univ _⟩)
            (fun k => (X n k ω) ^ 2) ∂μ ≤ C) →
    -- (b) max_{k ≤ t_n} |X_{k,n}| → 0 in probability
    TendstoInProbability μ
      (fun n ω => (Finset.univ : Finset (Fin (t n))).sup'
            (⟨⟨0, ht n⟩, Finset.mem_univ _⟩)
            (fun k => |X n k ω|)) 0 →
    -- (c) ∑_{k} X_{k,n}^2 → σ² = v in probability, for some v ∈ (0, ∞)
    TendstoInProbability μ
      (fun n ω => ∑ k : Fin (t n), (X n k ω) ^ 2) v →
    -- conclusion: ∑_{k} X_{k,n} → N(0, σ²) = N(0, v) in distribution
    TendstoInDistribution μ
      (fun n ω => ∑ k : Fin (t n), X n k ω) (Normal v)
-- FROZEN-STATEMENT-END

end IdlaCyl.External
