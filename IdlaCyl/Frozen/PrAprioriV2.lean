module

public import IdlaCyl.Support.AprioriEarlyBound
public import IdlaCyl.Support.AprioriFinal

@[expose] public section

/-!
# `pr:apriori`: both clauses as one canonical declaration

Proposition `pr:apriori` of *Gaussian fluctuations for Internal DLA on cylinders*
(Bou-Rabee, Silvestri, Yadin), `tex:559-567`, quoted verbatim:

> Let $(A(t))_{t \geq 0}$ be an IDLA process on $V_N \times \bbZ$ starting from
> $A(0) = R_0$.
> \begin{itemize}
> \item[(a)] Fix $C \in (0, \infty)$ and $\b > \max(1, e^2 C)$. Then, for every
>   integer $T \leq C N \log N$ and every $N$ large enough (depending on $C$ and
>   $\b$),
>   \[ \bbP \big( A(T) \nsubseteq R_{\b \log N} \big) \leq N^{-(\b - 1)}\,. \]
> \item[(b)] Fix $\b > e^2$. Then there exists $K_0 = K_0(\b) < \infty$ such that,
>   for every integer $T \geq K_0\, N\log N$ and every $N$ large enough,
>   \[ \bbP \big( A(T) \nsubseteq R_{\b T/N} \big) \leq \exp\!\Big( -\b\, \frac{T}{N}\Big)\,. \]
> \end{itemize}

The Lean statement reads `N` as `B.card` for an arbitrary base graph `B : Base`, takes the
probability under `idlaMeasure B` with the cluster `clusterTraj B ω T` (the IDLA process
from the flat configuration `R B 0`), and places the thresholds `N₀` and `K₀` before the
base graph and the time, so that each clause is the printed one.
-/

namespace IdlaCyl.Frozen

-- FROZEN-STATEMENT-BEGIN
theorem pr_apriori_canonical_v2 :
    (∀ C : ℝ, 0 < C → ∀ β : ℝ, max (1 : ℝ) (Real.exp 2 * C) < β →
      ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card → ∀ T : ℕ,
        (T : ℝ) ≤ C * (B.card : ℝ) * Real.log (B.card : ℝ) →
        idlaMeasure B {ω : TrajSeq B |
          ¬ (clusterTraj B ω T ⊆ R B (β * Real.log (B.card : ℝ)))} ≤
            ENNReal.ofReal ((B.card : ℝ) ^ (-(β - 1)))) ∧
    (∀ β : ℝ, Real.exp 2 < β → ∃ K₀ : ℝ, ∃ N₀ : ℕ,
      ∀ B : Base, N₀ ≤ B.card → ∀ T : ℕ,
        K₀ * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (T : ℝ) →
        idlaMeasure B {ω : TrajSeq B |
          ¬ (clusterTraj B ω T ⊆ R B (β * (T : ℝ) / (B.card : ℝ)))} ≤
            ENNReal.ofReal (Real.exp (-(β * (T : ℝ) / (B.card : ℝ)))))
-- FROZEN-STATEMENT-END
  := by
    refine ⟨pr_apriori_part_a, fun β hβ => ?_⟩
    obtain ⟨K₀, _, N₀, h⟩ := pr_apriori_part_b β hβ
    exact ⟨K₀, N₀, h⟩

-- Nonvacuity: clause (a) at `C = 1`, `β = 10` and clause (b) at `β = 10` both apply,
-- and each yields its cutoff (`N₀` in (a); `K₀` and `N₀` in (b)).
example :
    (∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card → ∀ T : ℕ,
      (T : ℝ) ≤ 1 * (B.card : ℝ) * Real.log (B.card : ℝ) →
      idlaMeasure B {ω : TrajSeq B |
        ¬ (clusterTraj B ω T ⊆ R B (10 * Real.log (B.card : ℝ)))} ≤
          ENNReal.ofReal ((B.card : ℝ) ^ (-((10 : ℝ) - 1)))) ∧
    (∃ K₀ : ℝ, ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card → ∀ T : ℕ,
      K₀ * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (T : ℝ) →
      idlaMeasure B {ω : TrajSeq B |
        ¬ (clusterTraj B ω T ⊆ R B (10 * (T : ℝ) / (B.card : ℝ)))} ≤
          ENNReal.ofReal (Real.exp (-(10 * (T : ℝ) / (B.card : ℝ))))) := by
  have hexp : Real.exp 2 < 10 := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    rw [h2]; nlinarith [Real.exp_pos 1]
  exact ⟨pr_apriori_canonical_v2.1 1 one_pos 10 (max_lt (by norm_num) (by linarith)),
    pr_apriori_canonical_v2.2 10 hexp⟩

end IdlaCyl.Frozen
