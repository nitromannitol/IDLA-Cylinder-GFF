/-
  Proposition `pr:hextension` from the paper *Gaussian fluctuations for Internal DLA on
  cylinders* (Bou-Rabee, Silvestri, Yadin).

  For $2 \leq k \leq N$, let $q_k > 0$ be the positive real number defined by
  \begin{equation}\label{def:qk}
   \cosh(q_k) = 2 - \l_k\,.
  \end{equation}
  (By irreducibility and laziness, $\l_k \in [0, 1)$ for $k \geq 2$, so $2 - \l_k \in (1, 2]$
  and $q_k > 0$.) Then, for every $h \in \bbZ$ and every sequence $(\a_k(h))_{2 \leq k \leq N}$
  of real numbers, the function
  \[ \psi(x, y) = \sum_{k=2}^N \a_k(h)\, f_k^N(x)\, e^{q_k(y - h)} \]
  is discrete harmonic on $\bbG_N$, decays exponentially as $y \to -\infty$, and satisfies
  $\psi(x, h) = \sum_{k=2}^N \a_k(h)\,f_k^N(x)$ on the line $\{(x, h) : x \in V_N\}$.

  tex:716-723
-/

import IdlaCyl.Support.Base
import IdlaCyl.Support.Cylinder
import IdlaCyl.Support.Spectral
import IdlaCyl.Support.HarmonicExtension
import IdlaCyl.Support.HarmonicIntegral

namespace IdlaCyl.Frozen

open IdlaCyl

-- FROZEN-STATEMENT-BEGIN
theorem pr_hextension (B : Base) (S : SpectralData B) (h : ℤ) (α : ℕ → ℝ) :
    let qk : ℕ → ℝ := fun k => Real.arcosh (2 - S.lam k);
    let ψ : Site B → ℝ := fun p =>
      Finset.sum (Finset.Icc 2 B.card)
        (fun k => α k * S.f k (Site.hor p) *
          Real.exp (qk k * ((Site.ver p : ℝ) - (h : ℝ))));
    (∀ p : Site B, ψ p = finsum (fun q : Site B => cylKernel B p q * ψ q)) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ p : Site B, Site.ver p ≤ h →
      |ψ p| ≤ C * Real.exp (c * ((Site.ver p : ℝ) - (h : ℝ)))) ∧
    (∀ x : B.V, ψ (x, h) = Finset.sum (Finset.Icc 2 B.card) (fun k => α k * S.f k x))
-- FROZEN-STATEMENT-END
:= by
  dsimp only
  have hψpt : ∀ p : Site B,
      (∑ k ∈ Finset.Icc 2 B.card, α k * S.f k (Site.hor p) *
        Real.exp (Real.arcosh (2 - S.lam k) * ((Site.ver p : ℝ) - (h : ℝ))))
        = psiExt B S h α p := by
    intro p
    simp only [psiExt, exponentialMode, Site.hor, Site.ver, SpectralData.qk]
    apply Finset.sum_congr rfl
    intro x _
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro p
    rw [hψpt p]
    have hR : finsum (fun q : Site B => cylKernel B p q *
          (∑ k ∈ Finset.Icc 2 B.card, α k * S.f k (Site.hor q) *
            Real.exp (Real.arcosh (2 - S.lam k) * ((Site.ver q : ℝ) - (h : ℝ)))))
        = finsum (fun q : Site B => cylKernel B p q * psiExt B S h α q) := by
      apply finsum_congr
      intro q
      rw [hψpt q]
    rw [hR]
    have hdh := psiExt_discreteHarmonic B S h α p
    have htsum := tsum_cylKernel_mul B p (psiExt B S h α)
    have hsupp : ∀ q ∉ (Finset.univ ×ˢ ({p.2 - 1, p.2, p.2 + 1} : Finset ℤ) :
        Finset (Site B)), cylKernel B p q * psiExt B S h α q = 0 := by
      intro q hq
      have hk0 : cylKernel B p q = 0 := by
        simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, not_or] at hq
        obtain ⟨hq1, hq2, hq3⟩ := hq
        unfold cylKernel
        split_ifs with h1 h2
        · exfalso
          obtain ⟨-, h1'⟩ := h1
          rcases Int.natAbs_eq (p.2 - q.2) with hd | hd <;> rw [h1'] at hd <;> omega
        · exact absurd h2.symm hq2
        · rfl
      rw [hk0, zero_mul]
    rw [finsum_eq_sum_of_support_subset _ (fun q hq => by
      by_contra hqS
      exact hq (hsupp q hqS))]
    rw [← tsum_eq_sum (L := SummationFilter.unconditional (Site B)) hsupp, htsum, hdh]
  · obtain ⟨C, hC, c, hc, hbound⟩ := psiExt_expDecay B S h α
    refine ⟨C, hC, c, hc, fun p hp => ?_⟩
    rw [hψpt p]
    exact hbound p (by simpa [Site.ver] using hp)
  · intro x
    rw [hψpt (x, h)]
    exact psiExt_boundary B S h α x

end IdlaCyl.Frozen
