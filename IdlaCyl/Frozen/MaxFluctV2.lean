module

/-
Source: paper/idla-cylinder-gff.tex, tex:268-280 (th:max_fluct). The printed proof uses pr:reduction (tex:1445-1453), whose
printed proof has a gap; this theorem is proved through a finite-coefficient form of the reduction instead
(ledger/ERRATA.md E18).
-/
public import IdlaCyl.Support.MaxFluctOfReduction
public import IdlaCyl.Support.Reduction.Assemble

@[expose] public section

namespace IdlaCyl.Frozen

open IdlaCyl IdlaCyl.Defs MeasureTheory

/-- `th:max_fluct` (`tex:271-280`):

> \begin{Theorem}\label{th:max_fluct}
> Let $(A(t))_{t\geq 0}$ denote an IDLA process on the cylinder $\bbG_N$ starting from $A(0) = R_0$. For every $\n > 0$ and every $m \geq 1$ there exists a constant $C = C(\n, m) < \infty$ such that, with
> 	\[ T^\sharp \coloneqq N \sqrt{\t_{mix}} \,(\log N)^2\,, \qquad \Delta_N \coloneqq C \max\!\left\{\, \log N,\; \sqrt{\frac{T \wedge T^\sharp}{N}\,\Big( \log N + \log_+\!\big( T/N \big) \Big)} \,\right\}\,, \]
> we have
> 	\begin{equation}\label{eq:fluct}
> 	\bbP \Big( R_{\lfloor T/N - \Delta_N \rfloor}
> 	\subseteq A(T) \subseteq R_{T/N +  \Delta_N } \Big) \geq 1-N^{-\n}
> 	\end{equation}
> uniformly over integer $T$ with $1 \leq T \leq N^m$, for every $N$ large enough. 
> \end{Theorem}

For every `ν > 0` and real `m ≥ 1` there is `C = C(ν, m) > 0` such that for every base sequence and all large `N`, every integer
`1 ≤ T ≤ N^m` has `R_{⌊T/N - Δ_N⌋} ⊆ A(T) ⊆ R_{T/N + Δ_N}` except with probability at most `N^{-ν}`. The theorem is conditional on
the cited Silvestri Proposition 2 (`External.silvestri_prop2`) and does not use the printed proof of `pr:reduction`. -/
-- FROZEN-STATEMENT-BEGIN
theorem max_fluct_v2 (hsil : IdlaCyl.External.silvestri_prop2)
    (ν : ℝ) (hν : 0 < ν) (m : ℝ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : BaseSeq, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ T : ℕ,
      1 ≤ T → (T : ℝ) ≤ (N : ℝ) ^ m →
      idlaMeasure (V.B N) ((eventAt (V.B N) T (delta (V.B N) C T))ᶜ) ≤
        ENNReal.ofReal ((N : ℝ) ^ (-ν))
-- FROZEN-STATEMENT-END
    := by
  obtain ⟨C, hC, N₀, h⟩ :=
    max_fluct_of_reduction (Reduction.pr_reduction_alpha_of_silvestri hsil) ν hν m hm
  refine ⟨C, hC, fun V => ⟨max N₀ 2, fun N hN T hT hTm => ?_⟩⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hcard : (V.B N).card = N := V.card_eq N hN2
  have hB : N₀ ≤ (V.B N).card := by rw [hcard]; exact le_trans (le_max_left _ _) hN
  have hTm' : (T : ℝ) ≤ ((V.B N).card : ℝ) ^ m := by rw [hcard]; exact hTm
  have hres := h (V.B N) hB T hT hTm'
  rwa [hcard] at hres

end IdlaCyl.Frozen
