/-
Source: paper/idla-cylinder-gff.tex, tex:268-280 (th:max_fluct), proved outright. The printed proof uses pr:reduction
(tex:1445-1453), whose printed proof has a gap; this theorem is proved through a weaker variant of the reduction with a constant
coefficient, which suffices (ledger/ERRATA.md E18), and Silvestri's Proposition 2, which is proved
(`IdlaCyl/External/Discharge/Silvestri.lean`).
-/
import IdlaCyl.Frozen.MaxFluctV2
import IdlaCyl.External.Discharge.Silvestri

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
`1 ≤ T ≤ N^m` has `R_{⌊T/N - Δ_N⌋} ⊆ A(T) ⊆ R_{T/N + Δ_N}` except with probability at most `N^{-ν}`. This is `max_fluct_v2` without its
hypothesis: Silvestri's Proposition 2 is proved (`External.silvestri_prop2_proved`). The proof does not use the printed proof of
`pr:reduction`; it goes through the weaker variant with a constant coefficient (`ledger/ERRATA.md`, E18). -/
-- FROZEN-STATEMENT-BEGIN
theorem max_fluct_v3 (ν : ℝ) (hν : 0 < ν) (m : ℝ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : BaseSeq, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ T : ℕ,
      1 ≤ T → (T : ℝ) ≤ (N : ℝ) ^ m →
      idlaMeasure (V.B N) ((eventAt (V.B N) T (delta (V.B N) C T))ᶜ) ≤
        ENNReal.ofReal ((N : ℝ) ^ (-ν))
-- FROZEN-STATEMENT-END
    :=
  max_fluct_v2 External.silvestri_prop2_proved ν hν m hm

end IdlaCyl.Frozen
