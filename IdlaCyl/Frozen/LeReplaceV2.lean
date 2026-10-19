import IdlaCyl.Support.Replace.ProbabilityBound
import IdlaCyl.Support.Replace.BetaEstimate

/-!
Lemma `le:replace` (`tex:784-789`):

> Fix $y_0 > 0$ and $\n > 0$, and assume $a_N \gg \log N + \log_+ a_N$ as $N \to \infty$ and that Assumption~\ref{a:spectral} holds for each $2 \leq k \leq K$. Let $T \coloneqq N \lfloor a_N y_0\rfloor$, $h \coloneqq T/N$, and let $(\Delta_N)_{N \geq 1}$ be positive reals satisfying $\Delta_N = O\!\left(\sqrt{a_N(\log N + \log_+ a_N)}\right)$ and
> 	\[ \bbP\big(R_{\lfloor h - \Delta_N\rfloor} \subseteq A(T) \subseteq R_{h + \Delta_N}\big) \geq 1 - N^{-\n} \qquad \text{for } N \text{ large enough}\,. \]
> Let $\phi : V_N \times \bbR \to \bbR$ be a test function of the form $\phi(x, y) = \sum_{k=2}^K \a_k(y)\, f_k^N(x)$, where each $\a_k : \bbR \to \bbR$ is independent of $N$ and has bounded derivative in a neighbourhood of $y_0$; let $\varphi(x, y) \coloneqq \phi(x, y/a_N)$, and let $\psi$ be the discrete harmonic extension of $\varphi$ defined in~\eqref{eq:truepsi}. Then
> 	\[ \frac{1}{\sqrt{Na_N}}\,\laa D_T, \varphi - \psi\raa \;\longrightarrow\; 0 \qquad \text{in probability as } N \to \infty\,. \]

Lean reads the conclusion as convergence to zero of the canonical probability
of each positive absolute-error threshold event.
-/

namespace IdlaCyl.Frozen

open IdlaCyl IdlaCyl.Defs IdlaCyl.Replace
open MeasureTheory Filter ProbabilityTheory
open scoped BigOperators Topology ENNReal

-- FROZEN-STATEMENT-BEGIN
theorem le_replace_v2 (U : Setup) (y₀ ν : ℝ)
    (hy₀ : 0 < y₀) (hν : 0 < ν) (K : ℕ) (hK : 2 ≤ K)
    (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K)
    (hgrowth : U.GrowthCondition) (d : ℕ → ℝ) (hd : ∀ N, 0 < d N)
    (horder : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in Filter.atTop,
      d N ≤ C * Real.sqrt (U.a N * (Real.log (N : ℝ) + logPlus (U.a N))))
    (hshape : ∀ᶠ N in Filter.atTop,
      idlaMeasure (U.B N) ((eventAt (U.B N) (time U y₀ N) (d N))ᶜ) ≤
        ENNReal.ofReal ((N : ℝ) ^ (-ν))) :
    ∀ ε : ℝ, 0 < ε → Filter.Tendsto (fun N =>
      (idlaMeasure (U.B N) {ω : TrajSeq (U.B N) |
        ε ≤ |(Real.sqrt ((N : ℝ) * U.a N))⁻¹ *
          pairingTraj (U.B N) ω (time U y₀ N)
            (fun p => testAt (U.B N) (U.S N) (U.a N) K α p - psi U K α y₀ N p)|}).toReal)
      Filter.atTop (nhds 0)
-- FROZEN-STATEMENT-END
:= by
  intro ε hε
  have hwidth := width_ratio_tendsto_zero U hgrowth d hd horder
  obtain ⟨C, hC, hlayer⟩ :=
    eventually_error_layerMeanSquare_le U y₀ hy₀ K α hα γ hspec d hd hwidth
  have hfloor := eventually_slab_lower_nonneg U y₀ hy₀ d hwidth
  have hheight := height_ratio_tendsto U y₀ hy₀.le
  have hbad : Tendsto (fun N : ℕ => (N : ℝ) ^ (-ν)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hν).comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (-ν) +
      (2 * C / ε ^ 2) * ((height U y₀ N : ℝ) / U.a N) * (d N / U.a N) ^ 2)
      atTop (nhds 0) := by
    simpa only [zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero] using
      hbad.add (((tendsto_const_nhds (x := 2 * C / ε ^ 2)).mul hheight).mul (hwidth.pow 2))
  refine squeeze_zero' (.of_forall fun _ => ENNReal.toReal_nonneg) ?_ hlim
  filter_upwards [hlayer, hfloor, hshape, eventually_ge_atTop K] with N hMN hLN hshapeN hlarge
  have hN : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hcard : (U.B N).card = N := U.card_eq N (by omega)
  let f : Site (U.B N) → ℝ := fun p =>
    testAt (U.B N) (U.S N) (U.a N) K α p - psi U K α y₀ N p
  have hzero : ZeroHorizontalAverage (U.B N) f := by
    exact error_zeroHorizontalAverage (U.B N) (U.S N) (U.a N)
      (height U y₀ N : ℤ) K α (by omega)
  have hM : 0 ≤ C * (d N / U.a N) ^ 2 := mul_nonneg hC (sq_nonneg _)
  have hp := pairing_tail_le (U.B N) (time U y₀ N) (d N) hLN f hzero
    (C * (d N / U.a N) ^ 2) hM hMN
    (Real.sqrt ((N : ℝ) * U.a N))⁻¹ ε hε
  have hb : (idlaMeasure (U.B N)).real (eventAt (U.B N) (time U y₀ N) (d N))ᶜ ≤
      (N : ℝ) ^ (-ν) := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hshapeN
    change ((idlaMeasure (U.B N)) (eventAt (U.B N) (time U y₀ N) (d N))ᶜ).toReal ≤ _
    simpa only [ENNReal.toReal_ofReal (Real.rpow_nonneg (Nat.cast_nonneg N) (-ν))] using ht
  have heq : (Real.sqrt ((N : ℝ) * U.a N))⁻¹ ^ 2 *
      (2 * (time U y₀ N : ℝ) * (C * (d N / U.a N) ^ 2)) / ε ^ 2 =
      (2 * C / ε ^ 2) * ((height U y₀ N : ℝ) / U.a N) * (d N / U.a N) ^ 2 := by
    rw [inv_pow, Real.sq_sqrt (mul_pos hN (U.a_pos N)).le]
    simp only [time, Nat.cast_mul, hcard]
    field_simp [hN.ne', (U.a_pos N).ne', hε.ne']
  change (idlaMeasure (U.B N)).real {ω | ε ≤ |(Real.sqrt ((N : ℝ) * U.a N))⁻¹ * pairingTraj (U.B N) ω (time U y₀ N) f|} ≤ _
  exact hp.trans (by rw [heq]; exact add_le_add hb le_rfl)

end IdlaCyl.Frozen
