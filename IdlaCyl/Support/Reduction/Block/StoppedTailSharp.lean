/-
The sharp lower tail of the stopped score and the block filling it gives with `e^{-H/4}`.
Source: paper/idla-cylinder-gff.tex, tex:1194-1251 (the lower tail of the stopped score and the
block filling of the stopped cluster).
-/
import IdlaCyl.Support.PrInnerStopped.BoundaryMeasure
import IdlaCyl.Support.PrInnerStopped.Martingale

/-!
# The sharp lower tail of the stopped score

The stopped score `M_ζ(T) = Σ_{s<T} (H_ζ(stopped settle site s) - 1/N)` has increments
`Y_s - 1/N` with `Y_s ∈ [0, 1]` and conditional mean zero. Convexity of the exponential gives the
conditional Laplace bound `E[exp(-a (Y_s - 1/N)) | 𝓕_s] ≤ exp(a² / (2N))` for `a ≥ 0`. Iterating
it and applying Markov's inequality to `exp(-a M_ζ(T))` with `a = u N / T` gives the tail
`P(M_ζ(T) ≤ -u) ≤ exp(-u² N / (2T))` for every `u ≥ 0`, which is sharper than the variance bound
`exp(-u² N / (4T))` of `LowerTail.lean` for all `u ≥ 0`.

On top of this tail, the block filling of `R_H` by `2 N H` stopped particles fails with probability
at most `N H e^{-H/4}`, with the same union bound over the sites of the block as `BlockFill.lean`.
-/

namespace IdlaCyl.Reduction

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

variable (B : Base)

/-- Convexity of the exponential on `[0, 1]`: `e^{-a y} ≤ 1 + (e^{-a} - 1) y`. -/
theorem exp_neg_mul_le_affine (a y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.exp (-a * y) ≤ 1 + (Real.exp (-a) - 1) * y := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-a)) (sub_nonneg.2 hy1) hy0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  have e : (Real.exp (-a) - 1) * y = y * Real.exp (-a) - y := by ring
  rw [show -a * y = y * (-a) by ring, e]
  linarith

/-- The quadratic bound `e^{-a} ≤ 1 - a + a²/2` for `a ≥ 0`. -/
theorem exp_neg_le_quad (a : ℝ) (ha : 0 ≤ a) :
    Real.exp (-a) ≤ 1 - a + a ^ 2 / 2 := by
  have hq : 1 + a + a ^ 2 / 2 ≤ Real.exp a := Real.quadratic_le_exp_of_nonneg ha
  have hprod : Real.exp (-a) * Real.exp a = 1 := by rw [← Real.exp_add]; simp
  have hqpos : 0 < 1 + a + a ^ 2 / 2 := by positivity
  have hle : Real.exp (-a) * (1 + a + a ^ 2 / 2) ≤ (1 - a + a ^ 2 / 2) * (1 + a + a ^ 2 / 2) := by
    have h1 : Real.exp (-a) * (1 + a + a ^ 2 / 2) ≤ Real.exp (-a) * Real.exp a :=
      mul_le_mul_of_nonneg_left hq (Real.exp_pos _).le
    have h2 : (1 - a + a ^ 2 / 2) * (1 + a + a ^ 2 / 2) = 1 + a ^ 4 / 4 := by ring
    have h3 : (0 : ℝ) ≤ a ^ 4 / 4 := by positivity
    linarith
  exact le_of_mul_le_mul_right hle hqpos

/-- The one-step constant: `e^{ac} (1 + (e^{-a} - 1) c) ≤ e^{a² c / 2}` for `c = 1/N ≤ 1`, `a ≥ 0`. -/
theorem exp_mul_affine_le (N : ℝ) (hN : 1 ≤ N) (a : ℝ) (ha : 0 ≤ a) :
    Real.exp (a * (1 / N)) * (1 + (Real.exp (-a) - 1) * (1 / N))
      ≤ Real.exp (a ^ 2 / (2 * N)) := by
  have hc : 0 ≤ 1 / N := by positivity
  have h1 : 1 + (Real.exp (-a) - 1) * (1 / N) ≤ Real.exp ((Real.exp (-a) - 1) * (1 / N)) := by
    linarith [Real.add_one_le_exp ((Real.exp (-a) - 1) * (1 / N))]
  have h2 := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (a * (1 / N))).le
  rw [← Real.exp_add] at h2
  refine h2.trans (Real.exp_le_exp.2 ?_)
  have h3 := mul_le_mul_of_nonneg_right (exp_neg_le_quad a ha) hc
  have hsq : a ^ 2 / (2 * N) = (a ^ 2 / 2) * (1 / N) := by ring
  rw [hsq]
  nlinarith [h3]

/-- Pointwise bound on the centred stopped hitting probability: `Y ∈ [0, 1]` and `Y ↦ e^{-a(Y-c)}`. -/
theorem exp_centered_le_affine (N : ℝ) (a y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Real.exp (-a * (y - 1 / N)) ≤ Real.exp (a * (1 / N)) * (1 + (Real.exp (-a) - 1) * y) := by
  have e1 : Real.exp (-a * (y - 1 / N)) = Real.exp (-a * y) * Real.exp (a * (1 / N)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1, mul_comm]
  exact mul_le_mul_of_nonneg_left (exp_neg_mul_le_affine a y hy0 hy1) (Real.exp_pos _).le

/-- The centred stopped hitting probability is in `[-1, 1]`. -/
theorem abs_hitProb_sub_le_one (N : ℝ) (hN : 1 ≤ N) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |x - 1 / N| ≤ 1 := by
  have hc0 : 0 ≤ 1 / N := by positivity
  have hc1 : 1 / N ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  rw [abs_le]
  constructor <;> linarith

/-- **Conditional Laplace bound**: for `a ≥ 0`, the conditional expectation
given the stopped settle-site filtration of `exp(-a (H_ζ - 1/N))` is at most `exp(a²/(2N))`. -/
theorem condExp_exp_centered_le (h : ℤ) (hh : 1 ≤ h) (ζ : Site B) (hζ : ζ.2 = h)
    (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    (idlaMeasure B)[fun ω : TrajSeq B =>
        Real.exp (-a * (hitProb B ζ (stoppedSettleSite B h ω k) - 1 / (B.card : ℝ)))
        | stoppedFiltration B h k]
      ≤ᵐ[idlaMeasure B] fun _ => Real.exp (a ^ 2 / (2 * (B.card : ℝ))) := by
  have h2N : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
  have hN1 : (1 : ℝ) ≤ (B.card : ℝ) := by linarith
  have hYint := integrable_hitProb_stoppedSettleSite B h ζ k
  have hYm : Measurable (fun ω : TrajSeq B => hitProb B ζ (stoppedSettleSite B h ω k)) :=
    (measurable_of_countable (hitProb B ζ)).comp (measurable_stoppedSettleSite B h k)
  have hgm : Measurable (fun ω : TrajSeq B =>
      Real.exp (-a * (hitProb B ζ (stoppedSettleSite B h ω k) - 1 / (B.card : ℝ)))) :=
    Real.continuous_exp.measurable.comp ((hYm.sub_const _).const_mul _)
  have hgb : ∀ ω : TrajSeq B,
      Real.exp (-a * (hitProb B ζ (stoppedSettleSite B h ω k) - 1 / (B.card : ℝ))) ≤ Real.exp a := by
    intro ω
    apply Real.exp_le_exp.2
    have hc1 : 1 / (B.card : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith [mul_nonneg ha (hitProb_nonneg B ζ (stoppedSettleSite B h ω k)),
      mul_le_of_le_one_right ha hc1]
  have hgint : Integrable (fun ω : TrajSeq B =>
      Real.exp (-a * (hitProb B ζ (stoppedSettleSite B h ω k) - 1 / (B.card : ℝ)))) (idlaMeasure B) :=
    Integrable.of_bound hgm.aestronglyMeasurable (Real.exp a) (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact hgb ω)
  have hL_int : Integrable ((fun _ : TrajSeq B => Real.exp (a * (1 / (B.card : ℝ))))
      + (fun ω : TrajSeq B => Real.exp (a * (1 / (B.card : ℝ))) * (Real.exp (-a) - 1)
        * hitProb B ζ (stoppedSettleSite B h ω k))) (idlaMeasure B) :=
    (integrable_const _).add (hYint.const_mul _)
  have hpt : ∀ ω : TrajSeq B,
      Real.exp (-a * (hitProb B ζ (stoppedSettleSite B h ω k) - 1 / (B.card : ℝ)))
        ≤ ((fun _ : TrajSeq B => Real.exp (a * (1 / (B.card : ℝ))))
          + (fun ω : TrajSeq B => Real.exp (a * (1 / (B.card : ℝ))) * (Real.exp (-a) - 1)
            * hitProb B ζ (stoppedSettleSite B h ω k))) ω := by
    intro ω
    have := exp_centered_le_affine (B.card : ℝ) a (hitProb B ζ (stoppedSettleSite B h ω k))
      (hitProb_nonneg B ζ _) (hitProb_le_one B ζ _)
    simp only [Pi.add_apply]
    linarith [this, show Real.exp (a * (1 / (B.card : ℝ))) * (1 + (Real.exp (-a) - 1)
        * hitProb B ζ (stoppedSettleSite B h ω k))
        = Real.exp (a * (1 / (B.card : ℝ))) + Real.exp (a * (1 / (B.card : ℝ))) * (Real.exp (-a) - 1)
          * hitProb B ζ (stoppedSettleSite B h ω k) by ring]
  have hcm := condExp_mono (m := stoppedFiltration B h k) hgint hL_int (Filter.Eventually.of_forall hpt)
  have hA := condExp_add (m := stoppedFiltration B h k) (integrable_const
    (Real.exp (a * (1 / (B.card : ℝ))))) (hYint.const_mul (Real.exp (a * (1 / (B.card : ℝ))) * (Real.exp (-a) - 1)))
  have hB : (idlaMeasure B)[fun ω : TrajSeq B => Real.exp (a * (1 / (B.card : ℝ))) * (Real.exp (-a) - 1)
        * hitProb B ζ (stoppedSettleSite B h ω k) | stoppedFiltration B h k]
      =ᵐ[idlaMeasure B] fun ω : TrajSeq B => Real.exp (a * (1 / (B.card : ℝ))) * (Real.exp (-a) - 1)
        * (idlaMeasure B)[fun ω' : TrajSeq B => hitProb B ζ (stoppedSettleSite B h ω' k)
          | stoppedFiltration B h k] ω :=
    condExp_smul (Real.exp (a * (1 / (B.card : ℝ))) * (Real.exp (-a) - 1))
      (fun ω : TrajSeq B => hitProb B ζ (stoppedSettleSite B h ω k)) (stoppedFiltration B h k)
  have hD : (idlaMeasure B)[fun _ : TrajSeq B => Real.exp (a * (1 / (B.card : ℝ)))
      | stoppedFiltration B h k] = fun _ => Real.exp (a * (1 / (B.card : ℝ))) :=
    condExp_const ((stoppedFiltration B h).le k) _
  have hC := condExp_hitProb_stoppedSettleSite B h hh ζ hζ k
  have hlin : (idlaMeasure B)[(fun _ : TrajSeq B => Real.exp (a * (1 / (B.card : ℝ))))
      + (fun ω : TrajSeq B => Real.exp (a * (1 / (B.card : ℝ))) * (Real.exp (-a) - 1)
        * hitProb B ζ (stoppedSettleSite B h ω k)) | stoppedFiltration B h k]
      =ᵐ[idlaMeasure B] fun _ => Real.exp (a * (1 / (B.card : ℝ)))
        + Real.exp (a * (1 / (B.card : ℝ))) * (Real.exp (-a) - 1) * (1 / (B.card : ℝ)) := by
    filter_upwards [hA, hB, hC] with ω h1 h2 h3
    simp only [h1, h2, h3, hD, Pi.add_apply]
  filter_upwards [hcm, hlin] with ω h1 h2
  calc (idlaMeasure B)[fun ω : TrajSeq B =>
          Real.exp (-a * (hitProb B ζ (stoppedSettleSite B h ω k) - 1 / (B.card : ℝ)))
          | stoppedFiltration B h k] ω
      ≤ (idlaMeasure B)[((fun _ : TrajSeq B => Real.exp (a * (1 / (B.card : ℝ))))
          + (fun ω : TrajSeq B => Real.exp (a * (1 / (B.card : ℝ))) * (Real.exp (-a) - 1)
            * hitProb B ζ (stoppedSettleSite B h ω k))) | stoppedFiltration B h k] ω := h1
    _ = Real.exp (a * (1 / (B.card : ℝ))) * (1 + (Real.exp (-a) - 1) * (1 / (B.card : ℝ))) := by
        rw [h2]; ring
    _ ≤ Real.exp (a ^ 2 / (2 * (B.card : ℝ))) :=
        exp_mul_affine_le (B.card : ℝ) hN1 a ha

/-- The stopped score is bounded by its length: `|M_ζ(t)| ≤ t`. -/
theorem abs_stoppedScore_le (h : ℤ) (ζ : Site B) (t : ℕ) (ω : TrajSeq B) :
    |stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) t ω| ≤ t := by
  have h2N : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
  have hN1 : (1 : ℝ) ≤ (B.card : ℝ) := by linarith
  simp only [stoppedScoreOf]
  calc |∑ s ∈ Finset.range t, (hitProb B ζ (stoppedSettleSite B h ω s) - 1 / (B.card : ℝ))|
      ≤ ∑ s ∈ Finset.range t, |hitProb B ζ (stoppedSettleSite B h ω s) - 1 / (B.card : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s ∈ Finset.range t, (1 : ℝ) := Finset.sum_le_sum fun s _ =>
        abs_hitProb_sub_le_one (B.card : ℝ) hN1 _ (hitProb_nonneg B ζ _) (hitProb_le_one B ζ _)
    _ = t := by simp

/-- The exponential of `-a M_ζ(t)` is at most `e^{a t}` for `a ≥ 0`. -/
theorem exp_neg_stoppedScore_le (h : ℤ) (ζ : Site B) (a : ℝ) (ha : 0 ≤ a) (t : ℕ) (ω : TrajSeq B) :
    Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) t ω)
      ≤ Real.exp (a * t) := by
  apply Real.exp_le_exp.2
  have h1 := (abs_le.1 (abs_stoppedScore_le B h ζ t ω)).1
  nlinarith [mul_nonneg ha (by linarith : (0 : ℝ) ≤
    stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) t ω + t)]

/-- The exponential of `-a M_ζ(t)` is integrable for `a ≥ 0`. -/
theorem integrable_exp_neg_stoppedScore (h : ℤ) (ζ : Site B) (a : ℝ) (ha : 0 ≤ a) (t : ℕ) :
    Integrable (fun ω : TrajSeq B =>
      Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) t ω))
      (idlaMeasure B) := by
  have hm : Measurable (fun ω : TrajSeq B =>
      stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) t ω) := by
    unfold stoppedScoreOf
    exact Finset.measurable_sum _ fun s _ =>
      ((measurable_of_countable (hitProb B ζ)).comp (measurable_stoppedSettleSite B h s)).sub
        measurable_const
  refine Integrable.of_bound
    (Real.continuous_exp.measurable.comp (hm.const_mul _)).aestronglyMeasurable (Real.exp (a * t))
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  exact exp_neg_stoppedScore_le B h ζ a ha t ω

/-- The stopped score at time `t` is measurable for the filtration at time `t`. -/
theorem measurable_stoppedScore_filtration (h : ℤ) (ζ : Site B) (t : ℕ) :
    Measurable[stoppedFiltration B h t] (fun ω : TrajSeq B =>
      stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) t ω) := by
  unfold stoppedScoreOf
  exact Finset.measurable_sum _ fun s hs =>
    ((measurable_of_countable (hitProb B ζ)).comp
      (measurable_stoppedSettleSite_filtration_of_lt B h (Finset.mem_range.mp hs))).sub
      measurable_const

/-- The centred stopped hitting probability is integrable, with exponential bounded by `e^{a}`. -/
theorem integrable_exp_centered (h : ℤ) (ζ : Site B) (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    Integrable (fun ω : TrajSeq B =>
      Real.exp (-a * (hitProb B ζ (stoppedSettleSite B h ω k) - 1 / (B.card : ℝ))))
      (idlaMeasure B) := by
  have h2N : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
  have hc1 : 1 / (B.card : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hYm : Measurable (fun ω : TrajSeq B => hitProb B ζ (stoppedSettleSite B h ω k)) :=
    (measurable_of_countable (hitProb B ζ)).comp (measurable_stoppedSettleSite B h k)
  refine Integrable.of_bound
    (Real.continuous_exp.measurable.comp ((hYm.sub_const _).const_mul _)).aestronglyMeasurable
    (Real.exp a) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.2
  nlinarith [mul_nonneg ha (hitProb_nonneg B ζ (stoppedSettleSite B h ω k)),
    mul_le_of_le_one_right ha hc1]

/-- **One step of the iteration.** `E[e^{-a M(t+1)}] ≤ e^{a²/(2N)} E[e^{-a M(t)}]` for `a ≥ 0`,
by the conditional Laplace bound and the pull-out property of the conditional expectation. -/
theorem integral_exp_neg_stoppedScore_succ_le (h : ℤ) (hh : 1 ≤ h) (ζ : Site B) (hζ : ζ.2 = h)
    (a : ℝ) (ha : 0 ≤ a) (t : ℕ) :
    ∫ ω, Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) (t + 1) ω)
        ∂(idlaMeasure B)
      ≤ Real.exp (a ^ 2 / (2 * (B.card : ℝ))) * ∫ ω,
        Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) t ω)
          ∂(idlaMeasure B) := by
  have hfac : ∀ ω : TrajSeq B,
      Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) (t + 1) ω)
        = Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) t ω)
          * Real.exp (-a * (hitProb B ζ (stoppedSettleSite B h ω t) - 1 / (B.card : ℝ))) := by
    intro ω
    rw [← Real.exp_add]
    congr 1
    simp only [stoppedScoreOf]
    rw [Finset.sum_range_succ]
    ring
  have hprod_int : Integrable (fun ω : TrajSeq B =>
      Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) t ω)
        * Real.exp (-a * (hitProb B ζ (stoppedSettleSite B h ω t) - 1 / (B.card : ℝ))))
      (idlaMeasure B) := by
    have := integrable_exp_neg_stoppedScore B h ζ a ha (t + 1)
    simpa only [hfac] using this
  have hWs : StronglyMeasurable[stoppedFiltration B h t] (fun ω : TrajSeq B =>
      Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) t ω)) :=
    (Real.continuous_exp.measurable.comp ((measurable_stoppedScore_filtration B h ζ t).const_mul _)).stronglyMeasurable
  have hW_int := integrable_exp_neg_stoppedScore B h ζ a ha t
  have hG_int := integrable_exp_centered B h ζ a ha t
  calc ∫ ω, Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) (t + 1) ω)
          ∂(idlaMeasure B)
      = ∫ ω, Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) t ω)
          * Real.exp (-a * (hitProb B ζ (stoppedSettleSite B h ω t) - 1 / (B.card : ℝ)))
          ∂(idlaMeasure B) := by simp only [hfac]
    _ = ∫ ω, (idlaMeasure B)[fun ω' : TrajSeq B =>
          Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) t ω')
          * Real.exp (-a * (hitProb B ζ (stoppedSettleSite B h ω' t) - 1 / (B.card : ℝ)))
          | stoppedFiltration B h t] ω ∂(idlaMeasure B) :=
        (integral_condExp ((stoppedFiltration B h).le t)).symm
    _ = ∫ ω, Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) t ω)
          * (idlaMeasure B)[fun ω' : TrajSeq B =>
            Real.exp (-a * (hitProb B ζ (stoppedSettleSite B h ω' t) - 1 / (B.card : ℝ)))
            | stoppedFiltration B h t] ω ∂(idlaMeasure B) := by
        refine integral_congr_ae ?_
        filter_upwards [condExp_mul_of_stronglyMeasurable_left hWs hprod_int hG_int] with ω hω
        exact hω
    _ ≤ ∫ ω, Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) t ω)
          * Real.exp (a ^ 2 / (2 * (B.card : ℝ))) ∂(idlaMeasure B) := by
        refine integral_mono_of_nonneg ?_ (hW_int.mul_const _) ?_
        · filter_upwards [condExp_nonneg (m := stoppedFiltration B h t)
            (Filter.Eventually.of_forall fun ω : TrajSeq B => (Real.exp_pos _).le)] with ω hω
          exact mul_nonneg (Real.exp_pos _).le hω
        · filter_upwards [condExp_exp_centered_le B h hh ζ hζ a ha t] with ω hω
          exact mul_le_mul_of_nonneg_left hω (Real.exp_pos _).le
    _ = Real.exp (a ^ 2 / (2 * (B.card : ℝ))) * ∫ ω,
          Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) t ω)
            ∂(idlaMeasure B) := by
        rw [integral_mul_const, mul_comm]

/-- **Iteration.** `E[e^{-a M(t)}] ≤ (e^{a²/(2N)})^t` for `a ≥ 0`. -/
theorem integral_exp_neg_stoppedScore_le (h : ℤ) (hh : 1 ≤ h) (ζ : Site B) (hζ : ζ.2 = h)
    (a : ℝ) (ha : 0 ≤ a) (t : ℕ) :
    ∫ ω, Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) t ω)
        ∂(idlaMeasure B)
      ≤ Real.exp (a ^ 2 / (2 * (B.card : ℝ))) ^ t := by
  induction t with
  | zero => simp [stoppedScoreOf]
  | succ t ih =>
    calc _ ≤ _ := integral_exp_neg_stoppedScore_succ_le B h hh ζ hζ a ha t
      _ ≤ Real.exp (a ^ 2 / (2 * (B.card : ℝ))) * Real.exp (a ^ 2 / (2 * (B.card : ℝ))) ^ t :=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
      _ = Real.exp (a ^ 2 / (2 * (B.card : ℝ))) ^ (t + 1) := (pow_succ' _ _).symm

/-- **Sharp lower tail of the stopped score**. For `1 ≤ h`, `ζ` on layer `h`,
`1 ≤ T` and every `u ≥ 0`, `P(M_ζ(T) ≤ -u) ≤ exp(-u² N / (2T))`. -/
theorem stoppedScoreOf_lower_tail_sharp (h : ℤ) (hh : 1 ≤ h) (ζ : Site B) (hζ : ζ.2 = h)
    (T : ℕ) (hT : 1 ≤ T) (u : ℝ) (hu : 0 ≤ u) :
    idlaMeasure B {ω : TrajSeq B |
        stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T ω ≤ -u}
      ≤ ENNReal.ofReal (Real.exp (-(u ^ 2 * (B.card : ℝ) / (2 * T)))) := by
  have h2N : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
  have hNpos : (0 : ℝ) < (B.card : ℝ) := by linarith
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = u * (B.card : ℝ) / T := ⟨_, rfl⟩
  have ha : 0 ≤ a := by rw [ha_def]; positivity
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := idlaMeasure B)
    (f := fun ω : TrajSeq B =>
      Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T ω))
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)
    (integrable_exp_neg_stoppedScore B h ζ a ha T) (Real.exp (a * u))
  have hsub : {ω : TrajSeq B |
        stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T ω ≤ -u}
      ⊆ {x : TrajSeq B | Real.exp (a * u)
        ≤ Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T x)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg ha (by linarith : (0 : ℝ) ≤ -u -
      stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T ω)]
  have hmeas := measureReal_mono (μ := idlaMeasure B) hsub (measure_ne_top _ _)
  have hint := integral_exp_neg_stoppedScore_le B h hh ζ hζ a ha T
  have h1 : Real.exp (a * u) * (idlaMeasure B).real {ω : TrajSeq B |
        stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T ω ≤ -u}
      ≤ Real.exp (T * (a ^ 2 / (2 * (B.card : ℝ)))) := by
    calc Real.exp (a * u) * (idlaMeasure B).real {ω : TrajSeq B |
            stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T ω ≤ -u}
        ≤ Real.exp (a * u) * (idlaMeasure B).real {x : TrajSeq B | Real.exp (a * u)
            ≤ Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T x)} :=
          mul_le_mul_of_nonneg_left hmeas (Real.exp_pos _).le
      _ ≤ ∫ ω, Real.exp (-a * stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T ω)
          ∂(idlaMeasure B) := hmk
      _ ≤ Real.exp (a ^ 2 / (2 * (B.card : ℝ))) ^ T := hint
      _ = Real.exp (T * (a ^ 2 / (2 * (B.card : ℝ)))) := (Real.exp_nat_mul _ _).symm
  have hexp : -(a * u) + T * (a ^ 2 / (2 * (B.card : ℝ)))
      = -(u ^ 2 * (B.card : ℝ) / (2 * T)) := by
    rw [ha_def]
    field_simp
    ring
  have hP : (idlaMeasure B).real {ω : TrajSeq B |
        stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T ω ≤ -u}
      ≤ Real.exp (-(u ^ 2 * (B.card : ℝ) / (2 * T))) := by
    calc (idlaMeasure B).real {ω : TrajSeq B |
            stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T ω ≤ -u}
        = Real.exp (-(a * u)) * (Real.exp (a * u) * (idlaMeasure B).real {ω : TrajSeq B |
            stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T ω ≤ -u}) := by
          rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp (-(a * u)) * Real.exp (T * (a ^ 2 / (2 * (B.card : ℝ)))) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = Real.exp (-(u ^ 2 * (B.card : ℝ) / (2 * T))) := by
          rw [← Real.exp_add, hexp]
  have hfin : idlaMeasure B {ω : TrajSeq B |
        stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T ω ≤ -u}
      = ENNReal.ofReal ((idlaMeasure B {ω : TrajSeq B |
        stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T ω ≤ -u}).toReal) :=
    (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [hfin]
  exact ENNReal.ofReal_le_ofReal hP

/-- The stopped block site bound with the sharper exponent: a site of the block `1 ≤ ζ.2 ≤ H` is
missed by the stopped cluster after `2 N H` steps with probability at most `e^{-H/4}`. -/
theorem site_not_mem_stoppedCluster_block_sharp (H : ℕ) (hH : 1 ≤ H) (ζ : Site B)
    (hζ1 : 1 ≤ ζ.2) (hζH : ζ.2 ≤ (H : ℤ)) :
    idlaMeasure B {ω : TrajSeq B | ζ ∉ stoppedCluster B (H : ℤ) ω (2 * B.card * H)}
      ≤ ENNReal.ofReal (Real.exp (-(H : ℝ) / 4)) := by
  have hN0 : 0 < B.card := lt_of_lt_of_le (by norm_num) B.nontrivial
  have hNR : (0 : ℝ) < B.card := by exact_mod_cast hN0
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hT : 1 ≤ 2 * B.card * H := Nat.mul_pos (Nat.mul_pos two_pos hN0) (by omega)
  have hTR : ((2 * B.card * H : ℕ) : ℝ) = 2 * (B.card : ℝ) * H := by push_cast; ring
  have hRHS : ((2 * B.card * H : ℕ) : ℝ) / (B.card : ℝ) = 2 * H := by
    rw [hTR]
    field_simp
  have hℓh : ((ζ.2 : ℤ) : ℝ) + (H : ℝ) ≤ ((2 * B.card * H : ℕ) : ℝ) / (B.card : ℝ) := by
    rw [hRHS]
    have hζR : ((ζ.2 : ℤ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hζH
    linarith
  have hsite := measure_not_mem_stoppedCluster_le_score B ζ.2 hζ1 ζ rfl (2 * B.card * H) (H : ℝ) hℓh
  have hscore := stoppedScoreOf_lower_tail_sharp B ζ.2 hζ1 ζ rfl (2 * B.card * H) hT (H : ℝ)
    (by positivity)
  have hH0 : (H : ℝ) ≠ 0 := hHR.ne'
  have hN0' : (B.card : ℝ) ≠ 0 := hNR.ne'
  have hexp : (H : ℝ) ^ 2 * (B.card : ℝ) / (2 * ((2 * B.card * H : ℕ) : ℝ)) = H / 4 := by
    rw [hTR]
    field_simp
    ring
  refine (measure_mono_ae ?_).trans (hsite.trans (hscore.trans (le_of_eq ?_)))
  · filter_upwards [idlaMeasure_ae_stopped_hyp B] with ω hω
    intro hnot hmem
    exact hnot (stoppedCluster_mono_height B hζH ω
      (fun t => hω.2.2.1 t (H : ℤ) (by exact_mod_cast hH)) (2 * B.card * H) hmem)
  · rw [hexp, neg_div]

/-- **Block filling with the sharper exponent**. With `2 N H`
stopped particles, the stopped cluster at height `H` contains `R_H` except on an event of
probability at most `N H e^{-H/4}`. Same union bound as `stopped_block_fill`. -/
theorem stopped_block_fill_sharp (H : ℕ) (hH : 1 ≤ H) :
    idlaMeasure B {ω : TrajSeq B | ¬ R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) ω (2 * B.card * H)}
      ≤ ENNReal.ofReal ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4)) := by
  classical
  let S : Finset (Site B) := (Finset.univ : Finset B.V) ×ˢ Finset.Icc (1 : ℤ) (H : ℤ)
  have hS : S.card = B.card * H := by
    simp [S, Finset.card_product, Int.card_Icc, IdlaCyl.Base.card]
  calc idlaMeasure B {ω : TrajSeq B | ¬ R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) ω (2 * B.card * H)}
      ≤ idlaMeasure B (⋃ ζ ∈ S,
          {ω : TrajSeq B | ζ ∉ stoppedCluster B (H : ℤ) ω (2 * B.card * H)}) := by
        refine measure_mono fun ω hω => ?_
        have hω' : ¬ R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) ω (2 * B.card * H) := hω
        obtain ⟨p, hpR, hpA⟩ := Set.not_subset.mp hω'
        have hpH : p.2 ≤ (H : ℤ) := by exact_mod_cast mem_R.mp hpR
        have hp1 : 1 ≤ p.2 := by
          by_contra hlt
          exact hpA (subset_R_zero_stoppedCluster B (H : ℤ) ω (2 * B.card * H)
            (mem_R.mpr (by exact_mod_cast (show p.2 ≤ 0 by omega))))
        have hpS : p ∈ S := Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_Icc.mpr ⟨hp1, hpH⟩⟩
        exact Set.mem_iUnion₂.mpr ⟨p, hpS, hpA⟩
    _ ≤ ∑ ζ ∈ S, idlaMeasure B {ω : TrajSeq B | ζ ∉ stoppedCluster B (H : ℤ) ω (2 * B.card * H)} :=
        measure_biUnion_finset_le S _
    _ ≤ ∑ _ζ ∈ S, ENNReal.ofReal (Real.exp (-(H : ℝ) / 4)) := by
        refine Finset.sum_le_sum fun ζ hζ => ?_
        have hζI := Finset.mem_Icc.mp (Finset.mem_product.mp hζ).2
        exact site_not_mem_stoppedCluster_block_sharp B H hH ζ hζI.1 hζI.2
    _ = ENNReal.ofReal ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4)) := by
        rw [Finset.sum_const, hS, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        push_cast
        ring

end IdlaCyl.Reduction
