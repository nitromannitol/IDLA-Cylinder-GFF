module

/-
Discharge of `External.Chernoff` from `LatticeProb.bernstein_one_sided`
(`~/lean/Lattice-Probability/LatticeProb/Prob/Bernstein.lean`).

Set `Y i ω := p - X i ω`.  The event `{∑ X i < (1-δ)(np)}` is contained in
`{t ≤ ∑ Y i}` for `t := δnp`, and `bernstein_one_sided` bounds the latter by
`exp(-(t²/2)/(B² + Mt/3))` with `M := 1` and `B² := ∑ᵢ ∫ Yᵢ² = n·p(1-p)`.  The
degenerate cases `t = 0` (any of `δ, n, p` vanishing) and `p = 1` (the variance
proxy `B²` would be forced to `0`, incompatible with `bernstein_one_sided`'s
`0 < B`) are handled directly: the former by `P _ ≤ 1`, the latter by showing
the event is `P`-null since `∫ Xᵢ = 1` forces `Xᵢ =ᵐ 1`.
-/
public import IdlaCyl.External.Basic
public import LatticeProb.Prob.Bernstein

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IdlaCyl.External

-- FROZEN-STATEMENT-BEGIN
theorem chernoff_of_latticeProb : Chernoff := by
  intro Ω _ P _ n p δ X hp0 hp1 hδ0 hδ1 hind hX01 hmean
  set t : ℝ := δ * (n : ℝ) * p with ht_def
  by_cases ht0 : t = 0
  · have hexp0 : -(δ ^ 2 * (n : ℝ) * p / 4) = 0 := by
      have h : δ ^ 2 * (n : ℝ) * p = δ * t := by rw [ht_def]; ring
      rw [h, ht0]; ring
    calc P {ω | (∑ i, X i ω) < (1 - δ) * ((n : ℝ) * p)}
        ≤ 1 := prob_le_one
      _ = ENNReal.ofReal (Real.exp (-(δ ^ 2 * (n : ℝ) * p / 4))) := by
            rw [hexp0, Real.exp_zero, ENNReal.ofReal_one]
  · obtain ⟨hδn, hpne⟩ := mul_ne_zero_iff.mp ht0
    obtain ⟨hδne, hnne⟩ := mul_ne_zero_iff.mp hδn
    have hnpos : 0 < (n : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg n) (Ne.symm hnne)
    have hδpos : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hδne)
    have hppos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpne)
    have htpos : 0 < t := by rw [ht_def]; exact mul_pos (mul_pos hδpos hnpos) hppos
    have hXi_int : ∀ i, Integrable (X i) P := by
      intro i
      by_contra hni
      exact hpne (by rw [← hmean i]; exact integral_undef hni)
    by_cases hp1eq : p = 1
    · subst hp1eq
      have hae : ∀ i, ∀ᵐ ω ∂P, X i ω = 1 := by
        intro i
        have hZnn : (0 : Ω → ℝ) ≤ fun ω => 1 - X i ω := by
          intro ω
          show (0 : ℝ) ≤ 1 - X i ω
          rcases hX01 i ω with h | h <;> rw [h] <;> norm_num
        have hZint : Integrable (fun ω => 1 - X i ω) P :=
          (integrable_const (1 : ℝ)).sub (hXi_int i)
        have hZ0 : ∫ ω, (1 - X i ω) ∂P = 0 := by
          have hsub := integral_sub (integrable_const (1 : ℝ)) (hXi_int i)
          simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hsub
          rw [hsub, hmean i]; ring
        have hz := (integral_eq_zero_iff_of_nonneg hZnn hZint).mp hZ0
        filter_upwards [hz] with ω hω
        simp only [Pi.zero_apply] at hω
        linarith
      have hall : ∀ᵐ ω ∂P, ∀ i, X i ω = 1 := ae_all_iff.mpr hae
      have hSnull : P {ω | ¬ ∀ i, X i ω = 1} = 0 := ae_iff.mp hall
      have hsub : {ω | (∑ i, X i ω) < (1 - δ) * ((n : ℝ) * 1)} ⊆
          {ω | ¬ ∀ i, X i ω = 1} := by
        intro ω hω hcon
        simp only [Set.mem_setOf_eq] at hω
        have heqsum : (∑ i : Fin n, X i ω) = (n : ℝ) := by
          have hc : (∑ i : Fin n, X i ω) = ∑ _i : Fin n, (1 : ℝ) :=
            Finset.sum_congr rfl (fun i _ => hcon i)
          rw [hc, Finset.sum_const, Finset.card_fin, nsmul_eq_mul, mul_one]
        rw [heqsum] at hω
        have hmn : 0 ≤ δ * (n : ℝ) := mul_nonneg hδ0 (le_of_lt hnpos)
        have heq : (1 - δ) * ((n : ℝ) * 1) = (n : ℝ) - δ * (n : ℝ) := by ring
        rw [heq] at hω
        linarith
      calc P {ω | (∑ i, X i ω) < (1 - δ) * ((n : ℝ) * 1)}
          ≤ P {ω | ¬ ∀ i, X i ω = 1} := measure_mono hsub
        _ = 0 := hSnull
        _ ≤ ENNReal.ofReal (Real.exp (-(δ ^ 2 * (n : ℝ) * 1 / 4))) := bot_le
    · have hplt1 : p < 1 := lt_of_le_of_ne hp1 hp1eq
      have hp1p : 0 < p - p ^ 2 := by
        have heq : p - p ^ 2 = p * (1 - p) := by ring
        rw [heq]; exact mul_pos hppos (by linarith)
      have hB2nn : (0 : ℝ) ≤ (n : ℝ) * (p - p ^ 2) := le_of_lt (mul_pos hnpos hp1p)
      set B : ℝ := Real.sqrt ((n : ℝ) * (p - p ^ 2)) with hB_def
      have hBpos : 0 < B := by
        rw [hB_def]; exact Real.sqrt_pos.mpr (mul_pos hnpos hp1p)
      have hB2 : B ^ 2 = (n : ℝ) * (p - p ^ 2) := by rw [hB_def]; exact Real.sq_sqrt hB2nn
      -- independence, integrability, mean, and boundedness of `Y i ω := p - X i ω`
      have hindY : iIndepFun (fun i ω => p - X i ω) P :=
        hind.comp (fun _ : Fin n => fun x : ℝ => p - x) (fun _ => measurable_const_sub p)
      have hYint : ∀ i, Integrable (fun ω => p - X i ω) P :=
        fun i => (integrable_const p).sub (hXi_int i)
      have hYmean : ∀ i, ∫ ω, (p - X i ω) ∂P = 0 := by
        intro i
        rw [integral_sub (integrable_const p) (hXi_int i), integral_const, probReal_univ,
          smul_eq_mul, one_mul, hmean i]
        ring
      have hYbound : ∀ i, ∀ᵐ ω ∂P, |p - X i ω| ≤ 1 := by
        intro i
        refine Filter.Eventually.of_forall (fun ω => ?_)
        rcases hX01 i ω with h | h <;> rw [h, abs_le] <;> constructor <;> linarith
      have hsqeq : ∀ i ω, (p - X i ω) ^ 2 = p ^ 2 + (1 - 2 * p) * X i ω := by
        intro i ω
        rcases hX01 i ω with h | h <;> rw [h] <;> ring
      have hYsqint : ∀ i, Integrable (fun ω => (p - X i ω) ^ 2) P := by
        intro i
        have heqf : (fun ω => (p - X i ω) ^ 2) = (fun ω => p ^ 2 + (1 - 2 * p) * X i ω) :=
          funext (hsqeq i)
        rw [heqf]
        exact (integrable_const (p ^ 2)).add ((hXi_int i).const_mul (1 - 2 * p))
      have hYsqval : ∀ i, ∫ ω, (p - X i ω) ^ 2 ∂P = p - p ^ 2 := by
        intro i
        have heqf : (fun ω => (p - X i ω) ^ 2) = (fun ω => p ^ 2 + (1 - 2 * p) * X i ω) :=
          funext (hsqeq i)
        rw [heqf, integral_add (integrable_const (p ^ 2)) ((hXi_int i).const_mul (1 - 2 * p)),
          integral_const, probReal_univ, smul_eq_mul, one_mul, integral_const_mul, hmean i]
        ring
      have hsum_val : ∑ i : Fin n, ∫ ω, (p - X i ω) ^ 2 ∂P = (n : ℝ) * (p - p ^ 2) := by
        have heq : ∑ i : Fin n, ∫ ω, (p - X i ω) ^ 2 ∂P = ∑ _i : Fin n, (p - p ^ 2) :=
          Finset.sum_congr rfl (fun i _ => hYsqval i)
        rw [heq, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      have hB2eq : B ^ 2 = ∑ i : Fin n, ∫ ω, (p - X i ω) ^ 2 ∂P := by rw [hB2, hsum_val]
      have hbern := LatticeProb.bernstein_one_sided P (fun i ω => p - X i ω) hindY hYint hYmean
        1 B (by norm_num) hBpos hYbound hB2eq hYsqint t htpos
      simp only [one_mul] at hbern
      -- event containment
      have hsub : {ω | (∑ i, X i ω) < (1 - δ) * ((n : ℝ) * p)} ⊆
          {ω | t ≤ ∑ i, (p - X i ω)} := by
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω ⊢
        have hsum : ∑ i : Fin n, (p - X i ω) = (n : ℝ) * p - ∑ i : Fin n, X i ω := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
        have hexpand : (1 - δ) * ((n : ℝ) * p) = (n : ℝ) * p - δ * (n : ℝ) * p := by ring
        rw [hexpand] at hω
        rw [hsum, ht_def]
        linarith
      -- exponent comparison: `B² ≤ np` and `t = δnp` reduce the target to `δ ≤ 3`
      have hB2le : B ^ 2 ≤ (n : ℝ) * p := by
        rw [hB2]
        have heq : (n : ℝ) * (p - p ^ 2) = (n : ℝ) * p - (n : ℝ) * p ^ 2 := by ring
        rw [heq]
        have hnn : 0 ≤ (n : ℝ) * p ^ 2 := mul_nonneg (le_of_lt hnpos) (sq_nonneg p)
        linarith
      have hD2pos : 0 < (n : ℝ) * p + t / 3 := by
        have hnppos : 0 < (n : ℝ) * p := mul_pos hnpos hppos
        linarith [htpos]
      have hDBpos : 0 < B ^ 2 + t / 3 := by
        have hB2pos : 0 < B ^ 2 := by rw [hB2]; exact mul_pos hnpos hp1p
        linarith [htpos]
      have hstep2 : δ ^ 2 * ((n : ℝ) * p) / 4 ≤ (t ^ 2 / 2) / ((n : ℝ) * p + t / 3) := by
        rw [le_div_iff₀ hD2pos]
        have hdiff : (t ^ 2 / 2) - δ ^ 2 * ((n : ℝ) * p) / 4 * ((n : ℝ) * p + t / 3)
            = δ ^ 2 * ((n : ℝ) * p) ^ 2 * (3 - δ) / 12 := by
          rw [ht_def]; ring
        have hnn : 0 ≤ δ ^ 2 * ((n : ℝ) * p) ^ 2 * (3 - δ) / 12 := by
          apply div_nonneg _ (by norm_num)
          exact mul_nonneg (mul_nonneg (sq_nonneg δ) (sq_nonneg ((n : ℝ) * p))) (by linarith)
        linarith [hdiff, hnn]
      have hstep1 : (t ^ 2 / 2) / ((n : ℝ) * p + t / 3) ≤ (t ^ 2 / 2) / (B ^ 2 + t / 3) :=
        div_le_div_of_nonneg_left (div_nonneg (sq_nonneg t) (by norm_num)) hDBpos
          (by linarith [hB2le])
      have hqp : δ ^ 2 * (n : ℝ) * p = δ ^ 2 * ((n : ℝ) * p) := by ring
      have hfinal : δ ^ 2 * (n : ℝ) * p / 4 ≤ (t ^ 2 / 2) / (B ^ 2 + t / 3) := by
        rw [hqp]; exact le_trans hstep2 hstep1
      calc P {ω | (∑ i, X i ω) < (1 - δ) * ((n : ℝ) * p)}
          ≤ P {ω | t ≤ ∑ i, (p - X i ω)} := measure_mono hsub
        _ ≤ ENNReal.ofReal (Real.exp (-(t ^ 2 / 2) / (B ^ 2 + t / 3))) := hbern
        _ ≤ ENNReal.ofReal (Real.exp (-(δ ^ 2 * (n : ℝ) * p / 4))) := by
              apply ENNReal.ofReal_le_ofReal
              apply Real.exp_le_exp.mpr
              rw [neg_div]
              linarith [hfinal]
-- FROZEN-STATEMENT-END

end IdlaCyl.External
