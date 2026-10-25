module

/-
Discharge of `External.Bernstein` from `LatticeProb.bernstein`
(`~/lean/Lattice-Probability/LatticeProb/Prob/Bernstein.lean`), for
`ext-bernstein` (`tex:1314-1320`).

Route: apply `LatticeProb.bernstein` to `Y i ω := X i ω - p i` with `M := 1`,
`t := ε`, `B := √(∑ᵢ ∫ Yᵢ²)`.  For indicators `∫ Yᵢ² = pᵢ − pᵢ² ≤ pᵢ`, so
`B² + ε/3 ≤ ∑ pᵢ + ε/3` and the exponent only increases.  Two degenerate
branches are split off first, because `LatticeProb.bernstein` needs `0 < t`
and `0 < B`:

* `ε = 0`: the event is all of `Ω`, and `1 ≤ ofReal 2 = RHS`.
* `∑ᵢ ∫ Yᵢ² = 0`: each `pᵢ(1 − pᵢ) = 0`, so `pᵢ ∈ {0,1}` and `Xᵢ =ᵐ pᵢ`;
  the event is then `P`-null and the bound is `0 ≤ RHS`.

----------------------------------------------------------------------------
ERRATUM E17 — `External.Bernstein` needs a measurability binder
----------------------------------------------------------------------------
`External.Bernstein` (`IdlaCyl/External/Basic.lean:45-52`) is **false** as
currently stated, so this file proves the repaired form and *not* `Bernstein`
itself.

`ProbabilityTheory.iIndepFun` is `Kernel.iIndepFun`, i.e. a statement about the
comap σ-algebras `(mβ i).comap (X i)` only; it does not imply that any `X i` is
`mΩ`-measurable.  A `{0,1}`-valued function on a probability space is
`Integrable` iff it is `AEStronglyMeasurable`, so for a non-measurable `X i`
the Bochner integral takes its junk value `0` and the hypothesis
`∫ ω, X i ω ∂P = p i` is satisfied with `p i = 0` while `X i` is wild.

Counterexample.  `n = 1`; `Ω = ℝ` with the Borel σ-algebra; `P` = Lebesgue
measure restricted to `[0,1]` (a probability measure); `B ⊆ [0,1]` a Bernstein
set (inner measure `0`, outer measure `1`); `X 0 = Set.indicator B 1`;
`p 0 = 0`; `ε = 1`.  Then
  * `iIndepFun X P` holds — with a single index the only nontrivial finset is
    `{0}`, where the condition is `P (f 0) = P (f 0)`;
  * `hp0`, `hp1`, `hε`, `hX01` hold;
  * `∫ ω, X 0 ω ∂P = 0 = p 0`, since `X 0` is not `AEStronglyMeasurable`
    (if `g` were Borel with `g =ᵐ 1_B`, then `B` minus a null Borel set would
    be Borel and inside `B`, hence null by inner regularity, forcing `B` to
    have outer measure `0`);
  * the conclusion asserts `P B ≤ ofReal (2 * exp (-(1/2)/(1/3)))
    = ofReal (2 * exp (-3/2)) ≈ 0.446`, whereas `P B = 1`, because `μ s` is the
    induced outer measure (`MeasureTheory.measure_eq_iInf`) and every Borel
    superset of `B` in `[0,1]` has measure `1`.

The hypotheses are satisfiable on a junk branch that they were meant to exclude.

The fix is to add `(∀ i, Measurable (X i))` to `External.Bernstein`, immediately
after the `iIndepFun X P` binder.  The paper's `Xᵢ` at `tex:1314-1320` are
indicators of measurable events, so this is not an extra assumption in the
paper; it is the binder Lean needs to rule out the junk branch.  With it,
`Bernstein` would be discharged by

    theorem bernstein_of_latticeProb : Bernstein :=
      fun P n p X ε hp0 hp1 hε hind hmeas hX01 hmean =>
        bernstein_of_latticeProb_of_measurable P n p X ε hp0 hp1 hε hind hmeas hX01 hmean

which is deliberately *not* included here, since it does not typecheck against
the unrepaired `Bernstein`.  `External.Chernoff` is unaffected: there `p` is a
single constant, and the `p = 0` branch has an empty event
(`{ω | ∑ Xᵢ ω < 0}` with `Xᵢ ≥ 0`), while `p ≠ 0` forces integrability.
-/
public import IdlaCyl.External.Basic
public import LatticeProb.Prob.Bernstein

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IdlaCyl.External

/-- `ext-bernstein` (`tex:1314-1320`), in the E17-repaired form: a two-sided
deviation bound for a sum of independent *measurable* indicators, with variance
proxy `∑ pᵢ` and the factor `2` of erratum E15.

The `hmeas` binder is the E17 repair; see the file header for the Bernstein-set
counterexample to the binder-free statement `External.Bernstein`. -/
-- FROZEN-STATEMENT-BEGIN
theorem bernstein_of_latticeProb_of_measurable
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (p : Fin n → ℝ) (X : Fin n → Ω → ℝ) (ε : ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hε : 0 ≤ ε)
    (hind : iIndepFun X P) (hmeas : ∀ i, Measurable (X i))
    (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hmean : ∀ i, ∫ ω, X i ω ∂P = p i) :
    P {ω | ε ≤ |(∑ i, X i ω) - ∑ i, p i|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 / 2) / (∑ i, p i + ε / 3))) := by
  -- Each `X i` is bounded and measurable, hence integrable.
  have hXint : ∀ i, Integrable (X i) P := by
    intro i
    refine Integrable.mono' (integrable_const (1 : ℝ)) (hmeas i).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rcases hX01 i ω with h | h <;> simp [h]
  -- `(X i ω - p i)² = (1 - 2 pᵢ) X i ω + pᵢ²` pointwise, because `X i ω ∈ {0,1}`.
  have hsq : ∀ (i : Fin n) (ω : Ω),
      (X i ω - p i) ^ 2 = (1 - 2 * p i) * X i ω + p i ^ 2 := by
    intro i ω
    rcases hX01 i ω with h | h <;> rw [h] <;> ring
  have hfeq : ∀ i : Fin n,
      (fun ω => (X i ω - p i) ^ 2) = (fun ω => (1 - 2 * p i) * X i ω + p i ^ 2) :=
    fun i => funext (hsq i)
  have hYsqint : ∀ i, Integrable (fun ω => (X i ω - p i) ^ 2) P := by
    intro i
    rw [hfeq i]
    exact ((hXint i).const_mul (1 - 2 * p i)).add (integrable_const (p i ^ 2))
  have hYsqval : ∀ i, ∫ ω, (X i ω - p i) ^ 2 ∂P = p i - p i ^ 2 := by
    intro i
    have hadd := integral_add ((hXint i).const_mul (1 - 2 * p i))
      (integrable_const (p i ^ 2))
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
      integral_const_mul] at hadd
    rw [hfeq i, hadd, hmean i]
    ring
  have hSval : ∑ i, ∫ ω, (X i ω - p i) ^ 2 ∂P = ∑ i, (p i - p i ^ 2) :=
    Finset.sum_congr rfl (fun i _ => hYsqval i)
  have hterm : ∀ i : Fin n, 0 ≤ p i - p i ^ 2 := by
    intro i
    have h : p i - p i ^ 2 = p i * (1 - p i) := by ring
    rw [h]
    exact mul_nonneg (hp0 i) (by linarith only [hp1 i])
  have hSnn : 0 ≤ ∑ i, ∫ ω, (X i ω - p i) ^ 2 ∂P := by
    rw [hSval]
    exact Finset.sum_nonneg (fun i _ => hterm i)
  have hSle : ∑ i, ∫ ω, (X i ω - p i) ^ 2 ∂P ≤ ∑ i, p i := by
    rw [hSval]
    exact Finset.sum_le_sum (fun i _ => by linarith only [sq_nonneg (p i)])
  -- mean, boundedness and independence of `Y i ω := X i ω - p i`
  have hYmean : ∀ i, ∫ ω, (X i ω - p i) ∂P = 0 := by
    intro i
    have hsub := integral_sub (hXint i) (integrable_const (p i))
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hsub
    rw [hsub, hmean i, sub_self]
  have hYbound : ∀ i, ∀ᵐ ω ∂P, |X i ω - p i| ≤ 1 := by
    intro i
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rcases hX01 i ω with h | h <;> rw [h, abs_le] <;> constructor <;>
      linarith only [hp0 i, hp1 i]
  have hgm : ∀ i : Fin n, Measurable (fun x : ℝ => x - p i) :=
    fun i => measurable_id.sub_const (p i)
  have hindY : iIndepFun (fun i ω => X i ω - p i) P :=
    hind.comp (fun i : Fin n => fun x : ℝ => x - p i) hgm
  have hYint : ∀ i, Integrable (fun ω => X i ω - p i) P :=
    fun i => (hXint i).sub (integrable_const (p i))
  by_cases hε0 : ε = 0
  · -- degenerate branch `ε = 0`: the event is everything and the bound is `2`
    subst hε0
    refine le_trans prob_le_one ?_
    have hz : -((0 : ℝ) ^ 2 / 2) / ((∑ i, p i) + 0 / 3) = 0 := by norm_num
    have h2 : (1 : ℝ) ≤ 2 * Real.exp (-((0 : ℝ) ^ 2 / 2) / ((∑ i, p i) + 0 / 3)) := by
      rw [hz, Real.exp_zero]
      norm_num
    calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := by simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal h2
  · have hεpos : 0 < ε := lt_of_le_of_ne hε (Ne.symm hε0)
    by_cases hS0 : (∑ i, ∫ ω, (X i ω - p i) ^ 2 ∂P) = 0
    · -- degenerate branch `B = 0`: every `pᵢ ∈ {0,1}` and `Xᵢ =ᵐ pᵢ`
      rw [hSval] at hS0
      have hzero : ∀ i ∈ (Finset.univ : Finset (Fin n)), p i - p i ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterm i)).mp hS0
      have hae : ∀ i, ∀ᵐ ω ∂P, X i ω = p i := by
        intro i
        have hpi : p i * (1 - p i) = 0 := by
          have h := hzero i (Finset.mem_univ i)
          have hr : p i * (1 - p i) = p i - p i ^ 2 := by ring
          rw [hr]
          exact h
        rcases mul_eq_zero.mp hpi with hp | hq
        · -- `p i = 0`, so `X i =ᵐ 0`
          have hXnn : (0 : Ω → ℝ) ≤ X i := by
            intro ω
            show (0 : ℝ) ≤ X i ω
            rcases hX01 i ω with h | h
            · simp [h]
            · simp [h]
          have hint0 : ∫ ω, X i ω ∂P = 0 := by rw [hmean i, hp]
          have hz := (integral_eq_zero_iff_of_nonneg hXnn (hXint i)).mp hint0
          filter_upwards [hz] with ω hω
          simp only [Pi.zero_apply] at hω
          rw [hω, hp]
        · -- `p i = 1`, so `X i =ᵐ 1`
          have hpi1 : p i = 1 := by linarith only [hq]
          have hZnn : (0 : Ω → ℝ) ≤ fun ω => 1 - X i ω := by
            intro ω
            show (0 : ℝ) ≤ 1 - X i ω
            rcases hX01 i ω with h | h <;> rw [h] <;> norm_num
          have hZint : Integrable (fun ω => 1 - X i ω) P :=
            (integrable_const (1 : ℝ)).sub (hXint i)
          have hZ0 : ∫ ω, (1 - X i ω) ∂P = 0 := by
            have hsub := integral_sub (integrable_const (1 : ℝ)) (hXint i)
            simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hsub
            rw [hsub, hmean i, hpi1]
            ring
          have hz := (integral_eq_zero_iff_of_nonneg hZnn hZint).mp hZ0
          filter_upwards [hz] with ω hω
          simp only [Pi.zero_apply] at hω
          rw [hpi1]
          linarith only [hω]
      have hall : ∀ᵐ ω ∂P, ∀ i, X i ω = p i := ae_all_iff.mpr hae
      have hnull : P {ω | ¬ ∀ i, X i ω = p i} = 0 := ae_iff.mp hall
      have hsubset : {ω | ε ≤ |(∑ i, X i ω) - ∑ i, p i|} ⊆
          {ω | ¬ ∀ i, X i ω = p i} := by
        intro ω hω hcon
        simp only [Set.mem_setOf_eq] at hω
        have heq : (∑ i, X i ω) = ∑ i, p i :=
          Finset.sum_congr rfl (fun i _ => hcon i)
        rw [heq, sub_self, abs_zero] at hω
        linarith only [hω, hεpos]
      calc P {ω | ε ≤ |(∑ i, X i ω) - ∑ i, p i|}
          ≤ P {ω | ¬ ∀ i, X i ω = p i} := measure_mono hsubset
        _ = 0 := hnull
        _ ≤ ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 / 2) / (∑ i, p i + ε / 3))) := bot_le
    · -- main branch: `0 < ε` and `0 < B`
      have hSpos : 0 < ∑ i, ∫ ω, (X i ω - p i) ^ 2 ∂P :=
        lt_of_le_of_ne hSnn (Ne.symm hS0)
      obtain ⟨B, hBpos, hB2⟩ :
          ∃ B : ℝ, 0 < B ∧ B ^ 2 = ∑ i, ∫ ω, (X i ω - p i) ^ 2 ∂P :=
        ⟨Real.sqrt (∑ i, ∫ ω, (X i ω - p i) ^ 2 ∂P),
          Real.sqrt_pos.mpr hSpos, Real.sq_sqrt hSnn⟩
      have hbern := LatticeProb.bernstein P (fun i ω => X i ω - p i) hindY hYint hYmean
        1 B (by norm_num) hBpos hYbound hB2 hYsqint ε hεpos
      simp only [one_mul] at hbern
      have hB2le : B ^ 2 ≤ ∑ i, p i := by rw [hB2]; exact hSle
      have hDBpos : 0 < B ^ 2 + ε / 3 := by
        rw [hB2]
        linarith only [hSpos, hεpos]
      have hstep1 : (ε ^ 2 / 2) / ((∑ i, p i) + ε / 3) ≤ (ε ^ 2 / 2) / (B ^ 2 + ε / 3) :=
        div_le_div_of_nonneg_left (div_nonneg (sq_nonneg ε) (by norm_num)) hDBpos
          (by linarith only [hB2le])
      have hset : {ω | ε ≤ |(∑ i, X i ω) - ∑ i, p i|}
          = {ω | ε ≤ |∑ i, (X i ω - p i)|} := by
        ext ω
        simp only [Set.mem_setOf_eq, Finset.sum_sub_distrib]
      rw [hset]
      refine le_trans hbern ?_
      apply ENNReal.ofReal_le_ofReal
      have hmono : -(ε ^ 2 / 2) / (B ^ 2 + ε / 3)
          ≤ -(ε ^ 2 / 2) / ((∑ i, p i) + ε / 3) := by
        rw [neg_div, neg_div]
        linarith only [hstep1]
      linarith only [Real.exp_le_exp.mpr hmono]
-- FROZEN-STATEMENT-END

end IdlaCyl.External
