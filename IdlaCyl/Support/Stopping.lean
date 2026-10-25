module

/-
Bounded optional stopping at an almost surely finite `ℕ∞`-valued stopping time
(`tex:696`, `tex:1200`).  Mathlib's `ℕ`-valued form does not
apply to `exitTime'`, which is finite only a.s.; the truncation plus dominated
convergence is done once, here, instead of being hidden in an inapplicable
`Prop` binder.
-/
public import IdlaCyl.Support.Canonical
public import Mathlib.Probability.Martingale.OptionalStopping

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IdlaCyl

/-- Bounded optional stopping at an almost surely finite `ℕ∞`-valued stopping
time: for a bounded martingale `M` and an a.s. finite `τ`,
`∫ M_{τ} = ∫ M_0`. -/
theorem integral_stoppedValue_of_ae_finite
    {Ω : Type*} [MeasurableSpace Ω] {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (M : ℕ → Ω → ℝ) (τ : Ω → ℕ∞) (C : ℝ)
    (hM : Martingale M ℱ P) (hbdd : ∀ t ω, |M t ω| ≤ C)
    (hτ : ∀ n : ℕ, MeasurableSet[ℱ n] {ω | τ ω ≤ (n : ℕ∞)})
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    ∫ ω, M ((τ ω).toNat) ω ∂P = ∫ ω, M 0 ω ∂P := by
  have hτ' : IsStoppingTime ℱ τ := hτ
  have hM' : Submartingale M ℱ P := hM.submartingale
  have hMneg' : Submartingale (-M) ℱ P := hM.neg.submartingale
  have hprog : IsStronglyProgressive ℱ M := hM.stronglyAdapted.isStronglyProgressive_of_discrete
  -- for each truncation level `n`, optional stopping between `0` and `τ ⊓ n` gives equality
  have hstep : ∀ n : ℕ,
      ∫ ω, stoppedValue M (fun ω => min (τ ω) (n : ℕ∞)) ω ∂P = ∫ ω, M 0 ω ∂P := by
    intro n
    have hπ : IsStoppingTime ℱ (fun ω => min (τ ω) (n : ℕ∞)) := hτ'.min_const n
    have hbddπ : ∀ ω, min (τ ω) (n : ℕ∞) ≤ (n : ℕ∞) := fun ω => min_le_right _ _
    have h1 := hM'.expected_stoppedValue_mono (isStoppingTime_const ℱ 0) hπ (fun _ => zero_le)
      hbddπ
    have h2 := hMneg'.expected_stoppedValue_mono (isStoppingTime_const ℱ 0) hπ (fun _ => zero_le)
      hbddπ
    simp only [stoppedValue_const] at h1 h2
    have hnegπ : ∀ ω, stoppedValue (-M) (fun ω' => min (τ ω') (n : ℕ∞)) ω
        = -(stoppedValue M (fun ω' => min (τ ω') (n : ℕ∞)) ω) := fun ω => rfl
    have hneg0 : ∀ ω, (-M) 0 ω = -(M 0 ω) := fun ω => rfl
    simp only [hneg0, hnegπ, integral_neg] at h2
    linarith
  -- the value at time `n ⊓ τ` converges pointwise a.e. to the value at time `τ.toNat`
  have hmeasπ : ∀ n : ℕ,
      AEStronglyMeasurable (stoppedValue M (fun ω => min (τ ω) (n : ℕ∞))) P := fun n =>
    ((stronglyMeasurable_stoppedValue_of_le hprog (hτ'.min_const n)
      (fun ω => min_le_right (τ ω) (n : ℕ∞))).mono (ℱ.le n)).aestronglyMeasurable
  have hbound : ∀ n : ℕ,
      ∀ᵐ ω ∂P, ‖stoppedValue M (fun ω => min (τ ω) (n : ℕ∞)) ω‖ ≤ C := fun n =>
    Filter.Eventually.of_forall fun ω => hbdd _ ω
  have key : ∀ ω, τ ω ≠ ⊤ → ∀ n : ℕ, (τ ω).toNat ≤ n →
      stoppedValue M (fun ω' => min (τ ω') (n : ℕ∞)) ω = M (τ ω).toNat ω := by
    intro ω hω n hn
    have hcoe : ((τ ω).toNat : ℕ∞) = τ ω := ENat.coe_toNat hω
    have hle : τ ω ≤ (n : ℕ∞) := by rw [← hcoe]; exact_mod_cast hn
    have hmin : min (τ ω) (n : ℕ∞) = ((τ ω).toNat : ℕ∞) := by
      rw [hcoe]; exact min_eq_left hle
    calc stoppedValue M (fun ω' => min (τ ω') (n : ℕ∞)) ω
        = M (min (τ ω) (n : ℕ∞)).untopA ω := rfl
      _ = M (((τ ω).toNat : ℕ∞)).untopA ω := by rw [hmin]
      _ = M (τ ω).toNat ω := congrFun (stoppedValue_const M (τ ω).toNat) ω
  have hlim : ∀ᵐ ω ∂P, Filter.Tendsto
      (fun n : ℕ => stoppedValue M (fun ω' => min (τ ω') (n : ℕ∞)) ω) Filter.atTop
      (nhds (M (τ ω).toNat ω)) := by
    filter_upwards [hfin] with ω hω
    exact tendsto_atTop_of_eventually_const (key ω hω)
  have hdct := tendsto_integral_of_dominated_convergence (fun _ : Ω => C) hmeasπ
    (integrable_const C) hbound hlim
  have hconst : Filter.Tendsto (fun n : ℕ =>
      ∫ ω, stoppedValue M (fun ω => min (τ ω) (n : ℕ∞)) ω ∂P) Filter.atTop
      (nhds (∫ ω, M 0 ω ∂P)) := by
    have heq : (fun n : ℕ => ∫ ω, stoppedValue M (fun ω => min (τ ω) (n : ℕ∞)) ω ∂P)
        = fun _ => ∫ ω, M 0 ω ∂P := funext hstep
    rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hdct hconst

end IdlaCyl
