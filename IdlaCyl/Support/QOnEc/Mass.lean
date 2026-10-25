module

/-
Source: paper/idla-cylinder-gff.tex, tex:901-903,941-967,990-998.
Measurability, integrability, and height bounds for the literal quadratic mass.
-/
public import IdlaCyl.Definitions.ShapeEvent
public import IdlaCyl.Support.ClmQOnEc
public import IdlaCyl.Support.HarmonicMartingaleIntegrable
public import IdlaCyl.Support.SpectralLimit
public import IdlaCyl.Support.WnLimit

@[expose] public section

namespace IdlaCyl.QOnEc

open IdlaCyl.Defs Filter MeasureTheory
open scoped Topology BigOperators

/-- The literal quadratic mass is nonnegative at every trajectory. -/
theorem qmass_nonneg (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ)
    (N : ℕ) (ω : TrajSeq (U.B N)) : 0 ≤ qmass U K α y₀ N ω := by
  unfold qmass QN
  have ha := U.a_pos (U.B N).card
  exact mul_nonneg (by positivity : 0 ≤ 1 / (((U.B N).card : ℝ) * U.a (U.B N).card))
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The quadratic mass over settling sites is measurable. -/
theorem measurable_QN (B : Base) (a : ℕ → ℝ) (T : ℕ) (ψ : Site B → ℝ) :
    Measurable (QN B a T ψ) := by
  have heq : QN B a T ψ = fun ω => 1 / ((B.card : ℝ) * a B.card) *
      ∑ p ∈ (Finset.range T).image (settleSite B ω),
        (if 1 ≤ p.2 then ψ p ^ 2 else 0) := by
    funext ω
    unfold QN
    rw [clusterPlusFinset, Finset.sum_filter]
  rw [heq]
  exact measurable_const.mul
    (measurable_sum_image B T (fun p => if 1 ≤ p.2 then ψ p ^ 2 else 0))

/-- The literal quadratic mass is integrable; the almost-sure height cap
makes its range bounded at each fixed observation time. -/
theorem integrable_qmass (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (N : ℕ) :
    Integrable (qmass U K α y₀ N) (idlaMeasure (U.B N)) := by
  let B := U.B N
  let T := time U y₀ N
  let ψ := psi U K α y₀ N
  let b := 1 / ((B.card : ℝ) * U.a B.card) *
    ∑ p ∈ (Finset.univ : Finset B.V).product (Finset.Icc 1 ((T : ℤ) + 1)), ψ p ^ 2
  apply Integrable.of_bound (measurable_QN B U.a T ψ).aestronglyMeasurable b
  filter_upwards [clusterTraj_ae_subset_R_time B T] with ω hω
  rw [Real.norm_eq_abs]
  change |qmass U K α y₀ N ω| ≤ b
  rw [abs_of_nonneg (qmass_nonneg U K α y₀ N ω)]
  exact qN_le_slabUpTo B U.a (U.a_pos B.card).le T ψ ω (by omega)
    (hω.trans (R_mono (by push_cast; linarith)))

/-- Identification of the printed harmonic sum with the harmonic extension. -/
theorem psi_eq_psiExt (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ)
    (N : ℕ) (hK : K ≤ (U.B N).card) :
    psi U K α y₀ N = psiExt (U.B N) (U.S N) (height U y₀ N : ℤ)
      (psiCoeff K α (U.a N) (height U y₀ N : ℤ)) := by
  rw [psiExt_psiCoeff_eq_modeSumPsi (U.B N) (U.S N) (height U y₀ N : ℤ)
    K α hK (U.a N)]
  funext p
  simp only [psi, harmAt, modeSumPsi, exponentialMode, Int.cast_natCast, mul_assoc]

/-- The quadratic mass below height `h` obeys the deterministic bound. -/
theorem qmass_le_at_height (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ)
    (N : ℕ) (hN : 2 ≤ N) (hK : K ≤ (U.B N).card) (h : ℕ) (hh : 1 ≤ h)
    (ω : TrajSeq (U.B N))
    (hω : clusterTraj (U.B N) ω (time U y₀ N) ⊆ R (U.B N) (h : ℝ)) :
    qmass U K α y₀ N ω ≤ (h : ℝ) / U.a N *
      ∑ k ∈ Finset.Icc 2 K, α k ((height U y₀ N : ℝ) / U.a N) ^ 2 *
        Real.exp (2 * (U.S N).qk k * ((h : ℝ) - (height U y₀ N : ℝ))) := by
  have hcard := U.card_eq N hN
  have hNpos : (0 : ℝ) < ((U.B N).card : ℝ) := by rw [hcard]; positivity
  have heq : qmass U K α y₀ N ω = QN (U.B N) (fun _ => U.a N) (time U y₀ N)
      (psiExt (U.B N) (U.S N) (height U y₀ N : ℤ)
        (psiCoeff K α (U.a N) (height U y₀ N : ℤ))) ω := by
    simp only [qmass, QN]
    rw [hcard, psi_eq_psiExt U K α y₀ N hK]
  rw [heq]
  have hb := qN_psiExt_le_at_height (U.B N) (U.S N) K α hK (U.a N)
    (U.a_pos N).le (height U y₀ N : ℤ) (time U y₀ N) ω
    (h := (h : ℤ)) (by exact_mod_cast hh) hω
  simp only [Int.cast_natCast] at hb
  have hcancel (s : ℝ) : 1 / (((U.B N).card : ℝ) * U.a N) *
      ((h : ℝ) * ((U.B N).card : ℝ) * s) = (h : ℝ) / U.a N * s := by
    field_simp
  rwa [hcancel] at hb

/-- Coefficient regularity and spectral convergence give a common height
bound, with constants chosen before the size, height, and trajectory. -/
theorem qmass_height_bound_eventually (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) :
    ∃ A b : ℝ, 0 < A ∧ 0 < b ∧ ∀ᶠ N in atTop, ∀ h : ℕ, 1 ≤ h →
      ∀ ω : TrajSeq (U.B N),
      clusterTraj (U.B N) ω (time U y₀ N) ⊆ R (U.B N) (h : ℝ) →
      qmass U K α y₀ N ω ≤ A * ((h : ℝ) / U.a N) *
        Real.exp (b * ((h : ℝ) / U.a N)) := by
  let A := (∑ k ∈ Finset.Icc 2 K, (α k y₀ ^ 2 + 1)) + 1
  let b := 2 * ((∑ k ∈ Finset.Icc 2 K, |γ k|) + 1)
  have hA : 0 < A := by dsimp [A]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hf : Tendsto (fun N => (height U y₀ N : ℝ) / U.a N) atTop (nhds y₀) :=
    (tendsto_nat_floor_mul_div_atTop hy₀.le).comp U.a_tendsto
  have hcoef : ∀ k ∈ Finset.Icc 2 K, ∀ᶠ N in atTop,
      α k ((height U y₀ N : ℝ) / U.a N) ^ 2 ≤ α k y₀ ^ 2 + 1 ∧
      2 * (U.a N * (U.S N).qk k) ≤ b := by
    intro k hk
    obtain ⟨hk2, hkK⟩ := Finset.mem_Icc.mp hk
    obtain ⟨s, hs, hd, -⟩ := hα k hk2 hkK
    have hc := (((hd y₀ (mem_of_mem_nhds hs)).continuousAt.tendsto.comp hf).pow 2)
    have hq := U.qkN_tendsto γ K hspec k hk2 hkK
    have hg : γ k < (∑ j ∈ Finset.Icc 2 K, |γ j|) + 1 := by
      have hle := Finset.single_le_sum (fun j (_ : j ∈ Finset.Icc 2 K) => abs_nonneg (γ j)) hk
      linarith [le_abs_self (γ k)]
    filter_upwards [hc.eventually (gt_mem_nhds (show α k y₀ ^ 2 < α k y₀ ^ 2 + 1 by linarith)),
      hq.eventually (gt_mem_nhds hg)] with N hcN hqN
    exact ⟨hcN.le, by dsimp [b]; linarith⟩
  refine ⟨A, b, hA, hb, ?_⟩
  filter_upwards [(Filter.eventually_all_finset _).2 hcoef,
    eventually_ge_atTop (max K 2)] with N hterms hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hKN : K ≤ (U.B N).card := by
    rw [U.card_eq N hN2]
    exact (le_max_left _ _).trans hN
  intro h hh ω hω
  have hr : 0 ≤ (h : ℝ) / U.a N := div_nonneg (Nat.cast_nonneg _) (U.a_pos N).le
  have hsum : (∑ k ∈ Finset.Icc 2 K,
      α k ((height U y₀ N : ℝ) / U.a N) ^ 2 *
        Real.exp (2 * (U.S N).qk k * ((h : ℝ) - (height U y₀ N : ℝ)))) ≤
      A * Real.exp (b * ((h : ℝ) / U.a N)) := by
    calc
      _ ≤ (∑ k ∈ Finset.Icc 2 K, (α k y₀ ^ 2 + 1) *
          Real.exp (b * ((h : ℝ) / U.a N))) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk2 := (Finset.mem_Icc.mp hk).1
        have hq0 := (U.S N).qk_pos hk2 ((Finset.mem_Icc.mp hk).2.trans hKN)
        have he : 2 * (U.S N).qk k * ((h : ℝ) - (height U y₀ N : ℝ)) ≤
            b * ((h : ℝ) / U.a N) := by
          calc _ ≤ 2 * (U.S N).qk k * (h : ℝ) :=
              mul_le_mul_of_nonneg_left (sub_le_self _ (Nat.cast_nonneg _)) (by positivity)
            _ = (2 * (U.a N * (U.S N).qk k)) * ((h : ℝ) / U.a N) := by field_simp [(U.a_pos N).ne']
            _ ≤ _ := mul_le_mul_of_nonneg_right (hterms k hk).2 hr
        exact mul_le_mul (hterms k hk).1 (Real.exp_le_exp.mpr he)
          (Real.exp_nonneg _) (by positivity)
      _ = (∑ k ∈ Finset.Icc 2 K, (α k y₀ ^ 2 + 1)) * Real.exp (b * ((h : ℝ) / U.a N)) :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ A * Real.exp (b * ((h : ℝ) / U.a N)) :=
        mul_le_mul_of_nonneg_right (by dsimp [A]; linarith) (Real.exp_nonneg _)
  calc qmass U K α y₀ N ω ≤ _ := qmass_le_at_height U K α y₀ N hN2 hKN h hh ω hω
    _ ≤ ((h : ℝ) / U.a N) * (A * Real.exp (b * ((h : ℝ) / U.a N))) :=
      mul_le_mul_of_nonneg_left hsum hr
    _ = _ := by ring

end IdlaCyl.QOnEc
