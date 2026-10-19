/-
The quadratic-mass comparison of `clm:Q-W` at the paper's time, on the good event
of `eq:fluct` (`paper/idla-cylinder-gff.tex:1003-1009`, with the good event at
`:908-909` and the width at `:273`).

The printed lemma: there is a constant `C > 0`, depending on `(α_k)_k` and `y₀`
but not on `N`, such that `|Q_N - W_N| 1_E ≤ C Δ_N/a_N`, and `C Δ_N/a_N → 0`.
The Lean statement takes the width constant as an input `C`, and returns the
printed constant as `A`; the bound holds for all large `N`, and the right-hand
side tends to zero.
-/
import IdlaCyl.Definitions.ShapeEvent
import IdlaCyl.Support.ClmQWFinal
import IdlaCyl.Support.HarmonicExtension
import IdlaCyl.Support.PsiSlab
import IdlaCyl.Support.SpectralLimit

namespace IdlaCyl.Frozen

open IdlaCyl.Defs Filter

private theorem clm_q_w_v2_R_floor (B : Base) (x : ℝ) :
    R B ((⌊x⌋ : ℤ) : ℝ) = R B x := by
  ext p
  change ((p.2 : ℤ) : ℝ) ≤ ((⌊x⌋ : ℤ) : ℝ) ↔ ((p.2 : ℤ) : ℝ) ≤ x
  constructor
  · intro h
    exact h.trans (Int.floor_le x)
  · intro h
    exact_mod_cast Int.le_floor.mpr h

private theorem clm_q_w_v2_shape_eq (B : Base) (T : ℕ) (d : ℝ) :
    eventAt B T d = goodEvent B T d := by
  unfold eventAt goodEvent
  simp only [clm_q_w_v2_R_floor]

private theorem clm_q_w_v2_harmAt_eq (B : Base) (S : SpectralData B) (a : ℝ) (h : ℤ)
    (K : ℕ) (α : ℕ → ℝ → ℝ) (hK : K ≤ B.card) :
    harmAt B S a h K α = psiExt B S h (psiCoeff K α a h) := by
  rw [psiExt_psiCoeff_eq_modeSumPsi B S h K α hK a]
  funext p
  simp only [harmAt, modeSumPsi, exponentialMode, mul_assoc]

private theorem clm_q_w_v2_center (U : Setup) (y₀ : ℝ) (N : ℕ) (hN : 2 ≤ N) :
    (time U y₀ N : ℝ) / ((U.B N).card : ℝ) = ((height U y₀ N : ℤ) : ℝ) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  unfold time
  rw [U.card_eq N hN]
  push_cast
  exact mul_div_cancel_left₀ _ hN0

private theorem clm_q_w_v2_width_eq (U : Setup) (C y₀ : ℝ) (N : ℕ) (hN : 2 ≤ N) :
    width U C y₀ N = C * max (Real.log N)
      (Real.sqrt ((min (time U y₀ N : ℝ) (sharp (U.B N)) / N) *
        (Real.log N + logPlus ((time U y₀ N : ℝ) / N)))) := by
  unfold width delta
  rw [U.card_eq N hN]

private theorem clm_q_w_v2_logPlus_nonneg (x : ℝ) : 0 ≤ logPlus x := by
  unfold logPlus
  exact le_max_right _ _

private theorem clm_q_w_v2_logPlus_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    logPlus x ≤ logPlus y := by
  unfold logPlus
  rcases hx.eq_or_lt with h0 | hpos
  · rw [← h0, Real.log_zero]
    exact max_le (le_max_right _ _) (le_max_right _ _)
  · exact max_le_max (Real.log_le_log hpos hxy) le_rfl

private theorem clm_q_w_v2_logPlus_mul_le {y a : ℝ} (hy : 0 < y) (ha : 0 < a) :
    logPlus (y * a) ≤ logPlus y + logPlus a := by
  unfold logPlus
  rw [Real.log_mul hy.ne' ha.ne']
  have h1 := le_max_left (Real.log y) 0
  have h2 := le_max_left (Real.log a) 0
  have h3 := le_max_right (Real.log y) 0
  have h4 := le_max_right (Real.log a) 0
  exact max_le (by linarith) (by linarith)

/-- The width, divided by `a_N`, is bounded by a quantity tending to zero. -/
private theorem clm_q_w_v2_width_div_le (U : Setup) (y₀ C : ℝ) (hy₀ : 0 < y₀)
    (hC : 0 < C) (N : ℕ) (hN : 2 ≤ N) :
    width U C y₀ N / U.a N ≤
      C * ((Real.log N + logPlus (U.a N)) / U.a N +
        Real.sqrt (y₀ * ((Real.log N + logPlus (U.a N)) / U.a N + logPlus y₀ / U.a N))) := by
  rw [clm_q_w_v2_width_eq U C y₀ N hN]
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN0 : (N : ℝ) ≠ 0 := hNr.ne'
  have ha : 0 < U.a N := U.a_pos N
  have ha0 : U.a N ≠ 0 := ha.ne'
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hT0 : (0 : ℝ) ≤ (time U y₀ N : ℝ) := Nat.cast_nonneg _
  have hTN : (time U y₀ N : ℝ) / N = (height U y₀ N : ℝ) := by
    have h := clm_q_w_v2_center U y₀ N hN
    rw [U.card_eq N hN, Int.cast_natCast] at h
    exact h
  have hTNle : (time U y₀ N : ℝ) / N ≤ y₀ * U.a N := by
    rw [hTN]
    exact Nat.floor_le (mul_nonneg hy₀.le ha.le)
  have hTN0 : 0 ≤ (time U y₀ N : ℝ) / N := div_nonneg hT0 hNr.le
  have hm1 : min (time U y₀ N : ℝ) (sharp (U.B N)) / N ≤ y₀ * U.a N :=
    (div_le_div_of_nonneg_right (min_le_left _ _) hNr.le).trans hTNle
  have hlp : logPlus ((time U y₀ N : ℝ) / N) ≤ logPlus y₀ + logPlus (U.a N) :=
    (clm_q_w_v2_logPlus_mono hTN0 hTNle).trans (clm_q_w_v2_logPlus_mul_le hy₀ ha)
  have hlp0 : 0 ≤ logPlus ((time U y₀ N : ℝ) / N) := clm_q_w_v2_logPlus_nonneg _
  have hX : min (time U y₀ N : ℝ) (sharp (U.B N)) / N *
      (Real.log N + logPlus ((time U y₀ N : ℝ) / N))
      ≤ U.a N ^ 2 * (y₀ * ((Real.log N + logPlus (U.a N)) / U.a N + logPlus y₀ / U.a N)) := by
    have h1 : min (time U y₀ N : ℝ) (sharp (U.B N)) / N *
        (Real.log N + logPlus ((time U y₀ N : ℝ) / N))
        ≤ y₀ * U.a N * (Real.log N + (logPlus y₀ + logPlus (U.a N))) :=
      mul_le_mul hm1 (by linarith) (by linarith) (mul_nonneg hy₀.le ha.le)
    have h2 : y₀ * U.a N * (Real.log N + (logPlus y₀ + logPlus (U.a N)))
        = U.a N ^ 2 * (y₀ * ((Real.log N + logPlus (U.a N)) / U.a N + logPlus y₀ / U.a N)) := by
      field_simp
      ring
    rw [h2] at h1
    exact h1
  have hsq : Real.sqrt (min (time U y₀ N : ℝ) (sharp (U.B N)) / N *
      (Real.log N + logPlus ((time U y₀ N : ℝ) / N)))
      ≤ U.a N * Real.sqrt (y₀ * ((Real.log N + logPlus (U.a N)) / U.a N + logPlus y₀ / U.a N)) := by
    calc Real.sqrt (min (time U y₀ N : ℝ) (sharp (U.B N)) / N *
          (Real.log N + logPlus ((time U y₀ N : ℝ) / N)))
        ≤ Real.sqrt (U.a N ^ 2 *
            (y₀ * ((Real.log N + logPlus (U.a N)) / U.a N + logPlus y₀ / U.a N))) :=
          Real.sqrt_le_sqrt hX
      _ = Real.sqrt (U.a N ^ 2) *
            Real.sqrt (y₀ * ((Real.log N + logPlus (U.a N)) / U.a N + logPlus y₀ / U.a N)) :=
          Real.sqrt_mul (sq_nonneg _) _
      _ = U.a N * Real.sqrt (y₀ * ((Real.log N + logPlus (U.a N)) / U.a N + logPlus y₀ / U.a N)) := by
          rw [Real.sqrt_sq ha.le]
  have hnn : 0 ≤ U.a N * Real.sqrt (y₀ * ((Real.log N + logPlus (U.a N)) / U.a N + logPlus y₀ / U.a N)) :=
    mul_nonneg ha.le (Real.sqrt_nonneg _)
  have hmax : max (Real.log N) (Real.sqrt (min (time U y₀ N : ℝ) (sharp (U.B N)) / N *
      (Real.log N + logPlus ((time U y₀ N : ℝ) / N))))
      ≤ Real.log N + U.a N * Real.sqrt (y₀ * ((Real.log N + logPlus (U.a N)) / U.a N + logPlus y₀ / U.a N)) :=
    max_le (by linarith) (by linarith)
  have hL' : Real.log N ≤ Real.log N + logPlus (U.a N) := by
    linarith [clm_q_w_v2_logPlus_nonneg (U.a N)]
  calc C * max (Real.log N) (Real.sqrt (min (time U y₀ N : ℝ) (sharp (U.B N)) / N *
          (Real.log N + logPlus ((time U y₀ N : ℝ) / N)))) / U.a N
      ≤ C * (Real.log N + U.a N * Real.sqrt (y₀ * ((Real.log N + logPlus (U.a N)) / U.a N +
          logPlus y₀ / U.a N))) / U.a N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hC.le) ha.le
    _ = C * (Real.log N / U.a N + Real.sqrt (y₀ * ((Real.log N + logPlus (U.a N)) / U.a N +
          logPlus y₀ / U.a N))) := by
        field_simp
    _ ≤ C * ((Real.log N + logPlus (U.a N)) / U.a N + Real.sqrt (y₀ *
          ((Real.log N + logPlus (U.a N)) / U.a N + logPlus y₀ / U.a N))) := by
        refine mul_le_mul_of_nonneg_left ?_ hC.le
        linarith [div_le_div_of_nonneg_right hL' ha.le]

-- FROZEN-STATEMENT-BEGIN
theorem clm_q_w_v2 (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K)
    (hgrowth : U.GrowthCondition) (C : ℝ) (hC : 0 < C) :
    ∃ A : ℝ, 0 < A ∧
      (∀ᶠ N in atTop, ∀ ω : TrajSeq (U.B N),
        |qmass U K α y₀ N ω - wmass U K α y₀ N| *
          (shape U C y₀ N).indicator (fun _ => (1 : ℝ)) ω ≤
            A * width U C y₀ N / U.a N) ∧
      Tendsto (fun N => A * width U C y₀ N / U.a N) atTop (nhds 0)
-- FROZEN-STATEMENT-END
  := by
  have _ := hK
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = ∑ k ∈ Finset.Icc 2 K, (α k y₀ ^ 2 + 1) * 2 :=
    ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := by
    rw [hC']
    exact Finset.sum_nonneg fun k _ => by positivity
  -- the width is eventually at least `1/2`
  have hΔE : ∀ᶠ N in atTop, 1 / 2 ≤ width U C y₀ N := by
    have hlog : ∀ᶠ N : ℕ in atTop, 1 / (2 * C) ≤ Real.log N :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
    filter_upwards [hlog, eventually_ge_atTop (2 : ℕ)] with N hlogN hN
    have hw : C * Real.log N ≤ width U C y₀ N := by
      rw [clm_q_w_v2_width_eq U C y₀ N hN]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) hC.le
    have h1 : C * (1 / (2 * C)) ≤ C * Real.log N := mul_le_mul_of_nonneg_left hlogN hC.le
    have hC0 : C ≠ 0 := hC.ne'
    have h2 : C * (1 / (2 * C)) = 1 / 2 := by
      field_simp
    linarith
  -- the growth condition gives `log N / a_N → 0` and `log_+ y₀ / a_N → 0`
  have hu : Tendsto (fun N : ℕ => (Real.log N + logPlus (U.a N)) / U.a N) atTop (nhds 0) :=
    hgrowth
  have hv : Tendsto (fun N : ℕ => logPlus y₀ / U.a N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop U.a_tendsto
  have hg : Tendsto (fun N : ℕ => C * ((Real.log N + logPlus (U.a N)) / U.a N +
      Real.sqrt (y₀ * ((Real.log N + logPlus (U.a N)) / U.a N + logPlus y₀ / U.a N))))
      atTop (nhds 0) := by
    have h := (hu.add ((hu.add hv).const_mul y₀).sqrt).const_mul C
    have h0 : C * (0 + Real.sqrt (y₀ * (0 + 0))) = 0 := by simp
    rw [h0] at h
    exact h
  have hwa : Tendsto (fun N => width U C y₀ N / U.a N) atTop (nhds 0) := by
    have hwnn : ∀ᶠ N in atTop, 0 ≤ width U C y₀ N / U.a N := by
      filter_upwards [hΔE] with N hN
      exact div_nonneg (by linarith) (U.a_pos N).le
    have hle : ∀ᶠ N in atTop, width U C y₀ N / U.a N ≤
        C * ((Real.log N + logPlus (U.a N)) / U.a N +
          Real.sqrt (y₀ * ((Real.log N + logPlus (U.a N)) / U.a N + logPlus y₀ / U.a N))) := by
      filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
      exact clm_q_w_v2_width_div_le U y₀ C hy₀ hC N hN
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg hwnn hle
  -- the coefficients `α_k(h/a_N)` are eventually at most `α_k(y₀)² + 1`
  have hcont : ∀ k, 2 ≤ k → k ≤ K → ContinuousAt (α k) y₀ := fun k hk1 hk2 => by
    obtain ⟨s, hs, hd, -⟩ := hα k hk1 hk2
    exact (hd y₀ (mem_of_mem_nhds hs)).continuousAt
  have hfloor : Tendsto (fun N => (height U y₀ N : ℝ) / U.a N) atTop (nhds y₀) := by
    unfold height
    exact (tendsto_nat_floor_mul_div_atTop hy₀.le).comp U.a_tendsto
  have hcoef : ∀ k ∈ Finset.Icc 2 K, ∀ᶠ N in atTop,
      α k ((height U y₀ N : ℝ) / U.a N) ^ 2 ≤ α k y₀ ^ 2 + 1 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have ht : Tendsto (fun N => α k ((height U y₀ N : ℝ) / U.a N) ^ 2) atTop
        (nhds (α k y₀ ^ 2)) :=
      ((hcont k hk.1 hk.2).tendsto.comp hfloor).pow 2
    filter_upwards [ht.eventually (gt_mem_nhds (show α k y₀ ^ 2 < α k y₀ ^ 2 + 1 by linarith))]
      with N hN
    exact hN.le
  -- the modes `exp(2 q_k Δ_N)` are eventually at most `2`
  have hexp : ∀ k ∈ Finset.Icc 2 K, ∀ᶠ N in atTop,
      Real.exp (2 * (U.S N).qk k * width U C y₀ N) < 2 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hq := U.qkN_tendsto γ K hspec k hk.1 hk.2
    have hprod : Tendsto (fun N => 2 * (U.a N * (U.S N).qk k) * (width U C y₀ N / U.a N))
        atTop (nhds (2 * γ k * 0)) :=
      (hq.const_mul 2).mul hwa
    rw [mul_zero] at hprod
    have h2 : Tendsto (fun N => 2 * (U.S N).qk k * width U C y₀ N) atTop (nhds 0) := by
      refine hprod.congr fun N => ?_
      have ha := (U.a_pos N).ne'
      field_simp
    have h3 := (Real.continuous_exp.tendsto 0).comp h2
    have hlt : Real.exp 0 < 2 := by
      rw [Real.exp_zero]
      norm_num
    filter_upwards [h3.eventually (gt_mem_nhds hlt)] with N hN
    exact hN
  have hterm : ∀ k ∈ Finset.Icc 2 K, ∀ᶠ N in atTop,
      α k ((height U y₀ N : ℝ) / U.a N) ^ 2 * Real.exp (2 * (U.S N).qk k * width U C y₀ N)
        ≤ (α k y₀ ^ 2 + 1) * 2 := by
    intro k hk
    filter_upwards [hcoef k hk, hexp k hk] with N h1 h2
    exact mul_le_mul h1 h2.le (Real.exp_nonneg _) (by positivity)
  have hsumE : ∀ᶠ N in atTop, ∀ k ∈ Finset.Icc 2 K,
      α k ((height U y₀ N : ℝ) / U.a N) ^ 2 * Real.exp (2 * (U.S N).qk k * width U C y₀ N)
        ≤ (α k y₀ ^ 2 + 1) * 2 :=
    (Filter.eventually_all_finset _).2 hterm
  refine ⟨4 * C' + 1, by linarith, ?_, ?_⟩
  · filter_upwards [hΔE, eventually_ge_atTop (2 : ℕ), eventually_ge_atTop K, hsumE]
      with N hΔN hN2 hKN hsN
    intro ω
    have hc : (U.B N).card = N := U.card_eq N hN2
    have hKc : K ≤ (U.B N).card := by
      rw [hc]
      exact hKN
    have hpsi : psi U K α y₀ N =
        psiExt (U.B N) (U.S N) (height U y₀ N : ℤ)
          (psiCoeff K α (U.a N) (height U y₀ N : ℤ)) := by
      unfold psi
      exact clm_q_w_v2_harmAt_eq _ _ _ _ _ _ hKc
    have hqm : qmass U K α y₀ N ω = QN (U.B N) (fun _ => U.a N) (time U y₀ N)
        (psiExt (U.B N) (U.S N) (height U y₀ N : ℤ)
          (psiCoeff K α (U.a N) (height U y₀ N : ℤ))) ω := by
      simp only [qmass, QN]
      rw [hc, hpsi]
    have hwm : wmass U K α y₀ N = WN (U.B N) (fun _ => U.a N) (time U y₀ N)
        (psiExt (U.B N) (U.S N) (height U y₀ N : ℤ)
          (psiCoeff K α (U.a N) (height U y₀ N : ℤ))) ω := by
      simp only [wmass, WN]
      rw [hc, hpsi]
    have hshape : shape U C y₀ N = goodEvent (U.B N) (time U y₀ N) (width U C y₀ N) :=
      clm_q_w_v2_shape_eq (U.B N) (time U y₀ N) (width U C y₀ N)
    have hsum : ∑ k ∈ Finset.Icc 2 K, α k (((height U y₀ N : ℤ) : ℝ) / U.a N) ^ 2 *
        Real.exp (2 * (U.S N).qk k * width U C y₀ N) ≤ C' := by
      rw [hC']
      refine Finset.sum_le_sum fun k hk => ?_
      rw [Int.cast_natCast]
      exact hsN k hk
    rw [hqm, hwm, hshape]
    by_cases hω : ω ∈ goodEvent (U.B N) (time U y₀ N) (width U C y₀ N)
    · have hb := clm_q_w_final_le (U.B N) (fun _ => U.a N) (U.a_pos N).le (U.S N)
        (height U y₀ N : ℤ) K α hKc (time U y₀ N) (width U C y₀ N) hΔN
        (clm_q_w_v2_center U y₀ N hN2) C' hC'0 hsum ω hω
      rw [Set.indicator_of_mem hω, mul_one]
      have key : 4 * C' * (width U C y₀ N / U.a N) ≤
          (4 * C' + 1) * width U C y₀ N / U.a N := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (by linarith)
          (div_nonneg (by linarith) (U.a_pos N).le)
      exact hb.trans key
    · rw [Set.indicator_of_notMem hω, mul_zero]
      exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (U.a_pos N).le
  · have h := hwa.const_mul (4 * C' + 1)
    rw [mul_zero] at h
    refine h.congr fun N => ?_
    exact (mul_div_assoc _ _ _).symm

/-- Nonvacuity: the good event is a well-typed set of trajectories at each `N`. -/
example (U : Setup) (C y₀ : ℝ) (N : ℕ) : Set (TrajSeq (U.B N)) :=
  shape U C y₀ N

/-- Nonvacuity: the existence statement applies at the width constant `C = 1`. -/
example (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀) (K : ℕ) (hK : 2 ≤ K)
    (α : ℕ → ℝ → ℝ) (hα : regular α K y₀) (γ : ℕ → ℝ)
    (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    ∃ A : ℝ, 0 < A := by
  obtain ⟨A, hA, -, -⟩ := clm_q_w_v2 U y₀ hy₀ K hK α hα γ hspec hgrowth 1 one_pos
  exact ⟨A, hA⟩

end IdlaCyl.Frozen
