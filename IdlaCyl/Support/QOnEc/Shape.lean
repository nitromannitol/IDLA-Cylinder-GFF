/-
Source: paper/idla-cylinder-gff.tex, tex:908-911,931-938.
The literal shape event has a polynomially small complement at the paper's
observation time, uniformly over all sufficiently large width constants.
-/
import IdlaCyl.Support.QOnEc.Sharp
import IdlaCyl.Support.ShapeModerate
import IdlaCyl.Support.WnLimit

namespace IdlaCyl.QOnEc

open IdlaCyl.Defs Filter MeasureTheory
open scoped Topology

/-- Growth implies `log N / a_N → 0`. -/
theorem log_div_scale_tendsto_zero (U : Setup) (hgrowth : U.GrowthCondition) :
    Tendsto (fun N : ℕ => Real.log N / U.a N) atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgrowth ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hN)) (U.a_pos N).le
  · filter_upwards with N
    exact div_le_div_of_nonneg_right
      (le_add_of_nonneg_right (le_max_right (Real.log (U.a N)) 0)) (U.a_pos N).le

/-- The observation time eventually exceeds any fixed multiple of `N log N`. -/
theorem time_ge_log_eventually (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (hgrowth : U.GrowthCondition) (L : ℝ) :
    ∀ᶠ N in atTop, L * ((U.B N).card : ℝ) * Real.log ((U.B N).card : ℝ) ≤
      (time U y₀ N : ℝ) := by
  have hf : Tendsto (fun N => (height U y₀ N : ℝ) / U.a N) atTop (nhds y₀) :=
    (tendsto_nat_floor_mul_div_atTop hy₀.le).comp U.a_tendsto
  have hL : Tendsto (fun N : ℕ => L * (Real.log N / U.a N)) atTop (nhds 0) := by
    simpa only [mul_zero] using (log_div_scale_tendsto_zero U hgrowth).const_mul L
  have hh := hf.eventually (lt_mem_nhds (show y₀ / 2 < y₀ by linarith))
  have hl := hL.eventually (gt_mem_nhds (show (0 : ℝ) < y₀ / 2 by linarith))
  filter_upwards [hh, hl, eventually_ge_atTop (2 : ℕ)] with N hN hLN hN2
  have hle : L * Real.log N ≤ (height U y₀ N : ℝ) := by
    have hdiv : L * Real.log N / U.a N ≤ (height U y₀ N : ℝ) / U.a N := by
      rw [mul_div_assoc]
      exact hLN.le.trans hN.le
    exact (div_le_div_iff_of_pos_right (U.a_pos N)).mp hdiv
  unfold time
  rw [Nat.cast_mul, U.card_eq N hN2]
  calc L * (N : ℝ) * Real.log N = (N : ℝ) * (L * Real.log N) := by ring
    _ ≤ (N : ℝ) * (height U y₀ N : ℝ) :=
      mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg N)

/-- Enlarging the width enlarges the shape event. -/
theorem eventAt_mono (B : Base) (T : ℕ) {d e : ℝ} (hde : d ≤ e) :
    eventAt B T d ⊆ eventAt B T e := by
  intro ω hω
  refine ⟨?_, hω.2.trans (R_mono (add_le_add_right hde _))⟩
  have hf := Int.floor_mono (sub_le_sub_left hde ((T : ℝ) / (B.card : ℝ)))
  exact (R_mono (by exact_mod_cast hf)).trans hω.1

/-- Below `T^sharp`, a suitable multiple of the printed width dominates the
moderate-time width. -/
theorem innerWidth_le_delta (B : Base) (T : ℕ) (hT : (T : ℝ) ≤ sharp B)
    (ν D C : ℝ) (hD : 0 ≤ D)
    (hC : D * (2 * Real.sqrt (ν + 4)) ≤ C) :
    D * innerWidth ν B.card T ≤ delta B C T := by
  unfold innerWidth delta
  rw [min_eq_left hT]
  have hs := Real.sqrt_nonneg (((T : ℝ) / (B.card : ℝ)) *
    (Real.log (B.card : ℝ) + logPlus ((T : ℝ) / (B.card : ℝ))))
  have hcoef : 0 ≤ D * (2 * Real.sqrt (ν + 4)) := mul_nonneg hD (by positivity)
  calc D * ((2 * Real.sqrt (ν + 4)) * _) =
        (D * (2 * Real.sqrt (ν + 4))) * _ := (mul_assoc _ _ _).symm
    _ ≤ C * _ := mul_le_mul_of_nonneg_right hC hs
    _ ≤ C * max (Real.log (B.card : ℝ)) _ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (hcoef.trans hC)

/-- The good event has failure probability at most `N^{-ν}` eventually for
all sufficiently large choices of its width constant. -/
theorem shape_compl_le_eventually (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (γ : ℕ → ℝ) (hγ : U.GammaLimit γ 2) (hgrowth : U.GrowthCondition)
    (ν : ℝ) (hν : 0 < ν) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ᶠ N in atTop,
      idlaMeasure (U.B N) (shape U C y₀ N)ᶜ ≤ ENNReal.ofReal ((N : ℝ) ^ (-ν)) := by
  obtain ⟨D, L, hD, -, N₀, hb⟩ := shape_moderate ν hν
  refine ⟨D * (2 * Real.sqrt (ν + 4)), mul_pos hD (mul_pos (by norm_num)
    (Real.sqrt_pos.mpr (by linarith))), ?_⟩
  intro C hC
  filter_upwards [time_le_sharp_eventually U y₀ hy₀ γ hγ,
    time_ge_log_eventually U y₀ hy₀ hgrowth L,
    eventually_ge_atTop (max N₀ 2)] with N ht htime hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hcard : (U.B N).card = N := U.card_eq N hN2
  have hNN : N₀ ≤ (U.B N).card := by rw [hcard]; exact (le_max_left _ _).trans hN
  have hwidth := innerWidth_le_delta (U.B N) (time U y₀ N) ht ν D C hD.le hC
  have hsub : (shape U C y₀ N)ᶜ ⊆
      (eventAt (U.B N) (time U y₀ N) (D * innerWidth ν (U.B N).card (time U y₀ N)))ᶜ :=
    Set.compl_subset_compl.mpr (eventAt_mono (U.B N) (time U y₀ N) hwidth)
  have h := (measure_mono hsub).trans (hb (U.B N) hNN (time U y₀ N) htime)
  rwa [hcard] at h

end IdlaCyl.QOnEc
