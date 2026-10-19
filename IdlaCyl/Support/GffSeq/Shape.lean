/-
Source: paper/idla-cylinder-gff.tex, tex:908-911,931-938.
The literal shape event has a polynomially small complement at the paper's
observation time, uniformly over all sufficiently large width constants.
-/
import IdlaCyl.Support.QOnEc.Shape
import IdlaCyl.Support.QOnEc.Sharp
import IdlaCyl.Support.ShapeModerate
import IdlaCyl.Support.WnLimit
import IdlaCyl.Support.GffSeq.Sharp
import IdlaCyl.Support.Torus.Sequence

namespace IdlaCyl.GffSeq.QOnEc

open IdlaCyl.Defs IdlaCyl.QOnEc Filter MeasureTheory
open scoped Topology

/-- Growth implies `log N / a_N → 0`. -/
theorem log_div_scale_tendsto_zero (U : SequenceSetup) (hgrowth : U.GrowthCondition) :
    Tendsto (fun N : ℕ => Real.log ((U.B N).card : ℝ) / U.a N) atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgrowth ?_ ?_
  · filter_upwards with N
    have hN : 1 ≤ (U.B N).card := Nat.one_le_of_lt (U.card_pos N)
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hN)) (U.a_pos N).le
  · filter_upwards with N
    exact div_le_div_of_nonneg_right
      (le_add_of_nonneg_right (le_max_right (Real.log (U.a N)) 0)) (U.a_pos N).le

/-- The observation time eventually exceeds any fixed multiple of `N log N`. -/
theorem time_ge_log_eventually (U : SequenceSetup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (hgrowth : U.GrowthCondition) (L : ℝ) :
    ∀ᶠ N in atTop, L * ((U.B N).card : ℝ) * Real.log ((U.B N).card : ℝ) ≤
      (SequenceSetup.time U y₀ N : ℝ) := by
  have hf : Tendsto (fun N => (SequenceSetup.height U y₀ N : ℝ) / U.a N) atTop (nhds y₀) :=
    (tendsto_nat_floor_mul_div_atTop hy₀.le).comp U.a_tendsto
  have hL : Tendsto (fun N : ℕ => L * (Real.log ((U.B N).card : ℝ) / U.a N)) atTop (nhds 0) := by
    simpa only [mul_zero] using (log_div_scale_tendsto_zero U hgrowth).const_mul L
  have hh := hf.eventually (lt_mem_nhds (show y₀ / 2 < y₀ by linarith))
  have hl := hL.eventually (gt_mem_nhds (show (0 : ℝ) < y₀ / 2 by linarith))
  filter_upwards [hh, hl] with N hN hLN
  have hle : L * Real.log ((U.B N).card : ℝ) ≤ (SequenceSetup.height U y₀ N : ℝ) := by
    have hdiv : L * Real.log ((U.B N).card : ℝ) / U.a N ≤ (SequenceSetup.height U y₀ N : ℝ) / U.a N := by
      rw [mul_div_assoc]
      exact hLN.le.trans hN.le
    exact (div_le_div_iff_of_pos_right (U.a_pos N)).mp hdiv
  unfold SequenceSetup.time
  rw [Nat.cast_mul]
  calc L * ((U.B N).card : ℝ) * Real.log ((U.B N).card : ℝ) = ((U.B N).card : ℝ) * (L * Real.log ((U.B N).card : ℝ)) := by ring
    _ ≤ ((U.B N).card : ℝ) * (SequenceSetup.height U y₀ N : ℝ) :=
      mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg (U.B N).card)

/-- The good event has failure probability at most `N^{-ν}` eventually for
all sufficiently large choices of its width constant. -/
theorem shape_compl_le_eventually (U : SequenceSetup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (γ : ℕ → ℝ) (hγ : U.GammaLimit γ 2) (hgrowth : U.GrowthCondition)
    (ν : ℝ) (hν : 0 < ν) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ᶠ N in atTop,
      idlaMeasure (U.B N) (SequenceSetup.shape U C y₀ N)ᶜ ≤ ENNReal.ofReal (((U.B N).card : ℝ) ^ (-ν)) := by
  obtain ⟨D, L, hD, -, N₀, hb⟩ := shape_moderate ν hν
  refine ⟨D * (2 * Real.sqrt (ν + 4)), mul_pos hD (mul_pos (by norm_num)
    (Real.sqrt_pos.mpr (by linarith))), ?_⟩
  intro C hC
  filter_upwards [time_le_sharp_eventually U y₀ hy₀ γ hγ,
    time_ge_log_eventually U y₀ hy₀ hgrowth L,
    U.eventually_modes N₀] with N ht htime hN
  have hNN := hN
  have hwidth := innerWidth_le_delta (U.B N) (SequenceSetup.time U y₀ N) ht ν D C hD.le hC
  have hsub : (SequenceSetup.shape U C y₀ N)ᶜ ⊆
      (eventAt (U.B N) (SequenceSetup.time U y₀ N) (D * innerWidth ν (U.B N).card (SequenceSetup.time U y₀ N)))ᶜ :=
    Set.compl_subset_compl.mpr (eventAt_mono (U.B N) (SequenceSetup.time U y₀ N) hwidth)
  have h := (measure_mono hsub).trans (hb (U.B N) hNN (SequenceSetup.time U y₀ N) htime)
  exact h

end IdlaCyl.GffSeq.QOnEc
