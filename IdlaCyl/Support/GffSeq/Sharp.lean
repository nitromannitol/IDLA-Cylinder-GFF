module

/-
Source: paper/idla-cylinder-gff.tex, tex:269-273,318-320,908-909.
The spectral normalization puts the paper's observation time below T^sharp
for all sufficiently large N.
-/
public import IdlaCyl.Support.QOnEc.Sharp
public import IdlaCyl.Definitions.ShapeEvent
public import IdlaCyl.Support.MixingLower
public import IdlaCyl.Support.Torus.Sequence

@[expose] public section

namespace IdlaCyl.GffSeq.QOnEc

open IdlaCyl.Defs IdlaCyl.QOnEc Filter
open scoped Topology

/-- Spectral normalization bounds `a_N` by a constant times `√τ_mix`. -/
theorem scale_le_sqrt_mixing (U : SequenceSetup) (γ : ℕ → ℝ)
    (hγ : U.GammaLimit γ 2) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ N in atTop,
      U.a N ≤ M * Real.sqrt (mixingTime (U.B N)) := by
  let M := |γ 2| + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hb : ∀ᶠ N in atTop,
      U.a N * Real.sqrt (2 * (1 - (U.S N).lam 2)) ≤ M := by
    have hlt : γ 2 < M := by dsimp [M]; linarith [le_abs_self (γ 2)]
    exact (hγ.eventually (gt_mem_nhds hlt)).mono fun _ h => h.le
  refine ⟨M, hM, ?_⟩
  filter_upwards [hb] with N hN
  have hg : 0 ≤ 2 * (1 - (U.S N).lam 2) := by
    have := (U.S N).lam_two_lt (U.B N).nontrivial
    linarith
  have hprod : 1 ≤ Real.sqrt (2 * (1 - (U.S N).lam 2)) *
      Real.sqrt (mixingTime (U.B N)) := by
    have hgap := mixing_gap_ge_one (U.B N) (U.S N)
    have heq : 2 * (mixingTime (U.B N) : ℝ) * (1 - (U.S N).lam 2) =
        (2 * (1 - (U.S N).lam 2)) * (mixingTime (U.B N) : ℝ) := by ring
    have hs := Real.sqrt_le_sqrt hgap
    rwa [Real.sqrt_one, heq, Real.sqrt_mul hg] at hs
  calc U.a N ≤ U.a N * (Real.sqrt (2 * (1 - (U.S N).lam 2)) *
        Real.sqrt (mixingTime (U.B N))) :=
      le_mul_of_one_le_right (U.a_pos N).le hprod
    _ = (U.a N * Real.sqrt (2 * (1 - (U.S N).lam 2))) *
        Real.sqrt (mixingTime (U.B N)) := (mul_assoc _ _ _).symm
    _ ≤ M * Real.sqrt (mixingTime (U.B N)) :=
      mul_le_mul_of_nonneg_right hN (Real.sqrt_nonneg _)

/-- At `T = N⌊y₀a_N⌋`, spectral normalization implies `T ≤ T^sharp` eventually. -/
theorem time_le_sharp_eventually (U : SequenceSetup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (γ : ℕ → ℝ) (hγ : U.GammaLimit γ 2) :
    ∀ᶠ N in atTop, (SequenceSetup.time U y₀ N : ℝ) ≤ sharp (U.B N) := by
  obtain ⟨M, hM, hb⟩ := scale_le_sqrt_mixing U γ hγ
  have hl : ∀ᶠ N : ℕ in atTop, max 1 (y₀ * M) ≤ Real.log ((U.B N).card : ℝ) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp U.card_tendsto)).eventually_ge_atTop _
  filter_upwards [hb, hl] with N hN hlog
  have hl1 : 1 ≤ Real.log ((U.B N).card : ℝ) := (le_max_left _ _).trans hlog
  have hly : y₀ * M ≤ Real.log ((U.B N).card : ℝ) := (le_max_right _ _).trans hlog
  have hlog2 : y₀ * M ≤ (Real.log ((U.B N).card : ℝ)) ^ 2 := by nlinarith
  have hf : (SequenceSetup.height U y₀ N : ℝ) ≤ y₀ * U.a N :=
    Nat.floor_le (mul_nonneg hy₀.le (U.a_pos N).le)
  have hh : (SequenceSetup.height U y₀ N : ℝ) ≤
      Real.sqrt (mixingTime (U.B N)) * (Real.log ((U.B N).card : ℝ)) ^ 2 := by
    calc (SequenceSetup.height U y₀ N : ℝ) ≤ y₀ * U.a N := hf
      _ ≤ y₀ * (M * Real.sqrt (mixingTime (U.B N))) :=
        mul_le_mul_of_nonneg_left hN hy₀.le
      _ = (y₀ * M) * Real.sqrt (mixingTime (U.B N)) := (mul_assoc _ _ _).symm
      _ ≤ (Real.log ((U.B N).card : ℝ)) ^ 2 * Real.sqrt (mixingTime (U.B N)) :=
        mul_le_mul_of_nonneg_right hlog2 (Real.sqrt_nonneg _)
      _ = _ := mul_comm _ _
  unfold SequenceSetup.time sharp
  rw [Nat.cast_mul]
  exact (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (U.B N).card)).trans_eq (mul_assoc _ _ _).symm

end IdlaCyl.GffSeq.QOnEc
