module

/-
The order of the width `Δ_N` at the paper's time `T = N ⌊y₀ a_N⌋`.

The width is `delta` of `ShapeEvent.lean` at `time U y₀ N` (`tex:273`, `tex:335`).
The order bound `Δ_N = O(√(a_N(log N + log₊ a_N)))` is stated at `tex:878-879`
and `tex:908`.  The two results here supply the `horder` and `hd` hypotheses of
`le_replace_v2`.
-/
public import IdlaCyl.Definitions.ShapeEvent
public import IdlaCyl.Support.Torus.Sequence

@[expose] public section

namespace IdlaCyl.GffSeq

open IdlaCyl.Defs Filter

/-- `log₊ s` is nonnegative. -/
private theorem widthOrder_logPlus_nonneg (s : ℝ) : 0 ≤ logPlus s :=
  le_max_right _ _

/-- `log₊ 0 = 0`. -/
private theorem widthOrder_logPlus_zero : logPlus 0 = 0 := by
  simp [logPlus]

/-- `log₊ h ≤ log₊ y + log₊ a` for `0 ≤ h ≤ y a` with `y, a > 0`. -/
private theorem widthOrder_logPlus_le {y a h : ℝ} (hy : 0 < y) (ha : 0 < a)
    (h0 : 0 ≤ h) (hh : h ≤ y * a) :
    logPlus h ≤ logPlus y + logPlus a := by
  have hL : 0 ≤ logPlus y + logPlus a :=
    add_nonneg (widthOrder_logPlus_nonneg y) (widthOrder_logPlus_nonneg a)
  rcases eq_or_lt_of_le h0 with h00 | hpos
  · rw [← h00, widthOrder_logPlus_zero]
    exact hL
  · have hlog : Real.log h ≤ Real.log y + Real.log a := by
      rw [← Real.log_mul hy.ne' ha.ne']
      exact Real.log_le_log hpos hh
    have hly : Real.log y ≤ logPlus y := le_max_left _ _
    have hla : Real.log a ≤ logPlus a := le_max_left _ _
    show max (Real.log h) 0 ≤ logPlus y + logPlus a
    exact max_le (by linarith) hL

/-- The width is positive: `log N ≥ log 2 > 0` by `Base.nontrivial`, and the maximum in
`delta` is at least `log N`. -/
theorem width_pos (U : SequenceSetup) (y₀ C : ℝ) (hC : 0 < C) (N : ℕ) : 0 < SequenceSetup.width U C y₀ N := by
  have h2n : 2 ≤ (U.B N).card := (U.B N).nontrivial
  have h2 : (2 : ℝ) ≤ ((U.B N).card : ℝ) := by exact_mod_cast h2n
  have hlog : 0 < Real.log ((U.B N).card : ℝ) := Real.log_pos (by linarith)
  unfold SequenceSetup.width delta
  exact mul_pos hC (lt_of_lt_of_le hlog (le_max_left _ _))

/-- The width is `O(√(a_N(log N + log₊ a_N)))` with constant `C · max{1, √(2y₀)}`.  The
square-root branch of `delta` is at most `√(2y₀)` times the target, and the logarithmic
branch is at most the target because the growth condition gives `log N ≤ a_N` eventually. -/
theorem width_le_order (U : SequenceSetup) (y₀ : ℝ) (hy₀ : 0 < y₀) (hgrowth : U.GrowthCondition)
    (C : ℝ) (hC : 0 < C) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ᶠ N in atTop,
      SequenceSetup.width U C y₀ N ≤ C' * Real.sqrt (U.a N * (Real.log ((U.B N).card : ℝ) + logPlus (U.a N))) := by
  have hM : 0 < max 1 (Real.sqrt (2 * y₀)) := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨C * max 1 (Real.sqrt (2 * y₀)), mul_pos hC hM, ?_⟩
  have hg : Tendsto (fun N : ℕ => (Real.log ((U.B N).card : ℝ) + logPlus (U.a N)) / U.a N)
      atTop (nhds 0) := hgrowth
  have hgr : ∀ᶠ N : ℕ in atTop, (Real.log ((U.B N).card : ℝ) + logPlus (U.a N)) / U.a N < 1 :=
    hg.eventually (gt_mem_nhds one_pos)
  have hlogN : ∀ᶠ N : ℕ in atTop, logPlus y₀ ≤ Real.log ((U.B N).card : ℝ) :=
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp U.card_tendsto)).eventually_ge_atTop (logPlus y₀)
  filter_upwards [hgr, hlogN] with N hgrN hlN
  have hNr : (2 : ℝ) ≤ (U.B N).card := by exact_mod_cast (U.B N).nontrivial
  have hNpos : (0 : ℝ) < (U.B N).card := by linarith
  have haN : 0 < U.a N := U.a_pos N
  have hlog0 : 0 ≤ Real.log ((U.B N).card : ℝ) := Real.log_nonneg (by linarith)
  have hh_le : (SequenceSetup.height U y₀ N : ℝ) ≤ y₀ * U.a N := by
    unfold SequenceSetup.height
    exact Nat.floor_le (mul_nonneg hy₀.le haN.le)
  have hTn : (SequenceSetup.time U y₀ N : ℝ) / ((U.B N).card : ℝ) = (SequenceSetup.height U y₀ N : ℝ) :=
    U.time_div_card y₀ N
  have hT : (SequenceSetup.time U y₀ N : ℝ) / ((U.B N).card : ℝ) ≤ y₀ * U.a N := by
    rw [hTn]
    exact hh_le
  have hp : min (SequenceSetup.time U y₀ N : ℝ) (sharp (U.B N)) / ((U.B N).card : ℝ) ≤ y₀ * U.a N :=
    (div_le_div_of_nonneg_right (min_le_left _ _) hNpos.le).trans hT
  have hq : Real.log ((U.B N).card : ℝ) + logPlus (SequenceSetup.height U y₀ N : ℝ) ≤
      2 * (Real.log ((U.B N).card : ℝ) + logPlus (U.a N)) := by
    have h1 := widthOrder_logPlus_le hy₀ haN (Nat.cast_nonneg _) hh_le
    linarith [widthOrder_logPlus_nonneg (U.a N)]
  have hX : min (SequenceSetup.time U y₀ N : ℝ) (sharp (U.B N)) / ((U.B N).card : ℝ) *
      (Real.log ((U.B N).card : ℝ) + logPlus ((SequenceSetup.time U y₀ N : ℝ) / ((U.B N).card : ℝ))) ≤
      2 * y₀ * (U.a N * (Real.log ((U.B N).card : ℝ) + logPlus (U.a N))) := by
    rw [hTn]
    have hq0 : 0 ≤ Real.log ((U.B N).card : ℝ) + logPlus (SequenceSetup.height U y₀ N : ℝ) :=
      add_nonneg hlog0 (widthOrder_logPlus_nonneg _)
    calc min (SequenceSetup.time U y₀ N : ℝ) (sharp (U.B N)) / ((U.B N).card : ℝ) *
          (Real.log ((U.B N).card : ℝ) + logPlus (SequenceSetup.height U y₀ N : ℝ))
        ≤ (y₀ * U.a N) * (Real.log ((U.B N).card : ℝ) + logPlus (SequenceSetup.height U y₀ N : ℝ)) :=
          mul_le_mul_of_nonneg_right hp hq0
      _ ≤ (y₀ * U.a N) * (2 * (Real.log ((U.B N).card : ℝ) + logPlus (U.a N))) :=
          mul_le_mul_of_nonneg_left hq (mul_nonneg hy₀.le haN.le)
      _ = 2 * y₀ * (U.a N * (Real.log ((U.B N).card : ℝ) + logPlus (U.a N))) := by ring
  have hS0 : 0 ≤ Real.sqrt (U.a N * (Real.log ((U.B N).card : ℝ) + logPlus (U.a N))) :=
    Real.sqrt_nonneg _
  have hlt : Real.log ((U.B N).card : ℝ) + logPlus (U.a N) < U.a N := (div_lt_one haN).mp hgrN
  have hlogle : Real.log ((U.B N).card : ℝ) ≤ U.a N := by
    linarith [widthOrder_logPlus_nonneg (U.a N)]
  have hsq : Real.log ((U.B N).card : ℝ) ≤ Real.sqrt (U.a N * (Real.log ((U.B N).card : ℝ) + logPlus (U.a N))) := by
    have h2 : Real.log ((U.B N).card : ℝ) ^ 2 ≤ U.a N * (Real.log ((U.B N).card : ℝ) + logPlus (U.a N)) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hlogle) hlog0,
        mul_nonneg haN.le (widthOrder_logPlus_nonneg (U.a N))]
    calc Real.log ((U.B N).card : ℝ) = Real.sqrt (Real.log ((U.B N).card : ℝ) ^ 2) := (Real.sqrt_sq hlog0).symm
      _ ≤ Real.sqrt (U.a N * (Real.log ((U.B N).card : ℝ) + logPlus (U.a N))) := Real.sqrt_le_sqrt h2
  have hsqrtX : Real.sqrt (min (SequenceSetup.time U y₀ N : ℝ) (sharp (U.B N)) / ((U.B N).card : ℝ) *
      (Real.log ((U.B N).card : ℝ) + logPlus ((SequenceSetup.time U y₀ N : ℝ) / ((U.B N).card : ℝ)))) ≤
      Real.sqrt (2 * y₀) * Real.sqrt (U.a N * (Real.log ((U.B N).card : ℝ) + logPlus (U.a N))) := by
    rw [← Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 2 * y₀)]
    exact Real.sqrt_le_sqrt hX
  have hmax : max (Real.log ((U.B N).card : ℝ)) (Real.sqrt (min (SequenceSetup.time U y₀ N : ℝ) (sharp (U.B N)) /
      ((U.B N).card : ℝ) * (Real.log ((U.B N).card : ℝ) + logPlus ((SequenceSetup.time U y₀ N : ℝ) / ((U.B N).card : ℝ))))) ≤
      max 1 (Real.sqrt (2 * y₀)) * Real.sqrt (U.a N * (Real.log ((U.B N).card : ℝ) + logPlus (U.a N))) :=
    max_le (hsq.trans (le_mul_of_one_le_left hS0 (le_max_left _ _)))
      (hsqrtX.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hS0))
  unfold SequenceSetup.width delta
  exact le_trans (mul_le_mul_of_nonneg_left hmax hC.le) (le_of_eq (by ring))

end IdlaCyl.GffSeq
