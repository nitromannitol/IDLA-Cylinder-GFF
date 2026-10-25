module

public import IdlaCyl.Frozen.PrOuterV2
public import IdlaCyl.Support.PrInnerStopped.Composition
public import IdlaCyl.Definitions.ShapeEvent
public import IdlaCyl.Support.Outer.StoppedBookkeeping

@[expose] public section

/-!
# Shape bound at moderate times

The event `eventAt B T (C * innerWidth ν N T)` has failure probability at most
`N^{-ν}` once `T ≥ K N log N`. The failure event is covered by two events: the
inner event `{¬ R_h ⊆ A(T)}` with `h = ⌊T/N - innerWidth ν N T⌋`, and the outer
event `{¬ A(T) ⊆ R_{T/N + C' · innerWidth ν N T}}`. Each has probability at most
`N^{-(ν+1)}`, and the two bounds sum to `N^{-ν}` for `N ≥ 2`.
-/

namespace IdlaCyl

open IdlaCyl.Defs
open MeasureTheory

/-- The shape bound at moderate times: for every `ν > 0` there are constants `C, K > 0`
and a size `N₀` such that, for every base with at least `N₀` sites and every time
`T ≥ K N log N`, the probability that the event `eventAt B T (C · innerWidth ν N T)`
fails is at most `N^{-ν}`. -/
theorem shape_moderate (ν : ℝ) (hν : 0 < ν) :
    ∃ C K : ℝ, 0 < C ∧ 0 < K ∧ ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card → ∀ T : ℕ,
      K * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (T : ℝ) →
      idlaMeasure B (eventAt B T (C * innerWidth ν B.card T))ᶜ ≤
        ENNReal.ofReal ((B.card : ℝ) ^ (-ν)) := by
  obtain ⟨C', K', -, hK', N₁, hout⟩ := Frozen.pr_outer_v2 ν hν
  refine ⟨max 1 C', max K' (16 * (2 * Real.sqrt (ν + 4)) ^ 2),
    lt_of_lt_of_le one_pos (le_max_left _ _), lt_of_lt_of_le hK' (le_max_left _ _),
    max N₁ (max ⌈256 * (2 * Real.sqrt (ν + 4)) ^ 4 + 1⌉₊ 2), ?_⟩
  intro B hB T hT
  have hBN₁ : N₁ ≤ B.card := le_trans (le_max_left _ _) hB
  have hBc : ⌈256 * (2 * Real.sqrt (ν + 4)) ^ 4 + 1⌉₊ ≤ B.card :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  have hB2 : 2 ≤ B.card := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  have hNreal : 256 * (2 * Real.sqrt (ν + 4)) ^ 4 + 1 ≤ (B.card : ℝ) :=
    (Nat.le_ceil (256 * (2 * Real.sqrt (ν + 4)) ^ 4 + 1)).trans (by exact_mod_cast hBc)
  have hN2 : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB2
  have hNpos : (0 : ℝ) < (B.card : ℝ) := by linarith
  have hlogN : (0 : ℝ) ≤ Real.log (B.card : ℝ) := Real.log_nonneg (by linarith)
  have hTout : K' * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (T : ℝ) :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hNpos.le)
      hlogN).trans hT
  have hTin : 16 * (2 * Real.sqrt (ν + 4)) ^ 2 * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (T : ℝ) :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hNpos.le)
      hlogN).trans hT
  -- the inner height and its producer
  obtain ⟨h, hh⟩ : ∃ h : ℤ, h = ⌊(T : ℝ) / (B.card : ℝ) - innerWidth ν B.card T⌋ := ⟨_, rfl⟩
  obtain ⟨-, hA, hS⟩ := pr_inner_probability_bound B ν hν hNreal T hTin h (hh.trans rfl)
  -- the event at the height `⌊T/N - C · innerWidth⌋` sits below the inner height
  have hCiw : innerWidth ν B.card T ≤ max 1 C' * innerWidth ν B.card T :=
    le_mul_of_one_le_left (innerWidth_nonneg ν B.card T) (le_max_left 1 C')
  have hfl : ⌊(T : ℝ) / (B.card : ℝ) - max 1 C' * innerWidth ν B.card T⌋ ≤ h := by
    rw [hh]
    exact Int.floor_mono (by linarith)
  have hR1 : R B ((⌊(T : ℝ) / (B.card : ℝ) - max 1 C' * innerWidth ν B.card T⌋ : ℤ) : ℝ)
      ⊆ R B (h : ℝ) :=
    R_mono (by exact_mod_cast hfl)
  have hmem : ∀ ω : TrajSeq B,
      ω ∈ eventAt B T (max 1 C' * innerWidth ν B.card T) ↔
        (R B ((⌊(T : ℝ) / (B.card : ℝ) - max 1 C' * innerWidth ν B.card T⌋ : ℤ) : ℝ)
            ⊆ clusterTraj B ω T ∧
          clusterTraj B ω T ⊆ R B ((T : ℝ) / (B.card : ℝ) + max 1 C' * innerWidth ν B.card T)) :=
    fun ω => Iff.rfl
  -- the failure event is covered by the inner and outer failure events
  have hcov : (eventAt B T (max 1 C' * innerWidth ν B.card T))ᶜ ⊆
      {ω : TrajSeq B | ¬ R B (h : ℝ) ⊆ clusterTraj B ω T} ∪
        {ω : TrajSeq B | ¬ clusterTraj B ω T ⊆
          R B ((T : ℝ) / (B.card : ℝ) + max 1 C' * innerWidth ν B.card T)} := by
    intro ω hω
    rw [Set.mem_compl_iff, hmem] at hω
    by_cases h1 : R B (h : ℝ) ⊆ clusterTraj B ω T
    · right
      intro hR2
      exact hω ⟨fun p hp => h1 (hR1 hp), hR2⟩
    · left
      exact h1
  -- the outer failure event at width `C'` contains the one at width `max 1 C'`
  have hO : (T : ℝ) / (B.card : ℝ) + C' * innerWidth ν B.card T ≤
      (T : ℝ) / (B.card : ℝ) + max 1 C' * innerWidth ν B.card T := by
    have := mul_le_mul_of_nonneg_right (le_max_right 1 C') (innerWidth_nonneg ν B.card T)
    linarith
  have hS2 : {ω : TrajSeq B | ¬ clusterTraj B ω T ⊆
        R B ((T : ℝ) / (B.card : ℝ) + max 1 C' * innerWidth ν B.card T)} ⊆
      {ω : TrajSeq B | ¬ clusterTraj B ω T ⊆
        R B ((T : ℝ) / (B.card : ℝ) + C' * innerWidth ν B.card T)} := by
    intro ω hω hR
    exact hω (fun p hp => R_mono hO (hR hp))
  have h1' := (measure_mono hS2).trans (hout B hBN₁ T hTout)
  have h2' := hA.trans hS
  -- the arithmetic of the two bounds
  have ha0 : (0 : ℝ) ≤ (B.card : ℝ) ^ (-(ν + 1)) := Real.rpow_nonneg hNpos.le _
  have hpow : (B.card : ℝ) ^ (-(ν + 1)) = (B.card : ℝ) ^ (-ν) * (B.card : ℝ)⁻¹ := by
    rw [show -(ν + 1) = -ν + -1 by ring, Real.rpow_add hNpos, Real.rpow_neg_one]
  have hinv' : (B.card : ℝ)⁻¹ * (B.card : ℝ) = 1 := inv_mul_cancel₀ hNpos.ne'
  have hinv : 2 * (B.card : ℝ)⁻¹ ≤ 1 := by
    linarith [mul_nonneg (inv_nonneg.mpr hNpos.le) (sub_nonneg.mpr hN2)]
  have harith : (B.card : ℝ) ^ (-(ν + 1)) + (B.card : ℝ) ^ (-(ν + 1)) ≤ (B.card : ℝ) ^ (-ν) := by
    rw [hpow]
    have hp0 : (0 : ℝ) ≤ (B.card : ℝ) ^ (-ν) := Real.rpow_nonneg hNpos.le _
    linarith [mul_le_mul_of_nonneg_left hinv hp0]
  have hsum : ENNReal.ofReal ((B.card : ℝ) ^ (-(ν + 1))) +
      ENNReal.ofReal ((B.card : ℝ) ^ (-(ν + 1))) ≤ ENNReal.ofReal ((B.card : ℝ) ^ (-ν)) := by
    rw [← ENNReal.ofReal_add ha0 ha0]
    exact ENNReal.ofReal_le_ofReal harith
  exact (measure_mono hcov).trans ((measure_union_le _ _).trans ((add_le_add h2' h1').trans hsum))
