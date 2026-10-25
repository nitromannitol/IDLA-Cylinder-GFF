module

public import IdlaCyl.Support.ShapeModerate
public import IdlaCyl.Support.AprioriEarlyBound
public import IdlaCyl.Support.CanonicalGrowth
public import IdlaCyl.Definitions.ShapeEvent

@[expose] public section

/-!
# The shape bound for every time up to `T^♯`

Source: `paper/idla-cylinder-gff.tex`, `tex:271-280` (`th:max_fluct`), restricted to
`T ≤ T^♯` (`tex:273`). The width is `delta B C T`, the printed `Δ_N` of
`IdlaCyl.Defs` (`tex:273`).

Moderate times, `K N log N ≤ T`, are covered by `shape_moderate`, whose width
`innerWidth` is dominated by `delta` once `C` exceeds `C_mod · 2√(ν+4)`.
Small times, `T < K N log N`, are covered by `pr_apriori_part_a`: the cluster lies in
`R_{β log N}` with failure probability `N^{-(β-1)}`, and the inner inclusion is automatic
because the width exceeds `K log N` and so `T/N - Δ ≤ 0`.
-/

namespace IdlaCyl

open IdlaCyl.Defs
open MeasureTheory

/-- Enlarging the width enlarges the event `eventAt`. -/
theorem eventAt_mono_width (B : Base) (T : ℕ) {d d' : ℝ} (h : d ≤ d') :
    eventAt B T d ⊆ eventAt B T d' := by
  rintro ω ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · refine (R_mono ?_).trans h1
    exact Int.cast_le.mpr (Int.floor_mono (by linarith))
  · exact h2.trans (R_mono (by linarith))

/-- When the time-to-size ratio lies below the width, the inner inclusion holds for free,
since the flat seed `R B 0` lies in every cluster. -/
theorem inner_inclusion_trivial (B : Base) (T : ℕ) (d : ℝ) (hd : (T : ℝ) / (B.card : ℝ) ≤ d)
    (ω : TrajSeq B) :
    R B ((Int.floor ((T : ℝ) / (B.card : ℝ) - d) : ℤ) : ℝ) ⊆ clusterTraj B ω T := by
  have h0 : Int.floor ((T : ℝ) / (B.card : ℝ) - d) ≤ 0 := by
    have := Int.floor_mono (show (T : ℝ) / (B.card : ℝ) - d ≤ 0 by linarith)
    simpa using this
  exact (R_mono (by exact_mod_cast h0)).trans (clusterTraj_plus_ncard_of_seed_subset B ω T)

/-- The shape bound for every time up to `T^♯`. The constant `C` and the size `N₀` are chosen
before the base and the time, and depend only on `ν`. -/
theorem max_fluct_upto_sharp (ν : ℝ) (hν : 0 < ν) (m : ℝ) (_hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card → ∀ T : ℕ,
      1 ≤ T → (T : ℝ) ≤ (B.card : ℝ) ^ m → (T : ℝ) ≤ sharp B →
      idlaMeasure B (eventAt B T (delta B C T))ᶜ ≤ ENNReal.ofReal ((B.card : ℝ) ^ (-ν)) := by
  obtain ⟨Cm, K, hCm, hK, N₁, hmod⟩ := shape_moderate ν hν
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = max 1 (Real.exp 2 * K) + ν + 1 := ⟨_, rfl⟩
  have hexp : (1 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hKeK : K ≤ Real.exp 2 * K := le_mul_of_one_le_left hK.le hexp
  have hβlt : max 1 (Real.exp 2 * K) < β := by
    rw [hβdef]
    linarith
  have hβν : ν ≤ β - 1 := by
    rw [hβdef]
    linarith [le_max_left 1 (Real.exp 2 * K)]
  have hβpos : 0 < β := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hβlt.le)
  obtain ⟨N₂, hsmall⟩ := pr_apriori_part_a K hK β hβlt
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max (Cm * (2 * Real.sqrt (ν + 4))) β := ⟨_, rfl⟩
  have hC0 : 0 < C := by
    rw [hCdef]
    exact lt_of_lt_of_le hβpos (le_max_right _ _)
  have hC1 : Cm * (2 * Real.sqrt (ν + 4)) ≤ C := by
    rw [hCdef]
    exact le_max_left _ _
  have hCβ : β ≤ C := by
    rw [hCdef]
    exact le_max_right _ _
  have hKC : K ≤ C := le_trans (le_trans (le_trans hKeK (le_max_right 1 (Real.exp 2 * K)))
    hβlt.le) hCβ
  refine ⟨C, hC0, max N₁ (max N₂ 1), ?_⟩
  intro B hB T _hT1 _hTm hTs
  have hBN₁ : N₁ ≤ B.card := le_trans (le_max_left _ _) hB
  have hBN₂ : N₂ ≤ B.card := le_trans (le_trans (le_max_left N₂ 1) (le_max_right N₁ _)) hB
  have hN1 : 1 ≤ B.card := le_trans (le_trans (le_max_right N₂ 1) (le_max_right N₁ _)) hB
  have hN1R : (1 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < (B.card : ℝ) := by linarith
  have hlogN : (0 : ℝ) ≤ Real.log (B.card : ℝ) := Real.log_nonneg hN1R
  by_cases hmod_case : K * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (T : ℝ)
  · -- moderate times: the width `delta` dominates `innerWidth`
    have hwidth : Cm * innerWidth ν B.card T ≤ delta B C T := by
      have hiw : innerWidth ν B.card T = 2 * Real.sqrt (ν + 4) *
          Real.sqrt ((T : ℝ) / (B.card : ℝ) *
            (Real.log (B.card : ℝ) + logPlus ((T : ℝ) / (B.card : ℝ)))) := rfl
      have hdl : delta B C T = C * max (Real.log (B.card : ℝ))
          (Real.sqrt ((T : ℝ) / (B.card : ℝ) *
            (Real.log (B.card : ℝ) + logPlus ((T : ℝ) / (B.card : ℝ))))) := by
        unfold delta
        rw [min_eq_left hTs]
      rw [hiw, hdl]
      calc Cm * (2 * Real.sqrt (ν + 4) * Real.sqrt ((T : ℝ) / (B.card : ℝ) *
              (Real.log (B.card : ℝ) + logPlus ((T : ℝ) / (B.card : ℝ)))))
          = (Cm * (2 * Real.sqrt (ν + 4))) * Real.sqrt ((T : ℝ) / (B.card : ℝ) *
              (Real.log (B.card : ℝ) + logPlus ((T : ℝ) / (B.card : ℝ)))) := by ring
        _ ≤ C * Real.sqrt ((T : ℝ) / (B.card : ℝ) *
              (Real.log (B.card : ℝ) + logPlus ((T : ℝ) / (B.card : ℝ)))) :=
          mul_le_mul_of_nonneg_right hC1 (Real.sqrt_nonneg _)
        _ ≤ C * max (Real.log (B.card : ℝ)) (Real.sqrt ((T : ℝ) / (B.card : ℝ) *
              (Real.log (B.card : ℝ) + logPlus ((T : ℝ) / (B.card : ℝ))))) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) hC0.le
    have hsub := eventAt_mono_width B T hwidth
    exact (measure_mono (Set.compl_subset_compl.mpr hsub)).trans
      (hmod B hBN₁ T hmod_case)
  · -- small times: the cluster lies in `R_{β log N}` and the inner inclusion is automatic
    have hTK : (T : ℝ) ≤ K * (B.card : ℝ) * Real.log (B.card : ℝ) :=
      le_of_lt (not_le.mp hmod_case)
    have hTK' : (T : ℝ) / (B.card : ℝ) ≤ K * Real.log (B.card : ℝ) := by
      rw [div_le_iff₀ hNpos]
      linarith [show K * Real.log (B.card : ℝ) * (B.card : ℝ) =
        K * (B.card : ℝ) * Real.log (B.card : ℝ) by ring]
    have hdlb : C * Real.log (B.card : ℝ) ≤ delta B C T := by
      unfold delta
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) hC0.le
    have hKlog : K * Real.log (B.card : ℝ) ≤ C * Real.log (B.card : ℝ) :=
      mul_le_mul_of_nonneg_right hKC hlogN
    have hβlog : β * Real.log (B.card : ℝ) ≤ C * Real.log (B.card : ℝ) :=
      mul_le_mul_of_nonneg_right hCβ hlogN
    have hsub : (eventAt B T (delta B C T))ᶜ ⊆
        {ω : TrajSeq B | ¬ (clusterTraj B ω T ⊆ R B (β * Real.log (B.card : ℝ)))} := by
      intro ω hω hgood
      apply hω
      refine ⟨inner_inclusion_trivial B T (delta B C T) (by linarith) ω, ?_⟩
      exact hgood.trans (R_mono (by
        have : (0 : ℝ) ≤ (T : ℝ) / (B.card : ℝ) := div_nonneg (Nat.cast_nonneg T) hNpos.le
        linarith))
    have hexp_ok : (B.card : ℝ) ^ (-(β - 1)) ≤ (B.card : ℝ) ^ (-ν) :=
      Real.rpow_le_rpow_of_exponent_le hN1R (by linarith)
    exact (measure_mono hsub).trans
      ((hsmall B hBN₂ T hTK).trans (ENNReal.ofReal_le_ofReal hexp_ok))

end IdlaCyl
