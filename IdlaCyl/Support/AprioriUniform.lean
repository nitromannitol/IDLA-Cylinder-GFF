/-
Uniform a priori height bounds for the canonical cylinder IDLA process.
Source: paper/idla-cylinder-gff.tex, tex:559-567,585-650,657-669.
Source SHA-256:
34a459e11753efc825c7a7b0534bb90598fc94a20f32ce8c7d53135c028e7701.

The thresholds in part (b) depend only on the lower exponent bound. Applying
these common thresholds to a base-graph family gives the eventual estimate
for the varying exponents and times of Remark 2.3.
-/
import IdlaCyl.Support.AprioriFinal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unnecessarySimpa true
set_option linter.deprecated true

namespace IdlaCyl

theorem pr_apriori_part_b_uniform
    (β₀ : ℝ) (hβ₀ : Real.exp 2 < β₀) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∃ N₀ : ℕ,
      ∀ B : Base, N₀ ≤ B.card →
      ∀ β : ℝ, β₀ ≤ β →
      ∀ T : ℕ,
        K₀ * (B.card : ℝ) * Real.log (B.card : ℝ) ≤
          (T : ℝ) →
        idlaMeasure B {ω : TrajSeq B |
            ¬ (clusterTraj B ω T ⊆
              R B (β * (T : ℝ) / (B.card : ℝ)))}
          ≤ ENNReal.ofReal
              (Real.exp (-(β * (T : ℝ) / (B.card : ℝ)))) := by
  have hβ₀pos : 0 < β₀ := lt_trans (Real.exp_pos 2) hβ₀
  have he₀ : Real.exp 1 < β₀ :=
    lt_trans (Real.exp_lt_exp.mpr (by norm_num)) hβ₀
  have hden₀ : 0 < 1 - Real.exp 1 / β₀ :=
    sub_pos.mpr ((div_lt_one hβ₀pos).mpr he₀)
  have hslack₀ : 0 < Real.log β₀ - 2 :=
    sub_pos.mpr ((Real.lt_log_iff_exp_lt hβ₀pos).mpr hβ₀)
  have hg₀ : 0 < β₀ * (Real.log β₀ - 2) := mul_pos hβ₀pos hslack₀
  refine ⟨2 / (β₀ * (Real.log β₀ - 2)), by positivity,
    ⌈(1 - Real.exp 1 / β₀)⁻¹⌉₊ + 2, ?_⟩
  intro B hNB β hβ T hT
  have hβexp : Real.exp 2 < β := lt_of_lt_of_le hβ₀ hβ
  have hβpos : 0 < β := lt_of_lt_of_le hβ₀pos hβ
  have hcard : 1 ≤ B.card := le_trans (by omega) hNB
  have hNpos : (0 : ℝ) < B.card :=
    by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hcard)
  have hdenle : 1 - Real.exp 1 / β₀ ≤ 1 - Real.exp 1 / β := by
    exact sub_le_sub_left (div_le_div_of_nonneg_left (Real.exp_pos 1).le hβ₀pos hβ) 1
  have hden : 0 < 1 - Real.exp 1 / β := lt_of_lt_of_le hden₀ hdenle
  have hlogN : -Real.log (1 - Real.exp 1 / β) ≤ Real.log (B.card : ℝ) := by
    have hge₀ : (1 - Real.exp 1 / β₀)⁻¹ ≤ (B.card : ℝ) := by
      have h1 : (⌈(1 - Real.exp 1 / β₀)⁻¹⌉₊ : ℝ) ≤ (B.card : ℝ) :=
        by exact_mod_cast (le_trans (Nat.le_add_right _ 2) hNB)
      exact (Nat.le_ceil _).trans h1
    have hge : (1 - Real.exp 1 / β)⁻¹ ≤ (B.card : ℝ) :=
      ((inv_le_inv₀ hden hden₀).mpr hdenle).trans hge₀
    have hlogs := Real.log_le_log (inv_pos.mpr hden) hge
    rwa [Real.log_inv] at hlogs
  have hg : β₀ * (Real.log β₀ - 2) ≤ β * (Real.log β - 2) := by
    calc
      β₀ * (Real.log β₀ - 2) ≤ β * (Real.log β₀ - 2) :=
        mul_le_mul_of_nonneg_right hβ hslack₀.le
      _ ≤ β * (Real.log β - 2) :=
        mul_le_mul_of_nonneg_left
          (sub_le_sub_right (Real.log_le_log hβ₀pos hβ) 2) hβpos.le
  have hK : 2 * Real.log (B.card : ℝ) ≤
      (β * (T : ℝ) / (B.card : ℝ)) * (Real.log β - 2) := by
    have key : (2 / (β₀ * (Real.log β₀ - 2))) * (B.card : ℝ) *
        Real.log (B.card : ℝ) * ((β₀ * (Real.log β₀ - 2)) / (B.card : ℝ)) =
        2 * Real.log (B.card : ℝ) := by
      field_simp
    calc
      2 * Real.log (B.card : ℝ) =
          (2 / (β₀ * (Real.log β₀ - 2))) * (B.card : ℝ) *
            Real.log (B.card : ℝ) * ((β₀ * (Real.log β₀ - 2)) / (B.card : ℝ)) :=
        key.symm
      _ ≤ (T : ℝ) * ((β₀ * (Real.log β₀ - 2)) / (B.card : ℝ)) :=
        mul_le_mul_of_nonneg_right hT (div_pos hg₀ hNpos).le
      _ = β₀ * (Real.log β₀ - 2) * ((T : ℝ) / (B.card : ℝ)) := by ring
      _ ≤ β * (Real.log β - 2) * ((T : ℝ) / (B.card : ℝ)) :=
        mul_le_mul_of_nonneg_right hg (by positivity)
      _ = (β * (T : ℝ) / (B.card : ℝ)) * (Real.log β - 2) := by ring
  have hmain := apriori_tsum_le_exp B External.lazyRwRecurrent_holds T β hβexp
    (β * (T : ℝ) / (B.card : ℝ)) (by positivity) rfl
  exact hmain.trans (ENNReal.ofReal_le_ofReal
    (arith_bound β hβexp B.card hcard
      (β * (T : ℝ) / (B.card : ℝ)) hlogN hK))


/- Remark 2.3: tex:657-669. The graph family is standing data; the
source inputs are ordered β₀, β_N, T_N. No condition is imposed at N = 0.
The size and time cutoffs, including positivity of N log N, are proved here.
-/
theorem rk_apriori_ndep_support
    (U : BaseSeq)
    (β₀ : ℝ) (hβ₀ : Real.exp 2 < β₀)
    (β : ℕ → ℝ) (hβ : ∀ N : ℕ, 1 ≤ N → β₀ ≤ β N)
    (T : ℕ → ℕ)
    (hT : Filter.Tendsto
      (fun N : ℕ => (T N : ℝ) / ((N : ℝ) * Real.log (N : ℝ)))
      Filter.atTop Filter.atTop) :
    ∀ᶠ N : ℕ in Filter.atTop,
      idlaMeasure (U.B N) {ω : TrajSeq (U.B N) |
          ¬ (clusterTraj (U.B N) ω (T N) ⊆
            R (U.B N) (β N * (T N : ℝ) / (N : ℝ)))}
        ≤ ENNReal.ofReal
            (Real.exp (-(β N * (T N : ℝ) / (N : ℝ)))) := by
  obtain ⟨K₀, _hK₀, N₀, huniform⟩ := pr_apriori_part_b_uniform β₀ hβ₀
  filter_upwards [Filter.eventually_ge_atTop (max N₀ 2),
    hT.eventually_ge_atTop K₀] with N hN htime
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN₂ : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hNreal : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hden : 0 < (N : ℝ) * Real.log (N : ℝ) :=
    mul_pos (lt_trans zero_lt_one hNreal) (Real.log_pos hNreal)
  have hcut : K₀ * (N : ℝ) * Real.log (N : ℝ) ≤ (T N : ℝ) := by
    rw [mul_assoc]
    exact (le_div_iff₀ hden).mp htime
  have hcard : (U.B N).card = N := U.card_eq N hN₂
  have hbase : N₀ ≤ (U.B N).card := by rw [hcard]; exact hN₀
  have htimeBase : K₀ * ((U.B N).card : ℝ) *
      Real.log ((U.B N).card : ℝ) ≤ (T N : ℝ) := by
    rw [hcard]
    exact hcut
  have hbound := huniform (U.B N) hbase (β N) (hβ N (by omega)) (T N) htimeBase
  rw [hcard] at hbound
  exact hbound

end IdlaCyl
