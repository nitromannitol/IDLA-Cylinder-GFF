/-
Source: paper/idla-cylinder-gff.tex, tex:910-911,931-938,990-998.
The uniform a priori bound at the observation time controls every integer
height above a fixed multiple of a_N with a common eventual cutoff.
-/
import IdlaCyl.Support.QOnEc.Shape
import IdlaCyl.Support.AprioriUniform
import IdlaCyl.Support.GffSeq.Shape
import IdlaCyl.Support.Torus.Sequence

namespace IdlaCyl.GffSeq.QOnEc

open IdlaCyl.Defs Filter MeasureTheory
open scoped Topology

/-- The a priori height tails hold simultaneously at all heights above
`exp(3) y₀ a_N`, with one cutoff independent of the height. -/
theorem height_tail_eventually (U : SequenceSetup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (hgrowth : U.GrowthCondition) :
    ∀ᶠ N in atTop, ∀ h : ℕ, Real.exp 3 * y₀ * U.a N ≤ (h : ℝ) →
      idlaMeasure (U.B N)
        {ω : TrajSeq (U.B N) | ¬ clusterTraj (U.B N) ω (SequenceSetup.time U y₀ N) ⊆
          R (U.B N) (h : ℝ)} ≤ ENNReal.ofReal (Real.exp (-(h : ℝ))) := by
  obtain ⟨L, -, N₀, hb⟩ := pr_apriori_part_b_uniform (Real.exp 3)
    (Real.exp_lt_exp.mpr (by norm_num))
  have ha : ∀ᶠ N in atTop, 1 / y₀ ≤ U.a N := U.a_tendsto.eventually_ge_atTop _
  filter_upwards [time_ge_log_eventually U y₀ hy₀ hgrowth L,
    U.eventually_modes N₀, ha] with N htime hN haN
  have hNN := hN
  have hheight : 0 < SequenceSetup.height U y₀ N := by
    unfold SequenceSetup.height
    apply Nat.floor_pos.mpr
    have h := (div_le_iff₀ hy₀).mp haN
    linarith
  have hhpos : (0 : ℝ) < (SequenceSetup.height U y₀ N : ℝ) := Nat.cast_pos.mpr hheight
  have hNpos : (0 : ℝ) < ((U.B N).card : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (U.B N).nontrivial)
  intro h hh
  let β := (h : ℝ) / (SequenceSetup.height U y₀ N : ℝ)
  have hβ : Real.exp 3 ≤ β := by
    apply (le_div_iff₀ hhpos).mpr
    have hf := Nat.floor_le (mul_nonneg hy₀.le (U.a_pos N).le)
    have hf' : (SequenceSetup.height U y₀ N : ℝ) ≤ y₀ * U.a N := hf
    calc Real.exp 3 * (SequenceSetup.height U y₀ N : ℝ) ≤ Real.exp 3 * (y₀ * U.a N) :=
        mul_le_mul_of_nonneg_left hf' (Real.exp_nonneg _)
      _ = Real.exp 3 * y₀ * U.a N := (mul_assoc _ _ _).symm
      _ ≤ (h : ℝ) := hh
  have hlink : β * (SequenceSetup.time U y₀ N : ℝ) / ((U.B N).card : ℝ) = (h : ℝ) := by
    unfold β SequenceSetup.time
    rw [Nat.cast_mul]
    field_simp
  have ht := hb (U.B N) hNN β hβ (SequenceSetup.time U y₀ N) htime
  rwa [hlink] at ht

end IdlaCyl.GffSeq.QOnEc
