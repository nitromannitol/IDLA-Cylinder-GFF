/-
Replacement asymptotics along rows. Source: paper/idla-cylinder-gff.tex, tex:784-817,846-848.
-/
import IdlaCyl.Support.Replace.SlabReduction
import IdlaCyl.Support.Torus.Sequence

/-!
The slab width and reference-height limits in the replacement lemma
(`tex:784-817`, `tex:846-848`). The width has exactly the printed order bound.
-/

namespace IdlaCyl.GffSeq.Replace

open Defs IdlaCyl.Replace Filter
open scoped Topology

/-- The reference time divided by the base size is the literal floor height. -/
theorem time_div_card (U : SequenceSetup) (y₀ : ℝ) (N : ℕ) :
    (SequenceSetup.time U y₀ N : ℝ) / ((U.B N).card : ℝ) = (SequenceSetup.height U y₀ N : ℝ) := by
  have hcard : ((U.B N).card : ℝ) ≠ 0 := by
    exact_mod_cast (show (U.B N).card ≠ 0 by
      change Fintype.card (U.B N).V ≠ 0
      have := (U.B N).nontrivial
      omega)
  simp only [SequenceSetup.time, Nat.cast_mul]
  field_simp

/-- The floor reference height divided by `a_N` tends to `y₀`. -/
theorem height_ratio_tendsto (U : SequenceSetup) (y₀ : ℝ) (hy₀ : 0 ≤ y₀) :
    Tendsto (fun N => (SequenceSetup.height U y₀ N : ℝ) / U.a N) atTop (nhds y₀) :=
  (tendsto_nat_floor_mul_div_atTop hy₀).comp U.a_tendsto

private theorem sqrt_mul_div (a b : ℝ) (ha : 0 < a) :
    Real.sqrt (a * b) / a = Real.sqrt (b / a) := by
  calc
    _ = Real.sqrt b * (Real.sqrt a / a) := by rw [Real.sqrt_mul ha.le]; ring
    _ = Real.sqrt b / Real.sqrt a := by rw [Real.sqrt_div_self]; rfl
    _ = _ := (Real.sqrt_div' b ha.le).symm

/-- The printed width order and growth assumptions imply `d_N/a_N → 0`. -/
theorem width_ratio_tendsto_zero (U : SequenceSetup) (hgrowth : U.GrowthCondition)
    (d : ℕ → ℝ) (hd : ∀ N, 0 < d N)
    (horder : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in atTop,
      d N ≤ C * Real.sqrt (U.a N * (Real.log ((U.B N).card : ℝ) + logPlus (U.a N)))) :
    Tendsto (fun N => d N / U.a N) atTop (nhds 0) := by
  obtain ⟨C, _, hbound⟩ := horder
  have hlim : Tendsto (fun N : ℕ => C * Real.sqrt
      ((Real.log ((U.B N).card : ℝ) + logPlus (U.a N)) / U.a N)) atTop (nhds 0) := by
    simpa only [Real.sqrt_zero, mul_zero] using (tendsto_const_nhds (x := C)).mul hgrowth.sqrt
  refine squeeze_zero' (.of_forall fun N => (div_pos (hd N) (U.a_pos N)).le) ?_ hlim
  filter_upwards [hbound] with N hN
  calc
    d N / U.a N ≤ (C * Real.sqrt
        (U.a N * (Real.log ((U.B N).card : ℝ) + logPlus (U.a N)))) / U.a N :=
      div_le_div_of_nonneg_right hN (U.a_pos N).le
    _ = _ := by rw [mul_div_assoc, sqrt_mul_div _ _ (U.a_pos N)]

/-- Every integer layer in the literal slab lies within its stated width. -/
theorem slabHeights_abs_sub_le (U : SequenceSetup) (y₀ : ℝ) (N : ℕ) (d : ℝ) (y : ℤ)
    (hy : y ∈ slabHeights (U.B N) (SequenceSetup.time U y₀ N) d) :
    |(y : ℝ) - (SequenceSetup.height U y₀ N : ℝ)| ≤ d := by
  unfold slabHeights at hy
  rw [time_div_card] at hy
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hy
  have hl : (SequenceSetup.height U y₀ N : ℝ) - d < (y : ℝ) := Int.floor_lt.mp hlo
  have hu : (y : ℝ) ≤ (SequenceSetup.height U y₀ N : ℝ) + d :=
    (show (y : ℝ) ≤ (⌊(SequenceSetup.height U y₀ N : ℝ) + d⌋ : ℤ) by exact_mod_cast hhi).trans
      (Int.floor_le _)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- For large `N`, the lower slab edge lies above the seed layer. -/
theorem eventually_slab_lower_nonneg (U : SequenceSetup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (hgrowth : U.GrowthCondition) (d : ℕ → ℝ) (hd : ∀ N, 0 < d N)
    (horder : ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in atTop,
      d N ≤ C * Real.sqrt (U.a N * (Real.log ((U.B N).card : ℝ) + logPlus (U.a N)))) :
    ∀ᶠ N in atTop, 0 ≤ ⌊(SequenceSetup.time U y₀ N : ℝ) / ((U.B N).card : ℝ) - d N⌋ := by
  have hwidth := width_ratio_tendsto_zero U hgrowth d hd horder
  have hlim : Tendsto (fun N => (SequenceSetup.height U y₀ N : ℝ) / U.a N - d N / U.a N)
      atTop (nhds y₀) := by
    simpa only [sub_zero] using (height_ratio_tendsto U y₀ hy₀.le).sub hwidth
  filter_upwards [hlim.eventually (lt_mem_nhds hy₀)] with N hN
  rw [time_div_card]
  apply Int.floor_nonneg.mpr
  rw [← sub_div] at hN
  exact ((div_pos_iff_of_pos_right (U.a_pos N)).mp hN).le

end IdlaCyl.GffSeq.Replace
