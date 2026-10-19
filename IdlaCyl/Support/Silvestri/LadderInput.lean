import Mathlib
import IdlaCyl.Support.Idla
import IdlaCyl.Support.FiniteProbability

/-!
# Ladder inputs and an inverse-CDF sampler for finite laws

This file gives the randomness used by the ladder construction in the proof of
Silvestri's Proposition 2, and the sampler that turns one uniform into an atom of
a finite law.

It proves the following.

1. `ladderInLaw` is the law of a family of i.i.d. uniform variables on `[0,1)`,
   indexed by `LadderIn = Fin 3 × ℕ × ℕ` (walker or coupling slot, attempt, step).
2. `stepType u` classifies one uniform as down, up or horizontal with
   probabilities `1/4`, `1/4` and `1/2`, and the vertical increment
   `stepIncr (stepType u)` has the explicit law of `typeLaw` (the driven walk's
   vertical increment).
3. `IdlaCyl.FiniteLaw.sample μ u` is the inverse-CDF sampler of a finite law `μ`.
   For `u` uniform on `[0,1)` it satisfies `P(sample μ u = a) = μ.weight a`, and
   on `[0,1)` it never returns an atom of weight zero.

The sampler is defined on the whole real line, so it needs a default atom for the
values outside `[0,1)`. The law statements do not use those values.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace IdlaCyl.Silvestri

noncomputable section

/-- The uniform law on `[0,1)` is a probability measure. -/
instance ladderStepLaw_isProbability : IsProbabilityMeasure stepLaw := by
  constructor
  norm_num [stepLaw, Measure.restrict_apply_univ]

/-- The input family of the ladder: one real coordinate for each triple of a
walker or coupling slot `Fin 3`, an attempt `ℕ`, and a step `ℕ`. -/
abbrev LadderIn : Type := Fin 3 × ℕ × ℕ → ℝ

/-- The law of the ladder inputs: the infinite product of the uniform law `stepLaw`
on `[0,1)`, so the coordinates are i.i.d. uniform. -/
def ladderInLaw : Measure LadderIn :=
  Measure.infinitePi fun _ : Fin 3 × ℕ × ℕ => stepLaw

/-- The step type of one uniform: `0` (down) on `[0, 1/4)`, `1` (up) on
`[1/4, 1/2)`, and `2` (horizontal) on `[1/2, 1)`. -/
def stepType (u : ℝ) : Fin 3 :=
  if u < 1 / 4 then 0 else if u < 1 / 2 then 1 else 2

/-- The step type `0` (down) is taken exactly on `(-∞, 1/4)`. -/
theorem stepType_eq_zero_iff (u : ℝ) : stepType u = 0 ↔ u < 1 / 4 := by
  unfold stepType
  split_ifs with h1 h2
  · exact ⟨fun _ => h1, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h h1⟩

/-- The step type `1` (up) is taken exactly on `[1/4, 1/2)`. -/
theorem stepType_eq_one_iff (u : ℝ) : stepType u = 1 ↔ 1 / 4 ≤ u ∧ u < 1 / 2 := by
  unfold stepType
  split_ifs with h1 h2
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h.1 (not_le.mpr h1)⟩
  · exact ⟨fun _ => ⟨not_lt.mp h1, h2⟩, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by decide), fun h => absurd h.2 h2⟩

/-- The step type `2` (horizontal) is taken exactly on `[1/2, ∞)`. -/
theorem stepType_eq_two_iff (u : ℝ) : stepType u = 2 ↔ 1 / 2 ≤ u := by
  unfold stepType
  split_ifs with h1 h2
  · exact ⟨fun h => absurd h (by decide), fun h => (show False by linarith).elim⟩
  · exact ⟨fun h => absurd h (by decide), fun h => (show False by linarith).elim⟩
  · exact ⟨fun _ => not_lt.mp h2, fun _ => rfl⟩

/-- The step type `0` has probability `1/4` under one uniform. -/
theorem stepLaw_stepType_eq_zero : stepLaw {u | stepType u = 0} = ENNReal.ofReal (1 / 4) := by
  have hset : {u : ℝ | stepType u = 0} ∩ Ico 0 1 = Ico 0 (1 / 4) := by
    ext u
    simp only [mem_inter_iff, mem_setOf_eq, mem_Ico]
    rw [stepType_eq_zero_iff]
    constructor
    · rintro ⟨h, h0, _⟩
      exact ⟨h0, h⟩
    · rintro ⟨h0, h⟩
      exact ⟨h, h0, by linarith⟩
  rw [stepLaw, Measure.restrict_apply' measurableSet_Ico, hset, Real.volume_Ico]
  norm_num

/-- The step type `1` has probability `1/4` under one uniform. -/
theorem stepLaw_stepType_eq_one : stepLaw {u | stepType u = 1} = ENNReal.ofReal (1 / 4) := by
  have hset : {u : ℝ | stepType u = 1} ∩ Ico 0 1 = Ico (1 / 4) (1 / 2) := by
    ext u
    simp only [mem_inter_iff, mem_setOf_eq, mem_Ico]
    rw [stepType_eq_one_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2⟩, by linarith, by linarith⟩
  rw [stepLaw, Measure.restrict_apply' measurableSet_Ico, hset, Real.volume_Ico]
  norm_num

/-- The step type `2` has probability `1/2` under one uniform. -/
theorem stepLaw_stepType_eq_two : stepLaw {u | stepType u = 2} = ENNReal.ofReal (1 / 2) := by
  have hset : {u : ℝ | stepType u = 2} ∩ Ico 0 1 = Ico (1 / 2) 1 := by
    ext u
    simp only [mem_inter_iff, mem_setOf_eq, mem_Ico]
    rw [stepType_eq_two_iff]
    constructor
    · rintro ⟨h, _, h1⟩
      exact ⟨h, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by linarith, h2⟩
  rw [stepLaw, Measure.restrict_apply' measurableSet_Ico, hset, Real.volume_Ico]
  norm_num

/-- The ladder inputs form a probability measure. -/
instance ladderInLaw_isProbability : IsProbabilityMeasure ladderInLaw := by
  unfold ladderInLaw
  infer_instance

end

end IdlaCyl.Silvestri

namespace IdlaCyl.FiniteLaw

noncomputable section

variable {α : Type*} [Fintype α]

/-- The cumulative weight of the atoms whose enumeration index (from
`Fintype.equivFin`) is below `j`. -/
def cum (μ : FiniteLaw α) (j : ℕ) : ℝ :=
  ∑ x, if (Fintype.equivFin α x : ℕ) < j then μ.weight x else 0

/-- The cumulative weight is zero before the first index. -/
theorem cum_zero (μ : FiniteLaw α) : μ.cum 0 = 0 := by
  simp [cum]

/-- The cumulative weight is nonnegative. -/
theorem cum_nonneg (μ : FiniteLaw α) (j : ℕ) : 0 ≤ μ.cum j :=
  Finset.sum_nonneg fun x _ => by
    split_ifs
    · exact μ.nonneg x
    · exact le_rfl

/-- The cumulative weight is monotone in the index. -/
theorem cum_mono (μ : FiniteLaw α) {j j' : ℕ} (h : j ≤ j') : μ.cum j ≤ μ.cum j' :=
  Finset.sum_le_sum fun x _ => by
    split_ifs with h1 h2 <;> first | exact le_rfl | exact μ.nonneg x | (exfalso; omega)

/-- The cumulative weight of all atoms is one. -/
theorem cum_card (μ : FiniteLaw α) : μ.cum (Fintype.card α) = 1 :=
  (Finset.sum_congr rfl fun x _ => if_pos (Fintype.equivFin α x).isLt).trans μ.total

/-- The increment of the cumulative weight across the enumeration index of `a` is
the weight of `a`. -/
theorem cum_succ_sub (μ : FiniteLaw α) (a : α) :
    μ.cum ((Fintype.equivFin α a : ℕ) + 1) - μ.cum (Fintype.equivFin α a : ℕ) =
      μ.weight a := by
  unfold cum
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    have hne : (Fintype.equivFin α b : ℕ) ≠ (Fintype.equivFin α a : ℕ) :=
      fun h => hb ((Fintype.equivFin α).injective (Fin.ext h))
    split_ifs <;> first | omega | simp
  · intro h
    exact absurd (Finset.mem_univ a) h

/-- The largest index `j ≤ card α` whose cumulative weight `cum j` is at most `u`. -/
def index (μ : FiniteLaw α) (u : ℝ) : ℕ :=
  Nat.findGreatest (fun j => μ.cum j ≤ u) (Fintype.card α)

/-- The atom of enumeration index `j`, with the default atom `Classical.arbitrary α`
for `j ≥ card α`. -/
def pick [Nonempty α] (j : ℕ) : α :=
  if h : j < Fintype.card α then (Fintype.equivFin α).symm ⟨j, h⟩
  else Classical.arbitrary α

/-- The inverse-CDF sampler: `sample μ u` is the atom whose cumulative interval
`[cum i, cum (i+1))` contains `u`. On `[0,1)` this is exact. Outside `[0,1)` it
returns a fixed atom, which the law statements never use. -/
def sample [Nonempty α] (μ : FiniteLaw α) (u : ℝ) : α :=
  pick (μ.index u)

/-- Within the range, `pick j` is the atom of enumeration index `j`. -/
theorem pick_eq_iff [Nonempty α] {j : ℕ} (hj : j < Fintype.card α) (a : α) :
    pick j = a ↔ j = (Fintype.equivFin α a : ℕ) := by
  unfold pick
  rw [dif_pos hj, Equiv.symm_apply_eq, Fin.ext_iff]

/-- For `u ≥ 0`, the index equals `i` exactly when `u` lies in `[cum i, cum (i+1))`. -/
theorem index_eq_iff (μ : FiniteLaw α) {i : ℕ} (hi : i < Fintype.card α) {u : ℝ}
    (hu : 0 ≤ u) : μ.index u = i ↔ μ.cum i ≤ u ∧ u < μ.cum (i + 1) := by
  unfold index
  have h0 : (fun j => μ.cum j ≤ u) 0 := by
    show μ.cum 0 ≤ u
    rw [cum_zero]
    exact hu
  constructor
  · intro h
    have hP : μ.cum (Nat.findGreatest (fun j => μ.cum j ≤ u) (Fintype.card α)) ≤ u :=
      Nat.findGreatest_spec (P := fun j => μ.cum j ≤ u) (Nat.zero_le _) h0
    rw [h] at hP
    refine ⟨hP, ?_⟩
    by_contra hc
    have hc' : μ.cum (i + 1) ≤ u := not_lt.mp hc
    have hle := Nat.le_findGreatest (P := fun j => μ.cum j ≤ u) hi hc'
    rw [h] at hle
    omega
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · by_contra hc
      have hc' : i < Nat.findGreatest (fun j => μ.cum j ≤ u) (Fintype.card α) :=
        not_le.mp hc
      have hP : μ.cum (Nat.findGreatest (fun j => μ.cum j ≤ u) (Fintype.card α)) ≤ u :=
        Nat.findGreatest_spec (P := fun j => μ.cum j ≤ u) (Nat.zero_le _) h0
      have hmono := μ.cum_mono (show i + 1 ≤ _ from hc')
      linarith
    · exact Nat.le_findGreatest hi.le h1

/-- On `[0,1)` the index is a valid enumeration index. -/
theorem index_lt (μ : FiniteLaw α) {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) :
    μ.index u < Fintype.card α := by
  unfold index
  refine lt_of_le_of_ne (Nat.findGreatest_le _) ?_
  intro h
  have h0 : (fun j => μ.cum j ≤ u) 0 := by
    show μ.cum 0 ≤ u
    rw [cum_zero]
    exact hu
  have hP : μ.cum (Nat.findGreatest (fun j => μ.cum j ≤ u) (Fintype.card α)) ≤ u :=
    Nat.findGreatest_spec (P := fun j => μ.cum j ≤ u) (Nat.zero_le _) h0
  rw [h, cum_card] at hP
  linarith

/-- On `[0,1)`, the sampler returns `a` exactly when `u` lies in the cumulative
interval of `a`. -/
theorem sample_eq_iff [Nonempty α] (μ : FiniteLaw α) (a : α) {u : ℝ} (hu : 0 ≤ u)
    (hu1 : u < 1) :
    μ.sample u = a ↔ μ.cum (Fintype.equivFin α a : ℕ) ≤ u ∧
      u < μ.cum ((Fintype.equivFin α a : ℕ) + 1) := by
  unfold sample
  rw [pick_eq_iff (μ.index_lt hu hu1) a]
  exact μ.index_eq_iff (Fintype.equivFin α a).isLt hu

/-- The sampler returns an atom of positive weight on `[0,1)`. -/
theorem sample_ne_zero_weight [Nonempty α] (μ : FiniteLaw α) {u : ℝ} (hu : 0 ≤ u)
    (hu1 : u < 1) : μ.weight (μ.sample u) ≠ 0 := by
  have h := (μ.sample_eq_iff (μ.sample u) hu hu1).1 rfl
  have hpos : 0 < μ.cum ((Fintype.equivFin α (μ.sample u) : ℕ) + 1) -
      μ.cum (Fintype.equivFin α (μ.sample u) : ℕ) := by
    linarith [h.1, h.2]
  rw [cum_succ_sub] at hpos
  exact hpos.ne'

/-- Inverse-CDF sampling is exact: for `u` uniform on `[0,1)`, the atom `a` is
returned with probability `μ.weight a`. -/
theorem sample_law [Nonempty α] (μ : FiniteLaw α) (a : α) :
    stepLaw {u | μ.sample u = a} = ENNReal.ofReal (μ.weight a) := by
  rw [stepLaw, Measure.restrict_apply' measurableSet_Ico]
  have hset : {u : ℝ | μ.sample u = a} ∩ Ico 0 1 =
      Ico (μ.cum (Fintype.equivFin α a : ℕ))
        (μ.cum ((Fintype.equivFin α a : ℕ) + 1)) := by
    ext u
    simp only [mem_inter_iff, mem_setOf_eq, mem_Ico]
    constructor
    · rintro ⟨hs, hu0, hu1⟩
      exact (μ.sample_eq_iff a hu0 hu1).1 hs
    · intro hu
      have hlow : 0 ≤ μ.cum (Fintype.equivFin α a : ℕ) := μ.cum_nonneg _
      have hhigh : μ.cum ((Fintype.equivFin α a : ℕ) + 1) ≤ 1 := by
        rw [← μ.cum_card]
        exact μ.cum_mono (Nat.succ_le_of_lt (Fintype.equivFin α a).isLt)
      exact ⟨(μ.sample_eq_iff a (by linarith [hu.1]) (by linarith [hu.2])).2 hu,
        by linarith [hu.1], by linarith [hu.2]⟩
  rw [hset, Real.volume_Ico, μ.cum_succ_sub a]

/-- The index is zero for negative `u`, where no cumulative weight is at most `u`. -/
theorem index_of_neg (μ : FiniteLaw α) {u : ℝ} (hu : u < 0) : μ.index u = 0 := by
  unfold index
  rw [Nat.findGreatest_eq_zero_iff]
  intro n _ _ hc
  have hc' : μ.cum n ≤ u := hc
  linarith [μ.cum_nonneg n]

/-- The index is monotone in `u`. -/
theorem index_monotone (μ : FiniteLaw α) : Monotone μ.index := by
  intro u v huv
  by_cases hu : 0 ≤ u
  · have h0 : (fun j => μ.cum j ≤ u) 0 := by
      show μ.cum 0 ≤ u
      rw [cum_zero]
      exact hu
    have hP : μ.cum (μ.index u) ≤ u :=
      Nat.findGreatest_spec (P := fun j => μ.cum j ≤ u) (Nat.zero_le _) h0
    exact Nat.le_findGreatest (P := fun j => μ.cum j ≤ v)
      (show μ.index u ≤ Fintype.card α from Nat.findGreatest_le _) (le_trans hP huv)
  · rw [not_le] at hu
    rw [μ.index_of_neg hu]
    exact Nat.zero_le _

/-- The index is a measurable function of `u`. -/
theorem measurable_index (μ : FiniteLaw α) : Measurable μ.index :=
  μ.index_monotone.measurable

/-- The sampler is measurable in `u`. -/
theorem measurable_sample [MeasurableSpace α] [Nonempty α] (μ : FiniteLaw α) :
    Measurable fun u : ℝ => μ.sample u :=
  (measurable_from_nat (f := pick (α := α))).comp μ.measurable_index

end

end IdlaCyl.FiniteLaw

namespace IdlaCyl.Silvestri

noncomputable section

/-- The vertical increment of a step type: down `-1`, up `1`, horizontal `0`. -/
def stepIncr : Fin 3 → ℤ := ![-1, 1, 0]

theorem stepIncr_eq_neg_one_iff (k : Fin 3) : stepIncr k = -1 ↔ k = 0 := by
  fin_cases k <;> simp [stepIncr]

theorem stepIncr_eq_one_iff (k : Fin 3) : stepIncr k = 1 ↔ k = 1 := by
  fin_cases k <;> simp [stepIncr]

theorem stepIncr_eq_zero_iff (k : Fin 3) : stepIncr k = 0 ↔ k = 2 := by
  fin_cases k <;> simp [stepIncr]

/-- The step type is measurable. -/
theorem measurable_stepType : Measurable stepType := by
  refine measurable_to_countable' fun k => ?_
  have hk0 : stepType ⁻¹' {0} = Iio (1 / 4) := by
    ext u
    simp only [mem_preimage, mem_singleton_iff, mem_Iio]
    exact stepType_eq_zero_iff u
  have hk1 : stepType ⁻¹' {1} = Ico (1 / 4) (1 / 2) := by
    ext u
    simp only [mem_preimage, mem_singleton_iff, mem_Ico]
    exact stepType_eq_one_iff u
  have hk2 : stepType ⁻¹' {2} = Ici (1 / 2) := by
    ext u
    simp only [mem_preimage, mem_singleton_iff, mem_Ici]
    exact stepType_eq_two_iff u
  fin_cases k
  · show MeasurableSet (stepType ⁻¹' {0})
    rw [hk0]
    exact measurableSet_Iio
  · show MeasurableSet (stepType ⁻¹' {1})
    rw [hk1]
    exact measurableSet_Ico
  · show MeasurableSet (stepType ⁻¹' {2})
    rw [hk2]
    exact measurableSet_Ici

theorem measurable_stepIncr_comp : Measurable fun u => stepIncr (stepType u) :=
  (measurable_of_finite stepIncr).comp measurable_stepType

/-- The vertical increment `stepIncr (stepType u)` of one uniform `u` has the explicit
law `1/4 δ_{-1} + 1/4 δ_{1} + 1/2 δ_{0}`, which is the law `typeLaw` of the driven
walk's vertical increment. -/
theorem stepLaw_map_stepIncr :
    stepLaw.map (fun u => stepIncr (stepType u)) =
      (1 / 4 : ℝ≥0∞) • Measure.dirac (-1 : ℤ) + (1 / 4 : ℝ≥0∞) • Measure.dirac (1 : ℤ) +
        (1 / 2 : ℝ≥0∞) • Measure.dirac (0 : ℤ) := by
  refine Measure.ext_of_singleton fun x => ?_
  rw [Measure.map_apply measurable_stepIncr_comp (measurableSet_singleton x)]
  rcases (show x = -1 ∨ x = 1 ∨ x = 0 ∨ (x ≠ -1 ∧ x ≠ 1 ∧ x ≠ 0) by omega) with
    rfl | rfl | rfl | ⟨h1, h2, h3⟩
  · have hp : (fun u => stepIncr (stepType u)) ⁻¹' {-1} = {u | stepType u = 0} := by
      ext u
      simp only [mem_preimage, mem_singleton_iff, mem_setOf_eq]
      exact stepIncr_eq_neg_one_iff _
    rw [hp, stepLaw_stepType_eq_zero]
    simp [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply']
  · have hp : (fun u => stepIncr (stepType u)) ⁻¹' {1} = {u | stepType u = 1} := by
      ext u
      simp only [mem_preimage, mem_singleton_iff, mem_setOf_eq]
      exact stepIncr_eq_one_iff _
    rw [hp, stepLaw_stepType_eq_one]
    simp [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply']
  · have hp : (fun u => stepIncr (stepType u)) ⁻¹' {0} = {u | stepType u = 2} := by
      ext u
      simp only [mem_preimage, mem_singleton_iff, mem_setOf_eq]
      exact stepIncr_eq_zero_iff _
    rw [hp, stepLaw_stepType_eq_two]
    simp [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply']
  · have hp : (fun u => stepIncr (stepType u)) ⁻¹' {x} = ∅ := by
      ext u
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro h
      have hne : ∀ k : Fin 3, stepIncr k ≠ x := by
        intro k
        fin_cases k <;> simp [stepIncr] <;> omega
      exact hne _ h
    rw [hp]
    simp [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply',
      Ne.symm h1, Ne.symm h2, Ne.symm h3]

end

end IdlaCyl.Silvestri
