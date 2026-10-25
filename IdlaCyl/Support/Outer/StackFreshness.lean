module

/-
Unused arrows after a finite exploration.
Source: paper/idla-cylinder-gff.tex, tex:1331-1351,1391-1396.
Independence is proved from disjoint coordinates of outerStackLaw, including
all of the infinitely many retained arrows.
-/
public import IdlaCyl.Support.Outer.StackWalk

@[expose] public section

attribute [local instance] Classical.propDecidable

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

/-- Drop the prescribed number of consumed entries at each site. -/
def outerUnused (B : Base) (u : Site B → ℕ) (r : OuterStacks B) : OuterStacks B :=
  fun e => r (e.1, u e.1 + e.2)

/-- The retained arrow field is measurable for each deterministic odometer. -/
theorem measurable_outerUnused (B : Base) (u : Site B → ℕ) :
    Measurable (outerUnused B u) :=
  measurable_pi_iff.mpr (fun e => measurable_pi_apply (e.1, u e.1 + e.2))

/-- Deterministic stack shifts preserve the full independent arrow law. -/
theorem outerUnused_law (B : Base) (u : Site B → ℕ) :
    (outerStackLaw B).map (outerUnused B u) = outerStackLaw B := by
  letI : ∀ e : Site B × ℕ, IsProbabilityMeasure (cylMeasure B e.1) :=
    fun e => cylMeasure_isProbability B e.1
  have hinj : Function.Injective (fun e : Site B × ℕ => (e.1, u e.1 + e.2)) := by
    rintro ⟨x, i⟩ ⟨y, j⟩ h
    have hs : x = y := congrArg Prod.fst h
    subst y
    have hi := congrArg Prod.snd h
    change u x + i = u x + j at hi
    simp only [Prod.mk.injEq, true_and]
    omega
  exact Measure.map_infinitePi_infinitePi_of_inj hinj

private theorem outerStack_indep_subfamilies (B : Base) {I J : Type*}
    (c : I → Site B × ℕ) (d : J → Site B × ℕ)
    (hdisj : Disjoint (Set.range c) (Set.range d)) :
    IndepFun (fun r : OuterStacks B => fun i => r (c i))
      (fun r : OuterStacks B => fun j => r (d j)) (outerStackLaw B) := by
  let m : (Site B × ℕ) → MeasurableSpace (OuterStacks B) :=
    fun e => MeasurableSpace.comap (fun r => r e) inferInstance
  have hi : Indep (⨆ e ∈ Set.range c, m e) (⨆ e ∈ Set.range d, m e)
      (outerStackLaw B) :=
    indep_iSup_of_disjoint (fun e => (measurable_pi_apply e).comap_le)
      (outerStackLaw_iIndepFun B) hdisj
  apply indep_of_indep_of_le hi
  · rw [MeasurableSpace.comap_process_pi]
    exact iSup_le (fun i => le_iSup_of_le (c i) (le_iSup_of_le ⟨i, rfl⟩ le_rfl))
  · rw [MeasurableSpace.comap_process_pi]
    exact iSup_le (fun j => le_iSup_of_le (d j) (le_iSup_of_le ⟨j, rfl⟩ le_rfl))

private theorem outerVisits_step_le (B : Base) (f : ℕ → Site B) (n : ℕ)
    (i : Fin n) : outerVisits B f i (f i) + 1 ≤ outerVisits B f n (f i) := by
  have hmono : ∀ j k : ℕ, j ≤ k → ∀ x : Site B,
      outerVisits B f j x ≤ outerVisits B f k x := by
    intro j k hjk x
    induction k, hjk using Nat.le_induction with
    | base => exact le_rfl
    | succ k _ ih =>
        simp only [outerVisits]
        omega
  have h := hmono (i + 1) n (by omega) (f i)
  simpa only [outerVisits, ite_true] using h

/-- Every exposed arrow is independent of the entire retained stack field. -/
theorem outerStack_prefix_indep_unused (B : Base) (f : ℕ → Site B) (n : ℕ) :
    IndepFun
      (fun r : OuterStacks B => fun i : Fin n => r (f i, outerVisits B f i (f i)))
      (outerUnused B (outerVisits B f n)) (outerStackLaw B) := by
  apply outerStack_indep_subfamilies B
  apply Set.disjoint_left.mpr
  rintro e ⟨i, hi⟩ ⟨j, hj⟩
  have hs : f i = j.1 := congrArg Prod.fst (hi.trans hj.symm)
  have hc : outerVisits B f i (f i) = outerVisits B f n j.1 + j.2 :=
    congrArg Prod.snd (hi.trans hj.symm)
  have hlt := outerVisits_step_le B f n i
  rw [← hs] at hc
  omega

/-- Freshness of all unused arrows on every prescribed finite path cylinder. -/
theorem outerStackWalk_prefix_unused (B : Base) (p : Site B) (f : ℕ → Site B)
    (n : ℕ) (A : Set (OuterStacks B)) (hA : MeasurableSet A) :
    outerStackLaw B ((outerStackWalk B p) ⁻¹' pathCyl B n f ∩
        (outerUnused B (outerVisits B f n)) ⁻¹' A) =
      outerStackLaw B ((outerStackWalk B p) ⁻¹' pathCyl B n f) * outerStackLaw B A := by
  by_cases hp : f 0 = p
  · let v : OuterStacks B → Fin n → Site B :=
      fun r i => r (f i, outerVisits B f i (f i))
    let z : Fin n → Site B := fun i => f (i + 1)
    have heq : (outerStackWalk B p) ⁻¹' pathCyl B n f = v ⁻¹' {z} := by
      ext r
      change (∀ i ≤ n, outerStackWalk B p r i = f i) ↔ v r = z
      rw [outerStackWalk_prefix_iff, and_iff_right hp]
      exact ⟨fun h => funext (fun i => h i i.2),
        fun h i hi => congrFun h ⟨i, hi⟩⟩
    rw [heq]
    have hi := (outerStack_prefix_indep_unused B f n).measure_inter_preimage_eq_mul
      {z} A (measurableSet_singleton z) hA
    rw [← Measure.map_apply (measurable_outerUnused B (outerVisits B f n)) hA,
      outerUnused_law] at hi
    exact hi
  · have heq : (outerStackWalk B p) ⁻¹' pathCyl B n f = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro r hr
      exact hp ((outerStackWalk_prefix_iff B p r n f).mp hr).1
    rw [heq, Set.empty_inter, measure_empty, zero_mul]


example (B : Base) :
    (outerStackLaw B).map (outerUnused B (fun _ => 1)) = outerStackLaw B :=
  outerUnused_law B (fun _ => 1)

end
end IdlaCyl
