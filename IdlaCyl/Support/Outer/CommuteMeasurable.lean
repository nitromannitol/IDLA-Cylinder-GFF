module

/-
Adjacent releases in law: measurable occupation outputs.
Source: paper/idla-cylinder-gff.tex, tex:1331-1351,1391-1396.
The two orders below use the literal addWalk and clusterCode maps. No pathwise
reordering of labelled walks is asserted.
-/
public import IdlaCyl.Support.Outer.StoppedBookkeeping

@[expose] public section

attribute [local instance] Classical.propDecidable

namespace IdlaCyl

open MeasureTheory ProbabilityTheory

noncomputable section

/-- Adding a walk to a fixed seed has measurable Boolean occupation coordinates. -/
theorem measurable_clusterCode_addWalk (B : Base) (A : Set (Site B)) :
    Measurable (fun X : ℕ → Site B => clusterCode B (addWalk B A X)) := by
  apply measurable_pi_iff.mpr
  intro z
  have hmem : MeasurableSet {X : ℕ → Site B | z ∈ addWalk B A X} := by
    have heq : {X : ℕ → Site B | z ∈ addWalk B A X} =
        {X : ℕ → Site B | z ∈ A} ∪ (exitSite' B A) ⁻¹' {z} := by
      ext X
      simp only [addWalk, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff,
        Set.mem_preimage, eq_comm]
    rw [heq]
    exact (MeasurableSet.const _).union ((measurable_exitSite' B A) (measurableSet_singleton z))
  exact Measurable.ite hmem measurable_const measurable_const

/-- The second exit is measurable jointly in the first settled site and the fresh walk. -/
theorem measurable_exitSite'_union_singleton (B : Base) (A : Set (Site B)) :
    Measurable (fun pX : Site B × (ℕ → Site B) => exitSite' B (A ∪ {pX.1}) pX.2) := by
  apply measurable_from_prod_countable_right
  intro p
  exact measurable_exitSite' B (A ∪ {p})

/-- Both adjacent-release outputs are measurable, for any fixed seed. -/
theorem measurable_addWalk_orders (B : Base) (A : Set (Site B)) :
    Measurable (fun XY : (ℕ → Site B) × (ℕ → Site B) =>
      clusterCode B (addWalk B (addWalk B A XY.1) XY.2)) ∧
    Measurable (fun XY : (ℕ → Site B) × (ℕ → Site B) =>
      clusterCode B (addWalk B (addWalk B A XY.2) XY.1)) := by
  have hf : Measurable (fun XY : (ℕ → Site B) × (ℕ → Site B) =>
      clusterCode B (addWalk B (addWalk B A XY.1) XY.2)) := by
    have hfirst : Measurable (fun XY : (ℕ → Site B) × (ℕ → Site B) =>
        exitSite' B A XY.1) := (measurable_exitSite' B A).comp measurable_fst
    have hsecond := (measurable_exitSite'_union_singleton B A).comp
      (hfirst.prodMk measurable_snd)
    apply measurable_pi_iff.mpr
    intro z
    have hmem : MeasurableSet {XY : (ℕ → Site B) × (ℕ → Site B) |
        z ∈ addWalk B (addWalk B A XY.1) XY.2} := by
      have heq : {XY : (ℕ → Site B) × (ℕ → Site B) |
          z ∈ addWalk B (addWalk B A XY.1) XY.2} =
          {XY : (ℕ → Site B) × (ℕ → Site B) | z ∈ A} ∪
          (fun XY => exitSite' B A XY.1) ⁻¹' {z} ∪
          (fun XY => exitSite' B (A ∪ {exitSite' B A XY.1}) XY.2) ⁻¹' {z} := by
        ext XY
        simp only [addWalk, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff,
          Set.mem_preimage, eq_comm]
      rw [heq]
      exact ((MeasurableSet.const _).union (hfirst (measurableSet_singleton z))).union
        (hsecond (measurableSet_singleton z))
    exact Measurable.ite hmem measurable_const measurable_const
  exact ⟨hf, hf.comp measurable_swap⟩

/-- The measurable part of the exact task-6 contract. -/
theorem addWalk_commute_measurable (B : Base) (a : ℤ) (F : Finset (Site B)) :
    Measurable (fun XY : (ℕ → Site B) × (ℕ → Site B) => clusterCode B
      (addWalk B (addWalk B (R B (a : ℝ) ∪ (F : Set (Site B))) XY.1) XY.2)) ∧
    Measurable (fun XY : (ℕ → Site B) × (ℕ → Site B) => clusterCode B
      (addWalk B (addWalk B (R B (a : ℝ) ∪ (F : Set (Site B))) XY.2) XY.1)) :=
  measurable_addWalk_orders B _


example (B : Base) (a : ℤ) (F : Finset (Site B)) (p : Site B) :
    IsProbabilityMeasure (((walkPathLaw B p).prod (walkPathLaw B p)).map
      (fun XY => clusterCode B
        (addWalk B (addWalk B (R B (a : ℝ) ∪ (F : Set (Site B))) XY.1) XY.2))) :=
  Measure.isProbabilityMeasure_map (addWalk_commute_measurable B a F).1.aemeasurable

end
end IdlaCyl
