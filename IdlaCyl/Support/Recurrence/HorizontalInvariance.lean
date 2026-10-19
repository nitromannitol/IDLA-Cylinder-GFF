import IdlaCyl.Support.FirstHit

/-!
# Horizontal invariance of the probability of never reaching a height

The probability that the cylinder walk started at `(x, y)` stays strictly below height `k`
forever does not depend on the horizontal coordinate `x`.  This is vertex-transitivity of the
base (`tex:229`), applied through the equivariance `walkPathLaw_map_siteEquiv` of the walk law
under a graph automorphism of the base.  It is one of the four ingredients in the discharge of
`IdlaCyl.External.LazyRwRecurrent` (`tex:600-604`).

Paper: `paper/idla-cylinder-gff.tex`.
-/

namespace IdlaCyl.Recurrence

open MeasureTheory

theorem neverReach_hor (B : Base) (k : ℤ) (x x' : B.V) (y : ℤ) :
    walkPathLaw B (x, y) {X : ℕ → Site B | ∀ n, (X n).2 < k}
      = walkPathLaw B (x', y) {X : ℕ → Site B | ∀ n, (X n).2 < k} := by
  obtain ⟨σ, hσ⟩ := B.vertexTransitive x x'
  have hmeas : Measurable (fun (X : ℕ → Site B) (n : ℕ) => horIso B σ (X n)) :=
    measurable_pi_lambda _ fun n =>
      (measurable_of_countable (horIso B σ)).comp (measurable_pi_apply n)
  have hE : MeasurableSet {X : ℕ → Site B | ∀ n, (X n).2 < k} := by
    have h : {X : ℕ → Site B | ∀ n, (X n).2 < k}
        = ⋂ n : ℕ, (fun X : ℕ → Site B => (X n).2) ⁻¹' {z : ℤ | z < k} := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [h]
    exact MeasurableSet.iInter fun n =>
      (measurable_snd.comp (measurable_pi_apply n)) (MeasurableSet.of_discrete)
  have hpre : (fun (X : ℕ → Site B) (n : ℕ) => horIso B σ (X n)) ⁻¹'
      {X : ℕ → Site B | ∀ n, (X n).2 < k} = {X : ℕ → Site B | ∀ n, (X n).2 < k} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_setOf_eq, horIso_apply]
  have hstart : horIso B σ ((x, y) : Site B) = ((x', y) : Site B) := by
    simp only [horIso_apply, hσ]
  have hlaw := walkPathLaw_map_siteEquiv B (horIso B σ) (cylKernel_horIso B σ) ((x, y) : Site B)
  rw [hstart] at hlaw
  rw [← hlaw, Measure.map_apply hmeas hE, hpre]

end IdlaCyl.Recurrence
