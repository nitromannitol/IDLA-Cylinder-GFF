/-
Outer domination in probability, for the literal ordinary and balanced laws.
Source: paper/idla-cylinder-gff.tex, tex:1385-1431.
The ordinary law is identified with task 7's fresh queue-completion experiment;
only the resulting laws, never reordered original labelled paths, are compared.
-/
import IdlaCyl.Support.Outer.FlatBalanced
import IdlaCyl.Support.Outer.Resume

attribute [local instance] Classical.propDecidable
namespace IdlaCyl
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

/-- Ordinary height failure is the integral of the actual conditional fresh queue law. -/
theorem outer_height_probability_eq_lintegral (B : Base) (h : ℤ) (hh : 1 ≤ h)
    (T : ℕ) (a : ℝ) :
    idlaMeasure B {ω : TrajSeq B | ¬ clusterTraj B ω T ⊆ R B a} =
      ∫⁻ ω, resumeRun B (resumePauseGrow B h ω T).1 (resumePauseGrow B h ω T).2
        (outerHeightEvent B a) ∂idlaMeasure B := by
  have heq := congrArg (fun μ : Measure (ResumeFinite B) => μ (outerHeightEvent B a))
    (resumePauseGrow_finish_law B h hh T)
  rw [Measure.bind_apply (Set.to_countable _).measurableSet
      (measurable_of_countable _).aemeasurable,
    lintegral_map (measurable_of_countable _ ) (measurable_resumePauseGrow B h T),
    Measure.map_apply (measurable_resumeGrow B (resumeEmpty B) T)
      (Set.to_countable _).measurableSet] at heq
  rw [heq]
  symm
  congr 1
  ext ω
  change (¬ resumeSeed B (resumeGrow B (resumeEmpty B) ω T) ⊆ R B a) ↔ _
  rw [resumeSeed_grow, resumeSeed_empty]
  rfl

/-- The union of fill failure and an excessive finite frozen multiplicity is measurable. -/
theorem measurableSet_outer_height_bad (B : Base) (h : ℤ) (T m : ℕ) :
    MeasurableSet {ω : TrajSeq B |
      ω ∉ outerFill B h T ∨ ∃ x : B.V, m < frozenCount B h T ω x} := by
  have hx (x : B.V) : MeasurableSet {ω : TrajSeq B | m < frozenCount B h T ω x} :=
    (measurable_frozenCount B h T x) (Set.to_countable {n : ℕ | m < n}).measurableSet
  have heq : {ω : TrajSeq B |
      ω ∉ outerFill B h T ∨ ∃ x : B.V, m < frozenCount B h T ω x} =
      (outerFill B h T)ᶜ ∪ ⋃ x : B.V, {ω : TrajSeq B | m < frozenCount B h T ω x} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion]
  rw [heq]
  exact (measurableSet_outerFill B h T).compl.union (MeasurableSet.iUnion hx)

/-- The exact outer-route comparison, without any supplied coupling or law hypothesis. -/
theorem outer_height_comparison (B : Base) (h : ℤ) (hh : 1 ≤ h)
    (T m : ℕ) (r : ℝ) :
  idlaMeasure B {ω : TrajSeq B |
    ¬ clusterTraj B ω T ⊆ R B ((h : ℝ) + r)} ≤
      idlaMeasure B {ω : TrajSeq B |
        ω ∉ outerFill B h T ∨ ∃ x : B.V, m < frozenCount B h T ω x} +
      balancedLaw B m {η : BalancedDriver B m |
        ¬ balancedCluster B m η ⊆ R B r} := by
  let bad : Set (TrajSeq B) := {ω |
    ω ∉ outerFill B h T ∨ ∃ x : B.V, m < frozenCount B h T ω x}
  let c := balancedLaw B m {η : BalancedDriver B m | ¬ balancedCluster B m η ⊆ R B r}
  have hbad : MeasurableSet bad := measurableSet_outer_height_bad B h T m
  have hpoint (ω : TrajSeq B) :
      resumeRun B (resumePauseGrow B h ω T).1 (resumePauseGrow B h ω T).2
        (outerHeightEvent B ((h : ℝ) + r)) ≤ bad.indicator (fun _ => (1 : ℝ≥0∞)) ω + c := by
    by_cases hb : ω ∈ bad
    · rw [Set.indicator_of_mem hb]
      exact (prob_le_one (μ := resumeRun B (resumePauseGrow B h ω T).1
        (resumePauseGrow B h ω T).2)).trans (le_add_of_nonneg_right bot_le)
    · rw [Set.indicator_of_notMem hb, zero_add]
      apply outerPaused_height_le B h hh T m r ω
      intro x
      by_contra hcount
      exact hb (Or.inr ⟨x, Nat.lt_of_not_ge hcount⟩)
  rw [outer_height_probability_eq_lintegral B h hh T ((h : ℝ) + r)]
  calc
    _ ≤ ∫⁻ ω, bad.indicator (fun _ => (1 : ℝ≥0∞)) ω + c ∂idlaMeasure B :=
      lintegral_mono hpoint
    _ = idlaMeasure B bad + c := by
      rw [lintegral_add_left (measurable_const.indicator hbad),
        lintegral_indicator_fun_one hbad, lintegral_const, measure_univ, mul_one]

/-- Two vertices, no particles: the theorem still has its literal probability meaning. -/
example (m : ℕ) (r : ℝ) :
    idlaMeasure PrInnerTail.K2 {ω : TrajSeq PrInnerTail.K2 |
      ¬ clusterTraj PrInnerTail.K2 ω 0 ⊆ R PrInnerTail.K2 ((1 : ℤ) + r)} ≤
      idlaMeasure PrInnerTail.K2 {ω : TrajSeq PrInnerTail.K2 |
        ω ∉ outerFill PrInnerTail.K2 1 0 ∨
          ∃ x : PrInnerTail.K2.V, m < frozenCount PrInnerTail.K2 1 0 ω x} +
      balancedLaw PrInnerTail.K2 m {η : BalancedDriver PrInnerTail.K2 m |
        ¬ balancedCluster PrInnerTail.K2 m η ⊆ R PrInnerTail.K2 r} :=
  outer_height_comparison PrInnerTail.K2 1 (by norm_num) 0 m r

end
end IdlaCyl
