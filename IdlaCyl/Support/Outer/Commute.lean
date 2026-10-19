/-
Adjacent walk releases commute in law.
Source: paper/idla-cylinder-gff.tex, tex:1331-1351,1391-1396.
Fresh independent site arrows realize both walk orders; finite abelianity
identifies their outputs on the probability-one event of termination.
-/
import IdlaCyl.Support.Outer.StackStopped
import IdlaCyl.Support.Outer.StackAbelian

attribute [local instance] Classical.propDecidable
namespace IdlaCyl
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section

/-- Both stages of the common-stack explorer terminate almost surely. -/
theorem outerStackPair_ae_finite (B : Base) (a : ℤ) (F : Finset (Site B)) (p q : Site B) :
    ∀ᵐ r ∂outerStackLaw B,
      exitTime' B (R B (a : ℝ) ∪ (F : Set (Site B))) (outerStackWalk B p r) ≠ ⊤ ∧
      exitTime' B (addWalk B (R B (a : ℝ) ∪ (F : Set (Site B))) (outerStackWalk B p r))
        (outerStackWalk B q (outerStackRemainder B (R B (a : ℝ) ∪ (F : Set (Site B))) p r)) ≠ ⊤ := by
  let A := R B (a : ℝ) ∪ (F : Set (Site B))
  let μ := (walkPathLaw B p).map (exitSite' B A)
  haveI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (measurable_exitSite' B A).aemeasurable
  have htime : Measurable (fun sr : Site B × OuterStacks B =>
      exitTime' B (A ∪ {sr.1}) (outerStackWalk B q sr.2)) := by
    apply measurable_from_prod_countable_right
    intro s
    exact (measurable_exitTime'_outer B (A ∪ {s})).comp (measurable_outerStackWalk B q)
  have hsecond : ∀ᵐ sr ∂μ.prod (outerStackLaw B),
      exitTime' B (A ∪ {sr.1}) (outerStackWalk B q sr.2) ≠ ⊤ := by
    have hmeas : MeasurableSet {sr : Site B × OuterStacks B |
        exitTime' B (A ∪ {sr.1}) (outerStackWalk B q sr.2) ≠ ⊤} :=
      (htime (measurableSet_singleton (⊤ : ℕ∞))).compl
    apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
    apply Filter.Eventually.of_forall
    intro s
    have hseed : A ∪ {s} = R B (a : ℝ) ∪ (↑(insert s F) : Set (Site B)) := by
      ext z
      simp only [A, Set.mem_union, Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_insert]
      tauto
    change ∀ᵐ r ∂outerStackLaw B, exitTime' B (A ∪ {s}) (outerStackWalk B q r) ≠ ⊤
    rw [hseed]
    exact outerStackWalk_ae_exit_ne_top B a (insert s F) q
  rw [← outerStack_exit_remainder_law B a F p] at hsecond
  have hstep : Measurable (fun r =>
      (exitSite' B A (outerStackWalk B p r), outerStackRemainder B A p r)) :=
    ((measurable_exitSite' B A).comp (measurable_outerStackWalk B p)).prodMk
      (measurable_outerStackRemainder B A p)
  have hsecond' := ae_of_ae_map hstep.aemeasurable hsecond
  filter_upwards [outerStackWalk_ae_exit_ne_top B a F p, hsecond'] with r hr hs
  exact ⟨hr, hs⟩

/-- Both release orders have the same common-stack output almost surely. -/
theorem outerStackPair_ae_commute (B : Base) (a : ℤ) (F : Finset (Site B)) (p q : Site B) :
    ∀ᵐ r ∂outerStackLaw B,
      outerStackPair B (R B (a : ℝ) ∪ (F : Set (Site B))) p q r =
        outerStackPair B (R B (a : ℝ) ∪ (F : Set (Site B))) q p r := by
  filter_upwards [outerStackPair_ae_finite B a F p q, outerStackPair_ae_finite B a F q p]
    with r hpq hqp
  exact OuterFinite.outerStackPair_commute_of_finite B _ p q r hpq.1 hpq.2 hqp.1 hqp.2

/-- Adjacent prescribed cylinder-walk releases commute in law, with measurable outputs. -/
theorem addWalk_commute_in_law (B : Base) (a : ℤ) (F : Finset (Site B))
    (p q : Site B) :
  Measurable (fun XY : (ℕ → Site B) × (ℕ → Site B) => clusterCode B
    (addWalk B (addWalk B (R B (a : ℝ) ∪ (F : Set (Site B))) XY.1) XY.2)) ∧
  Measurable (fun XY : (ℕ → Site B) × (ℕ → Site B) => clusterCode B
    (addWalk B (addWalk B (R B (a : ℝ) ∪ (F : Set (Site B))) XY.2) XY.1)) ∧
  ((walkPathLaw B p).prod (walkPathLaw B q)).map
      (fun XY => clusterCode B
        (addWalk B (addWalk B (R B (a : ℝ) ∪ (F : Set (Site B))) XY.1) XY.2)) =
  ((walkPathLaw B p).prod (walkPathLaw B q)).map
      (fun XY => clusterCode B
        (addWalk B (addWalk B (R B (a : ℝ) ∪ (F : Set (Site B))) XY.2) XY.1)) := by
  refine ⟨(addWalk_commute_measurable B a F).1, (addWalk_commute_measurable B a F).2, ?_⟩
  have hstack : (outerStackLaw B).map (fun r => clusterCode B
        (outerStackPair B (R B (a : ℝ) ∪ (F : Set (Site B))) p q r)) =
      (outerStackLaw B).map (fun r => clusterCode B
        (outerStackPair B (R B (a : ℝ) ∪ (F : Set (Site B))) q p r)) :=
    Measure.map_congr ((outerStackPair_ae_commute B a F p q).mono
      (fun _ h => congrArg (clusterCode B) h))
  rw [outerStackPair_law, outerStackPair_law] at hstack
  have hswap := Measure.map_map (addWalk_commute_measurable B a F).1 measurable_swap
    (μ := (walkPathLaw B p).prod (walkPathLaw B q))
  rw [Measure.prod_swap] at hswap
  exact hstack.trans hswap

/-- Equal starts are included, without weakening either measurability requirement. -/
example (B : Base) (a : ℤ) (F : Finset (Site B)) (p : Site B) :
    ((walkPathLaw B p).prod (walkPathLaw B p)).map
        (fun XY => clusterCode B
          (addWalk B (addWalk B (R B (a : ℝ) ∪ (F : Set (Site B))) XY.1) XY.2)) =
      ((walkPathLaw B p).prod (walkPathLaw B p)).map
        (fun XY => clusterCode B
          (addWalk B (addWalk B (R B (a : ℝ) ∪ (F : Set (Site B))) XY.2) XY.1)) :=
  (addWalk_commute_in_law B a F p p).2.2

/-- On K₂, distinct prescribed starting vertices give genuine probability outputs. -/
example : IsProbabilityMeasure
    (((walkPathLaw PrInnerTail.K2 ((0 : Fin 2), 0)).prod
      (walkPathLaw PrInnerTail.K2 ((1 : Fin 2), 0))).map
        (fun XY => clusterCode PrInnerTail.K2
          (addWalk PrInnerTail.K2 (addWalk PrInnerTail.K2
            (R PrInnerTail.K2 0 ∪ (↑(∅ : Finset (Site PrInnerTail.K2)) : Set (Site PrInnerTail.K2)))
              XY.1) XY.2))) :=
  Measure.isProbabilityMeasure_map
    (measurable_addWalk_orders PrInnerTail.K2
      (R PrInnerTail.K2 0 ∪ (↑(∅ : Finset (Site PrInnerTail.K2)) : Set (Site PrInnerTail.K2)))).1.aemeasurable

end
end IdlaCyl
