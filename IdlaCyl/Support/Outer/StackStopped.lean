module

/-
Fresh unused arrows at a genuine finite exit.
Source: paper/idla-cylinder-gff.tex, tex:1331-1351,1391-1396.
-/
public import IdlaCyl.Support.Outer.StackFreshness

@[expose] public section

attribute [local instance] Classical.propDecidable

namespace IdlaCyl
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section

/-- The total exit time is a measurable countable-valued random variable. -/
theorem measurable_exitTime'_outer (B : Base) (A : Set (Site B)) :
    Measurable (exitTime' B A) := by
  have hSc : MeasurableSet (Aᶜ : Set (Site B)) := (Set.to_countable _).measurableSet
  have hu : Adapted (⊤ : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Site B)))
      (fun n (X : ℕ → Site B) => X n) := fun n => measurable_pi_apply n
  have ht : IsStoppingTime (⊤ : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Site B)))
      (exitTime' B A) := hu.isStoppingTime_hittingAfter hSc
  apply measurable_to_countable'
  intro t
  cases t with
  | coe n => exact ht.measurableSet_eq n
  | top =>
      have heq : (exitTime' B A) ⁻¹' {⊤} =
          ⋂ n : ℕ, {X : ℕ → Site B | X n ∈ A} := by
        ext X
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
        constructor
        · intro h n
          exact not_not.mp ((hittingAfter_eq_top_iff.mp h) n (Nat.zero_le _))
        · intro h
          exact hittingAfter_eq_top_iff.mpr (fun n _ => not_not.mpr (h n))
      rw [heq]
      exact MeasurableSet.iInter (fun n => (measurable_pi_apply n) (Set.to_countable A).measurableSet)

private theorem measurable_outerVisits (B : Base) (n : ℕ) (x : Site B) :
    Measurable (fun X : ℕ → Site B => outerVisits B X n x) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hc : MeasurableSet {X : ℕ → Site B | X n = x} :=
        (measurable_pi_apply n : Measurable (fun X : ℕ → Site B => X n))
          (measurableSet_singleton x)
      exact ih.add (Measurable.ite hc measurable_const measurable_const)

/-- The untouched site-stack suffixes at the exit of a single release. -/
def outerStackRemainder (B : Base) (A : Set (Site B)) (p : Site B)
    (r : OuterStacks B) : OuterStacks B :=
  outerUnused B (outerVisits B (outerStackWalk B p r)
    (WithTop.untopA (exitTime' B A (outerStackWalk B p r)))) r

/-- The stopped suffix field is measurable even on the never-exiting branch. -/
theorem measurable_outerStackRemainder (B : Base) (A : Set (Site B)) (p : Site B) :
    Measurable (outerStackRemainder B A p) := by
  have htime : Measurable (fun r => WithTop.untopA
      (exitTime' B A (outerStackWalk B p r))) :=
    ((measurable_of_countable (fun t : ℕ∞ => WithTop.untopA t)).comp
      (measurable_exitTime'_outer B A)).comp
      (measurable_outerStackWalk B p)
  apply measurable_pi_iff.mpr
  intro e
  have hv : Measurable (fun nX : ℕ × (ℕ → Site B) => outerVisits B nX.2 nX.1 e.1) := by
    apply measurable_from_prod_countable_right
    intro n
    exact measurable_outerVisits B n e.1
  have hcount := hv.comp (htime.prodMk (measurable_outerStackWalk B p))
  have heval : Measurable (fun ir : ℕ × OuterStacks B => ir.2 (e.1, ir.1 + e.2)) := by
    apply measurable_from_prod_countable_right
    intro i
    exact measurable_pi_apply (e.1, i + e.2)
  exact heval.comp (hcount.prodMk measurable_id)

private abbrev OuterExitPrefix (B : Base) := Σ n : ℕ, (Π _ : Finset.Iic n, Site B)

private def outerExitCell (B : Base) (A : Set (Site B)) (p : Site B)
    (t : OuterExitPrefix B) : Set (OuterStacks B) :=
  {r | exitTime' B A (outerStackWalk B p r) = (t.1 : ℕ∞)} ∩
    (outerStackWalk B p) ⁻¹' pathCyl B t.1 (ofPrefix B t.1 t.2)

private theorem measurableSet_outerExitCell (B : Base) (A : Set (Site B)) (p : Site B)
    (t : OuterExitPrefix B) : MeasurableSet (outerExitCell B A p t) :=
  (((measurable_exitTime'_outer B A).comp (measurable_outerStackWalk B p))
    (measurableSet_singleton _)).inter
    ((measurable_outerStackWalk B p) (measurableSet_pathCyl B _ _))

private theorem outerExitCell_disjoint (B : Base) (A : Set (Site B)) (p : Site B) :
    Pairwise (Function.onFun Disjoint (outerExitCell B A p)) := by
  intro t s hts
  apply Set.disjoint_left.mpr
  rintro r ⟨ht, htf⟩ ⟨hs, hsf⟩
  have hn : t.1 = s.1 := ENat.coe_inj.mp (ht.symm.trans hs)
  obtain ⟨n, z⟩ := t
  obtain ⟨m, w⟩ := s
  dsimp only at hn
  subst m
  apply hts
  congr 1
  funext i
  have hz := htf i (Finset.mem_Iic.mp i.2)
  have hw := hsf i (Finset.mem_Iic.mp i.2)
  simpa only [ofPrefix_apply_coe] using hz.symm.trans hw

private theorem outerExitCell_cover (B : Base) (a : ℤ) (F : Finset (Site B))
    (p : Site B) :
    ∀ᵐ r ∂outerStackLaw B, ∃ t : OuterExitPrefix B,
      r ∈ outerExitCell B (R B (a : ℝ) ∪ (F : Set (Site B))) p t := by
  filter_upwards [outerStackWalk_ae_exit_ne_top B a F p] with r hr
  let n := (exitTime' B (R B (a : ℝ) ∪ (F : Set (Site B))) (outerStackWalk B p r)).toNat
  have hn : exitTime' B (R B (a : ℝ) ∪ (F : Set (Site B))) (outerStackWalk B p r) =
      (n : ℕ∞) := (ENat.coe_toNat hr).symm
  refine ⟨⟨n, Preorder.frestrictLe n (outerStackWalk B p r)⟩, hn, ?_⟩
  intro i hi
  exact (ofPrefix_apply_coe B n (Preorder.frestrictLe n (outerStackWalk B p r))
    ⟨i, Finset.mem_Iic.mpr hi⟩).symm

private theorem outerExitCell_eq_prefix (B : Base) (A : Set (Site B)) (p : Site B)
    (t : OuterExitPrefix B) (h : (outerExitCell B A p t).Nonempty) :
    outerExitCell B A p t = (outerStackWalk B p) ⁻¹' pathCyl B t.1 (ofPrefix B t.1 t.2) := by
  obtain ⟨r, htime, hprefix⟩ := h
  apply Set.Subset.antisymm Set.inter_subset_right
  intro s hs
  refine ⟨?_, hs⟩
  apply (hittingAfter_zero_eq_coe_iff).mpr
  have hc := (hittingAfter_zero_eq_coe_iff.mp htime)
  constructor
  · change outerStackWalk B p s t.1 ∉ A
    rw [hs _ le_rfl, ← hprefix _ le_rfl]
    exact hc.1
  · intro j hj
    rw [hs _ (by omega), ← hprefix _ (by omega)]
    exact hc.2 j hj

private theorem outerExitCell_site (B : Base) (A : Set (Site B)) (p : Site B)
    (t : OuterExitPrefix B) {r : OuterStacks B} (hr : r ∈ outerExitCell B A p t) :
    exitSite' B A (outerStackWalk B p r) = ofPrefix B t.1 t.2 t.1 := by
  change outerStackWalk B p r (WithTop.untopA (exitTime' B A (outerStackWalk B p r))) = _
  rw [hr.1, untopA_natCast]
  exact hr.2 _ le_rfl

private theorem outerExitCell_remainder (B : Base) (A : Set (Site B)) (p : Site B)
    (t : OuterExitPrefix B) {r : OuterStacks B} (hr : r ∈ outerExitCell B A p t) :
    outerStackRemainder B A p r =
      outerUnused B (outerVisits B (ofPrefix B t.1 t.2) t.1) r := by
  unfold outerStackRemainder
  rw [hr.1, untopA_natCast]
  have hv : ∀ n ≤ t.1, outerVisits B (outerStackWalk B p r) n =
      outerVisits B (ofPrefix B t.1 t.2) n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [outerVisits, ih (by omega), hr.2 n (by omega)]
  rw [hv _ le_rfl]


/-- At a genuine release exit, all untouched arrows are fresh and independent of the exit site. -/
theorem outerStack_exit_remainder_law (B : Base) (a : ℤ) (F : Finset (Site B))
    (p : Site B) :
    (outerStackLaw B).map (fun r =>
        (exitSite' B (R B (a : ℝ) ∪ (F : Set (Site B))) (outerStackWalk B p r),
          outerStackRemainder B (R B (a : ℝ) ∪ (F : Set (Site B))) p r)) =
      ((walkPathLaw B p).map (exitSite' B (R B (a : ℝ) ∪ (F : Set (Site B))))).prod
        (outerStackLaw B) := by
  let A := R B (a : ℝ) ∪ (F : Set (Site B))
  let loc : OuterStacks B → Site B := fun r => exitSite' B A (outerStackWalk B p r)
  let rem : OuterStacks B → OuterStacks B := outerStackRemainder B A p
  have hloc : Measurable loc := (measurable_exitSite' B A).comp (measurable_outerStackWalk B p)
  have hrem : Measurable rem := measurable_outerStackRemainder B A p
  haveI : IsProbabilityMeasure ((outerStackLaw B).map (fun r => (loc r, rem r))) :=
    Measure.isProbabilityMeasure_map (hloc.prodMk hrem).aemeasurable
  haveI : IsProbabilityMeasure ((walkPathLaw B p).map (exitSite' B A)) :=
    Measure.isProbabilityMeasure_map (measurable_exitSite' B A).aemeasurable
  apply Measure.ext_prod
  intro S U hS hU
  rw [Measure.map_apply (hloc.prodMk hrem) (hS.prod hU), Measure.prod_prod,
    ← outerStackWalk_law B p,
    Measure.map_map (measurable_exitSite' B A) (measurable_outerStackWalk B p)]
  change outerStackLaw B (loc ⁻¹' S ∩ rem ⁻¹' U) =
    ((outerStackLaw B).map loc) S * outerStackLaw B U
  rw [Measure.map_apply hloc hS]
  let E : OuterExitPrefix B → Set (OuterStacks B) :=
    fun t => outerExitCell B A p t ∩ loc ⁻¹' S
  have hmeas (t : OuterExitPrefix B) : MeasurableSet (E t) :=
    (measurableSet_outerExitCell B A p t).inter (hloc hS)
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro t s hts
    exact (outerExitCell_disjoint B A p hts).mono Set.inter_subset_left Set.inter_subset_left
  have hcover : ∀ᵐ r ∂outerStackLaw B, (r ∈ ⋃ t, E t) ↔ r ∈ loc ⁻¹' S := by
    filter_upwards [outerExitCell_cover B a F p] with r hr
    constructor
    · intro h
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp h
      exact ht.2
    · intro h
      exact Set.mem_iUnion.mpr ⟨hr.choose, hr.choose_spec, h⟩
  have hcoverU : ∀ᵐ r ∂outerStackLaw B,
      (r ∈ ⋃ t, E t ∩ rem ⁻¹' U) ↔ r ∈ loc ⁻¹' S ∩ rem ⁻¹' U := by
    filter_upwards [hcover] with r hr
    constructor
    · intro h
      obtain ⟨t, ht, hu⟩ := Set.mem_iUnion.mp h
      exact ⟨hr.mp (Set.mem_iUnion.mpr ⟨t, ht⟩), hu⟩
    · rintro ⟨hS, hu⟩
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (hr.mpr hS)
      exact Set.mem_iUnion.mpr ⟨t, ht, hu⟩
  have hpiece (t : OuterExitPrefix B) :
      outerStackLaw B (E t ∩ rem ⁻¹' U) = outerStackLaw B (E t) * outerStackLaw B U := by
    by_cases ht : (E t).Nonempty
    · obtain ⟨r, hcell, hrS⟩ := ht
      have hprefix := outerExitCell_eq_prefix B A p t ⟨r, hcell⟩
      have hsite : ofPrefix B t.1 t.2 t.1 ∈ S := by
        change exitSite' B A (outerStackWalk B p r) ∈ S at hrS
        rwa [outerExitCell_site B A p t hcell] at hrS
      have hE : E t = outerExitCell B A p t := by
        apply Set.Subset.antisymm Set.inter_subset_left
        intro s hs
        refine ⟨hs, ?_⟩
        change exitSite' B A (outerStackWalk B p s) ∈ S
        rw [outerExitCell_site B A p t hs]
        exact hsite
      have hreplace : E t ∩ rem ⁻¹' U = outerExitCell B A p t ∩
          (outerUnused B (outerVisits B (ofPrefix B t.1 t.2) t.1)) ⁻¹' U := by
        rw [hE]
        ext s
        constructor
        · rintro ⟨hs, hu⟩
          refine ⟨hs, ?_⟩
          change outerUnused B (outerVisits B (ofPrefix B t.1 t.2) t.1) s ∈ U
          change outerStackRemainder B A p s ∈ U at hu
          rwa [← outerExitCell_remainder B A p t hs]
        · rintro ⟨hs, hu⟩
          refine ⟨hs, ?_⟩
          change outerStackRemainder B A p s ∈ U
          rwa [outerExitCell_remainder B A p t hs]
      rw [hreplace, hE, hprefix]
      exact outerStackWalk_prefix_unused B p _ _ U hU
    · rw [Set.not_nonempty_iff_eq_empty.mp ht, Set.empty_inter, measure_empty, zero_mul]
  have hμU : outerStackLaw B (⋃ t, E t ∩ rem ⁻¹' U) =
      outerStackLaw B (loc ⁻¹' S ∩ rem ⁻¹' U) :=
    measure_congr (s := ⋃ t, E t ∩ rem ⁻¹' U) (t := loc ⁻¹' S ∩ rem ⁻¹' U)
      (hcoverU.mono (fun _ h => propext h))
  have hμS : outerStackLaw B (⋃ t, E t) = outerStackLaw B (loc ⁻¹' S) :=
    measure_congr (s := ⋃ t, E t) (t := loc ⁻¹' S)
      (hcover.mono (fun _ h => propext h))
  rw [← hμU, measure_iUnion (fun t s hts =>
      (hdisj hts).mono Set.inter_subset_left Set.inter_subset_left)
      (fun t => (hmeas t).inter (hrem hU))]
  simp_rw [hpiece]
  rw [ENNReal.tsum_mul_right, ← measure_iUnion hdisj hmeas, hμS]


/-- Two successive releases driven by one common arrow array, retaining the unused arrows. -/
def outerStackPair (B : Base) (A : Set (Site B)) (p q : Site B) (r : OuterStacks B) :
    Set (Site B) :=
  addWalk B (addWalk B A (outerStackWalk B p r))
    (outerStackWalk B q (outerStackRemainder B A p r))

/-- Measurability of the output of the common-stack two-release explorer. -/
theorem measurable_outerStackPair (B : Base) (A : Set (Site B)) (p q : Site B) :
    Measurable (fun r => clusterCode B (outerStackPair B A p q r)) :=
  (measurable_addWalk_orders B A).1.comp
    ((measurable_outerStackWalk B p).prodMk
      ((measurable_outerStackWalk B q).comp (measurable_outerStackRemainder B A p)))

/-- The common-stack sequential explorer has exactly the two-independent-walk release law. -/
theorem outerStackPair_law (B : Base) (a : ℤ) (F : Finset (Site B)) (p q : Site B) :
    (outerStackLaw B).map (fun r => clusterCode B
        (outerStackPair B (R B (a : ℝ) ∪ (F : Set (Site B))) p q r)) =
      ((walkPathLaw B p).prod (walkPathLaw B q)).map
        (fun XY => clusterCode B
          (addWalk B (addWalk B (R B (a : ℝ) ∪ (F : Set (Site B))) XY.1) XY.2)) := by
  let A := R B (a : ℝ) ∪ (F : Set (Site B))
  let step : OuterStacks B → Site B × OuterStacks B := fun r =>
    (exitSite' B A (outerStackWalk B p r), outerStackRemainder B A p r)
  let out : Site B × (ℕ → Site B) → Site B → Bool := fun sY =>
    clusterCode B (addWalk B (A ∪ {sY.1}) sY.2)
  let f : Site B × OuterStacks B → Site B → Bool := fun sr =>
    out (sr.1, outerStackWalk B q sr.2)
  have hstep : Measurable step :=
    ((measurable_exitSite' B A).comp (measurable_outerStackWalk B p)).prodMk
      (measurable_outerStackRemainder B A p)
  have hout : Measurable out := by
    apply measurable_from_prod_countable_right
    intro s
    exact measurable_clusterCode_addWalk B (A ∪ {s})
  have hf : Measurable f := hout.comp
    (measurable_fst.prodMk ((measurable_outerStackWalk B q).comp measurable_snd))
  have hprod : (((walkPathLaw B p).map (exitSite' B A)).prod (walkPathLaw B q)) =
      ((((walkPathLaw B p).map (exitSite' B A)).prod (outerStackLaw B)).map
        (Prod.map id (outerStackWalk B q))) := by
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_outerStackWalk B q),
      Measure.map_id, outerStackWalk_law]
  calc
    _ = ((outerStackLaw B).map step).map f := (Measure.map_map hf hstep).symm
    _ = ((((walkPathLaw B p).map (exitSite' B A)).prod (outerStackLaw B))).map f := by
      rw [outerStack_exit_remainder_law]
    _ = ((((walkPathLaw B p).map (exitSite' B A)).prod (walkPathLaw B q))).map out := by
      rw [hprod, Measure.map_map hout
        (measurable_id.prodMap (measurable_outerStackWalk B q))]
      rfl
    _ = _ := by
      rw [← Measure.map_id (μ := walkPathLaw B q),
        Measure.map_prod_map _ _ (measurable_exitSite' B A) measurable_id,
        Measure.map_map hout ((measurable_exitSite' B A).prodMap measurable_id),
        Measure.map_id]
      rfl


example (B : Base) (a : ℤ) (F : Finset (Site B)) (p q : Site B) :
    IsProbabilityMeasure ((outerStackLaw B).map (fun r => clusterCode B
      (outerStackPair B (R B (a : ℝ) ∪ (F : Set (Site B))) p q r))) :=
  Measure.isProbabilityMeasure_map (measurable_outerStackPair B _ p q).aemeasurable

end
end IdlaCyl
