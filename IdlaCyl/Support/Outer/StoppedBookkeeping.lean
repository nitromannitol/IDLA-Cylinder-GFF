/-
Literal ghost counts and the paused/fresh-resumed process for the outer bound.
Source: paper/idla-cylinder-gff.tex, tex:1271-1328,1373-1396.

The ghosts have one independent prescribed walk per interior site. The paused
cluster removes the stopping layer, and the chronological list retains all
copies of repeated pause locations. Fresh resumption is a separate random
experiment; equality with ordinary growth in law is not asserted here.
-/
import IdlaCyl.External.Discharge.Bernstein
import IdlaCyl.Support.PrInnerStopped.Boundary
import IdlaCyl.Support.PrInnerTail.Threshold
import IdlaCyl.Support.PrInnerTail.Nonvacuity

attribute [local instance] Classical.propDecidable

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

/-- Finite pause-label lists use their discrete measurable space. -/
instance outerListNatMeasurableSpace : MeasurableSpace (List ℕ) := ⊤

instance outerListNatMeasurableSingleton : MeasurableSingletonClass (List ℕ) :=
  ⟨fun _ => trivial⟩

/-- The actual width with the inner proof's supported C₁(ν). -/
def innerWidth (ν : ℝ) (N T : ℕ) : ℝ :=
  2 * Real.sqrt (ν + 4) *
    Real.sqrt ((T : ℝ) / (N : ℝ) * PrInnerTail.logTerm (N : ℝ) (T : ℝ))

/-- The width is nonnegative for all total inputs. -/
theorem innerWidth_nonneg (ν : ℝ) (N T : ℕ) : 0 ≤ innerWidth ν N T := by
  unfold innerWidth
  positivity

/-- On a legitimate base and at positive time, the supported width is strictly positive. -/
theorem innerWidth_pos (B : Base) (ν : ℝ) (hν : 0 < ν) (T : ℕ) (hT : 0 < T) :
    0 < innerWidth ν B.card T := by
  have hN : (1 : ℝ) < (B.card : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega) B.nontrivial)
  have hNpos : (0 : ℝ) < (B.card : ℝ) := by linarith
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hlog : 0 < PrInnerTail.logTerm (B.card : ℝ) (T : ℝ) := by
    unfold PrInnerTail.logTerm
    have := Real.log_pos hN
    linarith [le_max_right (Real.log ((T : ℝ) / (B.card : ℝ))) 0]
  unfold innerWidth
  exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by linarith)))
    (Real.sqrt_pos.mpr (mul_pos (div_pos hTpos hNpos) hlog))

/-- The exact change of inner parameter required in the last line of the outer proof. -/
theorem innerWidth_succ (ν : ℝ) (hν : 0 < ν) (N T : ℕ) :
    innerWidth (ν + 1) N T =
      ((2 * Real.sqrt (ν + 5)) / (2 * Real.sqrt (ν + 4))) * innerWidth ν N T := by
  have hden : 2 * Real.sqrt (ν + 4) ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by linarith)))
  simp only [innerWidth]
  rw [show ν + 1 + 4 = ν + 5 by ring, ← mul_assoc, div_mul_cancel₀ _ hden]

/-- The actual width has the exact squared exponent used in the source's tail estimates. -/
theorem innerWidth_exponent (B : Base) (ν : ℝ) (hν : 0 < ν) (T : ℕ) (hT : 0 < T) :
    innerWidth ν B.card T ^ 2 * (B.card : ℝ) / (4 * (T : ℝ)) =
      (ν + 4) * PrInnerTail.logTerm (B.card : ℝ) (T : ℝ) := by
  have hN : (1 : ℝ) ≤ (B.card : ℝ) := by
    exact_mod_cast (le_trans (by omega) B.nontrivial)
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  rw [innerWidth, PrInnerTail.ell_star_sq_mul_div _ _ _ hN hTpos,
    mul_pow, Real.sq_sqrt (by linarith : 0 ≤ ν + 4)]
  ring

/-- Positive sites strictly below the stopping layer. -/
def outerInterior (B : Base) (h : ℤ) : Finset (Site B) :=
  Finset.univ ×ˢ Finset.Icc (1 : ℤ) (h - 1)

/-- One ghost trajectory from each interior site. -/
abbrev GhostDriver (B : Base) (h : ℤ) :=
  (z : ↥(outerInterior B h)) → (ℕ → Site B)

/-- The independent prescribed law of the site ghosts. -/
def ghostLaw (B : Base) (h : ℤ) : Measure (GhostDriver B h) :=
  Measure.pi (fun z : ↥(outerInterior B h) => walkPathLaw B z.val)

instance ghostLaw_isProbability (B : Base) (h : ℤ) :
    IsProbabilityMeasure (ghostLaw B h) := by
  unfold ghostLaw
  infer_instance

/-- The paper's event G, with the already-present R₀ included. -/
def outerFill (B : Base) (h : ℤ) (T : ℕ) : Set (TrajSeq B) :=
  {ω | R B ((h - 1 : ℤ) : ℝ) ⊆ stoppedCluster B h ω T}

/-- Number of frozen particles, retaining repeated freezing sites. -/
def frozenCount (B : Base) (h : ℤ) (T : ℕ) (ω : TrajSeq B) (x : B.V) : ℕ :=
  ((Finset.range T).filter (fun j => stoppedSettleSite B h ω j = (x, h))).card

/-- First level-h hits of the full alive walks. -/
def aliveCount (B : Base) (h : ℤ) (T : ℕ) (ω : TrajSeq B) (x : B.V) : ℕ :=
  ((Finset.range T).filter (fun j => firstHitSite B h (ω j) = (x, h))).card

/-- All independent site ghosts whose first level-h hit is (x,h). -/
def ghostCount (B : Base) (h : ℤ) (U : GhostDriver B h) (x : B.V) : ℕ :=
  (Finset.univ.filter (fun z : ↥(outerInterior B h) =>
    firstHitSite B h (U z) = (x, h))).card

/-- Only the ghosts from occupied interior sites. -/
def settledGhostCount (B : Base) (h : ℤ) (T : ℕ)
    (ω : TrajSeq B) (U : GhostDriver B h) (x : B.V) : ℕ :=
  (Finset.univ.filter (fun z : ↥(outerInterior B h) =>
    z.val ∈ stoppedCluster B h ω T ∧ firstHitSite B h (U z) = (x, h))).card

/-- The lower cluster, with all stopping-layer sites removed. -/
def pausedCluster (B : Base) (h : ℤ) (ω : TrajSeq B) (T : ℕ) : Set (Site B) :=
  stoppedCluster B h ω T ∩ R B ((h - 1 : ℤ) : ℝ)

/-- Chronological particle labels at the stopping layer, including all copies. -/
def pauseList (B : Base) (h : ℤ) (T : ℕ) (ω : TrajSeq B) : List ℕ :=
  (List.range T).filter (fun j => (stoppedSettleSite B h ω j).2 = h)

/-- Prescribed starts of the fresh resumed walks; the unused extension is ignored. -/
def pausedStart (B : Base) (h : ℤ) (T : ℕ) (ω : TrajSeq B) : ℕ → Site B :=
  fun i => if hi : i < (pauseList B h T ω).length then
    stoppedSettleSite B h ω ((pauseList B h T ω)[i]) else (B.pt, h)

/-- Settle the paused multiplicities along an independent fresh trajectory stream. -/
def resumedCluster (B : Base) (h : ℤ) (T : ℕ) (ω η : TrajSeq B) : Set (Site B) :=
  clusterFrom B (pausedCluster B h ω T) η (pauseList B h T ω).length

/-- First sample the stopped stage, then fresh walks at all of its pause locations. -/
def resumeLaw (B : Base) (h : ℤ) (T : ℕ) : Measure (TrajSeq B × TrajSeq B) :=
  (idlaMeasure B).bind (fun ω =>
    (prescribedMeasure B (pausedStart B h T ω)).map (fun η => (ω, η)))

/-- Boolean occupation coordinates provide a canonical measurable output carrier. -/
def clusterCode (B : Base) (A : Set (Site B)) : Site B → Bool :=
  fun p => decide (p ∈ A)

/-- The insertion of one prescribed walk into a seed. -/
def addWalk (B : Base) (A : Set (Site B)) (X : ℕ → Site B) : Set (Site B) :=
  A ∪ {exitSite' B A X}

/-- Interior sites are exactly R_(h−1) minus the seed. -/
theorem mem_outerInterior (B : Base) (h : ℤ) (p : Site B) :
    p ∈ outerInterior B h ↔ p ∈ R B ((h - 1 : ℤ) : ℝ) ∧ p ∉ R B 0 := by
  simp only [outerInterior, Finset.mem_product, Finset.mem_univ, true_and,
    Finset.mem_Icc, mem_R, not_le]
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨by exact_mod_cast hhi, by exact_mod_cast (show (0 : ℤ) < p.2 by omega)⟩
  · rintro ⟨hhi, hlo⟩
    have hhi' : p.2 ≤ h - 1 := by exact_mod_cast hhi
    have hlo' : (0 : ℤ) < p.2 := by exact_mod_cast hlo
    exact ⟨by omega, hhi'⟩

/-- The finite ghost family has N*(h−1) indices when h≥1. -/
theorem outerInterior_card (B : Base) (h : ℤ) :
    (outerInterior B h).card = B.card * (h - 1).toNat := by
  simp only [outerInterior, Finset.card_product, Finset.card_univ, Int.card_Icc, Base.card]
  congr 1
  congr 1
  omega

/-- The fill event is exactly the source's inclusion of the positive interior. -/
theorem outerFill_iff (B : Base) (h : ℤ) (T : ℕ) (ω : TrajSeq B) :
    ω ∈ outerFill B h T ↔
      ∀ p ∈ outerInterior B h, p ∈ stoppedCluster B h ω T := by
  constructor
  · intro hG p hp
    exact hG ((mem_outerInterior B h p).mp hp).1
  · intro hG p hp
    by_cases h0 : p ∈ R B 0
    · exact subset_R_zero_stoppedCluster B h ω T h0
    · exact hG p ((mem_outerInterior B h p).mpr ⟨hp, h0⟩)

/-- On G every interior ghost is selected, so L equals tilde L. -/
theorem settledGhostCount_eq_on_fill (B : Base) (h : ℤ) (T : ℕ)
    (ω : TrajSeq B) (U : GhostDriver B h)
    (hG : ω ∈ outerFill B h T) (x : B.V) :
    settledGhostCount B h T ω U x = ghostCount B h U x := by
  unfold settledGhostCount ghostCount
  congr 1
  apply Finset.filter_congr
  intro z _
  exact and_iff_right ((outerFill_iff B h T ω).mp hG z.val z.property)

/-- A site ghost has its canonical prescribed walk marginal. -/
theorem ghostLaw_map_eval (B : Base) (h : ℤ) (z : ↥(outerInterior B h)) :
    (ghostLaw B h).map (fun U => U z) = walkPathLaw B z.val :=
  (measurePreserving_eval (fun z : ↥(outerInterior B h) => walkPathLaw B z.val) z).map_eq

/-- Ghost paths are jointly independent under the literal product law. -/
theorem ghostLaw_iIndepFun (B : Base) (h : ℤ) :
    iIndepFun (fun z (U : GhostDriver B h) => U z) (ghostLaw B h) :=
  iIndepFun_pi (μ := fun z : ↥(outerInterior B h) => walkPathLaw B z.val)
    (X := fun _ => (id : (ℕ → Site B) → (ℕ → Site B)))
    (fun _ => measurable_id.aemeasurable)

/-- Every ghost starts at its own site, on a single full-measure event. -/
theorem ghostLaw_ae_start (B : Base) (h : ℤ) :
    ∀ᵐ U ∂ghostLaw B h, ∀ z : ↥(outerInterior B h), U z 0 = z.val := by
  apply ae_all_iff.mpr
  intro z
  have hstart := walkPathLaw_ae_zero B z.val
  rw [← ghostLaw_map_eval B h z] at hstart
  exact ae_of_ae_map (measurable_pi_apply z).aemeasurable hstart

/-- No infinite hitting-time branch contributes under the site-ghost law. -/
theorem ghostLaw_ae_hitLevel_ne_top (B : Base) (h : ℤ) :
    ∀ᵐ U ∂ghostLaw B h, ∀ z : ↥(outerInterior B h), hitLevel B h (U z) ≠ ⊤ := by
  apply ae_all_iff.mpr
  intro z
  have hhit := ae_hitLevel_ne_top External.lazyRwRecurrent_holds B z.val h
  rw [← ghostLaw_map_eval B h z] at hhit
  exact ae_of_ae_map (measurable_pi_apply z).aemeasurable hhit

/-- Frozen counts are literal multiplicities and never exceed the number released. -/
theorem frozenCount_le (B : Base) (h : ℤ) (T : ℕ) (ω : TrajSeq B) (x : B.V) :
    frozenCount B h T ω x ≤ T :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_range T)

/-- Pausing leaves the entire lower seed when the stopping height is positive. -/
theorem pausedCluster_zero (B : Base) (h : ℤ) (hh : 1 ≤ h) (ω : TrajSeq B) :
    pausedCluster B h ω 0 = R B 0 := by
  apply Set.inter_eq_left.mpr
  apply R_mono
  have : (0 : ℤ) ≤ h - 1 := by omega
  exact_mod_cast this

/-- Removing the stopping layer discards exactly the boundary addition at each step. -/
theorem pausedCluster_succ (B : Base) (h : ℤ) (ω : TrajSeq B) (T : ℕ) :
    pausedCluster B h ω (T + 1) =
      if (stoppedSettleSite B h ω T).2 < h then
        pausedCluster B h ω T ∪ {stoppedSettleSite B h ω T}
      else pausedCluster B h ω T := by
  classical
  have hstep : stoppedCluster B h ω (T + 1) =
      stoppedCluster B h ω T ∪ {stoppedSettleSite B h ω T} := rfl
  unfold pausedCluster
  rw [hstep]
  have hR : stoppedSettleSite B h ω T ∈ R B ((h - 1 : ℤ) : ℝ) ↔
      (stoppedSettleSite B h ω T).2 < h := by
    rw [mem_R, Int.cast_le]
    omega
  by_cases hlt : (stoppedSettleSite B h ω T).2 < h
  · rw [if_pos hlt]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hp | hp, hq⟩
      · exact Or.inl ⟨hp, hq⟩
      · exact Or.inr hp
    · rintro (⟨hp, hq⟩ | rfl)
      · exact ⟨Or.inl hp, hq⟩
      · exact ⟨Or.inr rfl, hR.mpr hlt⟩
  · rw [if_neg hlt]
    ext p
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hp | rfl, hq⟩
      · exact ⟨hp, hq⟩
      · exact False.elim (hlt (hR.mp hq))
    · rintro ⟨hp, hq⟩
      exact ⟨Or.inl hp, hq⟩

/-- The literal paused seed is always below the stopping layer. -/
theorem pausedCluster_subset (B : Base) (h : ℤ) (ω : TrajSeq B) (T : ℕ) :
    pausedCluster B h ω T ⊆ R B ((h - 1 : ℤ) : ℝ) := Set.inter_subset_right

/-- Every genuine resumption start is on the stopping layer. -/
theorem pausedStart_ver (B : Base) (h : ℤ) (T : ℕ) (ω : TrajSeq B) (i : ℕ) :
    (pausedStart B h T ω i).2 = h := by
  unfold pausedStart
  split_ifs with hi
  · have hmem := List.getElem_mem hi
    exact of_decide_eq_true (List.mem_filter.mp hmem).2
  · rfl

/-- The chronological pause list is a measurable function of the stopped stage. -/
theorem measurable_pauseList (B : Base) (h : ℤ) (T : ℕ) :
    Measurable (pauseList B h T) := by
  induction T with
  | zero =>
      have heq : pauseList B h 0 = fun _ => ([] : List ℕ) := by
        funext ω
        rfl
      rw [heq]
      exact measurable_const
  | succ T ih =>
      have hstep : pauseList B h (T + 1) = fun ω => pauseList B h T ω ++
          (if (stoppedSettleSite B h ω T).2 = h then [T] else []) := by
        funext ω
        by_cases hT : (stoppedSettleSite B h ω T).2 = h <;>
          simp [pauseList, List.range_succ, hT]
      rw [hstep]
      have hcond : Measurable (fun ω : TrajSeq B =>
          if (stoppedSettleSite B h ω T).2 = h then [T] else ([] : List ℕ)) :=
        Measurable.ite (((measurable_snd.comp (measurable_stoppedSettleSite B h T)))
          (measurableSet_singleton h)) measurable_const measurable_const
      exact (measurable_of_countable (fun p : List ℕ × List ℕ => p.1 ++ p.2)).comp
        (ih.prodMk hcond)

/-- Selecting a pause location at a fixed index is measurable, including the unused extension. -/
theorem measurable_pausedStart (B : Base) (h : ℤ) (T : ℕ) :
    Measurable (pausedStart B h T) := by
  apply measurable_pi_iff.mpr
  intro i
  have hf : Measurable (fun p : List ℕ × TrajSeq B =>
      if hi : i < p.1.length then stoppedSettleSite B h p.2 (p.1[i]) else (B.pt, h)) := by
    apply measurable_from_prod_countable_right
    intro L
    dsimp only
    by_cases hi : i < L.length
    · simpa only [dif_pos hi] using measurable_stoppedSettleSite B h (L[i])
    · simpa only [dif_neg hi] using
        (measurable_const : Measurable (fun _ : TrajSeq B => (B.pt, h)))
  exact hf.comp ((measurable_pauseList B h T).prodMk measurable_id)

/-- The conditional fresh-tail experiment is a genuine measurable Markov kernel. -/
theorem measurable_resume_kernel (B : Base) (h : ℤ) (T : ℕ) :
    Measurable (fun ω : TrajSeq B =>
      (prescribedMeasure B (pausedStart B h T ω)).map (fun η => (ω, η))) := by
  let κ : Kernel (TrajSeq B) (TrajSeq B) :=
    { toFun := fun ω => prescribedMeasure B (pausedStart B h T ω)
      measurable' := (measurable_prescribedMeasure B).comp (measurable_pausedStart B h T) }
  haveI : IsMarkovKernel κ := ⟨fun ω => prescribedMeasure_isProbability B (pausedStart B h T ω)⟩
  have heq : (fun ω : TrajSeq B =>
      (prescribedMeasure B (pausedStart B h T ω)).map (fun η => (ω, η))) =
        fun ω => (Kernel.id.prod κ) ω := by
    funext ω
    rw [Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod]
    rfl
  rw [heq]
  exact (Kernel.id.prod κ).measurable

/-- Fresh resumption is a probability experiment, with no nonmeasurable-bind zero branch. -/
instance resumeLaw_isProbability (B : Base) (h : ℤ) (T : ℕ) :
    IsProbabilityMeasure (resumeLaw B h T) := by
  apply isProbabilityMeasure_bind (measurable_resume_kernel B h T).aemeasurable
  apply Filter.Eventually.of_forall
  intro ω
  exact Measure.isProbabilityMeasure_map measurable_prodMk_left.aemeasurable

/-- The first-stage marginal of the fresh-tail experiment is exactly the canonical law. -/
theorem resumeLaw_map_fst (B : Base) (h : ℤ) (T : ℕ) :
    (resumeLaw B h T).map Prod.fst = idlaMeasure B := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA, resumeLaw,
    Measure.bind_apply (measurable_fst hA) (measurable_resume_kernel B h T).aemeasurable]
  have hvalue (ω : TrajSeq B) :
      (prescribedMeasure B (pausedStart B h T ω)).map (fun η => (ω, η)) (Prod.fst ⁻¹' A) =
        A.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    rw [Measure.map_apply measurable_prodMk_left (measurable_fst hA)]
    by_cases hω : ω ∈ A
    · have hpre : (fun η : TrajSeq B => (ω, η)) ⁻¹' (Prod.fst ⁻¹' A) = Set.univ := by
        ext η
        exact iff_of_true hω (Set.mem_univ η)
      rw [hpre, measure_univ, Set.indicator_of_mem hω]
    · have hpre : (fun η : TrajSeq B => (ω, η)) ⁻¹' (Prod.fst ⁻¹' A) = ∅ := by
        ext η
        exact iff_of_false hω (Set.notMem_empty η)
      rw [hpre, measure_empty, Set.indicator_of_notMem hω]
  simp_rw [hvalue]
  exact lintegral_indicator_one hA

/-- Frozen multiplicities are measurable natural-valued random variables. -/
theorem measurable_frozenCount (B : Base) (h : ℤ) (T : ℕ) (x : B.V) :
    Measurable (fun ω : TrajSeq B => frozenCount B h T ω x) := by
  unfold frozenCount
  simp_rw [Finset.card_filter]
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite ((measurable_stoppedSettleSite B h j) (measurableSet_singleton (x, h)))
    measurable_const measurable_const

/-- The full-walk first-hit multiplicity is measurable. -/
theorem measurable_aliveCount (B : Base) (h : ℤ) (T : ℕ) (x : B.V) :
    Measurable (fun ω : TrajSeq B => aliveCount B h T ω x) := by
  unfold aliveCount
  simp_rw [Finset.card_filter]
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite (((measurable_firstHitSite B h).comp
    (measurable_pi_apply (j : ℕ))) (measurableSet_singleton (x, h))) measurable_const measurable_const

/-- The all-site ghost multiplicity is measurable. -/
theorem measurable_ghostCount (B : Base) (h : ℤ) (x : B.V) :
    Measurable (fun U : GhostDriver B h => ghostCount B h U x) := by
  unfold ghostCount
  simp_rw [Finset.card_filter]
  apply Finset.measurable_sum
  intro z _
  exact Measurable.ite (((measurable_firstHitSite B h).comp
    (measurable_pi_apply z)) (measurableSet_singleton (x, h))) measurable_const measurable_const

/-- The finite interior fill event is measurable on the canonical driver. -/
theorem measurableSet_outerFill (B : Base) (h : ℤ) (T : ℕ) :
    MeasurableSet (outerFill B h T) := by
  have hset : outerFill B h T = ⋂ z : ↥(outerInterior B h),
      {ω : TrajSeq B | z.val ∈ stoppedCluster B h ω T} := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_setOf_eq, outerFill_iff]
    exact ⟨fun H z => H z.val z.property, fun H p hp => H ⟨p, hp⟩⟩
  rw [hset]
  apply MeasurableSet.iInter
  intro z
  exact ((stoppedFiltration B h).le T) _
    (measurableSet_mem_stoppedCluster_filtration B h (le_refl T) z.val)

/-- The measurable real indicator for one walk's first hit at (x,h). -/
def outerHitIndicator (B : Base) (h : ℤ) (x : B.V) (X : ℕ → Site B) : ℝ :=
  if firstHitSite B h X = (x, h) then 1 else 0

/-- The indicator is measurable on full path space. -/
theorem measurable_outerHitIndicator (B : Base) (h : ℤ) (x : B.V) :
    Measurable (outerHitIndicator B h x) := by
  exact Measurable.ite (measurableSet_firstHit B (x, h)) measurable_const measurable_const

/-- Its values are genuinely Bernoulli, pointwise. -/
theorem outerHitIndicator_zero_or_one (B : Base) (h : ℤ) (x : B.V) (X : ℕ → Site B) :
    outerHitIndicator B h x X = 0 ∨ outerHitIndicator B h x X = 1 := by
  unfold outerHitIndicator
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Bounded measurability supplies integrability, independently of mean values. -/
theorem integrable_outerHitIndicator (B : Base) (h : ℤ) (x : B.V)
    (μ : Measure (ℕ → Site B)) [IsProbabilityMeasure μ] :
    Integrable (outerHitIndicator B h x) μ := by
  apply Integrable.of_bound (measurable_outerHitIndicator B h x).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun X => by
    rcases outerHitIndicator_zero_or_one B h x X with hX | hX <;> rw [hX] <;> norm_num)

/-- Fixed-start hit mean, with the out-of-range branch explicitly excluded. -/
theorem integral_outerHitIndicator (B : Base) (h : ℤ) (x : B.V) (p : Site B)
    (hp : p.2 ≤ h) :
    ∫ X, outerHitIndicator B h x X ∂walkPathLaw B p = hitProb B (x, h) p := by
  have hfun : outerHitIndicator B h x =
      {Y : ℕ → Site B | firstHitSite B h Y = (x, h)}.indicator (fun _ => (1 : ℝ)) := by
    funext X
    by_cases hX : firstHitSite B h X = (x, h) <;> simp [outerHitIndicator, hX]
  rw [hfun, integral_indicator_const 1 (measurableSet_firstHit B (x, h))]
  rw [hitProb_eq_toReal B (x, h) p (by exact not_lt.mpr hp)]
  simp only [smul_eq_mul, mul_one, Measure.real, hitProbE]

/-- The real ghost count is the sum of these measurable indicators. -/
theorem ghostCount_cast_eq_sum (B : Base) (h : ℤ) (U : GhostDriver B h) (x : B.V) :
    (ghostCount B h U x : ℝ) =
      ∑ z : ↥(outerInterior B h), outerHitIndicator B h x (U z) := by
  unfold ghostCount
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro z _
  unfold outerHitIndicator
  split_ifs <;> norm_num

/-- A single ghost indicator has the actual fixed-site hitting mean. -/
theorem integral_ghost_indicator (B : Base) (h : ℤ) (x : B.V)
    (z : ↥(outerInterior B h)) :
    ∫ U, outerHitIndicator B h x (U z) ∂ghostLaw B h = hitProb B (x, h) z.val := by
  have hmean := integral_outerHitIndicator B h x z.val (by
    have hz := (mem_outerInterior B h z.val).mp z.property
    have hz' : z.val.2 ≤ h - 1 := by exact_mod_cast (mem_R.mp hz.1)
    omega)
  rw [← ghostLaw_map_eval B h z] at hmean
  rw [integral_map (measurable_pi_apply z).aemeasurable
    (measurable_outerHitIndicator B h x).aestronglyMeasurable] at hmean
  exact hmean

/-- A uniformly started walk has mean 1/N for each target on every level. -/
theorem integral_outerHitIndicator_uniform (B : Base) (h : ℤ) (x : B.V) :
    ∫ X, outerHitIndicator B h x X ∂walkLawUniform B = 1 / (B.card : ℝ) := by
  have hprob : walkLawUniform B {X : ℕ → Site B | firstHitSite B h X = (x, h)} =
      (B.card : ℝ≥0∞)⁻¹ := by
    have hh := congrArg (fun μ : Measure (Site B) => μ {(x, h)})
      (unif_first_hit B 0 h External.lazyRwRecurrent_holds)
    rw [Measure.map_apply (measurable_firstHitSite B h) (measurableSet_singleton (x, h)),
      layerLawAt_singleton] at hh
    exact hh.trans (if_pos rfl)
  have hfun : outerHitIndicator B h x =
      {Y : ℕ → Site B | firstHitSite B h Y = (x, h)}.indicator (fun _ => (1 : ℝ)) := by
    funext X
    by_cases hX : firstHitSite B h X = (x, h) <;> simp [outerHitIndicator, hX]
  rw [hfun, integral_indicator_const 1 (measurableSet_firstHit B (x, h))]
  simp only [smul_eq_mul, mul_one, Measure.real, hprob, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, one_div]

/-- The real alive count is the literal sum over the first T walks. -/
theorem aliveCount_cast_eq_sum (B : Base) (h : ℤ) (T : ℕ) (ω : TrajSeq B) (x : B.V) :
    (aliveCount B h T ω x : ℝ) =
      ∑ j ∈ Finset.range T, outerHitIndicator B h x (ω j) := by
  unfold aliveCount
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold outerHitIndicator
  split_ifs <;> norm_num

/-- The actual alive first-hit count has mean T/N. -/
theorem integral_aliveCount (B : Base) (h : ℤ) (T : ℕ) (x : B.V) :
    ∫ ω, (aliveCount B h T ω x : ℝ) ∂idlaMeasure B = (T : ℝ) / (B.card : ℝ) := by
  have hmap (j : ℕ) : (idlaMeasure B).map (fun ω : TrajSeq B => ω j) = walkLawUniform B :=
    Measure.infinitePi_map_eval (fun _ : ℕ => walkLawUniform B) j
  have hint (j : ℕ) :
      Integrable (fun ω : TrajSeq B => outerHitIndicator B h x (ω j)) (idlaMeasure B) := by
    have hi := integrable_outerHitIndicator B h x (walkLawUniform B)
    rw [← hmap j] at hi
    exact hi.comp_measurable (measurable_pi_apply (j : ℕ))
  have hmean (j : ℕ) :
      ∫ ω, outerHitIndicator B h x (ω j) ∂idlaMeasure B = 1 / (B.card : ℝ) := by
    have hi := integral_outerHitIndicator_uniform B h x
    rw [← hmap j, integral_map (measurable_pi_apply (j : ℕ)).aemeasurable
      (measurable_outerHitIndicator B h x).aestronglyMeasurable] at hi
    exact hi
  simp_rw [aliveCount_cast_eq_sum]
  rw [integral_finsetSum _ (fun j _ => hint j)]
  simp only [hmean, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Alive first-hit indicators are jointly independent for distinct particle labels. -/
theorem idlaMeasure_iIndepFun_hit_indicator (B : Base) (h : ℤ) (x : B.V) :
    iIndepFun (fun j (ω : TrajSeq B) => outerHitIndicator B h x (ω j)) (idlaMeasure B) :=
  (iIndepFun_traj B).comp (fun _ => outerHitIndicator B h x)
    (fun _ => measurable_outerHitIndicator B h x)

/-- Ghost indicators, unlike the two different count families, are jointly independent. -/
theorem ghostLaw_iIndepFun_indicator (B : Base) (h : ℤ) (x : B.V) :
    iIndepFun (fun z (U : GhostDriver B h) => outerHitIndicator B h x (U z))
      (ghostLaw B h) :=
  (ghostLaw_iIndepFun B h).comp (fun _ => outerHitIndicator B h x)
    (fun _ => measurable_outerHitIndicator B h x)

/-- The full independent ghost count has mean h−1 for h≥1. -/
theorem integral_ghostCount (B : Base) (h : ℤ) (hh : 1 ≤ h) (x : B.V) :
    ∫ U, (ghostCount B h U x : ℝ) ∂ghostLaw B h = (h : ℝ) - 1 := by
  have hint : ∀ z : ↥(outerInterior B h),
      Integrable (fun U : GhostDriver B h => outerHitIndicator B h x (U z)) (ghostLaw B h) := by
    intro z
    have hi := integrable_outerHitIndicator B h x (walkPathLaw B z.val)
    rw [← ghostLaw_map_eval B h z] at hi
    exact hi.comp_measurable (measurable_pi_apply z)
  simp_rw [ghostCount_cast_eq_sum]
  rw [integral_finsetSum _ (fun z _ => hint z)]
  simp_rw [integral_ghost_indicator]
  rw [Finset.sum_coe_sort]
  exact sum_hitProb_layers_below B h hh (x, h) rfl

/-- The measurable Bernstein adapter reindexed to any actual finite index set. -/
theorem outer_bernstein_fintype {ι Ω : Type} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ι → ℝ) (X : ι → Ω → ℝ) (ε : ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hε : 0 ≤ ε)
    (hind : iIndepFun X P) (hmeas : ∀ i, Measurable (X i))
    (hX : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hmean : ∀ i, ∫ ω, X i ω ∂P = p i) :
    P {ω | ε ≤ |(∑ i, X i ω) - ∑ i, p i|} ≤
      ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 / 2) / (∑ i, p i + ε / 3))) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have H := External.bernstein_of_latticeProb_of_measurable P (Fintype.card ι)
    (fun i => p (e i)) (fun i => X (e i)) ε
    (fun i => hp0 (e i)) (fun i => hp1 (e i)) hε
    (iIndepFun.precomp e.injective hind) (fun i => hmeas (e i))
    (fun i => hX (e i)) (fun i => hmean (e i))
  have hsumX (ω : Ω) : (∑ i : Fin (Fintype.card ι), X (e i) ω) = ∑ i : ι, X i ω :=
    e.sum_comp (fun i => X i ω)
  simp_rw [hsumX, e.sum_comp p] at H
  exact H

/-- The canonical full-site ghost count satisfies Bernstein, with its actual mean h−1. -/
theorem ghostCount_abs_tail (B : Base) (h : ℤ) (hh : 1 ≤ h) (x : B.V)
    (ε : ℝ) (hε : 0 ≤ ε) :
    ghostLaw B h {U : GhostDriver B h | ε ≤ |(ghostCount B h U x : ℝ) - ((h : ℝ) - 1)|} ≤
      ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 / 2) / ((h : ℝ) - 1 + ε / 3))) := by
  have hsum : (∑ z : ↥(outerInterior B h), hitProb B (x, h) z.val) = (h : ℝ) - 1 := by
    rw [Finset.sum_coe_sort]
    exact sum_hitProb_layers_below B h hh (x, h) rfl
  have H := outer_bernstein_fintype (ghostLaw B h)
    (fun z : ↥(outerInterior B h) => hitProb B (x, h) z.val)
    (fun z U => outerHitIndicator B h x (U z)) ε
    (fun z => hitProb_nonneg B (x, h) z.val) (fun z => hitProb_le_one B (x, h) z.val) hε
    (ghostLaw_iIndepFun_indicator B h x)
    (fun z => (measurable_outerHitIndicator B h x).comp (measurable_pi_apply z))
    (fun _ U => outerHitIndicator_zero_or_one B h x (U _))
    (fun z => integral_ghost_indicator B h x z)
  simp_rw [← ghostCount_cast_eq_sum, hsum] at H
  exact H

/-- The canonical alive count satisfies Bernstein, with its actual mean T/N. -/
theorem aliveCount_abs_tail (B : Base) (h : ℤ) (T : ℕ) (x : B.V)
    (ε : ℝ) (hε : 0 ≤ ε) :
    idlaMeasure B {ω : TrajSeq B | ε ≤ |(aliveCount B h T ω x : ℝ) - (T : ℝ) / (B.card : ℝ)|} ≤
      ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 / 2) / ((T : ℝ) / (B.card : ℝ) + ε / 3))) := by
  have hcard : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
  have hsum (ω : TrajSeq B) : (∑ j : Fin T, outerHitIndicator B h x (ω j)) =
      (aliveCount B h T ω x : ℝ) := by
    exact (Fin.sum_univ_eq_sum_range (fun j => outerHitIndicator B h x (ω j)) T).trans
      (aliveCount_cast_eq_sum B h T ω x).symm
  have hsumP : (∑ _j : Fin T, (1 / (B.card : ℝ))) = (T : ℝ) / (B.card : ℝ) := by
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    ring
  have hmean (j : Fin T) :
      ∫ ω : TrajSeq B, outerHitIndicator B h x (ω j) ∂idlaMeasure B = 1 / (B.card : ℝ) := by
    have hi := integral_outerHitIndicator_uniform B h x
    have hmap : (idlaMeasure B).map (fun ω : TrajSeq B => ω j) = walkLawUniform B :=
      Measure.infinitePi_map_eval (fun _ : ℕ => walkLawUniform B) j
    rw [← hmap, integral_map (measurable_pi_apply (j : ℕ)).aemeasurable
      (measurable_outerHitIndicator B h x).aestronglyMeasurable] at hi
    exact hi
  have H := outer_bernstein_fintype (idlaMeasure B)
    (fun _ : Fin T => (1 / (B.card : ℝ)))
    (fun j : Fin T => fun ω : TrajSeq B => outerHitIndicator B h x (ω j)) ε
    (fun _ => by positivity) (fun _ => (div_le_one (by linarith)).mpr (by linarith)) hε
    (iIndepFun.precomp Fin.val_injective (idlaMeasure_iIndepFun_hit_indicator B h x))
    (fun j => (measurable_outerHitIndicator B h x).comp (measurable_pi_apply (j : ℕ)))
    (fun j ω => outerHitIndicator_zero_or_one B h x (ω j)) hmean
  simp_rw [hsum, hsumP] at H
  exact H

/- Nonvacuity: two ghosts at h=2 on K₂; no ghosts at h=1. All walks
in the example below start at the level-2 site of vertex 0, so that the
finite count visibly records two copies rather than a set of hit sites. -/
example : (outerInterior PrInnerTail.K2 2).card = 2 := by
  rw [outerInterior_card]
  rfl

example : (outerInterior PrInnerTail.K2 1).card = 0 := by
  rw [outerInterior_card]
  rfl

example : ghostLaw PrInnerTail.K2 2 Set.univ = 1 := measure_univ

example : 0 < innerWidth 1 PrInnerTail.K2.card 1 :=
  innerWidth_pos PrInnerTail.K2 1 (by norm_num) 1 (by norm_num)

example : resumeLaw PrInnerTail.K2 1 1 Set.univ = 1 := measure_univ

example : (resumeLaw PrInnerTail.K2 1 1).map Prod.fst = idlaMeasure PrInnerTail.K2 :=
  resumeLaw_map_fst PrInnerTail.K2 1 1

example : ghostCount PrInnerTail.K2 2 (fun _ _ => (PrInnerTail.K2.pt, (2 : ℤ))) PrInnerTail.K2.pt = 2 := by
  have hfirst : firstHitSite PrInnerTail.K2 2 (fun _ => (PrInnerTail.K2.pt, (2 : ℤ))) =
      (PrInnerTail.K2.pt, (2 : ℤ)) := by
    apply firstHitSite_eq_of_hitLevel_eq _ _ _ 0
    exact (hitLevel_eq_coe_iff _ _ _ _).mpr ⟨rfl, by intro n hn; omega⟩
  unfold ghostCount
  have hall : (Finset.univ.filter (fun z : ↥(outerInterior PrInnerTail.K2 2) =>
      firstHitSite PrInnerTail.K2 2 ((fun _ _ => (PrInnerTail.K2.pt, (2 : ℤ))) z) =
        (PrInnerTail.K2.pt, (2 : ℤ)))) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro z _
    exact hfirst
  rw [hall, Finset.card_univ, Fintype.card_coe, outerInterior_card]
  rfl

end
end IdlaCyl
