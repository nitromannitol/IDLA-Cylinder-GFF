/-
Finite cluster kernels for the fresh-resumption comparison.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396.
Only sites above the flat seed are stored, so occupation codes are injective.
-/
import IdlaCyl.Support.Outer.ResumeMeasurable
import IdlaCyl.Support.Outer.Commute

attribute [local instance] Classical.propDecidable

namespace IdlaCyl
open MeasureTheory ProbabilityTheory
noncomputable section

/-- Finite sets of cylinder sites use their countable discrete measurable space. -/
instance resumeFinsetMeasurableSpace (B : Base) : MeasurableSpace (Finset (Site B)) := ⊤

instance resumeFinsetMeasurableSingleton (B : Base) :
    MeasurableSingletonClass (Finset (Site B)) := ⟨fun _ => trivial⟩

/-- A canonical finite extension of the flat seed. -/
abbrev ResumeFinite (B : Base) := {F : Finset (Site B) // ∀ z ∈ F, z ∉ R B 0}

/-- The actual occupied set represented by a canonical finite extension. -/
def resumeSeed (B : Base) (F : ResumeFinite B) : Set (Site B) :=
  R B 0 ∪ (F.val : Set (Site B))

def resumeEmpty (B : Base) : ResumeFinite B := ⟨∅, by simp only [Finset.notMem_empty, false_implies, implies_true]⟩

theorem resumeSeed_empty (B : Base) : resumeSeed B (resumeEmpty B) = R B 0 := by
  change R B 0 ∪ ((∅ : Finset (Site B)) : Set (Site B)) = R B 0
  rw [Finset.coe_empty, Set.union_empty]

/-- Insert a settled site, suppressing sites already in the infinite seed. -/
def resumeInsert (B : Base) (F : ResumeFinite B) (z : Site B) : ResumeFinite B :=
  if hz : z ∈ R B 0 then F else
    ⟨insert z F.val, by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hz
      · exact F.property y hy⟩

theorem resumeSeed_insert (B : Base) (F : ResumeFinite B) (z : Site B) :
    resumeSeed B (resumeInsert B F z) = resumeSeed B F ∪ {z} := by
  unfold resumeInsert
  split_ifs with hz
  · apply Eq.symm
    apply Set.union_eq_left.mpr
    exact Set.singleton_subset_iff.mpr (show z ∈ resumeSeed B F from Or.inl hz)
  · ext y
    simp only [resumeSeed, Set.mem_union, Finset.mem_coe, Finset.mem_insert,
      Set.mem_singleton_iff]
    tauto

theorem resumeSeed_injective (B : Base) : Function.Injective (resumeSeed B) := by
  intro F G h
  apply Subtype.ext
  apply Finset.ext
  intro z
  have hz := Set.ext_iff.mp h z
  constructor
  · intro hF
    exact (hz.mp (Or.inr hF)).resolve_left (F.property z hF)
  · intro hG
    exact (hz.mpr (Or.inr hG)).resolve_left (G.property z hG)

theorem resumeCode_measurableEmbedding (B : Base) :
    MeasurableEmbedding (fun F : ResumeFinite B => clusterCode B (resumeSeed B F)) := by
  refine ⟨?_, measurable_of_countable _, fun {_} _ => (Set.to_countable _).image _ |>.measurableSet⟩
  intro F G h
  apply resumeSeed_injective B
  ext z
  have hz := congrFun h z
  simpa only [clusterCode, decide_eq_decide] using hz

/-- One independent prescribed release, retaining only the finite extension. -/
def resumeStep (B : Base) (p : Site B) (F : ResumeFinite B) : Measure (ResumeFinite B) :=
  (walkPathLaw B p).map (fun X => resumeInsert B F (exitSite' B (resumeSeed B F) X))

theorem measurable_resumeStep_output (B : Base) (F : ResumeFinite B) :
    Measurable (fun X => resumeInsert B F (exitSite' B (resumeSeed B F) X)) :=
  (measurable_of_countable (resumeInsert B F)).comp (measurable_exitSite' B (resumeSeed B F))

instance resumeStep_isProbability (B : Base) (p : Site B) (F : ResumeFinite B) :
    IsProbabilityMeasure (resumeStep B p F) :=
  Measure.isProbabilityMeasure_map (measurable_resumeStep_output B F).aemeasurable

/-- Push a measurable map through a measurable bind. -/
theorem resume_map_bind {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (κ : α → Measure β) (f : β → γ)
    (hκ : Measurable κ) (hf : Measurable f) :
    (μ.bind κ).map f = μ.bind (fun a => (κ a).map f) := by
  calc
    _ = (μ.bind κ).bind (fun b => Measure.dirac (f b)) :=
      (Measure.bind_dirac_eq_map _ hf).symm
    _ = μ.bind (fun a => (κ a).bind (fun b => Measure.dirac (f b))) :=
      Measure.bind_bind hκ.aemeasurable (Measure.measurable_dirac.comp hf).aemeasurable
    _ = _ := by
      congr 1
      funext a
      exact Measure.bind_dirac_eq_map _ hf

/-- Mapping one fixed measure by a jointly measurable map is measurable in its parameter. -/
theorem resume_measurable_param_map {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (ν : Measure β) [SFinite ν]
    (f : α × β → γ) (hf : Measurable f) :
    Measurable (fun a => ν.map (fun b => f (a, b))) := by
  let κ : Kernel α γ := (Kernel.id.prod (Kernel.const α ν)).map f
  have heq : (fun a => ν.map (fun b => f (a, b))) = fun a => κ a := by
    funext a
    rw [Kernel.map_apply _ hf, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
      Measure.dirac_prod, Measure.map_map hf measurable_prodMk_left]
    rfl
  rw [heq]
  exact κ.measurable

/-- A measurable image of a product is the corresponding iterated release kernel. -/
theorem resume_prod_map {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α × β → γ) (hf : Measurable f) :
    (μ.prod ν).map f = μ.bind (fun a => ν.map (fun b => f (a, b))) := by
  ext S hS
  rw [Measure.map_apply hf hS, Measure.prod_apply (hf hS),
    Measure.bind_apply hS (resume_measurable_param_map ν f hf).aemeasurable]
  apply lintegral_congr
  intro a
  exact (Measure.map_apply (hf.comp measurable_prodMk_left) hS).symm

/-- Pull a measurable input map through a bind. -/
theorem resume_bind_map {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (f : α → β) (κ : β → Measure γ)
    (hf : Measurable f) (hκ : Measurable κ) :
    (μ.map f).bind κ = μ.bind (fun a => κ (f a)) := by
  calc
    _ = (μ.bind (fun a => Measure.dirac (f a))).bind κ := by
      rw [Measure.bind_dirac_eq_map _ hf]
    _ = μ.bind (fun a => (Measure.dirac (f a)).bind κ) :=
      Measure.bind_bind (Measure.measurable_dirac.comp hf).aemeasurable hκ.aemeasurable
    _ = _ := by
      congr 1
      funext a
      exact Measure.dirac_bind hκ (f a)

/-- Sequential prescribed releases on the canonical finite state space. -/
def resumeRun (B : Base) (F : ResumeFinite B) : List (Site B) → Measure (ResumeFinite B)
  | [] => Measure.dirac F
  | p :: L => (resumeStep B p F).bind (fun G => resumeRun B G L)

instance resumeRun_isProbability (B : Base) (F : ResumeFinite B) (L : List (Site B)) :
    IsProbabilityMeasure (resumeRun B F L) := by
  induction L generalizing F with
  | nil => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac F))
  | cons p L ih =>
      apply isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
      exact Filter.Eventually.of_forall (fun G => ih G)

theorem resumeRun_append (B : Base) (F : ResumeFinite B) (L M : List (Site B)) :
    resumeRun B F (L ++ M) = (resumeRun B F L).bind (fun G => resumeRun B G M) := by
  induction L generalizing F with
  | nil =>
      change resumeRun B F M = (Measure.dirac F).bind (fun G => resumeRun B G M)
      exact (Measure.dirac_bind (measurable_of_countable (fun G => resumeRun B G M)) F).symm
  | cons p L ih =>
      change (resumeStep B p F).bind (fun G => resumeRun B G (L ++ M)) = _
      simp_rw [ih]
      exact (Measure.bind_bind (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable).symm

private theorem resumeStep_pair_code (B : Base) (F : ResumeFinite B) (p q : Site B) :
    (((resumeStep B p F).bind (resumeStep B q)).map
      (fun G => clusterCode B (resumeSeed B G))) =
      ((walkPathLaw B p).prod (walkPathLaw B q)).map
        (fun XY => clusterCode B (addWalk B (addWalk B (resumeSeed B F) XY.1) XY.2)) := by
  let e := fun X => resumeInsert B F (exitSite' B (resumeSeed B F) X)
  let code := fun G : ResumeFinite B => clusterCode B (resumeSeed B G)
  have he : Measurable e := measurable_resumeStep_output B F
  have hc : Measurable code := (resumeCode_measurableEmbedding B).measurable
  rw [resumeStep, resume_bind_map _ _ _ he (measurable_of_countable _)]
  change ((walkPathLaw B p).bind (fun X => resumeStep B q (e X))).map code = _
  have hk : Measurable (fun X => resumeStep B q (e X)) :=
    (measurable_of_countable (resumeStep B q)).comp he
  rw [resume_map_bind (walkPathLaw B p) (fun X => resumeStep B q (e X)) code hk hc]
  simp_rw [resumeStep, Measure.map_map hc (measurable_resumeStep_output B _)]
  have hprod : Measurable (fun XY : (ℕ → Site B) × (ℕ → Site B) =>
      clusterCode B (addWalk B (addWalk B (resumeSeed B F) XY.1) XY.2)) :=
    (measurable_addWalk_orders B _).1
  have h := resume_prod_map (walkPathLaw B p) (walkPathLaw B q) _ hprod
  rw [h]
  congr 1
  funext X
  congr 1
  funext Y
  simp only [Function.comp_def, code, e, resumeSeed_insert, addWalk]

/-- Task 6 yields commuting Markov kernels on actual finite cluster states. -/
theorem resumeStep_commute (B : Base) (F : ResumeFinite B) (p q : Site B) :
    (resumeStep B p F).bind (resumeStep B q) =
      (resumeStep B q F).bind (resumeStep B p) := by
  apply (resumeCode_measurableEmbedding B).map_injective
  rw [resumeStep_pair_code, resumeStep_pair_code]
  have h := (addWalk_commute_in_law B 0 F.val p q).2.2
  simp only [Int.cast_zero] at h
  have hswap := Measure.map_map (measurable_addWalk_orders B (resumeSeed B F)).1
    measurable_swap (μ := (walkPathLaw B p).prod (walkPathLaw B q))
  rw [Measure.prod_swap] at hswap
  exact h.trans hswap.symm

/-- A new release can pass through an arbitrary finite pending queue in law. -/
theorem resumeStep_commute_run (B : Base) (F : ResumeFinite B) (p : Site B)
    (L : List (Site B)) :
    (resumeStep B p F).bind (fun G => resumeRun B G L) =
      (resumeRun B F L).bind (resumeStep B p) := by
  induction L generalizing F with
  | nil =>
      simp only [resumeRun, Measure.bind_dirac,
        Measure.dirac_bind (measurable_of_countable (resumeStep B p))]
  | cons q L ih =>
      change (resumeStep B p F).bind (fun G =>
        (resumeStep B q G).bind (fun H => resumeRun B H L)) = _
      rw [← Measure.bind_bind (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable, resumeStep_commute]
      rw [Measure.bind_bind (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable]
      simp_rw [ih]
      exact (Measure.bind_bind (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable).symm

example : IsProbabilityMeasure (resumeRun PrInnerTail.K2 (resumeEmpty PrInnerTail.K2) []) :=
  inferInstance

example (p q : Site PrInnerTail.K2) :
    (resumeStep PrInnerTail.K2 p (resumeEmpty PrInnerTail.K2)).bind
      (resumeStep PrInnerTail.K2 q) =
    (resumeStep PrInnerTail.K2 q (resumeEmpty PrInnerTail.K2)).bind
      (resumeStep PrInnerTail.K2 p) :=
  resumeStep_commute PrInnerTail.K2 _ p q

end
end IdlaCyl
