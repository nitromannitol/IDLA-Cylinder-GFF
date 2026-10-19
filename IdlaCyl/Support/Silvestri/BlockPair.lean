import IdlaCyl.Support.Silvestri.BlockResample
import IdlaCyl.Support.Silvestri.WindowCouple
import Mathlib

/-!
# The block pair of two walks

Two walks started at `p` and `p'` each have a first block, and the two blocks are coupled
through the window coupling of their base windows. The file defines this joint law of the two
blocks as a measure on pairs of blocks, and proves the following.

* The first marginal of the pair is the image, under the rebuilding of the first block, of
  the window law of the first walk, integrated over the first block. Likewise for the second
  marginal. Both are stated as bind identities, with the other block integrated out. The
  identities that the two marginals equal the block laws are stated with the resampling
  identity of the block law as an explicit hypothesis.
-/

namespace IdlaCyl.Silvestri

open MeasureTheory
open IdlaCyl.External
open scoped ENNReal

noncomputable section

variable (B : Base)

/-- Every function on a pair of blocks is measurable, since blocks are countable with
measurable singletons. -/
theorem measurable_block_pair {X : Type*} [MeasurableSpace X] (f : Block B × Block B → X) :
    Measurable f :=
  measurable_of_countable f

/-- The joint law of the first blocks of the walks from `p` and `p'`: the two blocks are drawn
independently, and then the two windows of base vertices are coupled by the window coupling
and rebuilt on the blocks. -/
def blockPair (ℓ : ℤ) (p p' : Site B) : Measure (Block B × Block B) :=
  ((blockLaw B ℓ p).prod (blockLaw B ℓ p')).bind fun cc =>
    ((windowCouple B (hcount B p cc.1) (hcount B p' cc.2) p.1 p'.1).toMeasure).map
      fun ww => (reassemble B p cc.1 ww.1, reassemble B p' cc.2 ww.2)

/-- Pushing a bind forward along a measurable map pushes each kernel forward. -/
theorem map_bind_apply {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (m : Measure α) (F : α → Measure β) (f : β → γ) (hF : Measurable F)
    (hf : Measurable f) : (m.bind F).map f = m.bind fun a => (F a).map f := by
  ext s hs
  have hG : Measurable fun a => (F a).map f := (Measure.measurable_map f hf).comp hF
  rw [Measure.map_apply hf hs, Measure.bind_apply (hf hs) hF.aemeasurable,
    Measure.bind_apply hs hG.aemeasurable]
  exact lintegral_congr fun a => by rw [Measure.map_apply hf hs]

/-- Integrating out the second factor of a product: a bind along the first coordinate of a
product with a probability measure on the second factor is the bind of the first factor. -/
theorem bind_prod_fst_apply {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure ν]
    (G : α → Measure γ) (hG : Measurable G) :
    (μ.prod ν).bind (fun cc => G cc.1) = μ.bind G := by
  unfold Measure.bind
  rw [show (fun cc : α × β => G cc.1) = G ∘ Prod.fst from rfl,
    ← Measure.map_map hG measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]

/-- Integrating out the first factor of a product: a bind along the second coordinate of a
product with a probability measure on the first factor is the bind of the second factor. -/
theorem bind_prod_snd_apply {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [SFinite ν]
    (H : β → Measure γ) (hH : Measurable H) :
    (μ.prod ν).bind (fun cc => H cc.2) = ν.bind H := by
  unfold Measure.bind
  rw [show (fun cc : α × β => H cc.2) = H ∘ Prod.snd from rfl,
    ← Measure.map_map hH measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]

/-- The first marginal of the block pair, before the resampling identity: the first block is
the block law, and the window of the first walk is rebuilt on it, the second block being
integrated out. -/
theorem blockPair_map_fst_eq (ℓ : ℤ) (p p' : Site B) :
    (blockPair B ℓ p p').map Prod.fst = (blockLaw B ℓ p).bind
      (fun c => ((pathLaw B (hcount B p c) p.1).toMeasure).map (reassemble B p c)) := by
  unfold blockPair
  rw [map_bind_apply _ _ _ (measurable_block_pair B _) measurable_fst]
  have key : ∀ cc : Block B × Block B,
      (((windowCouple B (hcount B p cc.1) (hcount B p' cc.2) p.1 p'.1).toMeasure).map
        fun ww => (reassemble B p cc.1 ww.1, reassemble B p' cc.2 ww.2)).map Prod.fst
      = ((pathLaw B (hcount B p cc.1) p.1).toMeasure).map (reassemble B p cc.1) := by
    intro cc
    have hre : Measurable (reassemble B p cc.1 : (Fin (hcount B p cc.1) → B.V) → Block B) :=
      measurable_of_countable _
    rw [Measure.map_map measurable_fst (measurable_of_countable _)]
    change Measure.map (reassemble B p cc.1 ∘ Prod.fst) _ = _
    rw [← Measure.map_map hre measurable_fst,
      FiniteLaw.toMeasure_map_fst _ _ (windowCouple_fst_weight B _ _ _ _)]
  simp only [key]
  exact bind_prod_fst_apply (blockLaw B ℓ p) (blockLaw B ℓ p')
    (fun c => ((pathLaw B (hcount B p c) p.1).toMeasure).map (reassemble B p c))
    (measurable_of_countable _)

/-- The second marginal of the block pair, before the resampling identity: the second block
is the block law of `p'`, and the window of the second walk is rebuilt on it, the first block
being integrated out. -/
theorem blockPair_map_snd_eq (ℓ : ℤ) (p p' : Site B) :
    (blockPair B ℓ p p').map Prod.snd = (blockLaw B ℓ p').bind
      (fun c => ((pathLaw B (hcount B p' c) p'.1).toMeasure).map (reassemble B p' c)) := by
  unfold blockPair
  rw [map_bind_apply _ _ _ (measurable_block_pair B _) measurable_snd]
  have key : ∀ cc : Block B × Block B,
      (((windowCouple B (hcount B p cc.1) (hcount B p' cc.2) p.1 p'.1).toMeasure).map
        fun ww => (reassemble B p cc.1 ww.1, reassemble B p' cc.2 ww.2)).map Prod.snd
      = ((pathLaw B (hcount B p' cc.2) p'.1).toMeasure).map (reassemble B p' cc.2) := by
    intro cc
    have hre : Measurable (reassemble B p' cc.2 : (Fin (hcount B p' cc.2) → B.V) → Block B) :=
      measurable_of_countable _
    rw [Measure.map_map measurable_snd (measurable_of_countable _)]
    change Measure.map (reassemble B p' cc.2 ∘ Prod.snd) _ = _
    rw [← Measure.map_map hre measurable_snd,
      FiniteLaw.toMeasure_map_snd _ _ (windowCouple_snd_weight B _ _ _ _)]
  simp only [key]
  exact bind_prod_snd_apply (blockLaw B ℓ p) (blockLaw B ℓ p')
    (fun c => ((pathLaw B (hcount B p' c) p'.1).toMeasure).map (reassemble B p' c))
    (measurable_of_countable _)

/-- The first marginal of the block pair is the block law of `p`, given the resampling
identity of the block law (`hres`), which the block resampling lemma supplies. -/
theorem blockPair_map_fst (ℓ : ℤ) (p p' : Site B)
    (hres : (blockLaw B ℓ p).bind
      (fun c => ((pathLaw B (hcount B p c) p.1).toMeasure).map (reassemble B p c))
        = blockLaw B ℓ p) :
    (blockPair B ℓ p p').map Prod.fst = blockLaw B ℓ p :=
  (blockPair_map_fst_eq B ℓ p p').trans hres

/-- The second marginal of the block pair is the block law of `p'`, given the resampling
identity of the block law at `p'` (`hres'`). -/
theorem blockPair_map_snd (ℓ : ℤ) (p p' : Site B)
    (hres' : (blockLaw B ℓ p').bind
      (fun c => ((pathLaw B (hcount B p' c) p'.1).toMeasure).map (reassemble B p' c))
        = blockLaw B ℓ p') :
    (blockPair B ℓ p p').map Prod.snd = blockLaw B ℓ p' :=
  (blockPair_map_snd_eq B ℓ p p').trans hres'

/-- The value of a finite law at a set of atoms is the mass of the set of atoms. -/
theorem toMeasure_event {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : FiniteLaw α) (P : α → Prop) [DecidablePred P] :
    μ.toMeasure {z | P z} = ENNReal.ofReal (μ.event P) := by
  rw [FiniteLaw.toMeasure_apply, event_eq_sum', ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : P a <;> simp [h]
  · intro a _
    exact mul_nonneg (μ.nonneg a) (by split_ifs <;> norm_num)

end

end IdlaCyl.Silvestri
