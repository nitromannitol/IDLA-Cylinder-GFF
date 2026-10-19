import IdlaCyl.Support.Silvestri.BlockPair
import IdlaCyl.Support.FiniteCoupling
import Mathlib

/-!
# End-coupled block pairs

For a level `ℓ` and two starting sites `p`, `p'` below it, the first block of the walk from `p`
ends on layer `ℓ`. The file defines the law of its end vertex (`blockEndLaw`), the block law
conditioned on the end vertex (`condBlock`), and the end-coupled pair of blocks
(`endCoupledPair`): the two end vertices are drawn from the maximal coupling of their laws, and
the two blocks are then drawn independently from their conditional laws.

The file proves that the block law is the mixture over its end vertex of the conditional laws
(`blockLaw_eq_mix`), that the two marginals of the end-coupled pair are the block laws of `p`
and `p'` (`endCoupledPair_map_fst`, `endCoupledPair_map_snd`), and that the two block ends
differ with probability at most the total variation distance of the two end laws
(`endCoupledPair_end_ne`, for `p` and `p'` strictly below the level `ℓ`).
-/

namespace IdlaCyl.Silvestri

open MeasureTheory
open scoped ENNReal

noncomputable section

variable (B : Base)

/-- The law of the end vertex of the first block from `p`, the base vertex of its end. -/
def blockEndLaw (ℓ : ℤ) (p : Site B) : Measure B.V :=
  (blockLaw B ℓ p).map (fun c => (blockEnd B p c).1)

/-- The end law is a probability measure. -/
instance isProbabilityMeasure_blockEndLaw (ℓ : ℤ) (p : Site B) :
    IsProbabilityMeasure (blockEndLaw B ℓ p) :=
  Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

/-- The mass of the blocks whose end vertex is `z` is the end law at `z`. -/
theorem blockLaw_end_preimage (ℓ : ℤ) (p : Site B) (z : B.V) :
    blockLaw B ℓ p {c | (blockEnd B p c).1 = z} = blockEndLaw B ℓ p {z} := by
  unfold blockEndLaw
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton z)]
  rfl

/-- The block law conditioned on its end vertex `z`: the block law restricted to the blocks
ending at `z`, renormalised. It is a fixed block when `z` carries no mass. -/
def condBlock (ℓ : ℤ) (p : Site B) (z : B.V) : Measure (Block B) :=
  if blockEndLaw B ℓ p {z} = 0 then Measure.dirac default
  else (blockEndLaw B ℓ p {z})⁻¹ • (blockLaw B ℓ p).restrict {c | (blockEnd B p c).1 = z}

/-- The conditioned block law is a probability measure. -/
instance isProbabilityMeasure_condBlock (ℓ : ℤ) (p : Site B) (z : B.V) :
    IsProbabilityMeasure (condBlock B ℓ p z) := by
  unfold condBlock
  split_ifs with h
  · infer_instance
  · constructor
    rw [Measure.smul_apply, Measure.restrict_apply_univ, blockLaw_end_preimage, smul_eq_mul,
      ENNReal.inv_mul_cancel h (measure_ne_top _ _)]

/-- Restricting the block law to the blocks ending at `z` gives the end mass times the
conditioned law. -/
theorem blockLaw_restrict_end (ℓ : ℤ) (p : Site B) (z : B.V) (s : Set (Block B)) :
    blockEndLaw B ℓ p {z} * condBlock B ℓ p z s = blockLaw B ℓ p (s ∩ {c | (blockEnd B p c).1 = z}) := by
  unfold condBlock
  split_ifs with h
  · rw [h, zero_mul]
    exact (measure_mono_null Set.inter_subset_right
      (by rw [blockLaw_end_preimage, h])).symm
  · rw [Measure.smul_apply, Measure.restrict_apply' MeasurableSpace.measurableSet_top,
      smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel h (measure_ne_top _ _), one_mul,
      Set.inter_comm]

/-- The block law is the mixture over its end vertex of the block laws conditioned on it. -/
theorem blockLaw_eq_mix (ℓ : ℤ) (p : Site B) :
    blockLaw B ℓ p = (blockEndLaw B ℓ p).bind (condBlock B ℓ p) := by
  have hK : Measurable (condBlock B ℓ p) := measurable_of_countable _
  ext s hs
  rw [Measure.bind_apply hs hK.aemeasurable, lintegral_fintype]
  have hpart : ∑ z : B.V, blockLaw B ℓ p (s ∩ {c | (blockEnd B p c).1 = z}) =
      blockLaw B ℓ p s := by
    have h := sum_measure_preimage_singleton (μ := (blockLaw B ℓ p).restrict s)
      (f := fun c : Block B => (blockEnd B p c).1) Finset.univ
      (fun y _ => MeasurableSpace.measurableSet_top)
    simp only [Finset.coe_univ, Set.preimage_univ, Measure.restrict_apply_univ] at h
    rw [← h]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Measure.restrict_apply' MeasurableSpace.measurableSet_top, Set.inter_comm]
    rfl
  rw [← hpart]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [mul_comm, blockLaw_restrict_end]

/-- The end law of the block from `p`, as a finite law carrying the same measure. -/
theorem blockEndLaw_ofMeasure_toMeasure (ℓ : ℤ) (p : Site B) :
    (FiniteLaw.ofMeasure (blockEndLaw B ℓ p)).toMeasure = blockEndLaw B ℓ p := by
  refine Measure.ext_iff_singleton.2 fun z => ?_
  rw [FiniteLaw.toMeasure_singleton]
  change ENNReal.ofReal ((blockEndLaw B ℓ p).real {z}) = _
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The maximal coupling of the end laws of the blocks from `p` and `p'`. -/
def endCoupling (ℓ : ℤ) (p p' : Site B) : FiniteLaw (B.V × B.V) :=
  FiniteLaw.maximalCoupling (FiniteLaw.ofMeasure (blockEndLaw B ℓ p))
    (FiniteLaw.ofMeasure (blockEndLaw B ℓ p'))

/-- The end-coupled pair of blocks from `p` and `p'`: the two end vertices are drawn from the
maximal coupling of their end laws, and then the two blocks are drawn independently from their
conditioned laws. -/
def endCoupledPair (ℓ : ℤ) (p p' : Site B) : Measure (Block B × Block B) :=
  (endCoupling B ℓ p p').toMeasure.bind
    fun zz => (condBlock B ℓ p zz.1).prod (condBlock B ℓ p' zz.2)

/-- A bind along the first coordinate of a measure on pairs is the bind of its first marginal. -/
theorem bind_fst_eq_map {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure (α × β)) (K : α → Measure γ) (hK : Measurable K) :
    μ.bind (fun zz => K zz.1) = (μ.map Prod.fst).bind K := by
  unfold Measure.bind
  rw [show (fun zz : α × β => K zz.1) = K ∘ Prod.fst from rfl,
    ← Measure.map_map hK measurable_fst]

/-- A bind along the second coordinate of a measure on pairs is the bind of its second marginal. -/
theorem bind_snd_eq_map {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure (α × β)) (K : β → Measure γ) (hK : Measurable K) :
    μ.bind (fun zz => K zz.2) = (μ.map Prod.snd).bind K := by
  unfold Measure.bind
  rw [show (fun zz : α × β => K zz.2) = K ∘ Prod.snd from rfl,
    ← Measure.map_map hK measurable_snd]

/-- The first marginal of the end-coupled pair is the block law from `p`. -/
theorem endCoupledPair_map_fst (ℓ : ℤ) (p p' : Site B) :
    (endCoupledPair B ℓ p p').map Prod.fst = blockLaw B ℓ p := by
  have h1 : ∀ zz : B.V × B.V,
      ((condBlock B ℓ p zz.1).prod (condBlock B ℓ p' zz.2)).map Prod.fst =
        condBlock B ℓ p zz.1 := by
    intro zz
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  unfold endCoupledPair
  rw [map_bind_apply _ _ _ (measurable_of_countable _) measurable_fst]
  simp only [h1]
  rw [bind_fst_eq_map _ _ (measurable_of_countable _),
    FiniteLaw.toMeasure_map_fst (endCoupling B ℓ p p') (FiniteLaw.ofMeasure (blockEndLaw B ℓ p))
      (fun a => FiniteLaw.couplingWeight_row _ _ a),
    blockEndLaw_ofMeasure_toMeasure, ← blockLaw_eq_mix]

/-- The second marginal of the end-coupled pair is the block law from `p'`. -/
theorem endCoupledPair_map_snd (ℓ : ℤ) (p p' : Site B) :
    (endCoupledPair B ℓ p p').map Prod.snd = blockLaw B ℓ p' := by
  have h2 : ∀ zz : B.V × B.V,
      ((condBlock B ℓ p zz.1).prod (condBlock B ℓ p' zz.2)).map Prod.snd =
        condBlock B ℓ p' zz.2 := by
    intro zz
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  unfold endCoupledPair
  rw [map_bind_apply _ _ _ (measurable_of_countable _) measurable_snd]
  simp only [h2]
  rw [bind_snd_eq_map _ _ (measurable_of_countable _),
    FiniteLaw.toMeasure_map_snd (endCoupling B ℓ p p') (FiniteLaw.ofMeasure (blockEndLaw B ℓ p'))
      (fun b => FiniteLaw.couplingWeight_column _ _ b),
    blockEndLaw_ofMeasure_toMeasure, ← blockLaw_eq_mix]

/-- A block whose end vertex has no mass under the end law is never drawn from the conditioned
law of that vertex. -/
theorem condBlock_end_null (ℓ : ℤ) (p : Site B) (z : B.V) (hz : blockEndLaw B ℓ p {z} ≠ 0) :
    condBlock B ℓ p z {c | (blockEnd B p c).1 ≠ z} = 0 := by
  unfold condBlock
  rw [if_neg hz, Measure.smul_apply, Measure.restrict_apply' MeasurableSpace.measurableSet_top]
  have hempty : {c : Block B | (blockEnd B p c).1 ≠ z} ∩ {c | (blockEnd B p c).1 = z} = ∅ := by
    ext c
    simp
  rw [hempty, measure_empty, smul_zero]

/-- Off the diagonal of the end coupling, the two conditioned blocks have base ends that differ
only when one of them is off its end vertex. -/
theorem prod_condBlock_end_ne_null (ℓ : ℤ) (p p' : Site B) (z : B.V)
    (hz : blockEndLaw B ℓ p {z} ≠ 0) (hz' : blockEndLaw B ℓ p' {z} ≠ 0) :
    ((condBlock B ℓ p z).prod (condBlock B ℓ p' z))
      {cc | (blockEnd B p cc.1).1 ≠ (blockEnd B p' cc.2).1} = 0 := by
  have hsub : {cc : Block B × Block B | (blockEnd B p cc.1).1 ≠ (blockEnd B p' cc.2).1} ⊆
      Prod.fst ⁻¹' {c | (blockEnd B p c).1 ≠ z} ∪ Prod.snd ⁻¹' {c | (blockEnd B p' c).1 ≠ z} := by
    intro cc hcc
    by_contra hh
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_setOf_eq, not_or, not_not] at hh hcc
    exact hcc (hh.1.trans hh.2.symm)
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [← Measure.map_apply measurable_fst MeasurableSpace.measurableSet_top, Measure.map_fst_prod,
      measure_univ, one_smul, condBlock_end_null B ℓ p z hz]
  · rw [← Measure.map_apply measurable_snd MeasurableSpace.measurableSet_top, Measure.map_snd_prod,
      measure_univ, one_smul, condBlock_end_null B ℓ p' z hz']

/-- The end vertices of the end-coupled pair differ with probability at most the total
variation distance of the two end laws. -/
theorem endCoupledPair_end_ne (ℓ : ℤ) (p p' : Site B) (hp : p.2 < ℓ) (hp' : p'.2 < ℓ) :
    endCoupledPair B ℓ p p' {cc | blockEnd B p cc.1 ≠ blockEnd B p' cc.2} ≤
      ENNReal.ofReal ((1 / 2) * ∑ z, |(blockEndLaw B ℓ p {z}).toReal -
        (blockEndLaw B ℓ p' {z}).toReal|) := by
  have hrow : ∀ a, ∑ b, (endCoupling B ℓ p p').weight (a, b) =
      (FiniteLaw.ofMeasure (blockEndLaw B ℓ p)).weight a :=
    fun a => FiniteLaw.couplingWeight_row _ _ a
  have hcol : ∀ b, ∑ a, (endCoupling B ℓ p p').weight (a, b) =
      (FiniteLaw.ofMeasure (blockEndLaw B ℓ p')).weight b :=
    fun b => FiniteLaw.couplingWeight_column _ _ b
  -- a coupled diagonal atom forces both end laws to charge its vertex
  have hpos : ∀ z, (endCoupling B ℓ p p').weight (z, z) ≠ 0 →
      blockEndLaw B ℓ p {z} ≠ 0 ∧ blockEndLaw B ℓ p' {z} ≠ 0 := by
    intro z hw
    have h1 : (endCoupling B ℓ p p').weight (z, z) ≤
        (FiniteLaw.ofMeasure (blockEndLaw B ℓ p)).weight z := by
      rw [← hrow z]
      exact Finset.single_le_sum (f := fun b => (endCoupling B ℓ p p').weight (z, b))
        (fun b _ => (endCoupling B ℓ p p').nonneg (z, b)) (Finset.mem_univ z)
    have h2 : (endCoupling B ℓ p p').weight (z, z) ≤
        (FiniteLaw.ofMeasure (blockEndLaw B ℓ p')).weight z := by
      rw [← hcol z]
      exact Finset.single_le_sum (f := fun a => (endCoupling B ℓ p p').weight (a, z))
        (fun a _ => (endCoupling B ℓ p p').nonneg (a, z)) (Finset.mem_univ z)
    constructor
    · intro h
      have h0 : (FiniteLaw.ofMeasure (blockEndLaw B ℓ p)).weight z = 0 := by
        change (blockEndLaw B ℓ p).real {z} = 0
        rw [measureReal_def, h, ENNReal.toReal_zero]
      exact hw (le_antisymm (h1.trans h0.le) ((endCoupling B ℓ p p').nonneg _))
    · intro h
      have h0 : (FiniteLaw.ofMeasure (blockEndLaw B ℓ p')).weight z = 0 := by
        change (blockEndLaw B ℓ p').real {z} = 0
        rw [measureReal_def, h, ENNReal.toReal_zero]
      exact hw (le_antisymm (h2.trans h0.le) ((endCoupling B ℓ p p').nonneg _))
  -- the pairs whose base ends differ, up to null sets
  have hN1 : endCoupledPair B ℓ p p' {cc | ¬ ValidBlock B ℓ p cc.1} = 0 := by
    have h : (endCoupledPair B ℓ p p').map Prod.fst {c | ¬ ValidBlock B ℓ p c} = 0 := by
      rw [endCoupledPair_map_fst]
      exact ae_iff.mp (blockLaw_ae_valid B ℓ p hp)
    rwa [Measure.map_apply measurable_fst MeasurableSpace.measurableSet_top] at h
  have hN2 : endCoupledPair B ℓ p p' {cc | ¬ ValidBlock B ℓ p' cc.2} = 0 := by
    have h : (endCoupledPair B ℓ p p').map Prod.snd {c | ¬ ValidBlock B ℓ p' c} = 0 := by
      rw [endCoupledPair_map_snd]
      exact ae_iff.mp (blockLaw_ae_valid B ℓ p' hp')
    rwa [Measure.map_apply measurable_snd MeasurableSpace.measurableSet_top] at h
  have hsub : {cc : Block B × Block B | blockEnd B p cc.1 ≠ blockEnd B p' cc.2} ⊆
      ({cc : Block B × Block B | ¬ ValidBlock B ℓ p cc.1} ∪
        {cc | ¬ ValidBlock B ℓ p' cc.2}) ∪
        {cc | (blockEnd B p cc.1).1 ≠ (blockEnd B p' cc.2).1} := by
    intro cc hcc
    by_cases h1 : ValidBlock B ℓ p cc.1
    · by_cases h2 : ValidBlock B ℓ p' cc.2
      · right
        intro heq
        apply hcc
        exact Prod.ext heq (by rw [h1.2.2.1, h2.2.2.1])
      · left; right; exact h2
    · left; left; exact h1
  have hS : MeasurableSet {cc : Block B × Block B | (blockEnd B p cc.1).1 ≠ (blockEnd B p' cc.2).1} :=
    (Set.to_countable _).measurableSet
  have hF : Measurable (fun zz : B.V × B.V =>
      (condBlock B ℓ p zz.1).prod (condBlock B ℓ p' zz.2)) := measurable_of_countable _
  -- the coupled pair is the coupling mixture of the conditioned products
  have hbind : endCoupledPair B ℓ p p' {cc | (blockEnd B p cc.1).1 ≠ (blockEnd B p' cc.2).1} =
      ∑ zz : B.V × B.V, ((condBlock B ℓ p zz.1).prod (condBlock B ℓ p' zz.2))
        {cc | (blockEnd B p cc.1).1 ≠ (blockEnd B p' cc.2).1} *
        ENNReal.ofReal ((endCoupling B ℓ p p').weight zz) := by
    unfold endCoupledPair
    rw [Measure.bind_apply hS hF.aemeasurable, lintegral_fintype]
    refine Finset.sum_congr rfl fun zz _ => ?_
    rw [FiniteLaw.toMeasure_singleton]
  have hterm : ∀ zz : B.V × B.V,
      ((condBlock B ℓ p zz.1).prod (condBlock B ℓ p' zz.2))
          {cc | (blockEnd B p cc.1).1 ≠ (blockEnd B p' cc.2).1} *
        ENNReal.ofReal ((endCoupling B ℓ p p').weight zz) ≤
      if zz.1 ≠ zz.2 then ENNReal.ofReal ((endCoupling B ℓ p p').weight zz) else 0 := by
    rintro ⟨z, z'⟩
    by_cases hw : (endCoupling B ℓ p p').weight (z, z') = 0
    · rw [hw, ENNReal.ofReal_zero, mul_zero]
      exact zero_le
    by_cases hzz : z = z'
    · subst hzz
      obtain ⟨hz, hz'⟩ := hpos z hw
      rw [prod_condBlock_end_ne_null B ℓ p p' z hz hz', zero_mul]
      exact zero_le
    · rw [if_pos (show (z, z').1 ≠ (z, z').2 from hzz)]
      exact mul_le_of_le_one_left zero_le prob_le_one
  -- the deficit of the end laws is the half total variation distance
  have hreal : ∑ zz : B.V × B.V, (if zz.1 ≠ zz.2 then (endCoupling B ℓ p p').weight zz else 0) =
      (1 / 2) * ∑ z, |(blockEndLaw B ℓ p {z}).toReal - (blockEndLaw B ℓ p' {z}).toReal| := by
    have hagree : (endCoupling B ℓ p p').event (fun z => z.1 = z.2) =
        1 - (FiniteLaw.ofMeasure (blockEndLaw B ℓ p)).deficit
          (FiniteLaw.ofMeasure (blockEndLaw B ℓ p')) :=
      FiniteLaw.coupling_agreement _ _
    have hev : (endCoupling B ℓ p p').event (fun z => z.1 = z.2) =
        ∑ zz : B.V × B.V, (endCoupling B ℓ p p').weight zz * (if zz.1 = zz.2 then 1 else 0) := by
      unfold FiniteLaw.event FiniteLaw.expect
      refine Finset.sum_congr rfl fun zz _ => ?_
      by_cases h : zz.1 = zz.2 <;> simp [h]
    have hsplit : ∀ zz : B.V × B.V,
        (if zz.1 ≠ zz.2 then (endCoupling B ℓ p p').weight zz else 0) =
          (endCoupling B ℓ p p').weight zz -
            (endCoupling B ℓ p p').weight zz * (if zz.1 = zz.2 then 1 else 0) := by
      rintro ⟨z, z'⟩
      by_cases h : z = z' <;> simp [h]
    have hdef : (FiniteLaw.ofMeasure (blockEndLaw B ℓ p)).deficit
        (FiniteLaw.ofMeasure (blockEndLaw B ℓ p')) =
        (1 / 2) * ∑ z, |(blockEndLaw B ℓ p {z}).toReal - (blockEndLaw B ℓ p' {z}).toReal| := by
      rw [FiniteLaw.deficit_half_l1]
      simp only [FiniteLaw.ofMeasure, measureReal_def]
      ring
    simp_rw [hsplit]
    rw [Finset.sum_sub_distrib, (endCoupling B ℓ p p').total, ← hev, hagree, hdef]
    ring
  refine (measure_mono hsub).trans ?_
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (measure_union_le _ _) (le_refl _)).trans ?_
  rw [hN1, hN2, zero_add, zero_add, hbind]
  calc ∑ zz : B.V × B.V, ((condBlock B ℓ p zz.1).prod (condBlock B ℓ p' zz.2))
          {cc | (blockEnd B p cc.1).1 ≠ (blockEnd B p' cc.2).1} *
          ENNReal.ofReal ((endCoupling B ℓ p p').weight zz)
      ≤ ∑ zz : B.V × B.V, (if zz.1 ≠ zz.2 then ENNReal.ofReal ((endCoupling B ℓ p p').weight zz)
          else 0) := Finset.sum_le_sum fun zz _ => hterm zz
    _ = ENNReal.ofReal (∑ zz : B.V × B.V,
          (if zz.1 ≠ zz.2 then (endCoupling B ℓ p p').weight zz else 0)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        · exact Finset.sum_congr rfl fun zz _ => by split_ifs <;> simp
        · intro zz _
          split_ifs
          · exact (endCoupling B ℓ p p').nonneg zz
          · exact le_rfl
    _ = ENNReal.ofReal ((1 / 2) * ∑ z, |(blockEndLaw B ℓ p {z}).toReal -
          (blockEndLaw B ℓ p' {z}).toReal|) := by rw [hreal]

end

end IdlaCyl.Silvestri
