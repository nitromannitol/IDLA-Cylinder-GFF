import IdlaCyl.Support.Silvestri.BlockPair
import IdlaCyl.Support.Silvestri.HoldBlock
import IdlaCyl.Support.Silvestri.FinalArith
import Mathlib

/-!
# The end of the block pair, and its failure bound

The two first blocks of the block pair from two starts strictly below the level `ℓ` end at the
same site, except with a small probability. The file proves this in two forms.

* `blockPair_end_ne_le`: the probability that the two block ends differ is at most the two
  probabilities that a block has fewer than `m` horizontal steps, plus
  `2 (1/2) ^ (m / τ)`, where `τ = silvestriMixingTime B`.
* `blockPair_fail_le`: at the ladder spacing and the holding length of `Params`, the same
  probability is at most `holdFail B`.

On a fibre of the pair over two valid blocks with at least `m` horizontal steps each, both
block ends lie at level `ℓ`, so the ends differ only when the base endpoints of the two windows
differ. The window coupling bounds that probability (`blockPair_fibre_ne_le`).
-/

namespace IdlaCyl.Silvestri

open MeasureTheory
open IdlaCyl.External
open scoped ENNReal

noncomputable section

variable (B : Base)

/-- On the fibre of the block pair over two valid blocks with at least `m` horizontal steps
each, the rebuilt block ends differ with probability at most `2 (1/2) ^ (m / τ)`, where
`τ = silvestriMixingTime B`. Both ends lie at level `ℓ`, so the ends differ only when the base
endpoints of the two windows differ, and the window coupling bounds that. -/
theorem blockPair_fibre_ne_le (ℓ : ℤ) (p p' : Site B) (c c' : Block B)
    (hc : ValidBlock B ℓ p c) (hc' : ValidBlock B ℓ p' c') (m : ℕ)
    (hm : m ≤ hcount B p c) (hm' : m ≤ hcount B p' c') :
    ((windowCouple B (hcount B p c) (hcount B p' c') p.1 p'.1).toMeasure.map
      fun ww => (reassemble B p c ww.1, reassemble B p' c' ww.2))
      {cc | blockEnd B p cc.1 ≠ blockEnd B p' cc.2} ≤
      ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ (m / silvestriMixingTime B)) := by
  classical
  have hg : Measurable (fun ww : (Fin (hcount B p c) → B.V) × (Fin (hcount B p' c') → B.V) =>
      (reassemble B p c ww.1, reassemble B p' c' ww.2)) :=
    measurable_of_countable _
  rw [Measure.map_apply hg (Set.to_countable _).measurableSet]
  have hset : (fun ww : (Fin (hcount B p c) → B.V) × (Fin (hcount B p' c') → B.V) =>
      (reassemble B p c ww.1, reassemble B p' c' ww.2)) ⁻¹'
        {cc | blockEnd B p cc.1 ≠ blockEnd B p' cc.2}
      = {ww | pathEnd B p.1 (hcount B p c) ww.1 = pathEnd B p'.1 (hcount B p' c') ww.2}ᶜ := by
    ext ww
    simp [blockEnd_reassemble B p c ww.1 rfl, blockEnd_reassemble B p' c' ww.2 rfl,
      hc.2.2.1, hc'.2.2.1]
  rw [hset, prob_compl_eq_one_sub (Set.toFinite _).measurableSet, toMeasure_event]
  have hagree := windowCouple_agreement B (hcount B p c) (hcount B p' c') p.1 p'.1
  have hmono : (1 / 2 : ℝ) ^ (min (hcount B p c) (hcount B p' c') / silvestriMixingTime B)
      ≤ (1 / 2 : ℝ) ^ (m / silvestriMixingTime B) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (Nat.div_le_div_right (le_min hm hm'))
  rw [tsub_le_iff_right]
  calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
    _ ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ (m / silvestriMixingTime B) +
          (windowCouple B (hcount B p c) (hcount B p' c') p.1 p'.1).event
            (fun ww => pathEnd B p.1 (hcount B p c) ww.1 = pathEnd B p'.1 (hcount B p' c') ww.2)) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ (m / silvestriMixingTime B)) +
          ENNReal.ofReal ((windowCouple B (hcount B p c) (hcount B p' c') p.1 p'.1).event
            (fun ww => pathEnd B p.1 (hcount B p c) ww.1 = pathEnd B p'.1 (hcount B p' c') ww.2)) :=
        ENNReal.ofReal_add_le

/-- The probability that the two first blocks from `p` and `p'` end at different sites is at
most the two probabilities that a block has fewer than `m` horizontal steps, plus the dyadic
term `2 (1/2) ^ (m / τ)`, where `τ = silvestriMixingTime B`. The starts lie strictly below the
level `ℓ`. -/
theorem blockPair_end_ne_le (ℓ : ℤ) (p p' : Site B) (hp : p.2 < ℓ) (hp' : p'.2 < ℓ) (m : ℕ) :
    blockPair B ℓ p p' {cc | blockEnd B p cc.1 ≠ blockEnd B p' cc.2} ≤
      blockLaw B ℓ p {c | hcount B p c < m} + blockLaw B ℓ p' {c | hcount B p' c < m} +
        ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ (m / silvestriMixingTime B)) := by
  classical
  unfold blockPair
  have hE : MeasurableSet {cc : Block B × Block B | blockEnd B p cc.1 ≠ blockEnd B p' cc.2} :=
    (Set.to_countable _).measurableSet
  have hF : Measurable fun cc : Block B × Block B =>
      ((windowCouple B (hcount B p cc.1) (hcount B p' cc.2) p.1 p'.1).toMeasure).map
        fun ww => (reassemble B p cc.1 ww.1, reassemble B p' cc.2 ww.2) :=
    measurable_block_pair B _
  rw [Measure.bind_apply hE hF.aemeasurable]
  -- a.e. under the product, both coordinates are valid blocks
  have hae : ∀ᵐ cc ∂((blockLaw B ℓ p).prod (blockLaw B ℓ p')),
      ValidBlock B ℓ p cc.1 ∧ ValidBlock B ℓ p' cc.2 :=
    (Measure.quasiMeasurePreserving_fst.ae (blockLaw_ae_valid B ℓ p hp)).and
      (Measure.quasiMeasurePreserving_snd.ae (blockLaw_ae_valid B ℓ p' hp'))
  -- pointwise bound on the fibre, with the two indicators of the short blocks
  have hpt : ∀ z : Block B × Block B, ValidBlock B ℓ p z.1 → ValidBlock B ℓ p' z.2 →
      ((windowCouple B (hcount B p z.1) (hcount B p' z.2) p.1 p'.1).toMeasure.map
        fun ww => (reassemble B p z.1 ww.1, reassemble B p' z.2 ww.2))
        {cc | blockEnd B p cc.1 ≠ blockEnd B p' cc.2}
      ≤ ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ (m / silvestriMixingTime B))
        + (Prod.fst ⁻¹' {c | hcount B p c < m}).indicator 1 z
        + (Prod.snd ⁻¹' {c | hcount B p' c < m}).indicator 1 z := by
    intro z hz hz'
    have hprob : IsProbabilityMeasure
        ((windowCouple B (hcount B p z.1) (hcount B p' z.2) p.1 p'.1).toMeasure.map
          fun ww => (reassemble B p z.1 ww.1, reassemble B p' z.2 ww.2)) :=
      Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
    by_cases h1 : hcount B p z.1 < m
    · have hind : (Prod.fst ⁻¹' {c | hcount B p c < m}).indicator
          (1 : Block B × Block B → ℝ≥0∞) z = 1 :=
        Set.indicator_of_mem (show z ∈ Prod.fst ⁻¹' {c | hcount B p c < m} from h1) _
      rw [hind]
      exact le_trans prob_le_one (le_add_right (le_add_left le_rfl))
    · by_cases h2 : hcount B p' z.2 < m
      · have hind : (Prod.snd ⁻¹' {c | hcount B p' c < m}).indicator
            (1 : Block B × Block B → ℝ≥0∞) z = 1 :=
          Set.indicator_of_mem (show z ∈ Prod.snd ⁻¹' {c | hcount B p' c < m} from h2) _
        have hz0 : (Prod.fst ⁻¹' {c | hcount B p c < m}).indicator
            (1 : Block B × Block B → ℝ≥0∞) z = 0 :=
          Set.indicator_of_notMem (show z ∉ Prod.fst ⁻¹' {c | hcount B p c < m} from h1) _
        rw [hind, hz0]
        exact le_trans prob_le_one (by simp)
      · have hind1 : (Prod.fst ⁻¹' {c | hcount B p c < m}).indicator
            (1 : Block B × Block B → ℝ≥0∞) z = 0 :=
          Set.indicator_of_notMem (show z ∉ Prod.fst ⁻¹' {c | hcount B p c < m} from h1) _
        have hind2 : (Prod.snd ⁻¹' {c | hcount B p' c < m}).indicator
            (1 : Block B × Block B → ℝ≥0∞) z = 0 :=
          Set.indicator_of_notMem (show z ∉ Prod.snd ⁻¹' {c | hcount B p' c < m} from h2) _
        simp only [hind1, hind2, add_zero]
        exact blockPair_fibre_ne_le B ℓ p p' z.1 z.2 hz hz' m (not_lt.mp h1) (not_lt.mp h2)
  -- the integral of the bound, term by term
  have hS₁ : MeasurableSet {c : Block B | hcount B p c < m} := (Set.to_countable _).measurableSet
  have hS₂ : MeasurableSet {c : Block B | hcount B p' c < m} := (Set.to_countable _).measurableSet
  have hprod_fst : ∀ S : Set (Block B), MeasurableSet S →
      ((blockLaw B ℓ p).prod (blockLaw B ℓ p')) (Prod.fst ⁻¹' S) = blockLaw B ℓ p S := by
    intro S hS
    rw [← Measure.map_apply measurable_fst hS, Measure.map_fst_prod, measure_univ, one_smul]
  have hprod_snd : ∀ S : Set (Block B), MeasurableSet S →
      ((blockLaw B ℓ p).prod (blockLaw B ℓ p')) (Prod.snd ⁻¹' S) = blockLaw B ℓ p' S := by
    intro S hS
    rw [← Measure.map_apply measurable_snd hS, Measure.map_snd_prod, measure_univ, one_smul]
  refine (lintegral_mono_ae (hae.mono fun z hz => hpt z hz.1 hz.2)).trans (le_of_eq ?_)
  rw [lintegral_add_left (measurable_block_pair B _),
    lintegral_add_left (measurable_block_pair B _), lintegral_const, measure_univ, mul_one,
    lintegral_indicator_one (hS₁.preimage measurable_fst),
    lintegral_indicator_one (hS₂.preimage measurable_snd),
    hprod_fst _ hS₁, hprod_snd _ hS₂]
  ring

/-- At the ladder spacing and the holding length of `Params`, the probability that the two
first blocks from `p` and `p'` end at different sites is at most `holdFail B`. The starts lie at
distance at least the ladder spacing below the level `ℓ`. -/
theorem blockPair_fail_le (hN : 2 ≤ B.card) (ℓ : ℤ) (p p' : Site B)
    (hp : (p.2 : ℝ) + ladderStep B ≤ ℓ) (hp' : (p'.2 : ℝ) + ladderStep B ≤ ℓ) :
    blockPair B ℓ p p' {cc | blockEnd B p cc.1 ≠ blockEnd B p' cc.2} ≤
      ENNReal.ofReal (holdFail B) := by
  have hstep : (0 : ℝ) < ladderStep B := by exact_mod_cast ladderStep_pos B hN
  have hp1 : p.2 < ℓ := by
    have : (p.2 : ℝ) < ℓ := by linarith
    exact_mod_cast this
  have hp1' : p'.2 < ℓ := by
    have : (p'.2 : ℝ) < ℓ := by linarith
    exact_mod_cast this
  have h1 := blockLaw_hcount_lt_ladder B ℓ p hN hp
  have h2 := blockLaw_hcount_lt_ladder B ℓ p' hN hp'
  have hA : (0 : ℝ) ≤ Real.exp (-(ladderStep B : ℝ) ^ 2 / (4 * (holdLen B : ℝ)))
      + Real.exp (-(holdLen B : ℝ) / 2) := by positivity
  have hY : (0 : ℝ) ≤ 2 * (1 / 2 : ℝ) ^ (holdLen B / silvestriMixingTime B) := by positivity
  calc blockPair B ℓ p p' {cc | blockEnd B p cc.1 ≠ blockEnd B p' cc.2}
      ≤ blockLaw B ℓ p {c | hcount B p c < holdLen B}
          + blockLaw B ℓ p' {c | hcount B p' c < holdLen B}
          + ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ (holdLen B / silvestriMixingTime B)) :=
        blockPair_end_ne_le B ℓ p p' hp1 hp1' (holdLen B)
    _ ≤ ENNReal.ofReal (Real.exp (-(ladderStep B : ℝ) ^ 2 / (4 * (holdLen B : ℝ)))
          + Real.exp (-(holdLen B : ℝ) / 2))
        + ENNReal.ofReal (Real.exp (-(ladderStep B : ℝ) ^ 2 / (4 * (holdLen B : ℝ)))
          + Real.exp (-(holdLen B : ℝ) / 2))
        + ENNReal.ofReal (2 * (1 / 2 : ℝ) ^ (holdLen B / silvestriMixingTime B)) :=
        add_le_add (add_le_add h1 h2) le_rfl
    _ = ENNReal.ofReal ((Real.exp (-(ladderStep B : ℝ) ^ 2 / (4 * (holdLen B : ℝ)))
          + Real.exp (-(holdLen B : ℝ) / 2)) + (Real.exp (-(ladderStep B : ℝ) ^ 2 / (4 * (holdLen B : ℝ)))
          + Real.exp (-(holdLen B : ℝ) / 2))
        + 2 * (1 / 2 : ℝ) ^ (holdLen B / silvestriMixingTime B)) := by
        rw [ENNReal.ofReal_add (add_nonneg hA hA) hY, ENNReal.ofReal_add hA hA]
    _ ≤ ENNReal.ofReal (holdFail B) := by
        apply ENNReal.ofReal_le_ofReal
        unfold holdFail
        linarith

end

end IdlaCyl.Silvestri
