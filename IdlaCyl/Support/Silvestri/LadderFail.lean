module

public import IdlaCyl.Support.Silvestri.Ladder

@[expose] public section

/-!
# The failure bound of the ladder

The ladder law `ladderLaw B Q h j ℓ p p'` pairs two walks by `j` rounds of block couplings. This
file proves that the event that the two paths are not merged below a height grows by a factor of
at most `q` per round. If each round's couplings separate the block ends with probability at most
`q`, then after `K` rounds the failure probability is at most `q ^ K`, at the height
`ℓ + (K - 1) h`.

The main results are `measurableSet_mergedBelow`, which shows that merging below a height is a
measurable event, `ladderLaw_fail_le`, the bound by induction on the number of rounds, and
`ladderLaw_notPairGood_le`, the same bound for the pathwise success event.
-/

namespace IdlaCyl.Silvestri

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

variable (B : Base)

/-- Merging below a height is a measurable event of the pair of paths. -/
theorem measurableSet_mergedBelow (H : ℝ) :
    MeasurableSet {pp : (ℕ → Site B) × (ℕ → Site B) | MergedBelow B H pp.1 pp.2} := by
  have hcoord : ∀ k : ℕ, Measurable (fun pp : (ℕ → Site B) × (ℕ → Site B) => pp.1 k) :=
    fun k => (measurable_pi_apply k).comp measurable_fst
  have hcoord' : ∀ k : ℕ, Measurable (fun pp : (ℕ → Site B) × (ℕ → Site B) => pp.2 k) :=
    fun k => (measurable_pi_apply k).comp measurable_snd
  have hR : ∀ k : ℕ, MeasurableSet {pp : (ℕ → Site B) × (ℕ → Site B) | pp.1 k ∈ R B H} :=
    fun k => hcoord k (Set.to_countable (R B H)).measurableSet
  have hR' : ∀ k : ℕ, MeasurableSet {pp : (ℕ → Site B) × (ℕ → Site B) | pp.2 k ∈ R B H} :=
    fun k => hcoord' k (Set.to_countable (R B H)).measurableSet
  have heq : ∀ a b n : ℕ,
      MeasurableSet {pp : (ℕ → Site B) × (ℕ → Site B) | pp.1 (a + n) = pp.2 (b + n)} :=
    fun a b n => measurableSet_eq_fun (hcoord (a + n)) (hcoord' (b + n))
  have hset : {pp : (ℕ → Site B) × (ℕ → Site B) | MergedBelow B H pp.1 pp.2} =
      ⋃ a : ℕ, ⋃ b : ℕ,
        ((⋂ n : ℕ, {pp : (ℕ → Site B) × (ℕ → Site B) | pp.1 (a + n) = pp.2 (b + n)}) ∩
          (⋂ k : ℕ, ⋂ (_ : k < a), {pp : (ℕ → Site B) × (ℕ → Site B) | pp.1 k ∈ R B H}) ∩
          (⋂ k : ℕ, ⋂ (_ : k < b), {pp : (ℕ → Site B) × (ℕ → Site B) | pp.2 k ∈ R B H})) := by
    ext pp
    simp only [MergedBelow, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter,
      and_assoc]
  rw [hset]
  refine MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b => ?_
  refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
  · exact MeasurableSet.iInter fun n => heq a b n
  · exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => hR k
  · exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => hR' k

/-- A positive gap `h` between the height of the start and the level gives the strict height
bound used by the marginal lemmas of the ladder. -/
theorem height_lt_of_add_le {p : Site B} {ℓ : ℤ} {h : ℕ} (hh : 0 < h)
    (hp : (p.2 : ℝ) + h ≤ ℓ) : p.2 < ℓ := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have : (p.2 : ℝ) < ℓ := by linarith
  exact_mod_cast this

/-- Two continuations that start at a common block end, with the same shared tail, are merged
below any height at least the level of the blocks. So the failure event of the pair has
probability zero when the two prepended blocks end at the same site. -/
theorem prepend_pair_fail_eq (p p' : Site B) (c c' : Block B) {ℓ : ℤ} {H : ℝ}
    (hℓ : (ℓ : ℝ) ≤ H) (hc : ValidBlock B ℓ p c) (hc' : ValidBlock B ℓ p' c')
    (hE : blockEnd B p c = blockEnd B p' c') :
    ((walkPathLaw B (blockEnd B p c)).map fun Y => (prepend B p c Y, prepend B p' c' Y))
      {pp | ¬ MergedBelow B H pp.1 pp.2} = 0 := by
  have hS : MeasurableSet {pp : (ℕ → Site B) × (ℕ → Site B) | ¬ MergedBelow B H pp.1 pp.2} :=
    (measurableSet_mergedBelow B H).compl
  rw [Measure.map_apply ((measurable_prepend_block B p c).prodMk
    (measurable_prepend_block B p' c')) hS]
  have hae := ae_iff.mp (walkPathLaw_ae_start B (blockEnd B p c))
  refine measure_mono_null ?_ hae
  intro Y hY hY0
  exact hY (mergedBelow_prepend B p p' c c' hℓ hc hc' Y Y hY0 (hY0.trans hE)
    ⟨0, 0, fun n => rfl, fun k hk => absurd hk (Nat.not_lt_zero k),
      fun k hk => absurd hk (Nat.not_lt_zero k)⟩)

/-- Prepending valid blocks to a coupling of two continuations does not increase the failure of
merging below a height, when both continuations start at the block ends almost surely. -/
theorem prepend_pair_fail_le (p p' : Site B) (c c' : Block B) {ℓ : ℤ} {H : ℝ}
    (hℓ : (ℓ : ℝ) ≤ H) (hc : ValidBlock B ℓ p c) (hc' : ValidBlock B ℓ p' c')
    (μ : Measure ((ℕ → Site B) × (ℕ → Site B)))
    (hμ1 : ∀ᵐ pp ∂μ, pp.1 0 = blockEnd B p c) (hμ2 : ∀ᵐ pp ∂μ, pp.2 0 = blockEnd B p' c') :
    (μ.map (Prod.map (prepend B p c) (prepend B p' c'))) {pp | ¬ MergedBelow B H pp.1 pp.2} ≤
      μ {pp | ¬ MergedBelow B H pp.1 pp.2} := by
  have hS : MeasurableSet {pp : (ℕ → Site B) × (ℕ → Site B) | ¬ MergedBelow B H pp.1 pp.2} :=
    (measurableSet_mergedBelow B H).compl
  rw [Measure.map_apply ((measurable_prepend_block B p c).prodMap
    (measurable_prepend_block B p' c')) hS]
  refine measure_mono_ae ?_
  filter_upwards [hμ1, hμ2] with pp h1 h2 hX hm
  exact hX (mergedBelow_prepend B p p' c c' hℓ hc hc' pp.1 pp.2 h1 h2 hm)

/-- The failure bound of the ladder. After `K ≤ j` rounds, the event that the two paths are not
merged below the height `ℓ + (K - 1) h` has probability at most `q ^ K`, provided that each
round's couplings separate the block ends with probability at most `q`. -/
theorem ladderLaw_fail_le {Q : ℤ → Site B → Site B → Measure (Block B × Block B)}
    (hQ1 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.fst = blockLaw B ℓ p)
    (hQ2 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.snd = blockLaw B ℓ p')
    {h : ℕ} (hh : 0 < h) {q : ℝ} (hq : 0 ≤ q)
    (hQf : ∀ (ℓ : ℤ) (p p' : Site B), (p.2 : ℝ) + h ≤ ℓ → (p'.2 : ℝ) + h ≤ ℓ →
      Q ℓ p p' {cc | blockEnd B p cc.1 ≠ blockEnd B p' cc.2} ≤ ENNReal.ofReal q)
    (j K : ℕ) (hK : K ≤ j) (ℓ : ℤ) (p p' : Site B)
    (hp : (p.2 : ℝ) + h ≤ ℓ) (hp' : (p'.2 : ℝ) + h ≤ ℓ) :
    ladderLaw B Q h j ℓ p p' {pp | ¬ MergedBelow B ((ℓ : ℝ) + ((K : ℝ) - 1) * h) pp.1 pp.2} ≤
      ENNReal.ofReal (q ^ K) := by
  induction j generalizing K ℓ p p' with
  | zero =>
    obtain rfl : K = 0 := by omega
    simp only [pow_zero, ENNReal.ofReal_one]
    exact ladderLaw_fail_le_one B hQ1 hQ2 hh 0 _ ℓ p p' (height_lt_of_add_le B hh hp)
      (height_lt_of_add_le B hh hp')
  | succ j ih =>
    rcases Nat.eq_zero_or_pos K with rfl | hK0
    · simp only [pow_zero, ENNReal.ofReal_one]
      exact ladderLaw_fail_le_one B hQ1 hQ2 hh (j + 1) _ ℓ p p' (height_lt_of_add_le B hh hp)
        (height_lt_of_add_le B hh hp')
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have hK' : K' ≤ j := by omega
    have hp₁ : p.2 < ℓ := height_lt_of_add_le B hh hp
    have hp₂ : p'.2 < ℓ := height_lt_of_add_le B hh hp'
    have hHℓ : (ℓ : ℝ) ≤ (ℓ : ℝ) + (((K' + 1 : ℕ) : ℝ) - 1) * h := by
      have h0 : (0 : ℝ) ≤ (((K' + 1 : ℕ) : ℝ) - 1) * h :=
        mul_nonneg (by push_cast; linarith [(Nat.cast_nonneg K' : (0 : ℝ) ≤ K')])
          (Nat.cast_nonneg h)
      linarith
    have hS : MeasurableSet {pp : (ℕ → Site B) × (ℕ → Site B) |
        ¬ MergedBelow B ((ℓ : ℝ) + (((K' + 1 : ℕ) : ℝ) - 1) * h) pp.1 pp.2} :=
      (measurableSet_mergedBelow B _).compl
    have hD : MeasurableSet {cc : Block B × Block B | blockEnd B p cc.1 ≠ blockEnd B p' cc.2} :=
      (Set.to_countable _).measurableSet
    rw [ladderLaw, Measure.bind_apply hS (measurable_of_countable _).aemeasurable]
    refine le_trans (lintegral_mono_ae (g := {cc : Block B × Block B |
        blockEnd B p cc.1 ≠ blockEnd B p' cc.2}.indicator fun _ => ENNReal.ofReal (q ^ K')) ?_) ?_
    · filter_upwards [ae_valid_block_fst B hQ1 ℓ p p' hp₁ hp₂,
        ae_valid_block_snd B hQ2 ℓ p p' hp₁ hp₂] with cc hv1 hv2
      by_cases hE : blockEnd B p cc.1 = blockEnd B p' cc.2
      · have hnot : cc ∉ {cc : Block B × Block B | blockEnd B p cc.1 ≠ blockEnd B p' cc.2} :=
          fun hD' => hD' hE
        rw [if_pos hE, Set.indicator_of_notMem hnot]
        exact (prepend_pair_fail_eq B p p' cc.1 cc.2 hHℓ hv1 hv2 hE).le
      · have hmem : cc ∈ {cc : Block B × Block B | blockEnd B p cc.1 ≠ blockEnd B p' cc.2} := hE
        rw [if_neg hE, Set.indicator_of_mem hmem]
        have hlte : ((blockEnd B p cc.1).2 : ℝ) + h ≤ ((ℓ + h : ℤ) : ℝ) := by
          simp [hv1.2.2.1]
        have hlte' : ((blockEnd B p' cc.2).2 : ℝ) + h ≤ ((ℓ + h : ℤ) : ℝ) := by
          simp [hv2.2.2.1]
        have hlt₁ : (blockEnd B p cc.1).2 < ℓ + h := by
          rw [hv1.2.2.1]
          omega
        have hlt₂ : (blockEnd B p' cc.2).2 < ℓ + h := by
          rw [hv2.2.2.1]
          omega
        have hIH := ih K' hK' (ℓ + (h : ℤ)) (blockEnd B p cc.1) (blockEnd B p' cc.2) hlte hlte'
        have hHeq : ((ℓ + h : ℤ) : ℝ) + ((K' : ℝ) - 1) * h =
            (ℓ : ℝ) + (((K' + 1 : ℕ) : ℝ) - 1) * h := by
          push_cast
          ring
        rw [hHeq] at hIH
        have hN1 : ∀ᵐ pp ∂(ladderLaw B Q h j (ℓ + h) (blockEnd B p cc.1) (blockEnd B p' cc.2)),
            pp.1 0 = blockEnd B p cc.1 := by
          refine ae_of_ae_map (p := fun y : ℕ → Site B => y 0 = blockEnd B p cc.1)
            measurable_fst.aemeasurable ?_
          rw [ladderLaw_map_fst B hQ1 hQ2 hh j (ℓ + h) _ _ hlt₁ hlt₂]
          exact walkPathLaw_ae_start B _
        have hN2 : ∀ᵐ pp ∂(ladderLaw B Q h j (ℓ + h) (blockEnd B p cc.1) (blockEnd B p' cc.2)),
            pp.2 0 = blockEnd B p' cc.2 := by
          refine ae_of_ae_map (p := fun y : ℕ → Site B => y 0 = blockEnd B p' cc.2)
            measurable_snd.aemeasurable ?_
          rw [ladderLaw_map_snd B hQ1 hQ2 hh j (ℓ + h) _ _ hlt₁ hlt₂]
          exact walkPathLaw_ae_start B _
        exact le_trans (prepend_pair_fail_le B p p' cc.1 cc.2 hHℓ hv1 hv2 _ hN1 hN2) hIH
    · rw [lintegral_indicator_const hD, pow_succ, ENNReal.ofReal_mul (pow_nonneg hq K')]
      exact mul_le_mul_of_nonneg_left (hQf ℓ p p' hp hp') zero_le

/-- The failure bound of the ladder for the pathwise success event: the same bound holds for
the event that the paths are not good below the height `ℓ + (K - 1) h`. -/
theorem ladderLaw_notPairGood_le {Q : ℤ → Site B → Site B → Measure (Block B × Block B)}
    (hQ1 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.fst = blockLaw B ℓ p)
    (hQ2 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.snd = blockLaw B ℓ p')
    {h : ℕ} (hh : 0 < h) {q : ℝ} (hq : 0 ≤ q)
    (hQf : ∀ (ℓ : ℤ) (p p' : Site B), (p.2 : ℝ) + h ≤ ℓ → (p'.2 : ℝ) + h ≤ ℓ →
      Q ℓ p p' {cc | blockEnd B p cc.1 ≠ blockEnd B p' cc.2} ≤ ENNReal.ofReal q)
    (j K : ℕ) (hK : K ≤ j) (ℓ : ℤ) (p p' : Site B)
    (hp : (p.2 : ℝ) + h ≤ ℓ) (hp' : (p'.2 : ℝ) + h ≤ ℓ) :
    ladderLaw B Q h j ℓ p p' {pp | ¬ pairGood B ((ℓ : ℝ) + ((K : ℝ) - 1) * h) pp.1 pp.2} ≤
      ENNReal.ofReal (q ^ K) :=
  (ladderLaw_pairGood_le B hQ1 hQ2 hh j ℓ p p' (height_lt_of_add_le B hh hp)
    (height_lt_of_add_le B hh hp') _).trans
    (ladderLaw_fail_le B hQ1 hQ2 hh hq hQf j K hK ℓ p p' hp hp')

end

end IdlaCyl.Silvestri
