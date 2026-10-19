import IdlaCyl.Support.Silvestri.Blocks
import IdlaCyl.Support.Silvestri.AssembleDet
import IdlaCyl.Support.Silvestri.DrivenTypes

/-!
# The ladder: the pair law of two walks by a finite recursion over blocks

Given a family `Q` of couplings of the first-block laws of two walks, the ladder law
`ladderLaw B Q h j ℓ p p'` runs `j` rounds. In each round the two walks from `p` and `p'`
are cut at their first arrival at the current level `ℓ`, the two blocks are drawn from
`Q ℓ p p'`, and the walks are merged at the common block end if the two ends agree.
Otherwise the recursion continues one level higher, at `ℓ + h`.

The file proves that both marginals of the ladder law are the walk laws from `p` and
`p'`, provided `Q` has the same marginals as the block laws. The marginal identities are
proved by pushing a bind forward along a coordinate projection and then applying the
strong Markov decomposition of the walk law (`walkPathLaw_eq_bind_blockLaw`).
-/

namespace IdlaCyl.Silvestri

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

variable (B : Base)

/-- The ladder law. With `0` rounds the two walks are independent. Each further round draws
a pair of blocks from `Q ℓ p p'`; if their ends agree, the two walks continue from the common
end with one shared continuation, and otherwise the ladder recurses at the height `ℓ + h`. -/
def ladderLaw (Q : ℤ → Site B → Site B → Measure (Block B × Block B)) (h : ℕ) :
    ℕ → ℤ → Site B → Site B → Measure ((ℕ → Site B) × (ℕ → Site B))
  | 0, _, p, p' => (walkPathLaw B p).prod (walkPathLaw B p')
  | j + 1, ℓ, p, p' => (Q ℓ p p').bind fun cc =>
      if blockEnd B p cc.1 = blockEnd B p' cc.2 then
        (walkPathLaw B (blockEnd B p cc.1)).map fun Y => (prepend B p cc.1 Y, prepend B p' cc.2 Y)
      else (ladderLaw Q h j (ℓ + h) (blockEnd B p cc.1) (blockEnd B p' cc.2)).map
        (Prod.map (prepend B p cc.1) (prepend B p' cc.2))

/-- Splicing a block in front of a continuation is a measurable map of the continuation. -/
theorem measurable_prepend_block (p : Site B) (c : Block B) :
    Measurable (prepend B p c) :=
  (measurable_ghostSplicePath B).comp
    ((Measurable.prodMk (Measurable.prodMk measurable_const measurable_id) measurable_const))

/-- Pushing a bind forward along the first projection is the bind against the first marginals. -/
theorem ladder_map_fst_bind {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (F : α → Measure (β × γ)) (hF : Measurable F) :
    (μ.bind F).map Prod.fst = μ.bind (fun a => (F a).map Prod.fst) := by
  have hG : Measurable (fun a => (F a).map Prod.fst) :=
    (Measure.measurable_map _ measurable_fst).comp hF
  ext s hs
  rw [Measure.map_apply measurable_fst hs, Measure.bind_apply (measurable_fst hs) hF.aemeasurable,
    Measure.bind_apply hs hG.aemeasurable]
  exact lintegral_congr fun a => (Measure.map_apply measurable_fst hs).symm

/-- Pushing a bind forward along the second projection is the bind against the second marginals. -/
theorem ladder_map_snd_bind {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (F : α → Measure (β × γ)) (hF : Measurable F) :
    (μ.bind F).map Prod.snd = μ.bind (fun a => (F a).map Prod.snd) := by
  have hG : Measurable (fun a => (F a).map Prod.snd) :=
    (Measure.measurable_map _ measurable_snd).comp hF
  ext s hs
  rw [Measure.map_apply measurable_snd hs, Measure.bind_apply (measurable_snd hs) hF.aemeasurable,
    Measure.bind_apply hs hG.aemeasurable]
  exact lintegral_congr fun a => (Measure.map_apply measurable_snd hs).symm

/-- A bind along the first coordinate of a measure on a product is the bind against the first
marginal. -/
theorem ladder_bind_fst_eq {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure (α × β)) (G : α → Measure γ) (hG : Measurable G) :
    μ.bind (fun cc => G cc.1) = (μ.map Prod.fst).bind G := by
  have h1 : Measurable (fun cc : α × β => G cc.1) := hG.comp measurable_fst
  ext s hs
  have hf : Measurable (fun a => G a s) := (Measure.measurable_coe hs).comp hG
  rw [Measure.bind_apply hs h1.aemeasurable, Measure.bind_apply hs hG.aemeasurable]
  exact (lintegral_map hf measurable_fst).symm

/-- A bind along the second coordinate of a measure on a product is the bind against the second
marginal. -/
theorem ladder_bind_snd_eq {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure (α × β)) (G : β → Measure γ) (hG : Measurable G) :
    μ.bind (fun cc => G cc.2) = (μ.map Prod.snd).bind G := by
  have h1 : Measurable (fun cc : α × β => G cc.2) := hG.comp measurable_snd
  ext s hs
  have hf : Measurable (fun a => G a s) := (Measure.measurable_coe hs).comp hG
  rw [Measure.bind_apply hs h1.aemeasurable, Measure.bind_apply hs hG.aemeasurable]
  exact (lintegral_map hf measurable_snd).symm

/-- Under a coupling whose first marginal is the block law from `p`, the first block is valid
almost surely. -/
theorem ae_valid_block_fst {Q : ℤ → Site B → Site B → Measure (Block B × Block B)}
    (hQ1 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.fst = blockLaw B ℓ p)
    (ℓ : ℤ) (p p' : Site B) (hp : p.2 < ℓ) (hp' : p'.2 < ℓ) :
    ∀ᵐ cc ∂(Q ℓ p p'), ValidBlock B ℓ p cc.1 := by
  have hmap : ∀ᵐ c ∂((Q ℓ p p').map Prod.fst), ValidBlock B ℓ p c := by
    rw [hQ1 ℓ p p' hp hp']
    exact blockLaw_ae_valid B ℓ p hp
  exact (ae_map_iff measurable_fst.aemeasurable
    (Set.to_countable {c : Block B | ValidBlock B ℓ p c}).measurableSet).mp hmap

/-- Under a coupling whose second marginal is the block law from `p'`, the second block is valid
almost surely. -/
theorem ae_valid_block_snd {Q : ℤ → Site B → Site B → Measure (Block B × Block B)}
    (hQ2 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.snd = blockLaw B ℓ p')
    (ℓ : ℤ) (p p' : Site B) (hp : p.2 < ℓ) (hp' : p'.2 < ℓ) :
    ∀ᵐ cc ∂(Q ℓ p p'), ValidBlock B ℓ p' cc.2 := by
  have hmap : ∀ᵐ c ∂((Q ℓ p p').map Prod.snd), ValidBlock B ℓ p' c := by
    rw [hQ2 ℓ p p' hp hp']
    exact blockLaw_ae_valid B ℓ p' hp'
  exact (ae_map_iff measurable_snd.aemeasurable
    (Set.to_countable {c : Block B | ValidBlock B ℓ p' c}).measurableSet).mp hmap

/-- The first marginal of the ladder law is the walk law from `p`. -/
theorem ladderLaw_map_fst {Q : ℤ → Site B → Site B → Measure (Block B × Block B)}
    (hQ1 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.fst = blockLaw B ℓ p)
    (hQ2 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.snd = blockLaw B ℓ p')
    {h : ℕ} (hh : 0 < h) (j : ℕ) :
    ∀ (ℓ : ℤ) (p p' : Site B), p.2 < ℓ → p'.2 < ℓ →
      (ladderLaw B Q h j ℓ p p').map Prod.fst = walkPathLaw B p := by
  induction j with
  | zero =>
    intro ℓ p p' _ _
    simp only [ladderLaw, Measure.map_fst_prod, measure_univ, one_smul]
  | succ j ih =>
    intro ℓ p p' hp hp'
    rw [ladderLaw, ladder_map_fst_bind _ _ (measurable_of_countable _)]
    refine (Measure.bind_congr_right (g := fun cc : Block B × Block B =>
      (walkPathLaw B (blockEnd B p cc.1)).map (prepend B p cc.1)) ?_).trans ?_
    · filter_upwards [ae_valid_block_fst B hQ1 ℓ p p' hp hp',
        ae_valid_block_snd B hQ2 ℓ p p' hp hp'] with cc h1 h2
      by_cases hE : blockEnd B p cc.1 = blockEnd B p' cc.2
      · rw [if_pos hE, Measure.map_map measurable_fst
          ((measurable_prepend_block B p cc.1).prodMk (measurable_prepend_block B p' cc.2))]
        rfl
      · rw [if_neg hE, Measure.map_map measurable_fst
          ((measurable_prepend_block B p cc.1).prodMap (measurable_prepend_block B p' cc.2))]
        have hlt : (blockEnd B p cc.1).2 < ℓ + h := by
          rw [h1.2.2.1]
          omega
        have hlt' : (blockEnd B p' cc.2).2 < ℓ + h := by
          rw [h2.2.2.1]
          omega
        rw [show (Prod.fst ∘ Prod.map (prepend B p cc.1) (prepend B p' cc.2)) =
            (prepend B p cc.1) ∘ Prod.fst from rfl,
          ← Measure.map_map (measurable_prepend_block B p cc.1) measurable_fst,
          ih (ℓ + h) _ _ hlt hlt']
    · refine (ladder_bind_fst_eq _ (fun c : Block B =>
        (walkPathLaw B (blockEnd B p c)).map (prepend B p c)) (measurable_of_countable _)).trans ?_
      rw [hQ1 ℓ p p' hp hp', walkPathLaw_eq_bind_blockLaw B ℓ p]

/-- The second marginal of the ladder law is the walk law from `p'`. -/
theorem ladderLaw_map_snd {Q : ℤ → Site B → Site B → Measure (Block B × Block B)}
    (hQ1 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.fst = blockLaw B ℓ p)
    (hQ2 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.snd = blockLaw B ℓ p')
    {h : ℕ} (hh : 0 < h) (j : ℕ) :
    ∀ (ℓ : ℤ) (p p' : Site B), p.2 < ℓ → p'.2 < ℓ →
      (ladderLaw B Q h j ℓ p p').map Prod.snd = walkPathLaw B p' := by
  induction j with
  | zero =>
    intro ℓ p p' _ _
    simp only [ladderLaw, Measure.map_snd_prod, measure_univ, one_smul]
  | succ j ih =>
    intro ℓ p p' hp hp'
    rw [ladderLaw, ladder_map_snd_bind _ _ (measurable_of_countable _)]
    refine (Measure.bind_congr_right (g := fun cc : Block B × Block B =>
      (walkPathLaw B (blockEnd B p' cc.2)).map (prepend B p' cc.2)) ?_).trans ?_
    · filter_upwards [ae_valid_block_fst B hQ1 ℓ p p' hp hp',
        ae_valid_block_snd B hQ2 ℓ p p' hp hp'] with cc h1 h2
      by_cases hE : blockEnd B p cc.1 = blockEnd B p' cc.2
      · rw [if_pos hE, Measure.map_map measurable_snd
          ((measurable_prepend_block B p cc.1).prodMk (measurable_prepend_block B p' cc.2)), hE]
        rfl
      · rw [if_neg hE, Measure.map_map measurable_snd
          ((measurable_prepend_block B p cc.1).prodMap (measurable_prepend_block B p' cc.2))]
        have hlt : (blockEnd B p cc.1).2 < ℓ + h := by
          rw [h1.2.2.1]
          omega
        have hlt' : (blockEnd B p' cc.2).2 < ℓ + h := by
          rw [h2.2.2.1]
          omega
        rw [show (Prod.snd ∘ Prod.map (prepend B p cc.1) (prepend B p' cc.2)) =
            (prepend B p' cc.2) ∘ Prod.snd from rfl,
          ← Measure.map_map (measurable_prepend_block B p' cc.2) measurable_snd,
          ih (ℓ + h) _ _ hlt hlt']
    · refine (ladder_bind_snd_eq _ (fun c : Block B =>
        (walkPathLaw B (blockEnd B p' c)).map (prepend B p' c)) (measurable_of_countable _)).trans ?_
      rw [hQ2 ℓ p p' hp hp', walkPathLaw_eq_bind_blockLaw B ℓ p']

/-- The ladder law gives mass one to the whole path space. -/
theorem ladderLaw_univ {Q : ℤ → Site B → Site B → Measure (Block B × Block B)}
    (hQ1 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.fst = blockLaw B ℓ p)
    (hQ2 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.snd = blockLaw B ℓ p')
    {h : ℕ} (hh : 0 < h) (j : ℕ) (ℓ : ℤ) (p p' : Site B) (hp : p.2 < ℓ) (hp' : p'.2 < ℓ) :
    ladderLaw B Q h j ℓ p p' Set.univ = 1 := by
  have h2 : (ladderLaw B Q h j ℓ p p').map Prod.fst Set.univ = 1 := by
    rw [ladderLaw_map_fst B hQ1 hQ2 hh j ℓ p p' hp hp', measure_univ]
  rwa [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at h2

/-- Under the ladder law the first path is unbounded above, almost surely. -/
theorem ladderLaw_ae_above_fst {Q : ℤ → Site B → Site B → Measure (Block B × Block B)}
    (hQ1 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.fst = blockLaw B ℓ p)
    (hQ2 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.snd = blockLaw B ℓ p')
    {h : ℕ} (hh : 0 < h) (j : ℕ) (ℓ : ℤ) (p p' : Site B) (hp : p.2 < ℓ) (hp' : p'.2 < ℓ) :
    ∀ᵐ pp ∂(ladderLaw B Q h j ℓ p p'), ∀ M : ℤ, ∃ n, M < (pp.1 n).2 := by
  refine ae_of_ae_map (p := fun y : ℕ → Site B => ∀ M : ℤ, ∃ n, M < (y n).2)
    measurable_fst.aemeasurable ?_
  rw [ladderLaw_map_fst B hQ1 hQ2 hh j ℓ p p' hp hp']
  exact walkPathLaw_ae_above B p

/-- Under the ladder law the second path is unbounded above, almost surely. -/
theorem ladderLaw_ae_above_snd {Q : ℤ → Site B → Site B → Measure (Block B × Block B)}
    (hQ1 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.fst = blockLaw B ℓ p)
    (hQ2 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.snd = blockLaw B ℓ p')
    {h : ℕ} (hh : 0 < h) (j : ℕ) (ℓ : ℤ) (p p' : Site B) (hp : p.2 < ℓ) (hp' : p'.2 < ℓ) :
    ∀ᵐ pp ∂(ladderLaw B Q h j ℓ p p'), ∀ M : ℤ, ∃ n, M < (pp.2 n).2 := by
  refine ae_of_ae_map (p := fun y : ℕ → Site B => ∀ M : ℤ, ∃ n, M < (y n).2)
    measurable_snd.aemeasurable ?_
  rw [ladderLaw_map_snd B hQ1 hQ2 hh j ℓ p p' hp hp']
  exact walkPathLaw_ae_above B p'

/-- Failure of the pathwise success event under the ladder law is bounded by failure of merging:
the two paths are unbounded above almost surely. -/
theorem ladderLaw_pairGood_le {Q : ℤ → Site B → Site B → Measure (Block B × Block B)}
    (hQ1 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.fst = blockLaw B ℓ p)
    (hQ2 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.snd = blockLaw B ℓ p')
    {h : ℕ} (hh : 0 < h) (j : ℕ) (ℓ : ℤ) (p p' : Site B) (hp : p.2 < ℓ) (hp' : p'.2 < ℓ)
    (H : ℝ) :
    ladderLaw B Q h j ℓ p p' {pp | ¬ pairGood B H pp.1 pp.2} ≤
      ladderLaw B Q h j ℓ p p' {pp | ¬ MergedBelow B H pp.1 pp.2} := by
  refine measure_mono_ae ?_
  filter_upwards [ladderLaw_ae_above_fst B hQ1 hQ2 hh j ℓ p p' hp hp',
    ladderLaw_ae_above_snd B hQ1 hQ2 hh j ℓ p p' hp hp'] with pp h1 h2 hg
  intro hm
  exact hg ⟨hm, h1, h2⟩

/-- The trivial case `K = 0` of the failure bound: the ladder law has mass one, so the failure
event has mass at most one. -/
theorem ladderLaw_fail_le_one {Q : ℤ → Site B → Site B → Measure (Block B × Block B)}
    (hQ1 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.fst = blockLaw B ℓ p)
    (hQ2 : ∀ ℓ p p', p.2 < ℓ → p'.2 < ℓ → (Q ℓ p p').map Prod.snd = blockLaw B ℓ p')
    {h : ℕ} (hh : 0 < h) (j : ℕ) (H : ℝ) (ℓ : ℤ) (p p' : Site B) (hp : p.2 < ℓ) (hp' : p'.2 < ℓ) :
    ladderLaw B Q h j ℓ p p' {pp | ¬ MergedBelow B H pp.1 pp.2} ≤ 1 :=
  calc ladderLaw B Q h j ℓ p p' {pp | ¬ MergedBelow B H pp.1 pp.2}
      ≤ ladderLaw B Q h j ℓ p p' Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := ladderLaw_univ B hQ1 hQ2 hh j ℓ p p' hp hp'

/-- Prepending a block to a continuation that starts at the block end shifts the indices of the
continuation by the length of the block. -/
theorem prepend_length_add (p : Site B) (c : Block B) (Y : ℕ → Site B)
    (hY0 : Y 0 = blockEnd B p c) (m : ℕ) :
    prepend B p c Y ((c : List (Site B)).length + m) = Y m := by
  unfold prepend ghostSplicePath
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [blockPath_length, hY0]
  · have hn : ¬ ((c : List (Site B)).length + m ≤ (c : List (Site B)).length) := by omega
    rw [if_neg hn, Nat.add_sub_cancel_left]

/-- Entries of a prepended block up to its length are the entries of the block. -/
theorem prepend_of_le_length (p : Site B) (c : Block B) (Y : ℕ → Site B) {k : ℕ}
    (hk : k ≤ (c : List (Site B)).length) :
    prepend B p c Y k = blockPath B p c k := by
  unfold prepend ghostSplicePath
  rw [if_pos hk]

/-- Entries of a prepended block beyond its length are entries of the continuation. -/
theorem prepend_of_length_lt (p : Site B) (c : Block B) (Y : ℕ → Site B) {k : ℕ}
    (hk : (c : List (Site B)).length < k) :
    prepend B p c Y k = Y (k - (c : List (Site B)).length) := by
  unfold prepend ghostSplicePath
  rw [if_neg (Nat.not_le.mpr hk)]

/-- The entries of a valid block up to its end lie at height at most the target level. -/
theorem validBlock_height_le {ℓ : ℤ} {p : Site B} {c : Block B} (hc : ValidBlock B ℓ p c)
    {k : ℕ} (hk : k ≤ (c : List (Site B)).length) : (blockPath B p c k).2 ≤ ℓ := by
  rcases Nat.lt_or_ge k (c : List (Site B)).length with hlt | hge
  · exact (hc.2.1 k hlt).le
  · have hk' : k = (c : List (Site B)).length := le_antisymm hk hge
    subst hk'
    rw [blockPath_length, hc.2.2.1]

/-- Merging below a height survives prepending valid blocks, when the continuations start at the
block ends and the height is at least the level of the blocks. -/
theorem mergedBelow_prepend (p p' : Site B) (c c' : Block B) {ℓ : ℤ} {H : ℝ}
    (hℓ : (ℓ : ℝ) ≤ H) (hc : ValidBlock B ℓ p c) (hc' : ValidBlock B ℓ p' c')
    (Y Y' : ℕ → Site B) (hY0 : Y 0 = blockEnd B p c) (hY0' : Y' 0 = blockEnd B p' c')
    (hm : MergedBelow B H Y Y') :
    MergedBelow B H (prepend B p c Y) (prepend B p' c' Y') := by
  obtain ⟨a, b, hshift, hpre, hpre'⟩ := hm
  refine ⟨(c : List (Site B)).length + a, (c' : List (Site B)).length + b, ?_, ?_, ?_⟩
  · intro n
    rw [show (c : List (Site B)).length + a + n = (c : List (Site B)).length + (a + n) by omega,
      show (c' : List (Site B)).length + b + n = (c' : List (Site B)).length + (b + n) by omega,
      prepend_length_add B p c Y hY0, prepend_length_add B p' c' Y' hY0', hshift n]
  · intro k hk
    by_cases hkc : k ≤ (c : List (Site B)).length
    · rw [prepend_of_le_length B p c Y hkc, mem_R]
      have h1 : ((blockPath B p c k).2 : ℝ) ≤ (ℓ : ℝ) := by
        exact_mod_cast validBlock_height_le B hc hkc
      exact h1.trans hℓ
    · rw [prepend_of_length_lt B p c Y (by omega)]
      exact hpre _ (by omega)
  · intro k hk
    by_cases hkc : k ≤ (c' : List (Site B)).length
    · rw [prepend_of_le_length B p' c' Y' hkc, mem_R]
      have h1 : ((blockPath B p' c' k).2 : ℝ) ≤ (ℓ : ℝ) := by
        exact_mod_cast validBlock_height_le B hc' hkc
      exact h1.trans hℓ
    · rw [prepend_of_length_lt B p' c' Y' (by omega)]
      exact hpre' _ (by omega)

end

end IdlaCyl.Silvestri
