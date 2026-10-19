import IdlaCyl.Support.Silvestri.BlockResample
import Mathlib

/-!
# Window resampling preserves the block law

A block of the first passage from `p` to level `ℓ` is resampled by keeping its vertical
skeleton and redrawing its horizontal steps from the path law of the matching length,
started at the base vertex of `p`. The file proves that this resampling leaves the block
law unchanged: when `p` lies strictly below `ℓ`, the image of `blockLaw B ℓ p` under the
resampling kernel is `blockLaw B ℓ p`.

The proof compares the masses of singletons. A block is height-valid when it has the height
conditions of `ValidBlock` without the positivity of its steps; for such blocks the block law
is the path weight of the block. Rebuilding a valid block from a window keeps its heights, so
every rebuilt block has the block law of the window's path weight times the skeleton weight.
The blocks with a given skeleton carry the skeleton weight in total, and the windows that
rebuild a given block are exactly those that spell its horizontal list.
-/

open MeasureTheory

open scoped Classical

noncomputable section

namespace IdlaCyl.Silvestri

variable (B : Base)

/-- A block is height-valid from `p` to level `ℓ` when it is nonempty, its entries strictly
below `ℓ` precede its end, and its end lies at height `ℓ`. This is `ValidBlock` without the
positivity of the steps. -/
def HeightValid (ℓ : ℤ) (p : Site B) (c : Block B) : Prop :=
  (c : List (Site B)) ≠ [] ∧ (∀ n < (c : List (Site B)).length, (blockPath B p c n).2 < ℓ) ∧
    (blockEnd B p c).2 = ℓ

/-- The skeleton of a list of sites has the length of the list. -/
theorem length_skel (p : Site B) (c : List (Site B)) : (skel p c).length = c.length := by
  induction c generalizing p with
  | nil => rfl
  | cons q c ih => simp only [skel, List.length_cons, ih]

/-- The sum of the weights of the windows of a fixed length is `1`, and the weights are
positive for every skeleton: each factor of `skelWeight` is positive. -/
theorem skelWeight_pos (τ : List ℤ) : 0 < skelWeight τ := by
  unfold skelWeight
  apply List.prod_pos
  intro x hx
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
  split_ifs <;> norm_num

/-- The skeleton weight is nonnegative. -/
theorem skelWeight_nonneg (τ : List ℤ) : 0 ≤ skelWeight τ := (skelWeight_pos τ).le

/-- A block whose end is not valid has zero block law. -/
theorem blockLaw_singleton_eq_zero (ℓ : ℤ) (p : Site B) (hp : p.2 < ℓ) (c : Block B)
    (hc : ¬ ValidBlock B ℓ p c) : blockLaw B ℓ p {c} = 0 :=
  measure_mono_null (Set.singleton_subset_iff.mpr hc) (ae_iff.mp (blockLaw_ae_valid B ℓ p hp))

/-- The block law of a height-valid block is the path weight of its path. -/
theorem blockLaw_singleton_of_heightValid (ℓ : ℤ) (p : Site B) (hp : p.2 < ℓ) (c : Block B)
    (hc : HeightValid B ℓ p c) :
    blockLaw B ℓ p {c} = IdlaCyl.pathWeight B (c : List (Site B)).length (blockPath B p c) := by
  by_cases hv : ValidBlock B ℓ p c
  · exact blockLaw_singleton B ℓ p c hv
  · have hstep : ∃ n < (c : List (Site B)).length,
        cylKernel B (blockPath B p c n) (blockPath B p c (n + 1)) ≤ 0 := by
      by_contra hcon
      simp only [not_exists, not_and, not_le] at hcon
      exact hv ⟨hc.1, hc.2.1, hc.2.2, fun n hn => hcon n hn⟩
    obtain ⟨n, hn, hle⟩ := hstep
    have hz : cylKernel B (blockPath B p c n) (blockPath B p c (n + 1)) = 0 :=
      le_antisymm hle (cylKernel_nonneg _ _)
    have hprod : IdlaCyl.pathWeight B (c : List (Site B)).length (blockPath B p c) = 0 := by
      unfold IdlaCyl.pathWeight
      exact Finset.prod_eq_zero (Finset.mem_range.mpr hn) (by rw [hz, ENNReal.ofReal_zero])
    rw [blockLaw_singleton_eq_zero B ℓ p hp c hv, hprod]

/-- A positive kernel entry changes the height by at most one. -/
theorem step_height_of_cylKernel_pos {B : Base} {p q : Site B} (h : 0 < cylKernel B p q) :
    q.2 - p.2 = -1 ∨ q.2 - p.2 = 0 ∨ q.2 - p.2 = 1 := by
  by_cases hA : p.1 = q.1 ∧ (p.2 - q.2).natAbs = 1
  · rcases Int.natAbs_eq (p.2 - q.2) with h' | h' <;> rw [hA.2] at h' <;> omega
  · by_cases hne : p.2 = q.2
    · omega
    · unfold cylKernel at h
      simp [hA, hne] at h

/-- The vertical increments of a chain of positive kernel steps lie in `{-1, 0, 1}`. -/
theorem skel_mem_of_isChain (B : Base) : ∀ (c : List (Site B)) (p : Site B),
    List.IsChain (fun a b => 0 < cylKernel B a b) (p :: c) →
      ∀ d ∈ skel p c, d = -1 ∨ d = 0 ∨ d = 1 := by
  intro c
  induction c with
  | nil => intro p _ d hd; simp [skel] at hd
  | cons q c ih =>
    intro p hch d hd
    rw [List.isChain_cons_cons] at hch
    simp only [skel, List.mem_cons] at hd
    rcases hd with rfl | hd
    · exact step_height_of_cylKernel_pos hch.1
    · exact ih q hch.2 d hd

/-- The entries of `p :: c` and `p :: d` have the same heights when `c` and `d` do. -/
theorem snd_getD_eq (p : Site B) (c d : List (Site B)) (h : c.map Prod.snd = d.map Prod.snd)
    (i : ℕ) : ((p :: c).getD i p).2 = ((p :: d).getD i p).2 := by
  have hm : (p :: c).map Prod.snd = (p :: d).map Prod.snd := by simp [h]
  calc ((p :: c).getD i p).2 = ((p :: c).map Prod.snd).getD i p.2 := by rw [List.getD_map]
    _ = ((p :: d).map Prod.snd).getD i p.2 := by rw [hm]
    _ = ((p :: d).getD i p).2 := by rw [List.getD_map]

/-- The path of a block is the entries of `p :: c` below its length. -/
theorem blockPath_eq_getD (p : Site B) (c : Block B) (i : ℕ)
    (hi : i ≤ (c : List (Site B)).length) :
    blockPath B p c i = (p :: (c : List (Site B))).getD i p :=
  getD_congr_default _ (by simp only [List.length_cons]; omega) _ _

/-- The length of a rebuilt block is the length of the block. -/
theorem length_reassemble (p : Site B) (c : Block B) {s : ℕ} (w : Fin s → B.V) :
    (reassemble B p c w : List (Site B)).length = (c : List (Site B)).length := by
  unfold reassemble
  rw [length_assemble, length_skel]

/-- The horizontal list of a rebuilt block is the window. -/
theorem hors_reassemble (p : Site B) (c : Block B) (w : Fin (hcount B p c) → B.V) :
    hors p (reassemble B p c w : List (Site B)) = List.ofFn w := by
  have hws : (List.ofFn w).length = (skel p (c : List (Site B))).count 0 := by
    rw [List.length_ofFn, count_skel_zero]
    rfl
  exact hors_assemble p _ _ hws

/-- A rebuilt block of a valid block is height-valid. -/
theorem heightValid_reassemble (ℓ : ℤ) (p : Site B) (c : Block B) (hc : ValidBlock B ℓ p c)
    {s : ℕ} (w : Fin s → B.V) (hs : s = hcount B p c) :
    HeightValid B ℓ p (reassemble B p c w) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hl := length_reassemble B p c w
    rw [h, List.length_nil] at hl
    exact hc.1 (List.length_eq_zero_iff.mp hl.symm)
  · intro n hn
    rw [length_reassemble] at hn
    have h1 := hc.2.1 n hn
    rw [blockPath_eq_getD B p c n hn.le] at h1
    rw [blockPath_eq_getD B p _ n (by rw [length_reassemble]; exact hn.le)]
    have hmap : (reassemble B p c w : List (Site B)).map Prod.snd
        = (c : List (Site B)).map Prod.snd := map_snd_assemble_skel B p _ _
    rw [snd_getD_eq B p _ _ hmap n]
    exact h1
  · subst hs
    rw [blockEnd_reassemble B p c w rfl]
    exact hc.2.2.1

/-- The block law of a rebuilt block: the skeleton weight times the path weight of the window. -/
theorem blockLaw_reassemble (ℓ : ℤ) (p : Site B) (hp : p.2 < ℓ) (c : Block B)
    (hc : ValidBlock B ℓ p c) (w : Fin (hcount B p c) → B.V) :
    blockLaw B ℓ p {reassemble B p c w} =
      ENNReal.ofReal (skelWeight (skel p (c : List (Site B))) * pathWeight B p.1 (hcount B p c) w) := by
  have hτ := skel_mem_of_isChain B (c : List (Site B)) p (isChain_of_validBlock B ℓ p c hc)
  have hws : (List.ofFn w).length = (skel p (c : List (Site B))).count 0 := by
    rw [List.length_ofFn, count_skel_zero]
    rfl
  have hf : ∀ i ≤ (assemble p (skel p (c : List (Site B))) (List.ofFn w)).length,
      blockPath B p (reassemble B p c w) i
        = (p :: assemble p (skel p (c : List (Site B))) (List.ofFn w)).getD i p :=
    fun i hi => blockPath_eq_getD B p (reassemble B p c w) i hi
  have h := pathWeight_assemble p (skel p (c : List (Site B))) (List.ofFn w)
    (blockPath B p (reassemble B p c w)) hτ hws hf
  rw [listPathWeight_ofFn] at h
  rw [blockLaw_singleton_of_heightValid B ℓ p hp _
    (heightValid_reassemble B ℓ p c hc w rfl)]
  exact h

/-- The resampling kernel charges a block with the total path weight of the windows that
rebuild it. -/
theorem resample_apply_singleton (p : Site B) (c cs : Block B) :
    ((pathLaw B (hcount B p c) p.1).toMeasure.map (reassemble B p c)) {cs}
      = ∑ w : Fin (hcount B p c) → B.V,
          if reassemble B p c w = cs then ENNReal.ofReal (pathWeight B p.1 (hcount B p c) w)
          else 0 := by
  have hmeas : Measurable (reassemble B p c : (Fin (hcount B p c) → B.V) → Block B) :=
    measurable_to_countable' fun x => (Set.to_countable _).measurableSet
  rw [Measure.map_apply hmeas (measurableSet_singleton cs), FiniteLaw.toMeasure_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases h : reassemble B p c w = cs
  · rw [if_pos h]
    exact Set.indicator_of_mem (show w ∈ reassemble B p c ⁻¹' {cs} from h) _
  · rw [if_neg h]
    exact Set.indicator_of_notMem (show w ∉ reassemble B p c ⁻¹' {cs} from h) _

/-- Rebuilding a block from its own skeleton is possible only on its skeleton class. -/
theorem skel_eq_of_reassemble (p : Site B) (c cs : Block B) {s : ℕ} (w : Fin s → B.V)
    (h : reassemble B p c w = cs) : skel p (cs : List (Site B)) = skel p (c : List (Site B)) := by
  rw [← h]
  exact skel_reassemble B p c w

/-- Blocks with a different skeleton are never rebuilt from `c`. -/
theorem resample_apply_singleton_ne (p : Site B) (c cs : Block B)
    (hsk : skel p (c : List (Site B)) ≠ skel p (cs : List (Site B))) :
    ((pathLaw B (hcount B p c) p.1).toMeasure.map (reassemble B p c)) {cs} = 0 := by
  rw [resample_apply_singleton]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [if_neg]
  intro h
  exact hsk (skel_eq_of_reassemble B p c cs w h).symm

/-- The windows that rebuild a valid `cs` on the skeleton of `cs` are those spelling its
horizontal list. -/
theorem resample_apply_singleton_eq (ℓ : ℤ) (p : Site B) (c cs : Block B)
    (hcs : ValidBlock B ℓ p cs)
    (hsk : skel p (c : List (Site B)) = skel p (cs : List (Site B))) :
    ((pathLaw B (hcount B p c) p.1).toMeasure.map (reassemble B p c)) {cs}
      = ENNReal.ofReal (listPathWeight B p.1 (hors p (cs : List (Site B)))) := by
  rw [resample_apply_singleton]
  have hlen : (hors p (cs : List (Site B))).length = hcount B p c := by
    unfold hcount
    rw [← count_skel_zero, ← count_skel_zero, hsk]
  have hcond : ∀ w : Fin (hcount B p c) → B.V,
      (reassemble B p c w = cs ↔ List.ofFn w = hors p (cs : List (Site B))) := by
    intro w
    constructor
    · intro h
      have h2 : assemble p (skel p (c : List (Site B))) (List.ofFn w) = (cs : List (Site B)) := h
      exact (hors_reassemble B p c w).symm.trans (congrArg (hors p) h2)
    · intro h
      unfold reassemble
      rw [h, hsk]
      exact assemble_skel_hors p (cs : List (Site B)) (isChain_of_validBlock B ℓ p cs hcs)
  have hsum : ∑ w : Fin (hcount B p c) → B.V,
        (if reassemble B p c w = cs then ENNReal.ofReal (pathWeight B p.1 (hcount B p c) w) else 0)
      = ∑ w : Fin (hcount B p c) → B.V,
        (if List.ofFn w = hors p (cs : List (Site B)) then
          ENNReal.ofReal (pathWeight B p.1 (hcount B p c) w) else 0) :=
    Finset.sum_congr rfl fun w _ => by simp only [hcond w]
  rw [hsum]
  exact sum_window_eq B p.1 _ hlen

/-- A list of length `s` is the image of a window of length `s`. -/
theorem exists_ofFn_eq {V : Type*} (l : List V) (s : ℕ) (h : l.length = s) :
    ∃ W : Fin s → V, List.ofFn W = l := by
  subst h
  exact ⟨l.get, List.ofFn_get l⟩

/-- The blocks with a given skeleton carry the skeleton weight in total. -/
theorem blockLaw_class_mass (ℓ : ℤ) (p : Site B) (hp : p.2 < ℓ) (cs : Block B)
    (hcs : ValidBlock B ℓ p cs) :
    ∑' c : Block B, (if skel p (c : List (Site B)) = skel p (cs : List (Site B))
      then blockLaw B ℓ p {c} else 0)
      = ENNReal.ofReal (skelWeight (skel p (cs : List (Site B)))) := by
  have hinj : Function.Injective (fun w : Fin (hcount B p cs) → B.V => reassemble B p cs w) := by
    intro w w' h
    apply List.ofFn_injective
    rw [← hors_reassemble B p cs w, ← hors_reassemble B p cs w']
    exact congrArg (fun c : Block B => hors p (c : List (Site B))) h
  have hsupp : Function.support (fun c : Block B => if skel p (c : List (Site B))
      = skel p (cs : List (Site B)) then blockLaw B ℓ p {c} else 0)
      ⊆ Set.range (fun w : Fin (hcount B p cs) → B.V => reassemble B p cs w) := by
    intro c hc
    have hne : (if skel p (c : List (Site B)) = skel p (cs : List (Site B))
        then blockLaw B ℓ p {c} else 0) ≠ 0 := hc
    by_cases hsk : skel p (c : List (Site B)) = skel p (cs : List (Site B))
    · rw [if_pos hsk] at hne
      have hval : ValidBlock B ℓ p c := by
        by_contra hnv
        exact hne (blockLaw_singleton_eq_zero B ℓ p hp c hnv)
      have hlen : (hors p (c : List (Site B))).length = hcount B p cs := by
        unfold hcount
        rw [← count_skel_zero, ← count_skel_zero, hsk]
      obtain ⟨W, hW⟩ := exists_ofFn_eq (hors p (c : List (Site B))) (hcount B p cs) hlen
      refine ⟨W, ?_⟩
      show reassemble B p cs W = c
      unfold reassemble
      rw [hW, ← hsk]
      exact assemble_skel_hors p (c : List (Site B)) (isChain_of_validBlock B ℓ p c hval)
    · rw [if_neg hsk] at hne
      exact (hne rfl).elim
  have hterm : ∀ w : Fin (hcount B p cs) → B.V,
      (if skel p ((reassemble B p cs w : Block B) : List (Site B)) = skel p (cs : List (Site B))
        then blockLaw B ℓ p {reassemble B p cs w} else 0)
        = ENNReal.ofReal (skelWeight (skel p (cs : List (Site B))))
          * ENNReal.ofReal (pathWeight B p.1 (hcount B p cs) w) := by
    intro w
    have hsk' : skel p ((reassemble B p cs w : Block B) : List (Site B))
        = skel p (cs : List (Site B)) := skel_reassemble B p cs w
    rw [if_pos hsk', blockLaw_reassemble B ℓ p hp cs hcs w,
      ENNReal.ofReal_mul (skelWeight_nonneg _)]
  refine (Function.Injective.tsum_eq hinj hsupp).symm.trans ?_
  refine (tsum_congr hterm).trans ?_
  rw [ENNReal.tsum_mul_left, tsum_fintype,
    ← ENNReal.ofReal_sum_of_nonneg (fun w _ => pathWeight_nonneg B p.1 _ w),
    sum_pathWeight B p.1 (hcount B p cs), ENNReal.ofReal_one, mul_one]

/-- Window resampling preserves the block law. -/
theorem blockLaw_resample (ℓ : ℤ) (p : Site B) (hp : p.2 < ℓ) :
    (blockLaw B ℓ p).bind
        (fun c => ((pathLaw B (hcount B p c) p.1).toMeasure).map (reassemble B p c))
      = blockLaw B ℓ p := by
  refine Measure.ext_iff_singleton.2 fun cs => ?_
  rw [Measure.bind_apply (measurableSet_singleton cs) measurable_from_top.aemeasurable,
    lintegral_countable']
  by_cases hcs : ValidBlock B ℓ p cs
  · have hRHS : blockLaw B ℓ p {cs} = ENNReal.ofReal (skelWeight (skel p (cs : List (Site B)))
        * listPathWeight B p.1 (hors p (cs : List (Site B)))) := by
      have h := blockLaw_reassemble B ℓ p hp cs hcs
        (fun i : Fin (hcount B p cs) => (hors p (cs : List (Site B))).get ⟨i, i.2⟩)
      rw [reassemble_self B p cs (isChain_of_validBlock B ℓ p cs hcs)] at h
      have hW : List.ofFn (fun i : Fin (hcount B p cs) => (hors p (cs : List (Site B))).get ⟨i, i.2⟩)
          = hors p (cs : List (Site B)) := List.ofFn_get _
      rw [h, ← listPathWeight_ofFn, hW]
    have hpt : ∀ c : Block B,
        ((pathLaw B (hcount B p c) p.1).toMeasure.map (reassemble B p c)) {cs}
          * blockLaw B ℓ p {c}
        = ENNReal.ofReal (listPathWeight B p.1 (hors p (cs : List (Site B))))
          * (if skel p (c : List (Site B)) = skel p (cs : List (Site B))
              then blockLaw B ℓ p {c} else 0) := by
      intro c
      by_cases hsk : skel p (c : List (Site B)) = skel p (cs : List (Site B))
      · rw [if_pos hsk, resample_apply_singleton_eq B ℓ p c cs hcs hsk]
      · rw [if_neg hsk, resample_apply_singleton_ne B p c cs hsk, zero_mul, mul_zero]
    refine (tsum_congr hpt).trans ?_
    rw [ENNReal.tsum_mul_left, blockLaw_class_mass B ℓ p hp cs hcs, hRHS,
      ENNReal.ofReal_mul (skelWeight_nonneg _), mul_comm]
  · have hz : ∀ c : Block B, ValidBlock B ℓ p c →
        ((pathLaw B (hcount B p c) p.1).toMeasure.map (reassemble B p c)) {cs} = 0 := by
      intro c hc
      rw [resample_apply_singleton]
      refine Finset.sum_eq_zero fun w _ => ?_
      by_cases h : reassemble B p c w = cs
      · rw [if_pos h]
        have hK := blockLaw_reassemble B ℓ p hp c hc w
        rw [h, blockLaw_singleton_eq_zero B ℓ p hp cs hcs] at hK
        have hle : skelWeight (skel p (c : List (Site B))) * pathWeight B p.1 (hcount B p c) w ≤ 0 :=
          ENNReal.ofReal_eq_zero.mp hK.symm
        have hnp : pathWeight B p.1 (hcount B p c) w ≤ 0 := by
          by_contra hpos
          have := mul_pos (skelWeight_pos (skel p (c : List (Site B)))) (not_le.mp hpos)
          linarith
        exact ENNReal.ofReal_of_nonpos hnp
      · rw [if_neg h]
    have hK : ∀ c : Block B,
        ((pathLaw B (hcount B p c) p.1).toMeasure.map (reassemble B p c)) {cs}
          * blockLaw B ℓ p {c} = 0 := by
      intro c
      by_cases hc : ValidBlock B ℓ p c
      · rw [hz c hc, zero_mul]
      · rw [blockLaw_singleton_eq_zero B ℓ p hp c hc, mul_zero]
    refine (tsum_congr hK).trans ?_
    rw [tsum_zero, blockLaw_singleton_eq_zero B ℓ p hp cs hcs]

end IdlaCyl.Silvestri

end
