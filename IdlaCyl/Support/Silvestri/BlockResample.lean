module

public import IdlaCyl.Support.Silvestri.Blocks
public import IdlaCyl.Support.Silvestri.Skeleton
public import IdlaCyl.Support.Silvestri.WindowCouple
public import Mathlib

@[expose] public section

/-!
# Finite laws as measures, and rebuilt blocks

The file defines the measure of a finite law, and proves that the image of a finite law on
a product under a coordinate projection is the measure of the projected law, when the
projected weights are the marginal sums.

It defines the number of horizontal steps of a block, and the rebuilding of a block from a
window of base vertices on its vertical skeleton. It proves that the horizontal steps are the
zero increments of the skeleton, that a rebuilt block has the heights of the original, that
the end of a rebuilt block has the endpoint of the window as its base vertex and the height
of the original end, and that a block whose steps all have positive kernel entry is
recovered from its skeleton and its horizontal list. It also proves that the window sum
picks out the single window that spells a given list of base vertices.
-/

namespace IdlaCyl.FiniteLaw

open MeasureTheory

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The measure carried by a finite law: the atom `a` gets mass `μ.weight a`. -/
def toMeasure [MeasurableSpace α] (μ : FiniteLaw α) : Measure α :=
  Measure.sum fun a => ENNReal.ofReal (μ.weight a) • Measure.dirac a

section Singletons

variable [MeasurableSpace α] [MeasurableSingletonClass α]

/-- The mass of a set is the sum of the atom masses of its points. -/
theorem toMeasure_apply (μ : FiniteLaw α) (s : Set α) :
    μ.toMeasure s = ∑ a, s.indicator (fun a => ENNReal.ofReal (μ.weight a)) a := by
  classical
  unfold toMeasure
  rw [Measure.sum_apply _ (Set.toFinite s).measurableSet, tsum_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' a (Set.toFinite s).measurableSet, smul_eq_mul,
    Set.indicator_apply, Set.indicator_apply]
  by_cases h : a ∈ s <;> simp [h]

/-- The measure of a finite law is a probability measure. -/
instance isProbabilityMeasure_toMeasure (μ : FiniteLaw α) : IsProbabilityMeasure μ.toMeasure :=
  ⟨by
    rw [toMeasure_apply, Set.indicator_univ,
      ← ENNReal.ofReal_sum_of_nonneg (fun a _ => μ.nonneg a), μ.total, ENNReal.ofReal_one]⟩

/-- The mass of a singleton is the weight of its atom. -/
theorem toMeasure_singleton (μ : FiniteLaw α) (a : α) :
    μ.toMeasure {a} = ENNReal.ofReal (μ.weight a) := by
  classical
  rw [toMeasure_apply]
  simp [Set.indicator_apply]

end Singletons

section Projections

variable [MeasurableSpace α] [MeasurableSingletonClass α]
variable [MeasurableSpace β] [MeasurableSingletonClass β]

/-- Projecting a finite law on a product to its first factor gives the law with the
marginal weights. -/
theorem toMeasure_map_fst (μ : FiniteLaw (α × β)) (ν : FiniteLaw α)
    (h : ∀ a, ∑ b, μ.weight (a, b) = ν.weight a) :
    μ.toMeasure.map Prod.fst = ν.toMeasure := by
  classical
  refine Measure.ext_iff_singleton.2 fun a => ?_
  rw [Measure.map_apply measurable_fst (measurableSet_singleton a), toMeasure_singleton]
  have hpre : μ.toMeasure (Prod.fst ⁻¹' {a}) = ∑ b, ENNReal.ofReal (μ.weight (a, b)) := by
    rw [toMeasure_apply, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [Set.indicator_apply]
  rw [hpre, ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (f := fun b => μ.weight (a, b))
    (fun b _ => μ.nonneg _), h a]

/-- Projecting a finite law on a product to its second factor gives the law with the
marginal weights. -/
theorem toMeasure_map_snd (μ : FiniteLaw (α × β)) (ν : FiniteLaw β)
    (h : ∀ b, ∑ a, μ.weight (a, b) = ν.weight b) :
    μ.toMeasure.map Prod.snd = ν.toMeasure := by
  classical
  refine Measure.ext_iff_singleton.2 fun b => ?_
  rw [Measure.map_apply measurable_snd (measurableSet_singleton b), toMeasure_singleton]
  have hpre : μ.toMeasure (Prod.snd ⁻¹' {b}) = ∑ a, ENNReal.ofReal (μ.weight (a, b)) := by
    rw [toMeasure_apply, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Set.indicator_apply]
  rw [hpre, ← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (f := fun a => μ.weight (a, b))
    (fun a _ => μ.nonneg _), h b]

end Projections

end

end IdlaCyl.FiniteLaw

namespace IdlaCyl.Silvestri

open MeasureTheory

noncomputable section

variable (B : Base)

/-- The number of horizontal steps of the block `c` from `p`: the base vertices of the
entries of `c` that keep the height. -/
def hcount (p : Site B) (c : Block B) : ℕ :=
  (hors p (c : List (Site B))).length

/-- Rebuild a block from a window `w` of base vertices, on the vertical skeleton of `c`
read from `p`. -/
def reassemble (p : Site B) (c : Block B) {s : ℕ} (w : Fin s → B.V) : Block B :=
  (assemble p (skel p (c : List (Site B))) (List.ofFn w) : List (Site B))

/-- The skeleton of a list counts its zero increments as the horizontal steps. -/
theorem count_skel_zero (p : Site B) (c : List (Site B)) :
    (skel p c).count 0 = (hors p c).length := by
  induction c generalizing p with
  | nil => rfl
  | cons q c ih =>
    by_cases h : q.2 - p.2 = 0
    · simp [skel, hors, h, ih q]
    · simp [skel, hors, h, ih q]

/-- Rebuilding from the skeleton keeps the heights. -/
theorem map_snd_assemble_skel (p : Site B) (c : List (Site B)) (ws : List B.V) :
    (assemble p (skel p c) ws).map Prod.snd = c.map Prod.snd := by
  induction c generalizing p ws with
  | nil => rfl
  | cons q c ih =>
    by_cases h : q.2 - p.2 = 0
    · have hq : q.2 = p.2 := by omega
      rcases ws with _ | ⟨w, ws⟩
      · have e := map_snd_assemble (skel q c) p q [] [] (by simp [hq])
        simp only [skel, assemble, h, if_true, List.map_cons]
        rw [e.trans (ih q [])]
        simp [hq]
      · have e := map_snd_assemble (skel q c) (w, p.2) q ws ws (by simp [hq])
        simp only [skel, assemble, h, if_true, List.map_cons]
        rw [e.trans (ih q ws)]
        simp [hq]
    · have e := map_snd_assemble (skel q c) (p.1, p.2 + (q.2 - p.2)) q ws ws (by simp)
      simp only [skel, assemble, h, if_false, List.map_cons]
      rw [e.trans (ih q ws)]
      congr 1
      show p.2 + (q.2 - p.2) = q.2
      omega

/-- The last entry of a list read from its head, with a default equal to the head. -/
theorem getLastD_eq_getLast' (x : Site B) (L : List (Site B)) :
    (x :: L).getLastD x = (x :: L).getLast (List.cons_ne_nil _ _) := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast (List.cons_ne_nil _ _)]
  rfl

/-- The end of a rebuilt block: its base vertex is the endpoint of the window, and its
height is the height of the end of the original block. -/
theorem blockEnd_reassemble (p : Site B) (c : Block B) {s : ℕ} (w : Fin s → B.V)
    (hs : s = hcount B p c) :
    blockEnd B p (reassemble B p c w) = (pathEnd B p.1 s w, (blockEnd B p c).2) := by
  subst hs
  have hws : (List.ofFn w).length = (skel p (c : List (Site B))).count 0 := by
    rw [List.length_ofFn, count_skel_zero]
    rfl
  have h1 : blockEnd B p (reassemble B p c w)
      = (p :: assemble p (skel p (c : List (Site B))) (List.ofFn w)).getLast
          (List.cons_ne_nil _ _) :=
    getLastD_eq_getLast' B p _
  have h2 : blockEnd B p c = (p :: (c : List (Site B))).getLast (List.cons_ne_nil _ _) :=
    getLastD_eq_getLast' B p _
  rw [h1, h2]
  refine Prod.ext ?_ ?_
  · rw [fst_getLast_assemble _ p _ hws, getLast_cons_ofFn]
  · have hmap := map_snd_assemble_skel B p (c : List (Site B)) (List.ofFn w)
    rw [← List.getLast_map (f := Prod.snd), ← List.getLast_map (f := Prod.snd)]
    congr 1
    all_goals simp [hmap]

/-- A valid block is a chain of positive kernel steps from its start. -/
theorem isChain_of_validBlock (ℓ : ℤ) (p : Site B) (c : Block B) (hc : ValidBlock B ℓ p c) :
    List.IsChain (fun a b => 0 < cylKernel B a b) (p :: (c : List (Site B))) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hi' : i < (c : List (Site B)).length := by
    simp only [List.length_cons] at hi
    omega
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have h0 : (p :: (c : List (Site B)))[0] = blockPath B p c 0 := by
      rw [blockPath_zero]
      rfl
    have h1 : (p :: (c : List (Site B)))[0 + 1] = blockPath B p c (0 + 1) := by
      rw [blockPath_succ B p c 0 hi']
      rfl
    rw [h0, h1]
    exact hc.2.2.2 0 hi'
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    have hk : k < (c : List (Site B)).length := by omega
    have h0 : (p :: (c : List (Site B)))[k + 1] = blockPath B p c (k + 1) := by
      rw [blockPath_succ B p c k hk]
      rfl
    have h1 : (p :: (c : List (Site B)))[k + 1 + 1] = blockPath B p c (k + 1 + 1) := by
      rw [blockPath_succ B p c (k + 1) hi']
      rfl
    rw [h0, h1]
    exact hc.2.2.2 (k + 1) hi'

/-- A block is recovered from its skeleton and its horizontal list. -/
theorem reassemble_self (p : Site B) (c : Block B)
    (hc : List.IsChain (fun a b => 0 < cylKernel B a b) (p :: (c : List (Site B)))) :
    reassemble B p c (fun i : Fin (hcount B p c) => (hors p (c : List (Site B))).get ⟨i, i.2⟩)
      = c := by
  have hw : List.ofFn (fun i : Fin (hcount B p c) => (hors p (c : List (Site B))).get ⟨i, i.2⟩)
      = hors p (c : List (Site B)) := List.ofFn_get _
  unfold reassemble
  rw [hw]
  exact assemble_skel_hors p (c : List (Site B)) hc


/-- The skeleton of a rebuilt block is the skeleton of the original block. -/
theorem skel_reassemble (p : Site B) (c : Block B) {s : ℕ} (w : Fin s → B.V) :
    skel p (reassemble B p c w : List (Site B)) = skel p (c : List (Site B)) := by
  unfold reassemble
  exact skel_assemble p _ _

/-- The window sum of the path weights over the windows that spell a list `l` of length `s`
is the list weight of `l`. -/
theorem sum_window_eq (x : B.V) (l : List B.V) {s : ℕ} (hl : l.length = s) :
    ∑ w : Fin s → B.V, (if List.ofFn w = l then ENNReal.ofReal (pathWeight B x s w) else 0)
      = ENNReal.ofReal (listPathWeight B x l) := by
  classical
  subst hl
  rw [Finset.sum_eq_single (l.get)]
  · rw [if_pos (List.ofFn_get l), ← listPathWeight_ofFn, List.ofFn_get]
  · intro w _ hw
    rw [if_neg]
    intro h
    exact hw (List.ofFn_injective (h.trans (List.ofFn_get l).symm))
  · intro h
    exact absurd (Finset.mem_univ _) h

end

end IdlaCyl.Silvestri
