import IdlaCyl.Support.Base

/-!
# The neighbour fibre of the horizontal step

For a base `B`, a vertex `x`, and a neighbour `y` of `x`, the set of `s ∈ [0,1)` at which
the horizontal choice
`(B.graph.neighborFinset x).toList.getD ⌊(B.deg : ℝ) * s⌋₊ x`
returns `y` has Lebesgue measure `1 / deg`. This is the neighbour part of `cylStep`
(`IdlaCyl/Support/Idla.lean`), where `s = 2 * u.2 - 1` on the horizontal branch.

For a vertex `y` that is not a neighbour of `x` the same set is empty.

On `[0,1)` the horizontal choice is always a neighbour of `x`. In particular `getD`
never returns its default value `x` there, so the default is unreachable on the domain
used by the walk.

Source: `paper/idla-cylinder-gff.tex:229-237` (the lazy walk `P_N`) and
`paper/idla-cylinder-gff.tex:244-257` (the cylinder kernel, horizontal step).
-/

namespace IdlaCyl.Silvestri

open MeasureTheory
open scoped ENNReal

variable (B : Base)

/-- The floor of `deg · s` is below `deg` for `s ∈ [0,1)`, so the index used by the
horizontal choice is a valid index into the neighbour list. -/
private theorem horizontalFloor_lt_deg (s : ℝ) (h0 : 0 ≤ s) (h1 : s < 1) :
    ⌊(B.deg : ℝ) * s⌋₊ < B.deg := by
  have hd : (0 : ℝ) < (B.deg : ℝ) := by exact_mod_cast B.deg_pos
  have hprod₀ : 0 ≤ (B.deg : ℝ) * s := mul_nonneg hd.le h0
  have hprod₁ : (B.deg : ℝ) * s < (B.deg : ℝ) := by nlinarith
  rw [Nat.floor_lt hprod₀]
  exact_mod_cast hprod₁

/-- For `s ∈ [0,1)` the horizontal choice is a member of the neighbour set of `x`. -/
private theorem horizontalChoice_mem (x : B.V) {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    (B.graph.neighborFinset x).toList.getD ⌊(B.deg : ℝ) * s⌋₊ x ∈ B.graph.neighborFinset x := by
  have hlen : (B.graph.neighborFinset x).toList.length = B.deg := by
    rw [Finset.length_toList, SimpleGraph.card_neighborFinset_eq_degree, B.degree_eq x]
  have hn : ⌊(B.deg : ℝ) * s⌋₊ < (B.graph.neighborFinset x).toList.length := by
    rw [hlen]
    exact horizontalFloor_lt_deg B s h0 h1
  rw [List.getD_eq_getElem _ _ hn]
  exact Finset.mem_toList.mp (List.getElem_mem _)

/-- For `s ∈ [0,1)` the horizontal choice is adjacent to `x`: it is a neighbour of `x`
in the base graph. -/
theorem horizontalChoice_adj (x : B.V) {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    B.graph.Adj x ((B.graph.neighborFinset x).toList.getD ⌊(B.deg : ℝ) * s⌋₊ x) :=
  (SimpleGraph.mem_neighborFinset (G := B.graph) x _).mp (horizontalChoice_mem B x h0 h1)

/-- For `s ∈ [0,1)` the horizontal choice never equals the default value `x` of `getD`. -/
theorem horizontalChoice_ne_self (x : B.V) {s : ℝ} (h0 : 0 ≤ s) (h1 : s < 1) :
    (B.graph.neighborFinset x).toList.getD ⌊(B.deg : ℝ) * s⌋₊ x ≠ x := by
  intro h
  exact B.graph.irrefl (h ▸ horizontalChoice_adj B x h0 h1)

/-- The fibre of a non-neighbour `y` of `x` under the horizontal choice, restricted to
`s ∈ [0,1)`, is empty. -/
theorem horizontalFibre_eq_empty (x y : B.V) (hy : ¬ B.graph.Adj x y) :
    {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧
      (B.graph.neighborFinset x).toList.getD ⌊(B.deg : ℝ) * s⌋₊ x = y} = ∅ := by
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hs hget
  obtain ⟨h0, h1⟩ := Set.mem_Ico.mp hs
  apply hy
  rw [← hget]
  exact horizontalChoice_adj B x h0 h1

/-- The neighbour fibre: for a neighbour `y` of `x`, the set of `s ∈ [0,1)` at which the
horizontal choice `getD ⌊deg · s⌋₊ x` returns `y` has Lebesgue measure `1 / deg`.

The fibre of a fixed index `i` under `s ↦ ⌊deg · s⌋₊` is the interval
`[i/deg, (i+1)/deg)`, and the neighbour list is duplicate-free of length `deg`, so
each neighbour occupies exactly one index. -/
theorem horizontalFibre_volume (x y : B.V) (hy : B.graph.Adj x y) :
    volume {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧
        (B.graph.neighborFinset x).toList.getD ⌊(B.deg : ℝ) * s⌋₊ x = y}
      = ENNReal.ofReal (1 / (B.deg : ℝ)) := by
  set L := (B.graph.neighborFinset x).toList with hL
  have hlen : L.length = B.deg := by
    rw [hL, Finset.length_toList, SimpleGraph.card_neighborFinset_eq_degree, B.degree_eq x]
  have hnodup : L.Nodup := by
    rw [hL]
    exact Finset.nodup_toList _
  have hd : (0 : ℝ) < (B.deg : ℝ) := by exact_mod_cast B.deg_pos
  have hyL : y ∈ L := by
    rw [hL, Finset.mem_toList]
    exact (SimpleGraph.mem_neighborFinset (G := B.graph) x y).mpr hy
  obtain ⟨i, hi, hiy⟩ := List.mem_iff_getElem.mp hyL
  have hid : i < B.deg := by
    rw [← hlen]
    exact hi
  -- the index `⌊deg · s⌋₊` selects `y` exactly when it equals the index of `y` in `L`
  have hfib : ∀ s : ℝ, 0 ≤ s → s < 1 →
      (L.getD ⌊(B.deg : ℝ) * s⌋₊ x = y ↔ ⌊(B.deg : ℝ) * s⌋₊ = i) := by
    intro s h0 h1
    have hn : ⌊(B.deg : ℝ) * s⌋₊ < L.length := by
      rw [hlen]
      exact horizontalFloor_lt_deg B s h0 h1
    rw [List.getD_eq_getElem _ _ hn]
    constructor
    · intro h
      exact (List.Nodup.getElem_inj_iff hnodup).mp (h.trans hiy.symm)
    · intro h
      subst h
      exact hiy
  -- the floor of `deg · s` equals `i` exactly on `[i/deg, (i+1)/deg)`
  have hkey : ∀ s : ℝ, 0 ≤ s →
      (⌊(B.deg : ℝ) * s⌋₊ = i ↔ (i : ℝ) / B.deg ≤ s ∧ s < ((i : ℝ) + 1) / B.deg) := by
    intro s h0
    rw [Nat.floor_eq_iff (mul_nonneg hd.le h0), div_le_iff₀ hd, lt_div_iff₀ hd,
      mul_comm (B.deg : ℝ) s]
  have hset : {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧ L.getD ⌊(B.deg : ℝ) * s⌋₊ x = y}
      = Set.Ico ((i : ℝ) / B.deg) (((i : ℝ) + 1) / B.deg) := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨⟨h0, h1⟩, hg⟩
      exact (hkey s h0).mp ((hfib s h0 h1).mp hg)
    · rintro ⟨a, b⟩
      have hid' : i + 1 ≤ B.deg := hid
      have hi1 : (i : ℝ) + 1 ≤ (B.deg : ℝ) := by exact_mod_cast hid'
      have h0 : 0 ≤ s := le_trans (by positivity) a
      have h1 : s < 1 := lt_of_lt_of_le b ((div_le_one hd).mpr hi1)
      exact ⟨⟨h0, h1⟩, (hfib s h0 h1).mpr ((hkey s h0).mpr ⟨a, b⟩)⟩
  rw [hset, Real.volume_Ico]
  congr 1
  ring

end IdlaCyl.Silvestri
