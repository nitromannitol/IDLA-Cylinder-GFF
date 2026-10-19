import IdlaCyl.Support.FirstExit

set_option autoImplicit false

/-!
# Contraction under common trajectories

This replaces the particle-reordering argument in Proposition 3.3 of
arXiv:2604.21142v1. The input paths stay in their original order.

The stronger conclusion is that each directed difference is nonexpansive:
  |grow(A,ws) \ grow(B,ws)| ≤ |A \ B|.
-/

namespace IdlaCyl

variable {α : Type*} [DecidableEq α]

/-- Explicit finite symmetric difference, avoiding any infinite seed. -/
def differenceSupport (A B : Finset α) : Finset α := (A \ B) ∪ (B \ A)

@[simp] theorem mem_differenceSupport {x : α} {A B : Finset α} :
    x ∈ differenceSupport A B ↔ (x ∈ A ∧ x ∉ B) ∨ (x ∈ B ∧ x ∉ A) := by
  simp [differenceSupport]

theorem differenceSupport_comm (A B : Finset α) :
    differenceSupport A B = differenceSupport B A := by
  exact Finset.union_comm _ _

theorem directed_diff_subset_union (A B C : Finset α) :
    A \ C ⊆ (A \ B) ∪ (B \ C) := by
  intro x hx
  obtain ⟨ha, hc⟩ := Finset.mem_sdiff.mp hx
  by_cases hb : x ∈ B
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hb, hc⟩)
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ha, hb⟩)

theorem card_directed_diff_triangle (A B C : Finset α) :
    (A \ C).card ≤ (A \ B).card + (B \ C).card := by
  exact (Finset.card_le_card (directed_diff_subset_union A B C)).trans
    (Finset.card_union_le _ _)

namespace EscapingPath

variable {seed : Set α}

/-- Common ordered tails contract both directed differences. -/
theorem card_grow_sdiff_le (A B : Finset α) (ws : List (EscapingPath seed)) :
    (grow A ws \ grow B ws).card ≤ (A \ B).card := by
  let U := A ∪ B
  have hAU : A ⊆ U := by
    intro x hx
    exact Finset.mem_union_left _ hx
  have hBU : B ⊆ U := by
    intro x hx
    exact Finset.mem_union_right _ hx
  have hga : grow A ws ⊆ grow U ws := grow_mono ws hAU
  have hgb : grow B ws ⊆ grow U ws := grow_mono ws hBU
  have hd : grow A ws \ grow B ws ⊆ grow U ws \ grow B ws := by
    intro x hx
    obtain ⟨ha, hb⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hga ha, hb⟩
  have hcancel : (grow U ws \ grow B ws).card = (U \ B).card := by
    rw [Finset.card_sdiff_of_subset hgb, Finset.card_sdiff_of_subset hBU]
    simp only [card_grow]
    omega
  have hUB : U \ B = A \ B := by
    ext x
    simp only [U, Finset.mem_sdiff, Finset.mem_union]
    tauto
  calc
    (grow A ws \ grow B ws).card ≤ (grow U ws \ grow B ws).card :=
      Finset.card_le_card hd
    _ = (U \ B).card := hcancel
    _ = (A \ B).card := congrArg Finset.card hUB

/-- Two alternative next particles can create at most one unmatched site. -/
theorem card_settle_sdiff_le_one (A : Finset α) (p q : EscapingPath seed) :
    (settle A p \ settle A q).card ≤ 1 := by
  have hsub : settle A p \ settle A q ⊆ {p.exitSite A} := by
    intro x hx
    obtain ⟨hp, hq⟩ := Finset.mem_sdiff.mp hx
    rcases Finset.mem_insert.mp hp with hp | hp
    · exact Finset.mem_singleton.mpr hp
    · exact False.elim (hq (Finset.mem_insert_of_mem hp))
  simpa using Finset.card_le_card hsub

theorem one_change_directed (A : Finset α)
    (pre post : List (EscapingPath seed)) (p q : EscapingPath seed) :
    (grow A (pre ++ p :: post) \ grow A (pre ++ q :: post)).card ≤ 1 := by
  simp only [grow_append, grow_cons]
  exact (card_grow_sdiff_le _ _ post).trans (card_settle_sdiff_le_one _ p q)

/-- Proposition 3.3, with a direct proof and no particle permutation. -/
theorem one_change_stability (A : Finset α)
    (pre post : List (EscapingPath seed)) (p q : EscapingPath seed) :
    (differenceSupport (grow A (pre ++ p :: post))
      (grow A (pre ++ q :: post))).card ≤ 2 := by
  have hpq := one_change_directed A pre post p q
  have hqp := one_change_directed A pre post q p
  have hu := Finset.card_union_le
    (grow A (pre ++ p :: post) \ grow A (pre ++ q :: post))
    (grow A (pre ++ q :: post) \ grow A (pre ++ p :: post))
  unfold differenceSupport
  omega

/-- The same result for the finite added clusters above an arbitrary seed. -/
theorem one_change_stability_empty
    (pre post : List (EscapingPath seed)) (p q : EscapingPath seed) :
    (differenceSupport (grow ∅ (pre ++ p :: post))
      (grow ∅ (pre ++ q :: post))).card ≤ 2 :=
  one_change_stability ∅ pre post p q

end EscapingPath
end IdlaCyl
