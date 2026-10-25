module

public import Mathlib

@[expose] public section

set_option autoImplicit false

/-!
# First exits, with an arbitrary permanent seed

Only a finite set of sites outside the permanent seed is stored. An
`EscapingPath` visits the complement of every finite extension of the seed.
This is a *pathwise input condition*, not a probabilistic recurrence theorem.
No abelian / particle-order invariance is assumed.
-/

namespace IdlaCyl

variable {α : Type*} [DecidableEq α]

/-- An infinite trajectory which exits every finite extension of `seed`. -/
structure EscapingPath (seed : Set α) where
  position : ℕ → α
  escapes : ∀ A : Finset α, ∃ n, position n ∉ seed ∧ position n ∉ A

namespace EscapingPath

variable {seed : Set α}

noncomputable def exitTime (w : EscapingPath seed) (A : Finset α) : ℕ := by
  classical
  exact Nat.find (w.escapes A)

noncomputable def exitSite (w : EscapingPath seed) (A : Finset α) : α :=
  w.position (w.exitTime A)

theorem exit_spec (w : EscapingPath seed) (A : Finset α) :
    w.exitSite A ∉ seed ∧ w.exitSite A ∉ A := by
  classical
  exact Nat.find_spec (w.escapes A)

theorem exit_not_seed (w : EscapingPath seed) (A : Finset α) :
    w.exitSite A ∉ seed := (w.exit_spec A).1

theorem exit_fresh (w : EscapingPath seed) (A : Finset α) :
    w.exitSite A ∉ A := (w.exit_spec A).2

theorem exitTime_le (w : EscapingPath seed) (A : Finset α) {n : ℕ}
    (hn : w.position n ∉ seed ∧ w.position n ∉ A) : w.exitTime A ≤ n := by
  classical
  exact Nat.find_min' (w.escapes A) hn

theorem occupied_before_exit (w : EscapingPath seed) (A : Finset α)
    {n : ℕ} (hn : n < w.exitTime A) : w.position n ∈ seed ∨ w.position n ∈ A := by
  classical
  have h := Nat.find_min (w.escapes A) hn
  by_cases hs : w.position n ∈ seed
  · exact Or.inl hs
  · right
    by_contra ha
    exact h ⟨hs, ha⟩

/-- Identify an exit from a finite certificate for the visited prefix. -/
theorem exitTime_eq_of_first (w : EscapingPath seed) (A : Finset α) (n : ℕ)
    (hn : w.position n ∉ seed ∧ w.position n ∉ A)
    (hbefore : ∀ m < n, w.position m ∈ seed ∨ w.position m ∈ A) :
    w.exitTime A = n := by
  apply Nat.le_antisymm (w.exitTime_le A hn)
  by_contra h
  have ht : w.exitTime A < n := lt_of_not_ge h
  rcases hbefore (w.exitTime A) ht with hs | ha
  · exact w.exit_not_seed A hs
  · exact w.exit_fresh A ha

theorem exitSite_eq_of_first (w : EscapingPath seed) (A : Finset α) (n : ℕ)
    (hn : w.position n ∉ seed ∧ w.position n ∉ A)
    (hbefore : ∀ m < n, w.position m ∈ seed ∨ w.position m ∈ A) :
    w.exitSite A = w.position n := by
  unfold exitSite
  rw [w.exitTime_eq_of_first A n hn hbefore]

theorem exitTime_mono (w : EscapingPath seed) {A B : Finset α}
    (hAB : A ⊆ B) : w.exitTime A ≤ w.exitTime B := by
  apply w.exitTime_le A
  refine ⟨w.exit_not_seed B, ?_⟩
  exact fun ha => w.exit_fresh B (hAB ha)

/-- If the first exit from `A` also lies outside `B`, it is the same exit. -/
theorem exitSite_eq_of_not_mem (w : EscapingPath seed) {A B : Finset α}
    (hAB : A ⊆ B) (h : w.exitSite A ∉ B) :
    w.exitSite A = w.exitSite B := by
  have hBA : w.exitTime B ≤ w.exitTime A :=
    w.exitTime_le B ⟨w.exit_not_seed A, h⟩
  have ht : w.exitTime A = w.exitTime B :=
    Nat.le_antisymm (w.exitTime_mono hAB) hBA
  exact congrArg w.position ht

/-- Add the first site of this path outside the occupied set. -/
noncomputable def settle (A : Finset α) (w : EscapingPath seed) : Finset α :=
  insert (w.exitSite A) A

@[simp] theorem card_settle (A : Finset α) (w : EscapingPath seed) :
    (settle A w).card = A.card + 1 := by
  exact Finset.card_insert_of_notMem (w.exit_fresh A)

theorem subset_settle (A : Finset α) (w : EscapingPath seed) :
    A ⊆ settle A w := by
  intro x hx
  exact Finset.mem_insert_of_mem hx

/-- Same-path monotonicity. This does not permute particle trajectories. -/
theorem settle_mono (w : EscapingPath seed) {A B : Finset α}
    (hAB : A ⊆ B) : settle A w ⊆ settle B w := by
  intro x hx
  rcases Finset.mem_insert.mp hx with hx | hx
  · subst x
    by_cases h : w.exitSite A ∈ B
    · exact Finset.mem_insert_of_mem h
    · rw [w.exitSite_eq_of_not_mem hAB h]
      exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (hAB hx)

theorem settle_outside_seed (A : Finset α) (w : EscapingPath seed)
    (hA : ∀ x ∈ A, x ∉ seed) : ∀ x ∈ settle A w, x ∉ seed := by
  intro x hx
  rcases Finset.mem_insert.mp hx with hx | hx
  · subst x
    exact w.exit_not_seed A
  · exact hA x hx

/-- Processing a list, in its specified order, without restarting old paths. -/
noncomputable def grow (A : Finset α) : List (EscapingPath seed) → Finset α
  | [] => A
  | w :: ws => grow (settle A w) ws

@[simp] theorem grow_nil (A : Finset α) : grow A ([] : List (EscapingPath seed)) = A := rfl

@[simp] theorem grow_cons (A : Finset α) (w : EscapingPath seed)
    (ws : List (EscapingPath seed)) :
    grow A (w :: ws) = grow (settle A w) ws := rfl

@[simp] theorem card_grow (A : Finset α) (ws : List (EscapingPath seed)) :
    (grow A ws).card = A.card + ws.length := by
  induction ws generalizing A with
  | nil => simp
  | cons w ws ih =>
      simp only [grow_cons, ih, card_settle, List.length_cons]
      omega

theorem grow_mono (ws : List (EscapingPath seed)) {A B : Finset α}
    (hAB : A ⊆ B) : grow A ws ⊆ grow B ws := by
  induction ws generalizing A B with
  | nil => exact hAB
  | cons w ws ih => exact ih (settle_mono w hAB)

theorem subset_grow (A : Finset α) (ws : List (EscapingPath seed)) :
    A ⊆ grow A ws := by
  induction ws generalizing A with
  | nil => intro x hx; exact hx
  | cons w ws ih =>
      intro x hx
      exact ih _ (subset_settle A w hx)

theorem grow_append (A : Finset α) (us vs : List (EscapingPath seed)) :
    grow A (us ++ vs) = grow (grow A us) vs := by
  induction us generalizing A with
  | nil => rfl
  | cons w us ih => exact ih (settle A w)

theorem grow_outside_seed (A : Finset α) (ws : List (EscapingPath seed))
    (hA : ∀ x ∈ A, x ∉ seed) : ∀ x ∈ grow A ws, x ∉ seed := by
  induction ws generalizing A with
  | nil => exact hA
  | cons w ws ih => exact ih _ (settle_outside_seed A w hA)

end EscapingPath
end IdlaCyl
