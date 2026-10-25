module

public import IdlaCyl.Support.FirstExit

@[expose] public section

set_option autoImplicit false

/-!
# Pausing labelled paths, with all particle multiplicities retained

This is a bookkeeping model, not an assertion of abelianity for labelled paths.
`resume` follows the saved, particle-indexed tails, in their original order.
In general its result is NOT the ordinary ordered aggregate; see the explicit
four-particle example in docs/STACK_FOUNDATIONS.md and tests/stack_models.py.
The correct deterministic abelian result is in StackLeastAction.lean.
-/

namespace IdlaCyl

variable {α : Type*} [DecidableEq α] {seed : Set α}

namespace EscapingPath

/-- Every suffix of an escaping path still escapes every finite extension. -/
def suffix (w : EscapingPath seed) (k : ℕ) : EscapingPath seed where
  position n := w.position (k + n)
  escapes A := by
    let P : Finset α := (Finset.range k).image w.position
    obtain ⟨n, hs, hn⟩ := w.escapes (A ∪ P)
    have hnA : w.position n ∉ A := fun h => hn (Finset.mem_union_left P h)
    have hnP : w.position n ∉ P := fun h => hn (Finset.mem_union_right A h)
    have hkn : k ≤ n := by
      by_contra h
      have hnk : n < k := by omega
      exact hnP (Finset.mem_image_of_mem w.position (Finset.mem_range.mpr hnk))
    refine ⟨n - k, ?_, ?_⟩
    · simpa only [Nat.add_sub_of_le hkn] using hs
    · simpa only [Nat.add_sub_of_le hkn] using hnA

@[simp] theorem suffix_position (w : EscapingPath seed) (k n : ℕ) :
    (w.suffix k).position n = w.position (k + n) := rfl

@[simp] theorem suffix_start (w : EscapingPath seed) (k : ℕ) :
    (w.suffix k).position 0 = w.position k := by simp

end EscapingPath

/-- Frozen particles are a LIST, not a set: repeated pause sites remain distinct. -/
structure PausedState (seed : Set α) where
  settled : Finset α
  pending : List (EscapingPath seed)

namespace PausedState

open EscapingPath

noncomputable section

/-- Number of already-settled plus still-paused particles. -/
def mass (s : PausedState seed) : ℕ := s.settled.card + s.pending.length

/-- The multiplicity of the pause site `x`, including repeated locations. -/
def multiplicity (s : PausedState seed) (x : α) : ℕ :=
  (s.pending.map (fun w => w.position 0)).count x

/-- Pause at `boundary`, without adding a boundary site to the settled set. -/
def pauseOne (boundary : Set α) (s : PausedState seed) (w : EscapingPath seed) :
    PausedState seed := by
  classical
  exact if w.exitSite s.settled ∈ boundary then
    ⟨s.settled, s.pending ++ [w.suffix (w.exitTime s.settled)]⟩
  else
    ⟨settle s.settled w, s.pending⟩

def pauseAll (boundary : Set α) (s : PausedState seed) :
    List (EscapingPath seed) → PausedState seed
  | [] => s
  | w :: ws => pauseAll boundary (pauseOne boundary s w) ws

/-- Resume the saved labelled tails. No equality with unpaused growth is claimed. -/
def resume (s : PausedState seed) : Finset α := grow s.settled s.pending

@[simp] theorem mass_pauseOne (boundary : Set α) (s : PausedState seed)
    (w : EscapingPath seed) : (pauseOne boundary s w).mass = s.mass + 1 := by
  classical
  by_cases h : w.exitSite s.settled ∈ boundary
  · simp [pauseOne, h, mass, Nat.add_assoc]
  · simp [pauseOne, h, mass, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem mass_pauseAll (boundary : Set α) (s : PausedState seed)
    (ws : List (EscapingPath seed)) :
    (pauseAll boundary s ws).mass = s.mass + ws.length := by
  induction ws generalizing s with
  | nil => simp [pauseAll]
  | cons w ws ih =>
      simp only [pauseAll, ih, mass_pauseOne, List.length_cons]
      omega

@[simp] theorem card_resume (s : PausedState seed) : s.resume.card = s.mass := by
  exact card_grow s.settled s.pending

theorem settled_subset_pauseOne (boundary : Set α) (s : PausedState seed)
    (w : EscapingPath seed) : s.settled ⊆ (pauseOne boundary s w).settled := by
  classical
  by_cases h : w.exitSite s.settled ∈ boundary
  · simp [pauseOne, h]
  · simpa [pauseOne, h] using subset_settle s.settled w

theorem settled_avoids_boundary_pauseOne (boundary : Set α) (s : PausedState seed)
    (w : EscapingPath seed) (hs : ∀ z ∈ s.settled, z ∉ boundary) :
    ∀ z ∈ (pauseOne boundary s w).settled, z ∉ boundary := by
  classical
  by_cases h : w.exitSite s.settled ∈ boundary
  · simpa [pauseOne, h] using hs
  · simp only [pauseOne, if_neg h]
    intro z hz
    rcases Finset.mem_insert.mp hz with hz | hz
    · subst z
      exact h
    · exact hs z hz

theorem pending_on_boundary_pauseOne (boundary : Set α) (s : PausedState seed)
    (w : EscapingPath seed)
    (hs : ∀ p ∈ s.pending, p.position 0 ∈ boundary) :
    ∀ p ∈ (pauseOne boundary s w).pending, p.position 0 ∈ boundary := by
  classical
  by_cases h : w.exitSite s.settled ∈ boundary
  · simp only [pauseOne, if_pos h]
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hs p hp
    · have heq : p = w.suffix (w.exitTime s.settled) := by simpa using hp
      subst p
      simpa only [suffix_start, exitSite] using h
  · simpa [pauseOne, h] using hs

theorem settled_avoids_boundary_pauseAll (boundary : Set α) (s : PausedState seed)
    (ws : List (EscapingPath seed)) (hs : ∀ z ∈ s.settled, z ∉ boundary) :
    ∀ z ∈ (pauseAll boundary s ws).settled, z ∉ boundary := by
  induction ws generalizing s with
  | nil => exact hs
  | cons w ws ih =>
      exact ih (pauseOne boundary s w) (settled_avoids_boundary_pauseOne boundary s w hs)

theorem pending_on_boundary_pauseAll (boundary : Set α) (s : PausedState seed)
    (ws : List (EscapingPath seed))
    (hs : ∀ p ∈ s.pending, p.position 0 ∈ boundary) :
    ∀ p ∈ (pauseAll boundary s ws).pending, p.position 0 ∈ boundary := by
  induction ws generalizing s with
  | nil => exact hs
  | cons w ws ih =>
      exact ih (pauseOne boundary s w) (pending_on_boundary_pauseOne boundary s w hs)

/-- Resuming cannot remove a settled site and settles every pending particle. -/
theorem settled_subset_resume (s : PausedState seed) : s.settled ⊆ s.resume :=
  subset_grow s.settled s.pending

end
end PausedState
end IdlaCyl
