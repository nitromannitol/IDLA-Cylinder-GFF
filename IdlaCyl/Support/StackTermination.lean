import IdlaCyl.Support.StackLeastAction

set_option autoImplicit false

-- `active : Set V` forces `if · ∈ active` in statements; enable classical
-- decidability for the whole file rather than only inside proofs.
attribute [local instance] Classical.propDecidable

/-!
# Termination constructed from arbitrary finite instruction prefixes

After its prescribed finite prefix, each stack routes to an inactive reservoir.
The completion is an approximation device; its tail need not be a legal cylinder
edge. It agrees exactly with the prescribed instructions until a prefix is used
up. No statement here identifies this completed model with the infinite walk.

The explicit potential is
  (particles currently at active sites) + (unused prefix instructions).
It drops by at least one per legal firing. This proves termination and constructs
a stable legal schedule, rather than assuming a stabilizing comparator exists.
-/

namespace IdlaCyl.Stack

open scoped BigOperators
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Complete each finite prefix by routing every later instruction to `sink`. -/
def completeRoute (route : Routing V) (cutoff : V → ℕ) (sink : V) : Routing V :=
  fun x n => if n < cutoff x then route x n else sink

omit [Fintype V] [DecidableEq V] in
theorem completeRoute_prefix (route : Routing V) (cutoff : V → ℕ) (sink x : V)
    (n : ℕ) (hn : n < cutoff x) : completeRoute route cutoff sink x n = route x n := by
  simp [completeRoute, hn]

omit [Fintype V] [DecidableEq V] in
theorem completeRoute_tail (route : Routing V) (cutoff : V → ℕ) (sink x : V)
    (n : ℕ) (hn : cutoff x ≤ n) : completeRoute route cutoff sink x n = sink := by
  simp [completeRoute, not_lt_of_ge hn]

def activeMass (route : Routing V) (initial : V → ℤ) (active : Set V)
    (u : V → ℕ) : ℤ := by
  classical
  exact ∑ y ∈ Finset.univ.filter (fun y => y ∈ active), particles route initial u y

def unused (cutoff u : V → ℕ) : ℤ := ∑ x, ((cutoff x - u x : ℕ) : ℤ)

def potential (route : Routing V) (initial : V → ℤ) (active : Set V)
    (cutoff u : V → ℕ) : ℤ := activeMass route initial active u + unused cutoff u

theorem activeMass_nonneg (route : Routing V) (initial : V → ℤ) (active : Set V)
    (u : V → ℕ) (hu : ∀ x, 0 ≤ particles route initial u x) :
    0 ≤ activeMass route initial active u := by
  classical
  exact Finset.sum_nonneg (fun x _ => hu x)

omit [DecidableEq V] in
theorem unused_nonneg (cutoff u : V → ℕ) : 0 ≤ unused cutoff u := by
  exact Finset.sum_nonneg (fun x _ => Int.natCast_nonneg _)

theorem potential_nonneg (route : Routing V) (initial : V → ℤ) (active : Set V)
    (cutoff u : V → ℕ) (hu : ∀ x, 0 ≤ particles route initial u x) :
    0 ≤ potential route initial active cutoff u := by
  exact add_nonneg (activeMass_nonneg route initial active u hu) (unused_nonneg cutoff u)

theorem activeMass_bump (route : Routing V) (initial : V → ℤ) (active : Set V)
    (u : V → ℕ) (x : V) (hx : x ∈ active) :
    activeMass route initial active (bump u x) =
      activeMass route initial active u - 1 +
        if route x (u x) ∈ active then 1 else 0 := by
  classical
  unfold activeMass
  simp_rw [particles_bump]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [hx]

theorem unused_bump (cutoff u : V → ℕ) (x : V) :
    unused cutoff (bump u x) = unused cutoff u - if u x < cutoff x then 1 else 0 := by
  have hterm (y : V) : ((cutoff y - bump u x y : ℕ) : ℤ) =
      ((cutoff y - u y : ℕ) : ℤ) -
        if y = x then (if u x < cutoff x then 1 else 0) else 0 := by
    by_cases hy : y = x
    · subst y
      simp only [bump_same]
      split_ifs <;> omega
    · simp [bump, hy]
  unfold unused
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  simp

/-- All tail instructions at active sites lead to inactive reservoirs. -/
def ExitingTails (route : Routing V) (active : Set V) (cutoff : V → ℕ) : Prop :=
  ∀ x ∈ active, ∀ n, cutoff x ≤ n → route x n ∉ active

omit [Fintype V] [DecidableEq V] in
theorem completeRoute_exitingTails (route : Routing V) (active : Set V)
    (cutoff : V → ℕ) (sink : V) (hsink : sink ∉ active) :
    ExitingTails (completeRoute route cutoff sink) active cutoff := by
  intro x hx n hn
  simpa only [completeRoute_tail route cutoff sink x n hn] using hsink

/-- A concrete strict Lyapunov estimate, valid even when a prefix self-loops. -/
theorem potential_bump_le (route : Routing V) (initial : V → ℤ) (active : Set V)
    (cutoff u : V → ℕ) (htail : ExitingTails route active cutoff)
    (x : V) (hx : x ∈ active) :
    potential route initial active cutoff (bump u x) ≤
      potential route initial active cutoff u - 1 := by
  classical
  unfold potential
  rw [activeMass_bump route initial active u x hx, unused_bump]
  by_cases hprefix : u x < cutoff x
  · simp only [if_pos hprefix]
    split_ifs <;> omega
  · have hdest := htail x hx (u x) (by omega)
    simp only [if_neg hprefix, if_neg hdest]
    omega

/-- Potential decrease telescopes along any legal finite word. -/
theorem potential_run_add_length_le (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (cutoff u : V → ℕ)
    (htail : ExitingTails route active cutoff) (xs : List V)
    (hlegal : LegalFrom route initial capacity active u xs) :
    potential route initial active cutoff (run u xs) + (xs.length : ℤ) ≤
      potential route initial active cutoff u := by
  induction xs generalizing u with
  | nil => simp
  | cons x xs ih =>
      have hstep := potential_bump_le route initial active cutoff u htail x hlegal.1
      have hrest := ih (bump u x) hlegal.2.2
      simp only [run_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      omega

/-- An explicit bound on the length of every legal word. -/
theorem legal_length_le_potential (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (cutoff u : V → ℕ)
    (htail : ExitingTails route active cutoff)
    (hcap : ∀ x ∈ active, 0 ≤ capacity x)
    (hu : ∀ x, 0 ≤ particles route initial u x)
    (xs : List V) (hlegal : LegalFrom route initial capacity active u xs) :
    (xs.length : ℤ) ≤ potential route initial active cutoff u := by
  have hm := legalFrom_nonneg route initial capacity active u xs hcap hu hlegal
  have hp := potential_nonneg route initial active cutoff (run u xs) hm
  have hb := potential_run_add_length_le route initial capacity active cutoff u htail xs hlegal
  omega

def CanFire (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (u : V → ℕ) : Prop :=
  ∃ x, x ∈ active ∧ capacity x < particles route initial u x

theorem stable_of_not_canFire (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (u : V → ℕ)
    (h : ¬ CanFire route initial capacity active u) :
    Stable route initial capacity active u := by
  intro x hx
  by_contra he
  exact h ⟨x, hx, lt_of_not_ge he⟩

/-- A total fuel-bounded legal scheduler; choices are among currently legal sites. -/
def greedy (route : Routing V) (initial capacity : V → ℤ) (active : Set V) :
    ℕ → (V → ℕ) → List V
  | 0, _ => []
  | n + 1, u => by
      classical
      exact if h : CanFire route initial capacity active u then
        let x := Classical.choose h
        x :: greedy route initial capacity active n (bump u x)
      else []

theorem greedy_legal (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (fuel : ℕ) (u : V → ℕ) :
    LegalFrom route initial capacity active u (greedy route initial capacity active fuel u) := by
  classical
  induction fuel generalizing u with
  | zero => trivial
  | succ n ih =>
      by_cases h : CanFire route initial capacity active u
      · simp only [greedy, dif_pos h, LegalFrom]
        exact ⟨(Classical.choose_spec h).1, (Classical.choose_spec h).2,
          ih (bump u (Classical.choose h))⟩
      · simp [greedy, h, LegalFrom]

/-- Enough explicit fuel always reaches a stable configuration. -/
theorem greedy_stable (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (cutoff : V → ℕ)
    (htail : ExitingTails route active cutoff)
    (hcap : ∀ x ∈ active, 0 ≤ capacity x)
    (fuel : ℕ) (u : V → ℕ)
    (hu : ∀ x, 0 ≤ particles route initial u x)
    (hfuel : potential route initial active cutoff u < (fuel : ℤ)) :
    Stable route initial capacity active
      (run u (greedy route initial capacity active fuel u)) := by
  classical
  induction fuel generalizing u with
  | zero =>
      have hp := potential_nonneg route initial active cutoff u hu
      norm_num at hfuel
      omega
  | succ n ih =>
      by_cases h : CanFire route initial capacity active u
      · let x := Classical.choose h
        have hx : x ∈ active := (Classical.choose_spec h).1
        have hex : capacity x < particles route initial u x := (Classical.choose_spec h).2
        have hm := particles_bump_nonneg route initial capacity u x (hcap x hx) hu hex
        have hp := potential_bump_le route initial active cutoff u htail x hx
        have hnext : potential route initial active cutoff (bump u x) < (n : ℤ) := by
          have hf := hfuel
          simp only [Nat.cast_add, Nat.cast_one] at hf
          omega
        have hs := ih (bump u x) hm hnext
        simpa only [greedy, dif_pos h, run_cons] using hs
      · simp only [greedy, dif_neg h, run_nil]
        exact stable_of_not_canFire route initial capacity active u h

/-- Existence is proved by a total scheduler, not an assumed stable comparator. -/
theorem exists_legal_stabilization (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (cutoff u : V → ℕ)
    (htail : ExitingTails route active cutoff)
    (hcap : ∀ x ∈ active, 0 ≤ capacity x)
    (hu : ∀ x, 0 ≤ particles route initial u x) :
    ∃ xs : List V, LegalFrom route initial capacity active u xs ∧
      Stable route initial capacity active (run u xs) := by
  obtain ⟨fuel, hfuel⟩ := exists_nat_gt (potential route initial active cutoff u)
  exact ⟨greedy route initial capacity active fuel u,
    greedy_legal route initial capacity active fuel u,
    greedy_stable route initial capacity active cutoff htail hcap fuel u hu hfuel⟩

/-- Any finite collection of arbitrary instructions has a terminating completion. -/
theorem completed_stabilization_exists (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (cutoff : V → ℕ) (sink : V) (hsink : sink ∉ active)
    (hcap : ∀ x ∈ active, 0 ≤ capacity x) (hinitial : ∀ x, 0 ≤ initial x) :
    ∃ xs : List V,
      LegalFrom (completeRoute route cutoff sink) initial capacity active (fun _ => 0) xs ∧
      Stable (completeRoute route cutoff sink) initial capacity active (run (fun _ => 0) xs) := by
  apply exists_legal_stabilization (completeRoute route cutoff sink) initial capacity active
    cutoff (fun _ => 0) (completeRoute_exitingTails route active cutoff sink hsink) hcap
  intro x
  simpa using hinitial x

end
end IdlaCyl.Stack
