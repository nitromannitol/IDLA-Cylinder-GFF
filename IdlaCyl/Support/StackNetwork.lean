module

public import Mathlib

@[expose] public section

set_option autoImplicit false

/-!
# Finite site-indexed instruction stacks

A configuration records INTEGER particle multiplicities at every site. Sites
outside `active` never fire; they retain all arrivals, including repeated pause
locations. Capacities may be zero (a permanently occupied seed, whose background
particle is not counted) or one (an ordinary IDLA site).

There is no probability law or termination assumption in this module. The mass
formula is defined directly from the first `u x` instructions at each site.
-/

namespace IdlaCyl.Stack

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Instruction number `j` at `x` sends a particle to `route x j`. -/
abbrev Routing (V : Type*) := V → ℕ → V

/-- Counts arrivals at `y` from the first `n` instructions at `x`. -/
def sent (route : Routing V) (x y : V) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sent route x y n + if route x n = y then 1 else 0

omit [Fintype V] in
@[simp] theorem sent_zero (route : Routing V) (x y : V) : sent route x y 0 = 0 := rfl

omit [Fintype V] in
@[simp] theorem sent_succ (route : Routing V) (x y : V) (n : ℕ) :
    sent route x y (n + 1) = sent route x y n + if route x n = y then 1 else 0 := rfl

omit [Fintype V] in
theorem sent_mono (route : Routing V) (x y : V) {m n : ℕ} (h : m ≤ n) :
    sent route x y m ≤ sent route x y n := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact le_rfl
  | succ n ih =>
      by_cases hmn : m ≤ n
      · have h' := ih hmn
        simp only [sent_succ]
        omega
      · have hm : m = n + 1 := by omega
        subst m
        exact le_rfl

/-- Increase a single odometer coordinate. -/
def bump (u : V → ℕ) (x : V) : V → ℕ :=
  fun y => if y = x then u y + 1 else u y

omit [Fintype V] in
@[simp] theorem bump_same (u : V → ℕ) (x : V) : bump u x x = u x + 1 := by
  simp [bump]

omit [Fintype V] in
theorem bump_other (u : V → ℕ) {x y : V} (h : y ≠ x) : bump u x y = u y := by
  simp [bump, h]

omit [Fintype V] in
theorem le_bump (u : V → ℕ) (x y : V) : u y ≤ bump u x y := by
  by_cases h : y = x <;> simp [bump, h]

def incoming (route : Routing V) (u : V → ℕ) (y : V) : ℤ :=
  ∑ x, (sent route x y (u x) : ℤ)

/-- Exact particle balance after the firing-count vector `u`. -/
def particles (route : Routing V) (initial : V → ℤ) (u : V → ℕ) (y : V) : ℤ :=
  initial y - (u y : ℤ) + incoming route u y

@[simp] theorem particles_zero (route : Routing V) (initial : V → ℤ) (y : V) :
    particles route initial (fun _ => 0) y = initial y := by
  simp [particles, incoming]

theorem incoming_mono (route : Routing V) {u v : V → ℕ}
    (h : ∀ x, u x ≤ v x) (y : V) : incoming route u y ≤ incoming route v y := by
  apply Finset.sum_le_sum
  intro x _
  exact_mod_cast sent_mono route x y (h x)

/-- The monotonicity needed at the first would-be excessive firing. -/
theorem particles_le_of_le_of_eq (route : Routing V) (initial : V → ℤ)
    {u v : V → ℕ} (h : ∀ x, u x ≤ v x) (y : V) (hy : u y = v y) :
    particles route initial u y ≤ particles route initial v y := by
  have hi := incoming_mono route h y
  unfold particles
  rw [hy]
  omega

theorem particles_mono_initial (route : Routing V) {a b : V → ℤ}
    (h : ∀ x, a x ≤ b x) (u : V → ℕ) (y : V) :
    particles route a u y ≤ particles route b u y := by
  have hy := h y
  unfold particles
  omega

/-- Local arrival update, including self-loops. -/
theorem incoming_bump (route : Routing V) (u : V → ℕ) (x y : V) :
    incoming route (bump u x) y = incoming route u y +
      if route x (u x) = y then 1 else 0 := by
  have hterm (z : V) :
      (sent route z y (bump u x z) : ℤ) = (sent route z y (u z) : ℤ) +
        if z = x then (if route x (u x) = y then 1 else 0) else 0 := by
    by_cases hz : z = x
    · subst z
      simp only [bump_same, sent_succ, Nat.cast_add]
      by_cases hxy : route x (u x) = y <;> simp [hxy]
    · simp [bump, hz]
  unfold incoming
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp

/-- Firing sends exactly one particle along the next instruction. -/
theorem particles_bump (route : Routing V) (initial : V → ℤ)
    (u : V → ℕ) (x y : V) :
    particles route initial (bump u x) y = particles route initial u y -
      (if y = x then 1 else 0) + (if route x (u x) = y then 1 else 0) := by
  unfold particles
  rw [incoming_bump]
  by_cases hy : y = x
  · subst y
    simp only [bump_same, Nat.cast_add, Nat.cast_one, ↓reduceIte]
    ring
  · simp only [bump_other u hy, if_neg hy]
    ring

/-- One legal firing preserves nonnegative particle counts. -/
theorem particles_bump_nonneg (route : Routing V) (initial capacity : V → ℤ)
    (u : V → ℕ) (x : V)
    (hc : 0 ≤ capacity x) (hm : ∀ y, 0 ≤ particles route initial u y)
    (hx : capacity x < particles route initial u x) :
    ∀ y, 0 ≤ particles route initial (bump u x) y := by
  intro y
  rw [particles_bump]
  have hy := hm y
  by_cases heq : y = x
  · subst y
    simp only
    split_ifs <;> omega
  · simp only [if_neg heq]
    split_ifs <;> omega

/-- Exact conservation, counting inactive sites as particle reservoirs. -/
theorem total_particles_bump (route : Routing V) (initial : V → ℤ)
    (u : V → ℕ) (x : V) :
    (∑ y, particles route initial (bump u x) y) =
      ∑ y, particles route initial u y := by
  simp_rw [particles_bump]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp

/-- Chronological execution of a finite word of firing sites. -/
def run (u : V → ℕ) : List V → V → ℕ
  | [] => u
  | x :: xs => run (bump u x) xs

omit [Fintype V] in
@[simp] theorem run_nil (u : V → ℕ) : run u [] = u := rfl
omit [Fintype V] in
@[simp] theorem run_cons (u : V → ℕ) (x : V) (xs : List V) :
    run u (x :: xs) = run (bump u x) xs := rfl

omit [Fintype V] in
theorem run_append (u : V → ℕ) (xs ys : List V) :
    run u (xs ++ ys) = run (run u xs) ys := by
  induction xs generalizing u with
  | nil => rfl
  | cons x xs ih => exact ih (bump u x)

omit [Fintype V] in
theorem le_run (u : V → ℕ) (xs : List V) (y : V) : u y ≤ run u xs y := by
  induction xs generalizing u with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_bump u x y).trans (ih (bump u x))

/-- Only excess particles at active sites may move. -/
def LegalFrom (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (u : V → ℕ) : List V → Prop
  | [] => True
  | x :: xs => x ∈ active ∧ capacity x < particles route initial u x ∧
      LegalFrom route initial capacity active (bump u x) xs

def Stable (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (u : V → ℕ) : Prop :=
  ∀ x ∈ active, particles route initial u x ≤ capacity x

theorem legalFrom_append (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (u : V → ℕ) (xs ys : List V) :
    LegalFrom route initial capacity active u (xs ++ ys) ↔
      LegalFrom route initial capacity active u xs ∧
      LegalFrom route initial capacity active (run u xs) ys := by
  induction xs generalizing u with
  | nil => simp [LegalFrom]
  | cons x xs ih =>
      simp only [List.cons_append, LegalFrom, run_cons, ih]
      tauto

theorem legalFrom_mono_active (route : Routing V) (initial capacity : V → ℤ)
    {small large : Set V} (hsub : small ⊆ large) (u : V → ℕ) (xs : List V)
    (h : LegalFrom route initial capacity small u xs) :
    LegalFrom route initial capacity large u xs := by
  induction xs generalizing u with
  | nil => trivial
  | cons x xs ih => exact ⟨hsub h.1, h.2.1, ih (bump u x) h.2.2⟩

theorem legalFrom_mono_initial (route : Routing V) {a b : V → ℤ}
    (hsub : ∀ x, a x ≤ b x) (capacity : V → ℤ) (active : Set V)
    (u : V → ℕ) (xs : List V) (h : LegalFrom route a capacity active u xs) :
    LegalFrom route b capacity active u xs := by
  induction xs generalizing u with
  | nil => trivial
  | cons x xs ih =>
      exact ⟨h.1, h.2.1.trans_le (particles_mono_initial route hsub u x),
        ih (bump u x) h.2.2⟩

theorem legalFrom_nonneg (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (u : V → ℕ) (xs : List V)
    (hc : ∀ x ∈ active, 0 ≤ capacity x)
    (hm : ∀ x, 0 ≤ particles route initial u x)
    (h : LegalFrom route initial capacity active u xs) :
    ∀ x, 0 ≤ particles route initial (run u xs) x := by
  induction xs generalizing u with
  | nil => exact hm
  | cons x xs ih =>
      exact ih (bump u x)
        (particles_bump_nonneg route initial capacity u x (hc x h.1) hm h.2.1) h.2.2

theorem total_particles_run (route : Routing V) (initial : V → ℤ)
    (u : V → ℕ) (xs : List V) :
    (∑ y, particles route initial (run u xs) y) =
      ∑ y, particles route initial u y := by
  induction xs generalizing u with
  | nil => rfl
  | cons x xs ih =>
      exact (ih (bump u x)).trans (total_particles_bump route initial u x)

/-- An inactive vertex consumes no instructions, even when it receives many chips. -/
theorem run_eq_at_inactive (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (u : V → ℕ) (xs : List V)
    (h : LegalFrom route initial capacity active u xs) {y : V} (hy : y ∉ active) :
    run u xs y = u y := by
  induction xs generalizing u with
  | nil => rfl
  | cons x xs ih =>
      have hyx : y ≠ x := fun heq => hy (heq.symm ▸ h.1)
      exact (ih (bump u x) h.2.2).trans (bump_other u hyx)

end IdlaCyl.Stack
