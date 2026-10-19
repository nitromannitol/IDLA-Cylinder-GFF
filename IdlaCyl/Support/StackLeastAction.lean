import IdlaCyl.Support.StackNetwork

set_option autoImplicit false

/-!
# Least action and pause/resume for site-indexed stacks

The input is the actual instruction array. Abelianity is a conclusion, not an
input field. Termination is NOT assumed here as a global axiom: comparisons in
this file explicitly take finite legal schedules and stable final states.
StackTermination.lean supplies terminating completions of arbitrary finite
instruction prefixes.
-/

namespace IdlaCyl.Stack

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No legal execution can overtake a stabilizing firing vector. -/
theorem least_action (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) {u v : V → ℕ} (xs : List V)
    (hstart : ∀ x, u x ≤ v x)
    (hlegal : LegalFrom route initial capacity active u xs)
    (hstable : Stable route initial capacity active v) :
    ∀ x, run u xs x ≤ v x := by
  induction xs generalizing u with
  | nil => exact hstart
  | cons x xs ih =>
      have hstrict : u x < v x := by
        by_contra hnot
        have heq : u x = v x := by have hu := hstart x; omega
        have hmass := particles_le_of_le_of_eq route initial hstart x heq
        have hcap := hstable x hlegal.1
        have hex := hlegal.2.1
        omega
      have hnext : ∀ y, bump u x y ≤ v y := by
        intro y
        by_cases hy : y = x
        · subst y
          simp only [bump_same]
          omega
        · simpa only [bump_other u hy] using hstart y
      exact ih (u := bump u x) hnext hlegal.2.2

/-- Two legal stabilizations consume exactly the same instructions. -/
theorem abelian_odometer (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (u : V → ℕ) (xs ys : List V)
    (hx : LegalFrom route initial capacity active u xs)
    (hy : LegalFrom route initial capacity active u ys)
    (hsx : Stable route initial capacity active (run u xs))
    (hsy : Stable route initial capacity active (run u ys)) :
    run u xs = run u ys := by
  have hxy := least_action route initial capacity active xs (le_run u ys) hx hsy
  have hyx := least_action route initial capacity active ys (le_run u xs) hy hsx
  funext z
  exact Nat.le_antisymm (hxy z) (hyx z)

/-- Hence the entire final multiplicity configuration agrees, including sinks. -/
theorem abelian_particles (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (u : V → ℕ) (xs ys : List V)
    (hx : LegalFrom route initial capacity active u xs)
    (hy : LegalFrom route initial capacity active u ys)
    (hsx : Stable route initial capacity active (run u xs))
    (hsy : Stable route initial capacity active (run u ys)) :
    particles route initial (run u xs) = particles route initial (run u ys) := by
  rw [abelian_odometer route initial capacity active u xs ys hx hy hsx hsy]

/-- Adding input particles increases the stabilizing odometer. -/
theorem stabilization_odometer_mono (route : Routing V) {a b : V → ℤ}
    (hab : ∀ x, a x ≤ b x) (capacity : V → ℤ) (active : Set V)
    (xs ys : List V)
    (hx : LegalFrom route a capacity active (fun _ => 0) xs)
    (hy : LegalFrom route b capacity active (fun _ => 0) ys)
    (hsy : Stable route b capacity active (run (fun _ => 0) ys)) :
    ∀ x, run (fun _ => 0) xs x ≤ run (fun _ => 0) ys x := by
  have _ := hy
  exact least_action route b capacity active xs
    (fun x => Nat.zero_le _) (legalFrom_mono_initial route hab capacity active _ xs hx) hsy

/-- Once a site's retained mass reaches its capacity, legal firings preserve that. -/
theorem capacity_le_bump (route : Routing V) (initial capacity : V → ℤ)
    (u : V → ℕ) (x y : V)
    (hx : capacity x < particles route initial u x)
    (hy : capacity y ≤ particles route initial u y) :
    capacity y ≤ particles route initial (bump u x) y := by
  rw [particles_bump]
  by_cases heq : y = x
  · subst y
    simp only
    split_ifs <;> omega
  · simp only [if_neg heq]
    split_ifs <;> omega

theorem capacity_le_run (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (u : V → ℕ) (xs : List V) (y : V)
    (hlegal : LegalFrom route initial capacity active u xs)
    (hy : capacity y ≤ particles route initial u y) :
    capacity y ≤ particles route initial (run u xs) y := by
  induction xs generalizing u with
  | nil => exact hy
  | cons x xs ih =>
      exact ih (u := bump u x) hlegal.2.2 (capacity_le_bump route initial capacity u x y hlegal.2.1 hy)

/-- Every site which actually fires retains at least its capacity thereafter. -/
theorem fired_retains_capacity (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (u : V → ℕ) (xs : List V) (y : V)
    (hlegal : LegalFrom route initial capacity active u xs)
    (hfired : u y < run u xs y) :
    capacity y ≤ particles route initial (run u xs) y := by
  induction xs generalizing u with
  | nil => simp only [run_nil] at hfired; omega
  | cons x xs ih =>
      by_cases hy : y = x
      · subst y
        have hfirst : capacity x ≤ particles route initial (bump u x) x := by
          rw [particles_bump]
          have he := hlegal.2.1
          simp only
          split_ifs <;> omega
        exact capacity_le_run route initial capacity active (bump u x) xs x hlegal.2.2 hfirst
      · apply ih (u := bump u x) hlegal.2.2
        simpa only [run_cons, bump_other u hy] using hfired

/-- Stable particle counts are monotone in the input, including paused reservoirs. -/
theorem stabilization_particles_mono (route : Routing V) {a b : V → ℤ}
    (hab : ∀ x, a x ≤ b x) (capacity : V → ℤ) (active : Set V)
    (xs ys : List V)
    (hx : LegalFrom route a capacity active (fun _ => 0) xs)
    (hy : LegalFrom route b capacity active (fun _ => 0) ys)
    (hsx : Stable route a capacity active (run (fun _ => 0) xs))
    (hsy : Stable route b capacity active (run (fun _ => 0) ys)) :
    ∀ z, particles route a (run (fun _ => 0) xs) z ≤
      particles route b (run (fun _ => 0) ys) z := by
  have hu := stabilization_odometer_mono route hab capacity active xs ys hx hy hsy
  intro z
  by_cases hz : run (fun _ => 0) ys z = 0
  · have hzero : run (fun _ => 0) xs z = 0 := by have h := hu z; omega
    have hm := particles_le_of_le_of_eq route a hu z (hzero.trans hz.symm)
    exact hm.trans (particles_mono_initial route hab _ z)
  · have hzactive : z ∈ active := by
      by_contra hza
      exact hz (run_eq_at_inactive route b capacity active _ ys hy hza)
    have hcap := fired_retains_capacity route b capacity active (fun _ => 0) ys z hy
      (by omega : 0 < run (fun _ => 0) ys z)
    exact (hsx z hzactive).trans hcap

/-- Enlarging the active region permits exactly the same first-stage firings. -/
theorem pause_resume_odometer (route : Routing V) (initial capacity : V → ℤ)
    {paused full : Set V} (hregion : paused ⊆ full)
    (u : V → ℕ) (pfx continuation ordinary : List V)
    (hprefix : LegalFrom route initial capacity paused u pfx)
    (hcontinuation : LegalFrom route initial capacity full (run u pfx) continuation)
    (hordinary : LegalFrom route initial capacity full u ordinary)
    (hfinished : Stable route initial capacity full (run (run u pfx) continuation))
    (hordinaryFinished : Stable route initial capacity full (run u ordinary)) :
    run (run u pfx) continuation = run u ordinary := by
  have hp := legalFrom_mono_active route initial capacity hregion u pfx hprefix
  have hwhole : LegalFrom route initial capacity full u (pfx ++ continuation) :=
    (legalFrom_append route initial capacity full u pfx continuation).mpr ⟨hp, hcontinuation⟩
  have hs : Stable route initial capacity full (run u (pfx ++ continuation)) := by
    simpa only [run_append] using hfinished
  simpa only [run_append] using
    abelian_odometer route initial capacity full u (pfx ++ continuation) ordinary
      hwhole hordinary hs hordinaryFinished

/-- The pause/resume theorem preserves the FULL counts, not merely occupied sets. -/
theorem pause_resume_particles (route : Routing V) (initial capacity : V → ℤ)
    {paused full : Set V} (hregion : paused ⊆ full)
    (u : V → ℕ) (pfx continuation ordinary : List V)
    (hprefix : LegalFrom route initial capacity paused u pfx)
    (hcontinuation : LegalFrom route initial capacity full (run u pfx) continuation)
    (hordinary : LegalFrom route initial capacity full u ordinary)
    (hfinished : Stable route initial capacity full (run (run u pfx) continuation))
    (hordinaryFinished : Stable route initial capacity full (run u ordinary)) :
    particles route initial (run (run u pfx) continuation) =
      particles route initial (run u ordinary) := by
  rw [pause_resume_odometer route initial capacity hregion u pfx continuation ordinary
    hprefix hcontinuation hordinary hfinished hordinaryFinished]

/-- At an inactive pause site, all incoming particles are retained with multiplicity. -/
theorem paused_multiplicity (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (xs : List V)
    (h : LegalFrom route initial capacity active (fun _ => 0) xs)
    (y : V) (hy : y ∉ active) :
    particles route initial (run (fun _ => 0) xs) y =
      initial y + incoming route (run (fun _ => 0) xs) y := by
  unfold particles
  rw [run_eq_at_inactive route initial capacity active _ xs h hy]
  simp

end IdlaCyl.Stack
