import IdlaCyl.Support.StackTermination

set_option autoImplicit false

/-!
# Finite certificates for stack stabilization

A finite stabilization reads finitely many site instructions. Every completion
agreeing on those instructions has the same stabilization. This is an exact
identity, not an asymptotic estimate. It supplies the deterministic part of a
passage from total finite completed-stack models to almost-surely terminating
random stacks. The probability-one termination event is a separate obligation.
-/

namespace IdlaCyl.Stack

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two instruction fields agree through a prescribed firing-count vector. -/
def AgreeBelow (r s : Routing V) (bound : V → ℕ) : Prop :=
  ∀ x, ∀ n < bound x, r x n = s x n

omit [Fintype V] [DecidableEq V] in
theorem agreeBelow_mono {r s : Routing V} {u v : V → ℕ}
    (h : AgreeBelow r s v) (huv : ∀ x, u x ≤ v x) : AgreeBelow r s u := by
  intro x n hn
  exact h x n (hn.trans_le (huv x))

omit [Fintype V] in
theorem sent_eq_of_prefix (r s : Routing V) (x y : V) (n : ℕ)
    (h : ∀ j < n, r x j = s x j) : sent r x y n = sent s x y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [sent_succ, sent_succ, ih (fun j hj => h j (by omega)), h n (by omega)]

theorem incoming_eq_of_prefix {r s : Routing V} {u : V → ℕ}
    (h : AgreeBelow r s u) (y : V) : incoming r u y = incoming s u y := by
  unfold incoming
  apply Finset.sum_congr rfl
  intro x _
  rw [sent_eq_of_prefix r s x y (u x) (h x)]

theorem particles_eq_of_prefix {r s : Routing V} (initial : V → ℤ) {u : V → ℕ}
    (h : AgreeBelow r s u) : particles r initial u = particles s initial u := by
  funext y
  unfold particles
  rw [incoming_eq_of_prefix h y]

/-- The same chronological word remains legal when its consumed instructions agree. -/
theorem legalFrom_of_prefix {r s : Routing V} (initial capacity : V → ℤ)
    (active : Set V) (u : V → ℕ) (xs : List V)
    (hagree : AgreeBelow r s (run u xs))
    (hlegal : LegalFrom r initial capacity active u xs) :
    LegalFrom s initial capacity active u xs := by
  induction xs generalizing u with
  | nil => trivial
  | cons x xs ih =>
      have hnow : AgreeBelow r s u := agreeBelow_mono hagree (le_run u (x :: xs))
      have hm := congrFun (particles_eq_of_prefix initial hnow) x
      refine ⟨hlegal.1, ?_, ih (bump u x) hagree hlegal.2.2⟩
      rw [← hm]
      exact hlegal.2.1

theorem stable_of_prefix {r s : Routing V} (initial capacity : V → ℤ)
    (active : Set V) (u : V → ℕ) (hagree : AgreeBelow r s u)
    (hstable : Stable r initial capacity active u) : Stable s initial capacity active u := by
  intro x hx
  rw [← congrFun (particles_eq_of_prefix initial hagree) x]
  exact hstable x hx

/-- Agreement on all consumed entries is a certificate for identical stabilization. -/
theorem stabilization_eq_of_prefix {r s : Routing V} (initial capacity : V → ℤ)
    (active : Set V) (u : V → ℕ) (xs ys : List V)
    (hx : LegalFrom r initial capacity active u xs)
    (hsx : Stable r initial capacity active (run u xs))
    (hagree : AgreeBelow r s (run u xs))
    (hy : LegalFrom s initial capacity active u ys)
    (hsy : Stable s initial capacity active (run u ys)) :
    run u xs = run u ys ∧
      particles r initial (run u xs) = particles s initial (run u ys) := by
  have hxs := legalFrom_of_prefix initial capacity active u xs hagree hx
  have hsxs := stable_of_prefix initial capacity active _ hagree hsx
  have hu := abelian_odometer s initial capacity active u xs ys hxs hy hsxs hsy
  refine ⟨hu, ?_⟩
  calc
    particles r initial (run u xs) = particles s initial (run u xs) :=
      particles_eq_of_prefix initial hagree
    _ = particles s initial (run u ys) := by rw [hu]

omit [Fintype V] [DecidableEq V] in
/-- A cutoff beyond each consumed prefix satisfies the certificate exactly. -/
theorem agreeBelow_completion (route : Routing V) (cutoff used : V → ℕ)
    (sink : V) (h : ∀ x, used x ≤ cutoff x) :
    AgreeBelow route (completeRoute route cutoff sink) used := by
  intro x n hn
  exact (completeRoute_prefix route cutoff sink x n (hn.trans_le (h x))).symm

/-- Every sufficiently large completed model reproduces a finite raw stabilization. -/
theorem completed_stabilization_exact (route : Routing V) (initial capacity : V → ℤ)
    (active : Set V) (cutoff : V → ℕ) (sink : V) (xs ys : List V)
    (hx : LegalFrom route initial capacity active (fun _ => 0) xs)
    (hsx : Stable route initial capacity active (run (fun _ => 0) xs))
    (hcutoff : ∀ x, run (fun _ => 0) xs x ≤ cutoff x)
    (hy : LegalFrom (completeRoute route cutoff sink) initial capacity active (fun _ => 0) ys)
    (hsy : Stable (completeRoute route cutoff sink) initial capacity active (run (fun _ => 0) ys)) :
    run (fun _ => 0) xs = run (fun _ => 0) ys ∧
      particles route initial (run (fun _ => 0) xs) =
        particles (completeRoute route cutoff sink) initial (run (fun _ => 0) ys) := by
  exact stabilization_eq_of_prefix initial capacity active (fun _ => 0) xs ys hx hsx
    (agreeBelow_completion route cutoff _ sink hcutoff) hy hsy

end IdlaCyl.Stack
