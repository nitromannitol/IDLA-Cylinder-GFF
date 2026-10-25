module

public import IdlaCyl.Support.PausedPaths
public import IdlaCyl.Support.OrderCounterexample

@[expose] public section

set_option autoImplicit false

/-!
# Pausing and resuming the ORIGINAL labelled tails is not pathwise invariant

Four nearest-neighbour paths on the two-vertex cylinder, starting from R₀,
are enough. The two paused particles even resume in their ORIGINAL order.
This is not a counterexample to site-stack abelianity or to a coupling in law.
-/

namespace IdlaCyl.PauseCounterexample

open EscapingPath PausedState

abbrev a : Cylinder Bool := (false, 1)
abbrev b : Cylinder Bool := (false, 2)
abbrev c : Cylinder Bool := (true, 1)
abbrev d : Cylinder Bool := (true, 2)
abbrev e : Cylinder Bool := (false, 3)
abbrev p : EscapingPath (flatSeed Bool) := OrderCounterexample.p

def rPosition (n : ℕ) : Cylinder Bool := (true, (n : ℤ))

def qPosition : ℕ → Cylinder Bool
  | 0 => (false, 0)
  | 1 => a
  | 2 => b
  | 3 => a
  | 4 => c
  | 5 => a
  | 6 => b
  | n + 7 => (false, (n : ℤ) + 3)

def r : EscapingPath (flatSeed Bool) := escapingOfCofinal rPosition (by
  intro h
  obtain ⟨n, hn⟩ := exists_nat_gt h
  exact ⟨n, hn⟩)

def q : EscapingPath (flatSeed Bool) := escapingOfCofinal qPosition (by
  intro h
  obtain ⟨n, hn⟩ := exists_nat_gt h
  refine ⟨n + 7, ?_⟩
  simp only [qPosition]
  omega)

@[simp] theorem q_position (n : ℕ) : q.position n = qPosition n := rfl
@[simp] theorem r_position (n : ℕ) : r.position n = rPosition n := rfl

def boundary : Set (Cylinder Bool) := {z | 2 ≤ z.2}

theorem p_admissible : CylinderAdmissible OrderCounterexample.twoVertexGraph p :=
  OrderCounterexample.p_admissible

theorem r_admissible : CylinderAdmissible OrderCounterexample.twoVertexGraph r := by
  constructor
  · rfl
  · intro n
    left
    refine ⟨rfl, Or.inl ?_⟩
    simp [rPosition]

theorem q_admissible : CylinderAdmissible OrderCounterexample.twoVertexGraph q := by
  constructor
  · rfl
  · intro n
    by_cases hn : n < 7
    · interval_cases n <;>
        norm_num [CylinderStep, q_position, qPosition, a, b, c,
          OrderCounterexample.twoVertexGraph]
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k + 7 := ⟨n - 7, by omega⟩
      have heq : k + 7 + 1 = (k + 1) + 7 := by omega
      simp only [q_position, heq, qPosition]
      left
      refine ⟨rfl, Or.inl ?_⟩
      simp
      omega

@[simp] theorem p_exit_empty : p.exitSite ∅ = a := OrderCounterexample.p_exit_empty
@[simp] theorem p_exit_a : p.exitSite {a} = b := OrderCounterexample.p_exit_singleton

@[simp] theorem p_time_a : p.exitTime {a} = 2 := by
  apply p.exitTime_eq_of_first {a} 2
  · norm_num [OrderCounterexample.p_position, OrderCounterexample.pPosition, flatSeed, a]
  · intro n hn
    interval_cases n <;>
      norm_num [OrderCounterexample.p_position, OrderCounterexample.pPosition, flatSeed, a]

@[simp] theorem q_time_a : q.exitTime {a} = 2 := by
  apply q.exitTime_eq_of_first {a} 2
  · norm_num [q_position, qPosition, flatSeed, a, b]
  · intro n hn
    interval_cases n <;> norm_num [q_position, qPosition, flatSeed, a]

@[simp] theorem q_exit_a : q.exitSite {a} = b := by
  simp only [exitSite, q_time_a, q_position, qPosition]

@[simp] theorem q_time_ba : q.exitTime {b, a} = 4 := by
  apply q.exitTime_eq_of_first {b, a} 4
  · norm_num [q_position, qPosition, flatSeed, a, b, c]
  · intro n hn
    interval_cases n <;> norm_num [q_position, qPosition, flatSeed, a, b]

@[simp] theorem q_exit_ba : q.exitSite {b, a} = c := by
  simp only [exitSite, q_time_ba, q_position, qPosition]

@[simp] theorem r_time_a : r.exitTime {a} = 1 := by
  apply r.exitTime_eq_of_first {a} 1
  · norm_num [r_position, rPosition, flatSeed, a]
  · intro n hn
    have hn0 : n = 0 := by omega
    subst n
    norm_num [r_position, rPosition, flatSeed]

@[simp] theorem r_exit_a : r.exitSite {a} = c := by
  simp only [exitSite, r_time_a, r_position, rPosition]
  rfl

@[simp] theorem r_time_cba : r.exitTime {c, b, a} = 2 := by
  apply r.exitTime_eq_of_first {c, b, a} 2
  · norm_num [r_position, rPosition, flatSeed, a, b, c]
  · intro n hn
    interval_cases n <;> norm_num [r_position, rPosition, flatSeed, a, b, c]

@[simp] theorem r_exit_cba : r.exitSite {c, b, a} = d := by
  simp only [exitSite, r_time_cba, r_position, rPosition]
  rfl

theorem ordinary_cluster : grow ∅ [p, p, q, r] = {d, c, b, a} := by
  simp only [grow_cons, grow_nil, settle, p_exit_empty, Finset.insert_empty,
    p_exit_a, q_exit_ba, r_exit_cba]

/-- The first-stage cluster has two settled sites and TWO particles paused at b. -/
theorem paused_state :
    pauseAll boundary (⟨∅, []⟩ : PausedState (flatSeed Bool)) [p, p, q, r] =
      ⟨{c, a}, [p.suffix 2, q.suffix 2]⟩ := by
  classical
  simp [pauseAll, pauseOne, settle, p_exit_empty, p_exit_a, q_exit_a, r_exit_a,
    p_time_a, q_time_a, boundary, a, b, c]

theorem p_suffix_exit : (p.suffix 2).exitSite {c, a} = b := by
  have h := (p.suffix 2).exitSite_eq_of_first {c, a} 0 (by
    norm_num [suffix_position, OrderCounterexample.p_position,
      OrderCounterexample.pPosition, flatSeed, a, b, c]) (by
    intro n hn
    omega)
  simpa [OrderCounterexample.pPosition, a, b, c] using h

theorem q_suffix_exit : (q.suffix 2).exitSite {b, c, a} = e := by
  have h := (q.suffix 2).exitSite_eq_of_first {b, c, a} 5 (by
    norm_num [suffix_position, q_position, qPosition, flatSeed, a, b, c]) (by
    intro n hn
    interval_cases n <;>
      norm_num [suffix_position, q_position, qPosition, flatSeed, a, b, c])
  simpa [qPosition, e] using h

theorem resumed_cluster :
    (pauseAll boundary (⟨∅, []⟩ : PausedState (flatSeed Bool)) [p, p, q, r]).resume =
      {e, b, c, a} := by
  rw [paused_state]
  simp only [resume, grow_cons, grow_nil, settle, p_suffix_exit, q_suffix_exit]

theorem two_paused_at_same_site :
    (pauseAll boundary (⟨∅, []⟩ : PausedState (flatSeed Bool)) [p, p, q, r]).multiplicity b = 2 := by
  rw [paused_state]
  norm_num [PausedState.multiplicity, suffix_start, OrderCounterexample.p_position,
    OrderCounterexample.pPosition, q_position, qPosition, b]

/-- Even chronological resumption of the original tails can change the cluster. -/
theorem not_original_tail_pause_invariant :
    grow ∅ [p, p, q, r] ≠
      (pauseAll boundary (⟨∅, []⟩ : PausedState (flatSeed Bool)) [p, p, q, r]).resume := by
  rw [ordinary_cluster, resumed_cluster]
  intro h
  have hd : d ∈ ({d, c, b, a} : Finset (Cylinder Bool)) := by simp
  rw [h] at hd
  norm_num [a, b, c, d, e] at hd

end IdlaCyl.PauseCounterexample
