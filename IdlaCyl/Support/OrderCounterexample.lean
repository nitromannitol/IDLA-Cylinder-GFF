import IdlaCyl.Support.Geometry

set_option autoImplicit false

/-!
# Fixed particle trajectories do not commute

This example uses the two-vertex cylinder and the actual `EscapingPath.grow`
definition. Both trajectories have legal nearest-neighbor prefixes and an
upward continuation. The finite prefixes already determine the two different
clusters. This does NOT refute an abelian statement for site-indexed stacks,
nor invariance in law under an exchange of independent particle labels.
-/

namespace IdlaCyl.OrderCounterexample

open EscapingPath

abbrev a : Cylinder Bool := (false, 1)
abbrev b : Cylinder Bool := (false, 2)
abbrev c : Cylinder Bool := (true, 1)

def pPosition (n : ℕ) : Cylinder Bool := (false, (n : ℤ))

def qPosition (n : ℕ) : Cylinder Bool :=
  if n < 2 then (false, (n : ℤ)) else (true, (n : ℤ) - 1)

def p : EscapingPath (flatSeed Bool) := escapingOfCofinal pPosition (by
  intro h
  obtain ⟨n, hn⟩ := exists_nat_gt h
  exact ⟨n, hn⟩)

def q : EscapingPath (flatSeed Bool) := escapingOfCofinal qPosition (by
  intro h
  obtain ⟨n, hn⟩ := exists_nat_gt h
  refine ⟨n + 2, ?_⟩
  have hn2 : ¬ n + 2 < 2 := by omega
  simp only [qPosition, if_neg hn2, Nat.cast_add, Nat.cast_ofNat]
  omega)

@[simp] theorem p_position (n : ℕ) : p.position n = pPosition n := rfl
@[simp] theorem q_position (n : ℕ) : q.position n = qPosition n := rfl

/-- The complete graph on two vertices is the base in this example. -/
def twoVertexGraph : SimpleGraph Bool := ⊤

theorem p_admissible : CylinderAdmissible twoVertexGraph p := by
  constructor
  · rfl
  · intro n
    left
    refine ⟨rfl, Or.inl ?_⟩
    simp [pPosition]

theorem q_admissible : CylinderAdmissible twoVertexGraph q := by
  constructor
  · norm_num [q_position, qPosition]
  · intro n
    by_cases hn0 : n = 0
    · subst n
      norm_num [CylinderStep, q_position, qPosition]
    · by_cases hn1 : n = 1
      · subst n
        norm_num [CylinderStep, q_position, qPosition, twoVertexGraph]
      · have hn : ¬ n < 2 := by omega
        have hn' : ¬ n + 1 < 2 := by omega
        left
        refine ⟨?_, Or.inl ?_⟩
        · simp [qPosition, hn, hn']
        · simp only [q_position, qPosition, if_neg hn, if_neg hn']
          push_cast
          ring

theorem p_exit_empty : p.exitSite ∅ = a := by
  have h := p.exitSite_eq_of_first ∅ 1 (by
    norm_num [p_position, pPosition, flatSeed]) (by
    intro n hn
    have hn0 : n = 0 := by omega
    subst n
    simp [pPosition, flatSeed])
  simpa [pPosition] using h

theorem q_exit_empty : q.exitSite ∅ = a := by
  have h := q.exitSite_eq_of_first ∅ 1 (by
    norm_num [q_position, qPosition, flatSeed]) (by
    intro n hn
    have hn0 : n = 0 := by omega
    subst n
    simp [qPosition, flatSeed])
  simpa [qPosition] using h

theorem p_exit_singleton : p.exitSite {a} = b := by
  have h := p.exitSite_eq_of_first {a} 2 (by
    norm_num [p_position, pPosition, flatSeed, a]) (by
    intro n hn
    have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl <;> simp [pPosition, flatSeed, a])
  simpa [pPosition] using h

theorem q_exit_singleton : q.exitSite {a} = c := by
  have h := q.exitSite_eq_of_first {a} 2 (by
    norm_num [q_position, qPosition, flatSeed, a]) (by
    intro n hn
    have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl <;> simp [qPosition, flatSeed, a])
  simpa [qPosition] using h

theorem grow_pq : grow ∅ [p, q] = {a, c} := by
  simp only [grow_cons, grow_nil, settle, p_exit_empty, Finset.insert_empty,
    q_exit_singleton]
  ext z
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem grow_qp : grow ∅ [q, p] = {a, b} := by
  simp only [grow_cons, grow_nil, settle, q_exit_empty, Finset.insert_empty,
    p_exit_singleton]
  ext z
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- A concrete failure of pathwise particle-order invariance. -/
theorem not_particle_order_invariant : grow ∅ [p, q] ≠ grow ∅ [q, p] := by
  rw [grow_pq, grow_qp]
  intro h
  have hc : c ∈ ({a, c} : Finset (Cylinder Bool)) := by simp
  rw [h] at hc
  norm_num [a, b, c] at hc

end IdlaCyl.OrderCounterexample
