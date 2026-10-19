/-
The cycle base `ℤ_N` of the paper, for `N ≥ 3`, as a `Base`.

`paper/idla-cylinder-gff.tex:474-475`: "For `N ≥ 2`, let `V_N = ℤ_N` be the cycle on `N`
vertices." The cycle theorem `thm:cycle` (`tex:486-493`) is the GFF limit on this base.

The vertex set is `Fin N` and the graph is Mathlib's `SimpleGraph.cycleGraph N`, whose adjacency
is `u - v = 1 ∨ v - u = 1` in `Fin N` (`SimpleGraph.cycleGraph_adj`). Vertex-transitivity is by the
rotations `x ↦ x + c`, which are graph automorphisms.

The paper's `N ≥ 2` (`tex:475`) is narrowed to `N ≥ 3` here. For `N = 2` the simple graph
`cycleGraph 2` is `K₂`, of degree `1`, so the common degree `2` of the cycle fails.
-/
import Mathlib
import IdlaCyl.Support.Base

namespace IdlaCyl

open SimpleGraph

/-- The rotation `x ↦ x + c` of `Fin N` as a graph automorphism of the cycle `cycleGraph N`.
Adjacency is `u - v = 1 ∨ v - u = 1`, and this is invariant under a common translation. -/
def cycleRot {N : ℕ} [NeZero N] (c : Fin N) : cycleGraph N ≃g cycleGraph N where
  toEquiv := Equiv.addRight c
  map_rel_iff' := by
    intro u v
    simp only [Equiv.coe_addRight, cycleGraph_adj', add_sub_add_right_eq_sub]

/-- The cycle base `ℤ_N` for `N ≥ 3` (`tex:474-475`): finite, connected, vertex-transitive, with
`N` vertices. The paper's `N ≥ 2` is narrowed to `N ≥ 3`, as explained in the header. -/
def cycleBase (N : ℕ) (hN : 3 ≤ N) : Base where
  V := Fin N
  graph := cycleGraph N
  connected := by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 3 := ⟨N - 3, by omega⟩
    exact cycleGraph_connected
  vertexTransitive := by
    intro x y
    haveI : NeZero N := ⟨by omega⟩
    refine ⟨cycleRot (y - x), ?_⟩
    show x + (y - x) = y
    simp
  nontrivial := by
    rw [Fintype.card_fin]
    omega

/-- The graph of the cycle base is Mathlib's `cycleGraph N` (`tex:475`). -/
theorem cycleBase_graph (N : ℕ) (hN : 3 ≤ N) : (cycleBase N hN).graph = cycleGraph N :=
  rfl

/-- The cycle base has `N` vertices (`tex:475`). -/
theorem cycleBase_card (N : ℕ) (hN : 3 ≤ N) : (cycleBase N hN).card = N :=
  Fintype.card_fin N

/-- The common degree of the cycle base is `d = 2` (`tex:475`, with `d` as in `tex:229`). -/
theorem cycleBase_deg (N : ℕ) (hN : 3 ≤ N) : (cycleBase N hN).deg = 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 3 := ⟨N - 3, by omega⟩
  rw [← Base.degree_eq (cycleBase (n + 3) hN) (0 : Fin (n + 3))]
  exact cycleGraph_degree_three_le

/-- The family `n ↦ ℤ_{n+3}`: the member indexed by `n` is the cycle on `n + 3` vertices, so every
member is a cycle base in the sense of `cycleBase` (`tex:474-475`). -/
def cycleSeq (n : ℕ) : Base :=
  cycleBase (n + 3) (by omega)

/-- The `n`-th member of the cycle family has `n + 3` vertices. -/
theorem cycleSeq_card (n : ℕ) : (cycleSeq n).card = n + 3 :=
  cycleBase_card (n + 3) (by omega)

/-! ### Nonvacuity -/

/-- The smallest admissible cycle `ℤ_3` has `3` vertices. -/
theorem cycleBase_three_card : (cycleBase 3 le_rfl).card = 3 :=
  cycleBase_card 3 le_rfl

/-- In the triangle `ℤ_3` the vertices `0` and `1` are adjacent. -/
theorem cycleBase_three_adj : (cycleBase 3 le_rfl).graph.Adj (0 : Fin 3) (1 : Fin 3) := by
  rw [cycleBase_graph, cycleGraph_three_eq_top]
  simp

end IdlaCyl
