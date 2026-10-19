/-
The base graph of the cylinder, and the lazy simple random walk on it.

`paper/idla-cylinder-gff.tex:229-237`:

  "For each integer `N ≥ 2`, let `V_N = (V, E)` be a finite, connected,
   vertex-transitive graph on `N` vertices (so that `|V| = N`) ... every vertex
   has a common degree `d = d(N) ≥ 1`, allowed to depend on `N` ... Let `P_N`
   be the transition matrix of the lazy simple random walk on `V_N`:
   `P_N(x,x') = 1/(2d)` if `x ~ x'`, `1/2` if `x = x'`, `0` otherwise."

Vertex-transitivity is stated here as transitivity of the automorphism group
action, exactly as the paper states it, and the common degree is *derived*
from it rather than assumed: `Base.degree_eq` below.  The paper's `d` is
`Base.deg`, the degree of an arbitrary but fixed vertex, which
`Base.degree_eq` shows is the degree of every vertex.
-/
import Mathlib

namespace IdlaCyl

open scoped BigOperators

/-- A finite, connected, vertex-transitive base graph.  The paper's `V_N`;
`N` is `Fintype.card V`.

`vertexTransitive` says the automorphism group acts transitively on vertices,
which is the paper's definition (`tex:229`).  `nontrivial` records `N ≥ 2`,
also from `tex:229`; without it the degree is `0` and the lazy kernel is junk. -/
structure Base where
  /-- The vertex set. -/
  V : Type
  [fintypeV : Fintype V]
  [decEqV : DecidableEq V]
  /-- The adjacency relation, written `∼` in the paper. -/
  graph : SimpleGraph V
  [decRel : DecidableRel graph.Adj]
  /-- `V_N` is connected (`tex:229`). -/
  connected : graph.Connected
  /-- `V_N` is vertex-transitive: `Aut(V_N)` acts transitively (`tex:229`). -/
  vertexTransitive : ∀ x y : V, ∃ σ : graph ≃g graph, σ x = y
  /-- `N ≥ 2` (`tex:229`). -/
  nontrivial : 2 ≤ Fintype.card V

namespace Base

attribute [instance] Base.fintypeV Base.decEqV Base.decRel

variable (B : Base)

instance : Nonempty B.V := by
  have : 0 < Fintype.card B.V := lt_of_lt_of_le (by norm_num) B.nontrivial
  exact Fintype.card_pos_iff.mp this

/-- `N`, the number of vertices (`tex:229`). -/
def card : ℕ := Fintype.card B.V

/-- An arbitrary but fixed base point, used only to name the common degree. -/
noncomputable def pt : B.V := Classical.arbitrary B.V

/-- The paper's common degree `d = d(N)` (`tex:229`).  `degree_eq` shows it is
the degree of every vertex, so the choice of `pt` is immaterial. -/
noncomputable def deg : ℕ := B.graph.degree B.pt

/-- Vertex-transitivity makes the degree common to all vertices: the paper's
"every vertex has a common degree `d`" (`tex:229`). -/
theorem degree_eq (x : B.V) : B.graph.degree x = B.deg := by
  obtain ⟨σ, hσ⟩ := B.vertexTransitive x B.pt
  have h := SimpleGraph.Iso.degree_eq σ x
  rw [hσ] at h
  unfold deg
  omega

/-- The degree is positive: a connected graph on at least two vertices has no
isolated vertex.  Needed before `1/(2d)` is anything but a junk value. -/
theorem deg_pos : 0 < B.deg := by
  have h1 : 1 < Fintype.card B.V := lt_of_lt_of_le (by norm_num) B.nontrivial
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card h1 B.pt
  obtain ⟨w⟩ := B.connected.preconnected B.pt y
  cases w with
  | nil => exact absurd rfl hy
  | cons h _ =>
      have hpos : 0 < B.graph.degree B.pt :=
        (B.graph.degree_pos_iff_exists_adj B.pt).mpr ⟨_, h⟩
      simpa [deg] using hpos

/-- The lazy simple random walk kernel `P_N` on the base (`tex:230-236`,
equation `eq:PN`):
`P x x' = 1/(2d)` if `x ∼ x'`, `1/2` if `x = x'`, and `0` otherwise. -/
noncomputable def P (x x' : B.V) : ℝ :=
  if B.graph.Adj x x' then 1 / (2 * B.deg)
  else if x = x' then 1 / 2
  else 0

/-- `P_N` is symmetric, "by symmetry of the adjacency relation" (`tex:237`). -/
theorem P_symm (x x' : B.V) : B.P x x' = B.P x' x := by
  unfold P
  by_cases h : B.graph.Adj x x'
  · simp [h, h.symm]
  · have h' : ¬ B.graph.Adj x' x := fun hc => h hc.symm
    by_cases hxx : x = x'
    · simp [hxx]
    · have hxx' : ¬ x' = x := fun hc => hxx hc.symm
      simp [h, h', hxx, hxx']

/-- Every entry of `P_N` is nonnegative. -/
theorem P_nonneg (x x' : B.V) : 0 ≤ B.P x x' := by
  unfold P
  split_ifs <;> positivity

/-- `P_N` is stochastic: rows sum to one (`tex:237`, "doubly stochastic"). -/
theorem P_row_sum (x : B.V) : ∑ x' : B.V, B.P x x' = 1 := by
  classical
  have hsplit :
      ∑ x' : B.V, B.P x x'
        = ∑ x' ∈ B.graph.neighborFinset x, B.P x x' + B.P x x := by
    rw [← Finset.sum_subset (Finset.subset_univ (insert x (B.graph.neighborFinset x)))]
    · rw [Finset.sum_insert (by simp [SimpleGraph.mem_neighborFinset])]
      ring
    · intro y _ hy
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or] at hy
      unfold P
      simp [hy.2, Ne.symm hy.1]
  have hnb : ∑ x' ∈ B.graph.neighborFinset x, B.P x x'
      = (B.deg : ℝ) * (1 / (2 * B.deg)) := by
    rw [Finset.sum_congr rfl (fun y hy => ?_), Finset.sum_const, nsmul_eq_mul,
      SimpleGraph.card_neighborFinset_eq_degree, B.degree_eq]
    · simp [SimpleGraph.mem_neighborFinset] at hy
      unfold P
      simp [hy]
  have hd : (B.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr B.deg_pos.ne'
  have hxx : B.P x x = 1 / 2 := by unfold P; simp
  rw [hsplit, hnb, hxx]
  field_simp
  norm_num

end Base

end IdlaCyl
