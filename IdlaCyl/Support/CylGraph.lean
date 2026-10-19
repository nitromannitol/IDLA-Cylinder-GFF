/-
The cylinder graph `G_N = V_N × ℤ` and connected seeds.

The cylinder `G_N := V_N × ℤ` (`paper/idla-cylinder-gff.tex:239-256`) is a graph whose edges join
`(v, y)` and `(v', y')` when `v ∼ v'` in the base and `y = y'`, or `v = v'` and `|y − y'| = 1`;
the cylinder walk moves along these edges or holds. Silvestri's Proposition 2 concerns IDLA
started from a connected set of sites (Silvestri, ECP 25 (2020) paper 61, Definition 2). This file
defines the graph and connectedness of a set of sites, and proves:

* `seedConnected_R`: every half-cylinder `R_k` is connected;
* `SeedConnected.insert_of_adj`: adding a site adjacent to a connected set keeps it connected;
* `seedConnected_image_vshift`: vertical translation preserves connectedness;
* `cylGraph_adj_of_cylKernel_pos`: every positive off-diagonal kernel entry is an edge.
-/
import IdlaCyl.Support.Cylinder
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace IdlaCyl

open MeasureTheory

/-- The cylinder graph on `Site B = V_N × ℤ`.  Two sites are adjacent when they lie on
the same layer and their base vertices are adjacent in `V_N` (a horizontal step), or
they share their base vertex and their heights differ by one (a vertical step):
`(p.1 = q.1 ∧ (p.2 - q.2).natAbs = 1) ∨ (p.2 = q.2 ∧ B.graph.Adj p.1 q.1)`. -/
def cylGraph (B : Base) : SimpleGraph (Site B) where
  Adj p q := (p.1 = q.1 ∧ (p.2 - q.2).natAbs = 1) ∨ (p.2 = q.2 ∧ B.graph.Adj p.1 q.1)
  symm := ⟨fun p q h => by
    rcases h with h | h
    · refine Or.inl ⟨h.1.symm, ?_⟩
      rw [← neg_sub, Int.natAbs_neg]
      exact h.2
    · exact Or.inr ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun p h => by
    rcases h with h | h
    · rw [sub_self, Int.natAbs_zero] at h
      exact absurd h.2 (by norm_num)
    · exact B.graph.irrefl h.2⟩

/-- The defining edge rule of `cylGraph B`, unfolded (`tex:246-255`). -/
theorem cylGraph_adj_iff (B : Base) (p q : Site B) :
    (cylGraph B).Adj p q ↔
      (p.1 = q.1 ∧ (p.2 - q.2).natAbs = 1) ∨ (p.2 = q.2 ∧ B.graph.Adj p.1 q.1) :=
  Iff.rfl

/-- A seed `S` of the cylinder is connected when the subgraph induced on `S` is connected.
This is the hypothesis of Silvestri's Proposition 2 (`tex:1440-1453`). -/
def SeedConnected (B : Base) (S : Set (Site B)) : Prop :=
  ((cylGraph B).induce S).Connected

/-- Every vertex of a walk of `cylGraph B` lying in `S`, with both endpoints in `S`, gives a
walk of the induced subgraph.  Used to lift paths of the ambient graph to seeds. -/
theorem reachable_induce_of_walk (B : Base) {S : Set (Site B)} {a b : Site B}
    (w : (cylGraph B).Walk a b) (ha : a ∈ S) (hb : b ∈ S)
    (hw : ∀ x ∈ w.support, x ∈ S) :
    ((cylGraph B).induce S).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v c hadj p ih =>
      have hv : v ∈ S := hw v (List.mem_cons_of_mem _ p.start_mem_support)
      have hadj' : ((cylGraph B).induce S).Adj ⟨u, ha⟩ ⟨v, hv⟩ := hadj
      exact (SimpleGraph.Adj.reachable hadj').trans
        (ih hv hb fun x hx => hw x (List.mem_cons_of_mem _ hx))

/-- Every half-cylinder `R_k` is connected (`tex:261-262`): each site descends vertically to
the top layer `⌊k⌋` inside `R_k`, and the base graph is connected on that layer. -/
theorem seedConnected_R (B : Base) (k : ℝ) : SeedConnected B (R B k) := by
  obtain ⟨h, hdef⟩ : ∃ h : ℤ, h = ⌊k⌋ := ⟨_, rfl⟩
  have hh : (h : ℝ) ≤ k := by rw [hdef]; exact Int.floor_le k
  have hmemL : ∀ x : B.V, ((x, h) : Site B) ∈ R B k := fun x => mem_R.mpr hh
  have hvert : ∀ (n : ℕ) (x : B.V) (y : ℤ) (hy : ((x, y) : Site B) ∈ R B k),
      y + n = h → ((cylGraph B).induce (R B k)).Reachable ⟨(x, y), hy⟩ ⟨(x, h), hmemL x⟩ := by
    intro n
    induction n with
    | zero =>
        intro x y hy hyh
        have hyh' : y = h := by simpa using hyh
        subst hyh'
        exact SimpleGraph.Reachable.refl _
    | succ n ih =>
        intro x y hy hyh
        push_cast at hyh
        have hle : y + 1 ≤ h := by omega
        have hle' : ((y + 1 : ℤ) : ℝ) ≤ (h : ℝ) := by exact_mod_cast hle
        have hy1 : ((x, y + 1) : Site B) ∈ R B k := mem_R.mpr (le_trans hle' hh)
        have hadj : ((cylGraph B).induce (R B k)).Adj ⟨(x, y), hy⟩ ⟨(x, y + 1), hy1⟩ :=
          Or.inl ⟨rfl, by simp⟩
        exact (SimpleGraph.Adj.reachable hadj).trans (ih x (y + 1) hy1 (by omega))
  have hbase : ∀ {x x' : B.V} (w : B.graph.Walk x x'),
      ((cylGraph B).induce (R B k)).Reachable ⟨(x, h), hmemL x⟩ ⟨(x', h), hmemL x'⟩ := by
    intro x x' w
    induction w with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons u v c hadj p ih =>
        have hadj' : ((cylGraph B).induce (R B k)).Adj ⟨(u, h), hmemL u⟩ ⟨(v, h), hmemL v⟩ :=
          Or.inr ⟨rfl, hadj⟩
        exact (SimpleGraph.Adj.reachable hadj').trans ih
  have hup : ∀ (p : Site B) (hp : p ∈ R B k),
      ((cylGraph B).induce (R B k)).Reachable ⟨p, hp⟩ ⟨(p.1, h), hmemL p.1⟩ := by
    intro p hp
    have hle : p.2 ≤ h := by
      rw [hdef]
      exact Int.le_floor.mpr (mem_R.mp hp)
    exact hvert (h - p.2).toNat p.1 p.2 hp (by omega)
  unfold SeedConnected
  refine { preconnected := fun a b => ?_, nonempty := ⟨⟨(B.pt, h), hmemL B.pt⟩⟩ }
  obtain ⟨w⟩ := B.connected.preconnected a.1.1 b.1.1
  exact (hup a.1 a.2).trans ((hbase w).trans (hup b.1 b.2).symm)

/-- Adding a site adjacent to a connected seed keeps it connected. -/
theorem SeedConnected.insert_of_adj {B : Base} {S : Set (Site B)} (hS : SeedConnected B S)
    {q z : Site B} (hq : q ∈ S) (hadj : (cylGraph B).Adj q z) :
    SeedConnected B (S ∪ {z}) := by
  unfold SeedConnected at hS ⊢
  have hsingle : ((cylGraph B).induce ({z} : Set (Site B))).Preconnected := by
    intro a b
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    rw [Set.mem_singleton_iff] at ha hb
    subst ha
    subst hb
    exact SimpleGraph.Reachable.refl _
  exact SimpleGraph.connected_induce_union hS.preconnected hsingle hq
    (Set.mem_singleton z) hadj

/-- Vertical translation of the cylinder by `L` layers (`tex:246-255`, the shift by `y ↦ y + L`):
`(x, y) ↦ (x, y + L)`. -/
def vshift (B : Base) (L : ℤ) (p : Site B) : Site B := (p.1, p.2 + L)

/-- Vertical translation is an automorphism of the cylinder graph, so it preserves adjacency
in both directions. -/
theorem cylGraph_adj_vshift (B : Base) (L : ℤ) (p q : Site B) :
    (cylGraph B).Adj (vshift B L p) (vshift B L q) ↔ (cylGraph B).Adj p q := by
  rw [cylGraph_adj_iff, cylGraph_adj_iff]
  simp only [vshift, add_left_inj, add_sub_add_right_eq_sub]

/-- Vertical translation carries a connected seed to a connected seed. -/
theorem seedConnected_image_vshift {B : Base} {S : Set (Site B)} (L : ℤ)
    (hS : SeedConnected B S) : SeedConnected B (vshift B L '' S) := by
  unfold SeedConnected at hS ⊢
  let φ : S → (vshift B L '' S) := fun x => ⟨vshift B L x.1, x.1, x.2, rfl⟩
  let f : (cylGraph B).induce S →g (cylGraph B).induce (vshift B L '' S) :=
    ⟨φ, fun {x y} h => (cylGraph_adj_vshift B L x.1 y.1).mpr h⟩
  obtain ⟨⟨s, hs⟩⟩ := hS.nonempty
  refine { preconnected := fun u v => ?_, nonempty := ⟨⟨vshift B L s, s, hs, rfl⟩⟩ }
  obtain ⟨u, a, ha, rfl⟩ := u
  obtain ⟨v, b, hb, rfl⟩ := v
  exact (hS.preconnected ⟨a, ha⟩ ⟨b, hb⟩).map f

/-- The cylinder graph contains every positive off-diagonal kernel entry as an edge: a positive
vertical weight is a vertical step, and a positive horizontal weight forces `B.graph.Adj`
because `B.P` is positive off the diagonal only on edges (`tex:246-255`, `tex:229-237`). -/
theorem cylGraph_adj_of_cylKernel_pos {B : Base} {p q : Site B} (h : 0 < cylKernel B p q)
    (hne : p ≠ q) : (cylGraph B).Adj p q := by
  unfold cylKernel at h
  by_cases h1 : p.1 = q.1 ∧ (p.2 - q.2).natAbs = 1
  · exact Or.inl h1
  · rw [if_neg h1] at h
    by_cases h2 : p.2 = q.2
    · rw [if_pos h2] at h
      have hP : 0 < B.P p.1 q.1 := by linarith
      unfold Base.P at hP
      by_cases ha : B.graph.Adj p.1 q.1
      · exact Or.inr ⟨h2, ha⟩
      · rw [if_neg ha] at hP
        by_cases hx : p.1 = q.1
        · exact absurd (Prod.ext hx h2) hne
        · rw [if_neg hx] at hP
          exact absurd hP (lt_irrefl 0)
    · rw [if_neg h2] at h
      exact absurd h (lt_irrefl 0)

end IdlaCyl
