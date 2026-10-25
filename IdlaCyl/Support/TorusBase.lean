module

public import IdlaCyl.Support.Base

@[expose] public section

/-!
# The discrete torus `(ℤ/N)^d` as a base

`paper/idla-cylinder-gff.tex:229-237` takes a base `V_N` to be a finite, connected,
vertex-transitive graph on `N ≥ 2` vertices. The torus examples at
`paper/idla-cylinder-gff.tex:502-514` take `V_N = ℤ_n^d` with vertex count `N = n^d`.
Here the side length is called `N` (the paper's `n`), so the vertex count is `N ^ d`.

The paper does not write out the adjacency of `ℤ_n^d`. We take the nearest-neighbour
relation: `x ∼ y` iff `x` and `y` differ in exactly one coordinate `i`, by `±1` in `ℤ/N`.
This is the relation whose lazy walk has the eigenvalue expansion quoted at `tex:502-514`
and common degree `2d`. Requiring `3 ≤ N` makes `+1 ≠ -1` in `ℤ/N`, so every vertex has
exactly `2d` neighbours.
-/

namespace IdlaCyl

/-! ### Facts about `ℤ/N` for `N ≥ 3` -/

/-- `1 ≠ 0` in `ℤ/N` for `N ≥ 3`. -/
theorem torus_one_ne_zero {N : ℕ} (hN : 3 ≤ N) : (1 : ZMod N) ≠ 0 := by
  intro h
  have h' : ((1 : ℕ) : ZMod N) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd Nat.one_pos h'
  omega

/-- `2 ≠ 0` in `ℤ/N` for `N ≥ 3`. -/
theorem torus_two_ne_zero {N : ℕ} (hN : 3 ≤ N) : (2 : ZMod N) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod N) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  omega

/-- `1 ≠ -1` in `ℤ/N` for `N ≥ 3`: the neighbours `x ± e_i` are distinct. -/
theorem torus_one_ne_neg_one {N : ℕ} (hN : 3 ≤ N) : (1 : ZMod N) ≠ -1 := by
  intro h
  exact torus_two_ne_zero hN (by linear_combination h)

/-! ### Nearest-neighbour adjacency on `(ℤ/N)^d` -/

/-- Nearest-neighbour adjacency on `(ℤ/N)^d`, the torus `ℤ_n^d` of `tex:502-514`:
`x ∼ y` iff some coordinate `i` has `y i = x i ± 1` and all other coordinates agree. -/
def torusAdj (d N : ℕ) (x y : Fin d → ZMod N) : Prop :=
  ∃ i : Fin d, (∀ j, j ≠ i → x j = y j) ∧ (y i = x i + 1 ∨ y i = x i - 1)

instance torusAdj_decidable (d N : ℕ) (x y : Fin d → ZMod N) : Decidable (torusAdj d N x y) := by
  unfold torusAdj
  infer_instance

/-- The torus adjacency is symmetric. -/
theorem torusAdj_symm {d N : ℕ} {x y : Fin d → ZMod N} (h : torusAdj d N x y) :
    torusAdj d N y x := by
  unfold torusAdj at h ⊢
  obtain ⟨i, h1, h2⟩ := h
  refine ⟨i, fun j hj => (h1 j hj).symm, ?_⟩
  rcases h2 with h2 | h2
  · exact Or.inr (by linear_combination -h2)
  · exact Or.inl (by linear_combination -h2)

/-- No vertex of the torus is adjacent to itself, since `1 ≠ 0` in `ℤ/N`. -/
theorem torusAdj_irrefl {d N : ℕ} (hN : 3 ≤ N) (x : Fin d → ZMod N) : ¬ torusAdj d N x x := by
  unfold torusAdj
  rintro ⟨i, -, h⟩
  rcases h with h | h
  · exact torus_one_ne_zero hN (by linear_combination -h)
  · exact torus_one_ne_zero hN (by linear_combination h)

/-- The torus adjacency is invariant under translation. -/
theorem torusAdj_add {d N : ℕ} (c x y : Fin d → ZMod N) :
    torusAdj d N (x + c) (y + c) ↔ torusAdj d N x y := by
  simp only [torusAdj, Pi.add_apply]
  constructor
  · rintro ⟨i, h1, h2⟩
    refine ⟨i, fun j hj => ?_, ?_⟩
    · linear_combination h1 j hj
    · rcases h2 with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
  · rintro ⟨i, h1, h2⟩
    refine ⟨i, fun j hj => ?_, ?_⟩
    · linear_combination h1 j hj
    · rcases h2 with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)

/-! ### The torus graph -/

/-- The torus graph on `(ℤ/N)^d` (`tex:502-514`), with the nearest-neighbour adjacency. -/
def torusGraph (d N : ℕ) (hN : 3 ≤ N) : SimpleGraph (Fin d → ZMod N) where
  Adj := torusAdj d N
  symm := ⟨fun _ _ h => torusAdj_symm h⟩
  loopless := ⟨fun x => torusAdj_irrefl hN x⟩

instance torusGraph_decRel (d N : ℕ) (hN : 3 ≤ N) : DecidableRel (torusGraph d N hN).Adj :=
  fun x y => torusAdj_decidable d N x y

/-- Translation by `c` is an automorphism of the torus graph. -/
def torusTranslate (d N : ℕ) (hN : 3 ≤ N) (c : Fin d → ZMod N) :
    torusGraph d N hN ≃g torusGraph d N hN where
  toEquiv := Equiv.addRight c
  map_rel_iff' := fun {a b} => torusAdj_add c a b

/-- The torus graph is vertex-transitive: translations act transitively (`tex:229`). -/
theorem torusGraph_transitive (d N : ℕ) (hN : 3 ≤ N) (x y : Fin d → ZMod N) :
    ∃ σ : torusGraph d N hN ≃g torusGraph d N hN, σ x = y :=
  ⟨torusTranslate d N hN (y - x), by
    show x + (y - x) = y
    abel⟩

/-- The torus graph is connected: any vertex is reached from `0` by moving one coordinate at a
time, one unit step at a time (`tex:502-514`). -/
theorem torusGraph_connected (d N : ℕ) (hN : 3 ≤ N) : (torusGraph d N hN).Connected := by
  haveI : NeZero N := ⟨by omega⟩
  -- Moving coordinate `i` up by `n` unit steps, one edge at a time.
  have step : ∀ (x : Fin d → ZMod N) (i : Fin d) (n : ℕ),
      (torusGraph d N hN).Reachable x (x + Pi.single i (n : ZMod N)) := by
    intro x i n
    induction n with
    | zero => simp
    | succ n ih =>
      have hadj : torusAdj d N (x + Pi.single i (n : ZMod N))
          (x + Pi.single i ((n + 1 : ℕ) : ZMod N)) := by
        unfold torusAdj
        refine ⟨i, fun j hj => ?_, Or.inl ?_⟩
        · simp [Pi.single_eq_of_ne hj]
        · simp only [Pi.add_apply, Pi.single_eq_same]
          push_cast
          ring
      exact ih.trans (SimpleGraph.Adj.reachable (G := torusGraph d N hN) hadj)
  -- Any displacement in a single coordinate.
  have stepAll : ∀ (x : Fin d → ZMod N) (i : Fin d) (c : ZMod N),
      (torusGraph d N hN).Reachable x (x + Pi.single i c) := by
    intro x i c
    have h := step x i c.val
    rwa [ZMod.natCast_zmod_val] at h
  -- Every vertex is reached from `0` by summing its coordinates one at a time.
  have reach0 : ∀ x : Fin d → ZMod N, (torusGraph d N hN).Reachable 0 x := by
    intro x
    have hs : ∀ s : Finset (Fin d),
        (torusGraph d N hN).Reachable 0 (∑ i ∈ s, Pi.single i (x i)) := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simp
      · intro a s ha ih
        rw [Finset.sum_insert ha, add_comm]
        exact ih.trans (stepAll _ a (x a))
    have hx : ∑ i : Fin d, Pi.single i (x i) = x := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    have h := hs Finset.univ
    rwa [hx] at h
  exact { preconnected := fun x y => (reach0 x).symm.trans (reach0 y) }

/-! ### Counting the torus -/

/-- The vertex count of `(ℤ/N)^d` is `N ^ d`, the paper's `N = n^d` (`tex:502-514`). -/
theorem torus_card (d N : ℕ) [NeZero N] : Fintype.card (Fin d → ZMod N) = N ^ d := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- The torus has at least two vertices when `d ≥ 1` and `N ≥ 3`. -/
theorem torus_two_le (d N : ℕ) (hd : 1 ≤ d) (hN : 3 ≤ N) [NeZero N] :
    2 ≤ Fintype.card (Fin d → ZMod N) := by
  rw [torus_card]
  exact le_trans (show 2 ≤ N by omega) (Nat.le_self_pow (by omega) N)

/-- The `2d` unit vectors `± e_i` of `(ℤ/N)^d`, indexed by `(i, b)`: `b = true` gives `+e_i`,
`b = false` gives `-e_i`. -/
def torusDir (d N : ℕ) (p : Fin d × Bool) : Fin d → ZMod N :=
  Pi.single p.1 (cond p.2 1 (-1))

/-- The unit vectors `± e_i` are distinct, for `N ≥ 3`. -/
theorem torusDir_injective (d N : ℕ) (hN : 3 ≤ N) : Function.Injective (torusDir d N) := by
  rintro ⟨i, b⟩ ⟨i', b'⟩ h
  have hi := congrFun h i
  dsimp only [torusDir] at hi
  by_cases hii : i = i'
  · subst hii
    rw [Pi.single_eq_same, Pi.single_eq_same] at hi
    cases b <;> cases b'
    · rfl
    · exact absurd hi.symm (torus_one_ne_neg_one hN)
    · exact absurd hi (torus_one_ne_neg_one hN)
    · rfl
  · rw [Pi.single_eq_same, Pi.single_eq_of_ne hii] at hi
    cases b
    · exact absurd (neg_eq_zero.mp hi) (torus_one_ne_zero hN)
    · exact absurd hi (torus_one_ne_zero hN)

/-- The neighbours of `0` in the torus are exactly the `2d` unit vectors `± e_i`
(`tex:502-514`, common degree `2d`). -/
theorem torusGraph_neighborFinset_zero (d N : ℕ) (hN : 3 ≤ N) [NeZero N] :
    (torusGraph d N hN).neighborFinset 0 = Finset.univ.image (torusDir d N) := by
  ext y
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
  constructor
  · intro hy
    have hy' : torusAdj d N 0 y := hy
    obtain ⟨i, h1, h2⟩ := hy'
    have hzero : ∀ j, j ≠ i → y j = 0 := fun j hj => (h1 j hj).symm
    rcases h2 with h2 | h2
    · refine ⟨(i, true), Finset.mem_univ _, ?_⟩
      funext j
      by_cases hj : j = i
      · simp [torusDir, hj, h2]
      · simp [torusDir, Pi.single_eq_of_ne hj, hzero j hj]
    · refine ⟨(i, false), Finset.mem_univ _, ?_⟩
      funext j
      by_cases hj : j = i
      · simp [torusDir, hj, h2]
      · simp [torusDir, Pi.single_eq_of_ne hj, hzero j hj]
  · rintro ⟨⟨i, b⟩, -, rfl⟩
    show torusAdj d N 0 (torusDir d N (i, b))
    unfold torusAdj
    cases b
    · refine ⟨i, fun j hj => ?_, Or.inr ?_⟩
      · simp [torusDir, Pi.single_eq_of_ne hj]
      · simp [torusDir]
    · refine ⟨i, fun j hj => ?_, Or.inl ?_⟩
      · simp [torusDir, Pi.single_eq_of_ne hj]
      · simp [torusDir]

/-- The degree of the torus is `2d` (`tex:502-514`). -/
theorem torusGraph_degree_zero (d N : ℕ) (hN : 3 ≤ N) [NeZero N] :
    (torusGraph d N hN).degree 0 = 2 * d := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, torusGraph_neighborFinset_zero,
    Finset.card_image_of_injective _ (torusDir_injective d N hN), Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

/-! ### The torus as a `Base` -/

/-- The discrete torus `(ℤ/N)^d` as a `Base` (`tex:229`, torus examples `tex:502-514`).
Here `d ≥ 1` is the dimension and `N ≥ 3` the side length (the paper's `n`), so the vertex
count is `N ^ d`, the paper's `N = n^d`. -/
def torusBase (d N : ℕ) (hd : 1 ≤ d) (hN : 3 ≤ N) : Base := by
  haveI : NeZero N := ⟨by omega⟩
  exact
    { V := Fin d → ZMod N
      graph := torusGraph d N hN
      connected := torusGraph_connected d N hN
      vertexTransitive := torusGraph_transitive d N hN
      nontrivial := torus_two_le d N hd hN }

/-- The vertex count of `torusBase d N` is `N ^ d` (`tex:502-514`). -/
theorem torusBase_card (d N : ℕ) (hd : 1 ≤ d) (hN : 3 ≤ N) :
    (torusBase d N hd hN).card = N ^ d := by
  haveI : NeZero N := ⟨by omega⟩
  exact torus_card d N

/-- The common degree of `torusBase d N` is `2d` (`tex:229`, `tex:502-514`). -/
theorem torusBase_deg (d N : ℕ) (hd : 1 ≤ d) (hN : 3 ≤ N) :
    (torusBase d N hd hN).deg = 2 * d := by
  haveI : NeZero N := ⟨by omega⟩
  rw [← Base.degree_eq (torusBase d N hd hN) (0 : Fin d → ZMod N)]
  exact torusGraph_degree_zero d N hN

/-- Adjacency of `torusBase d N` in coordinates (`tex:502-514`): `x ∼ y` iff for some coordinate
`i` all other coordinates agree and `y i = x i ± 1`. The coordinate map is the identity
equivalence `Equiv.refl`, so the statement is the coordinate form of the adjacency for the
vertex set `Fin d → ZMod N` itself. -/
theorem torusBase_hgraph (d N : ℕ) (hd : 1 ≤ d) (hN : 3 ≤ N) (x y : Fin d → ZMod N) :
    (torusBase d N hd hN).graph.Adj x y ↔
      ∃ i : Fin d,
        (∀ j, j ≠ i → Equiv.refl (Fin d → ZMod N) x j = Equiv.refl (Fin d → ZMod N) y j) ∧
          (Equiv.refl (Fin d → ZMod N) y i = Equiv.refl (Fin d → ZMod N) x i + 1 ∨
            Equiv.refl (Fin d → ZMod N) y i = Equiv.refl (Fin d → ZMod N) x i - 1) :=
  Iff.rfl

/-! ### Nonvacuity: the smallest admissible torus -/

/-- The smallest admissible torus, `d = 1` and `N = 3`, is the triangle, with three vertices. -/
theorem torusBase_one_three_card : (torusBase 1 3 le_rfl le_rfl).card = 3 := by
  rw [torusBase_card, pow_one]

/-- In the triangle `d = 1`, `N = 3`, the vertex `0` is adjacent to the vertex `1`. -/
theorem torusBase_one_three_adj :
    (torusBase 1 3 le_rfl le_rfl).graph.Adj (fun _ : Fin 1 => (0 : ZMod 3))
      (fun _ : Fin 1 => (1 : ZMod 3)) :=
  (torusBase_hgraph 1 3 le_rfl le_rfl _ _).mpr
    ⟨0, fun j hj => absurd (Subsingleton.elim j 0) hj, Or.inl (by decide)⟩

end IdlaCyl
