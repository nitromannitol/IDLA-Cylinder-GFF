module

public import IdlaCyl.Support.Outer.StackStopped
public import IdlaCyl.Support.StackLeastAction

@[expose] public section

/-
Finite stack certificates for two releases.
Source: paper/idla-cylinder-gff.tex, tex:1331-1351,1391-1396.
-/

attribute [local instance] Classical.propDecidable

namespace IdlaCyl.OuterFinite
open IdlaCyl.Stack
open scoped BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]

private def pathWord (f : ℕ → V) (n : ℕ) : List V := (List.range n).map f

omit [Fintype V] [DecidableEq V] in
private theorem pathWord_succ (f : ℕ → V) (n : ℕ) :
    pathWord f (n + 1) = pathWord f n ++ [f n] := by
  simp only [pathWord, List.range_succ, List.map_append, List.map_singleton]

omit [Fintype V] in
private theorem run_count (u : V → ℕ) (xs : List V) (x : V) :
    run u xs x = u x + xs.count x := by
  induction xs generalizing u with
  | nil => simp only [run_nil, List.count_nil, Nat.add_zero]
  | cons y ys ih =>
      rw [run_cons, ih, List.count_cons]
      by_cases hy : y = x
      · subst y
        simp only [bump_same, beq_self_eq_true, ite_true]
        omega
      · have hxy := Ne.symm hy
        simp only [bump_other u hxy, beq_iff_eq, if_neg hy, Nat.add_zero]

private theorem path_mass (route : Routing V) (initial : V → ℤ) (u : V → ℕ)
    (f : ℕ → V) (n : ℕ)
    (hedge : ∀ i < n, route (f i) (run u (pathWord f i) (f i)) = f (i + 1)) (y : V) :
    particles route initial (run u (pathWord f n)) y =
      particles route initial u y - (if y = f 0 then 1 else 0) +
        (if y = f n then 1 else 0) := by
  induction n with
  | zero =>
      change particles route initial u y = particles route initial u y - _ + _
      omega
  | succ n ih =>
      rw [pathWord_succ, run_append]
      change particles route initial (bump (run u (pathWord f n)) (f n)) y = _
      rw [particles_bump, ih (fun i hi => hedge i (by omega)), hedge n (by omega)]
      simp only [eq_comm (a := f (n + 1)) (b := y)]
      omega

private theorem path_legal (route : Routing V) (initial capacity : V → ℤ)
    (u : V → ℕ) (f : ℕ → V) (n : ℕ)
    (hedge : ∀ i < n, route (f i) (run u (pathWord f i) (f i)) = f (i + 1))
    (hbefore : ∀ i < n, capacity (f i) < particles route initial u (f i) -
      (if f i = f 0 then 1 else 0) + 1) :
    LegalFrom route initial capacity Set.univ u (pathWord f n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
      rw [pathWord_succ, legalFrom_append]
      refine ⟨ih (fun i hi => hedge i (by omega)) (fun i hi => hbefore i (by omega)),
        Set.mem_univ _, ?_, trivial⟩
      rw [path_mass route initial u f n (fun i hi => hedge i (by omega)), if_pos rfl]
      exact hbefore n (by omega)

private def initialPair (p q : V) : V → ℤ :=
  fun x => (if x = p then 1 else 0) + (if x = q then 1 else 0)

private def seedCapacity (A : Set V) : V → ℤ := fun x => if x ∈ A then 0 else 1

/-- A finite stack-read path stops exactly at its first unoccupied site. -/
private structure ReleasePath (route : Routing V) (A : Set V) (u : V → ℕ) (p : V) where
  pos : ℕ → V
  time : ℕ
  start : pos 0 = p
  step : ∀ i < time, route (pos i) (run u (pathWord pos i) (pos i)) = pos (i + 1)
  before : ∀ i < time, pos i ∈ A
  finish : pos time ∉ A

private theorem two_release_legal (route : Routing V) (A : Set V) (p q : V)
    (f : ReleasePath route A (fun _ => 0) p)
    (g : ReleasePath route (A ∪ {f.pos f.time}) (run (fun _ => 0) (pathWord f.pos f.time)) q) :
    LegalFrom route (initialPair p q) (seedCapacity A) Set.univ (fun _ => 0)
      (pathWord f.pos f.time ++ pathWord g.pos g.time) := by
  rw [legalFrom_append]
  constructor
  · apply path_legal route (initialPair p q) (seedCapacity A) _ _ _ f.step
    intro i hi
    rw [particles_zero, f.start]
    simp only [initialPair, seedCapacity, if_pos (f.before i hi)]
    split_ifs <;> omega
  · apply path_legal route (initialPair p q) (seedCapacity A) _ _ _ g.step
    intro i hi
    rw [path_mass route (initialPair p q) (fun _ => 0) _ _ f.step,
      particles_zero, f.start, g.start]
    simp only [initialPair]
    rcases g.before i hi with hA | hs
    · simp only [seedCapacity, if_pos hA]
      split_ifs <;> omega
    · have hs' : g.pos i = f.pos f.time := hs
      simp only [seedCapacity]
      rw [if_pos hs']
      split_ifs <;> omega

private theorem two_release_mass (route : Routing V) (A : Set V) (p q : V)
    (f : ReleasePath route A (fun _ => 0) p)
    (g : ReleasePath route (A ∪ {f.pos f.time}) (run (fun _ => 0) (pathWord f.pos f.time)) q)
    (y : V) :
    particles route (initialPair p q)
      (run (fun _ => 0) (pathWord f.pos f.time ++ pathWord g.pos g.time)) y =
      (if y = f.pos f.time then 1 else 0) + (if y = g.pos g.time then 1 else 0) := by
  rw [run_append, path_mass route (initialPair p q) _ _ _ g.step,
    path_mass route (initialPair p q) _ _ _ f.step, particles_zero, f.start, g.start]
  simp only [initialPair]
  omega

private theorem two_release_stable (route : Routing V) (A : Set V) (p q : V)
    (f : ReleasePath route A (fun _ => 0) p)
    (g : ReleasePath route (A ∪ {f.pos f.time}) (run (fun _ => 0) (pathWord f.pos f.time)) q) :
    Stable route (initialPair p q) (seedCapacity A) Set.univ
      (run (fun _ => 0) (pathWord f.pos f.time ++ pathWord g.pos g.time)) := by
  intro y _
  rw [two_release_mass]
  have hfirst := f.finish
  have hsecond := g.finish
  simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hsecond
  unfold seedCapacity
  split_ifs <;> subst_vars <;> simp_all

/-- Both release orders have identical occupied sets, on the same site stacks. -/
private theorem two_release_abelian (route : Routing V) (A : Set V) (p q : V)
    (f : ReleasePath route A (fun _ => 0) p)
    (g : ReleasePath route (A ∪ {f.pos f.time}) (run (fun _ => 0) (pathWord f.pos f.time)) q)
    (f' : ReleasePath route A (fun _ => 0) q)
    (g' : ReleasePath route (A ∪ {f'.pos f'.time}) (run (fun _ => 0) (pathWord f'.pos f'.time)) p) :
    A ∪ {f.pos f.time, g.pos g.time} = A ∪ {f'.pos f'.time, g'.pos g'.time} := by
  have hinitial : initialPair q p = initialPair p q := by
    funext x
    exact add_comm _ _
  have hl := two_release_legal route A p q f g
  have hr := two_release_legal route A q p f' g'
  have hsl := two_release_stable route A p q f g
  have hsr := two_release_stable route A q p f' g'
  rw [hinitial] at hr hsr
  have hm := abelian_particles route (initialPair p q) (seedCapacity A) Set.univ
    (fun _ => 0) _ _ hl hr hsl hsr
  ext y
  have hy := congrFun hm y
  rw [two_release_mass route A p q f g,
    ← hinitial, two_release_mass route A q p f' g'] at hy
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  split_ifs at hy <;> simp_all


/-- Two initially empty sites on a two-site carrier give a concrete finite certificate. -/
example : (∅ : Set (Fin 2)) ∪ {(0 : Fin 2), (1 : Fin 2)} =
    (∅ : Set (Fin 2)) ∪ {(1 : Fin 2), (0 : Fin 2)} := by
  let route : Routing (Fin 2) := fun _ _ => 0
  let f : ReleasePath route ∅ (fun _ => 0) 0 :=
    { pos := fun _ => 0, time := 0, start := rfl
      step := by intro i hi; omega
      before := by intro i hi; omega
      finish := by simp }
  let f' : ReleasePath route ∅ (fun _ => 0) 1 :=
    { pos := fun _ => 1, time := 0, start := rfl
      step := by intro i hi; omega
      before := by intro i hi; omega
      finish := by simp }
  let g : ReleasePath route (∅ ∪ {f.pos f.time})
      (run (fun _ => 0) (pathWord f.pos f.time)) 1 :=
    { pos := fun _ => 1, time := 0, start := rfl
      step := by intro i hi; omega
      before := by intro i hi; omega
      finish := by change (1 : Fin 2) ∉ (∅ : Set (Fin 2)) ∪ {0}; norm_num }
  let g' : ReleasePath route (∅ ∪ {f'.pos f'.time})
      (run (fun _ => 0) (pathWord f'.pos f'.time)) 0 :=
    { pos := fun _ => 0, time := 0, start := rfl
      step := by intro i hi; omega
      before := by intro i hi; omega
      finish := by change (0 : Fin 2) ∉ (∅ : Set (Fin 2)) ∪ {1}; norm_num }
  exact two_release_abelian route ∅ 0 1 f g f' g'

end
end IdlaCyl.OuterFinite

/-
Finite restrictions of the actual cylinder-stack explorer.
Source: paper/idla-cylinder-gff.tex, tex:1331-1351,1391-1396.
-/

attribute [local instance] Classical.propDecidable
namespace IdlaCyl.OuterFinite
open IdlaCyl.Stack
noncomputable section

private def encodeSite (B : Base) (D : Finset (Site B)) (d₀ : ↥D) (x : Site B) : ↥D :=
  if hx : x ∈ D then ⟨x, hx⟩ else d₀

private theorem encodeSite_val (B : Base) (D : Finset (Site B)) (d₀ : ↥D)
    (x : Site B) (hx : x ∈ D) : (encodeSite B D d₀ x).val = x := by
  simp only [encodeSite, dif_pos hx]

private def encodeRoute (B : Base) (D : Finset (Site B)) (d₀ : ↥D)
    (r : OuterStacks B) : Routing ↥D :=
  fun x n => encodeSite B D d₀ (r (x.val, n))

private theorem encode_run (B : Base) (D : Finset (Site B)) (d₀ : ↥D)
    (X : ℕ → Site B) (n : ℕ) (hX : ∀ i < n, X i ∈ D) (u : ↥D → ℕ) (x : ↥D) :
    run u (pathWord (fun i => encodeSite B D d₀ (X i)) n) x =
      u x + outerVisits B X n x.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pathWord_succ, run_append]
      change bump (run u (pathWord (fun i => encodeSite B D d₀ (X i)) n))
        (encodeSite B D d₀ (X n)) x = _
      rw [bump, ih (fun i hi => hX i (by omega))]
      have heq : (x = encodeSite B D d₀ (X n)) ↔ X n = x.val := by
        rw [Subtype.ext_iff, encodeSite_val B D d₀ _ (hX n (by omega))]
        exact eq_comm
      simp only [outerVisits]
      by_cases h : X n = x.val
      · simp only [if_pos h, if_pos (heq.mpr h)]
        omega
      · simp only [if_neg h, if_neg (fun hx => h (heq.mp hx)), Nat.add_zero]

private def liftRelease (B : Base) (D : Finset (Site B)) (d₀ : ↥D)
    (r : OuterStacks B) (A : Set (Site B)) (w : Site B → ℕ) (u : ↥D → ℕ)
    (hu : ∀ x : ↥D, u x = w x.val) (p : Site B) (hp : p ∈ D)
    (X : ℕ → Site B) (n : ℕ) (hstart : X 0 = p)
    (hstep : ∀ i < n, X (i + 1) = r (X i, w (X i) + outerVisits B X i (X i)))
    (hbefore : ∀ i < n, X i ∈ A) (hfinish : X n ∉ A)
    (hD : ∀ i ≤ n, X i ∈ D) :
    ReleasePath (encodeRoute B D d₀ r) {x : ↥D | x.val ∈ A} u ⟨p, hp⟩ where
  pos := fun i => encodeSite B D d₀ (X i)
  time := n
  start := by
    apply Subtype.ext
    rw [encodeSite_val B D d₀ _ (hD 0 (Nat.zero_le _)), hstart]
  step := by
    intro i hi
    unfold encodeRoute
    rw [encode_run B D d₀ X i (fun j hj => hD j (by omega)) u,
      hu, encodeSite_val B D d₀ _ (hD i (by omega))]
    exact congrArg (encodeSite B D d₀) (hstep i hi).symm
  before := by
    intro i hi
    change (encodeSite B D d₀ (X i)).val ∈ A
    rw [encodeSite_val B D d₀ _ (hD i (by omega))]
    exact hbefore i hi
  finish := by
    change (encodeSite B D d₀ (X n)).val ∉ A
    rw [encodeSite_val B D d₀ _ (hD n le_rfl)]
    exact hfinish


private theorem run_visits (B : Base) (u : Site B → ℕ) (X : ℕ → Site B)
    (n : ℕ) (x : Site B) :
    run u (pathWord X n) x = u x + outerVisits B X n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pathWord_succ, run_append]
      change bump (run u (pathWord X n)) (X n) x = _
      rw [bump, ih]
      simp only [outerVisits]
      by_cases hx : X n = x
      · subst x
        simp only [ite_true]
        omega
      · simp only [if_neg hx, if_neg (Ne.symm hx), Nat.add_zero]

private theorem preimage_seed_insert (B : Base) (D : Finset (Site B)) (d₀ : ↥D)
    (A : Set (Site B)) (x : Site B) (hx : x ∈ D) :
    {d : ↥D | d.val ∈ A ∪ {x}} =
      {d : ↥D | d.val ∈ A} ∪ {encodeSite B D d₀ x} := by
  ext d
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  rw [Subtype.ext_iff, encodeSite_val B D d₀ x hx]

private def pathRange (B : Base) (X : ℕ → Site B) (n : ℕ) : Finset (Site B) :=
  (Finset.range (n + 1)).image X

private theorem mem_pathRange (B : Base) (X : ℕ → Site B) (n i : ℕ) (hi : i ≤ n) :
    X i ∈ pathRange B X n := Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩

/-- Finite cylinder-stack release certificates reduce to the finite abelian theorem. -/
private theorem raw_two_release_abelian (B : Base) (r : OuterStacks B) (A : Set (Site B))
    (p q : Site B)
    (f : ReleasePath (fun x n => r (x, n)) A (fun _ => 0) p)
    (g : ReleasePath (fun x n => r (x, n)) (A ∪ {f.pos f.time})
      (run (fun _ => 0) (pathWord f.pos f.time)) q)
    (f' : ReleasePath (fun x n => r (x, n)) A (fun _ => 0) q)
    (g' : ReleasePath (fun x n => r (x, n)) (A ∪ {f'.pos f'.time})
      (run (fun _ => 0) (pathWord f'.pos f'.time)) p) :
    A ∪ {f.pos f.time, g.pos g.time} = A ∪ {f'.pos f'.time, g'.pos g'.time} := by
  let D := pathRange B f.pos f.time ∪ (pathRange B g.pos g.time ∪
    (pathRange B f'.pos f'.time ∪ pathRange B g'.pos g'.time))
  have hD₁ (i : ℕ) (hi : i ≤ f.time) : f.pos i ∈ D :=
    Finset.mem_union_left _ (mem_pathRange B _ _ i hi)
  have hD₂ (i : ℕ) (hi : i ≤ g.time) : g.pos i ∈ D :=
    Finset.mem_union_right _ (Finset.mem_union_left _ (mem_pathRange B _ _ i hi))
  have hD₃ (i : ℕ) (hi : i ≤ f'.time) : f'.pos i ∈ D :=
    Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_union_left _ (mem_pathRange B _ _ i hi)))
  have hD₄ (i : ℕ) (hi : i ≤ g'.time) : g'.pos i ∈ D :=
    Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_union_right _ (mem_pathRange B _ _ i hi)))
  have hp : p ∈ D := f.start ▸ hD₁ 0 (Nat.zero_le _)
  have hq : q ∈ D := f'.start ▸ hD₃ 0 (Nat.zero_le _)
  let d₀ : ↥D := ⟨p, hp⟩
  let route := encodeRoute B D d₀ r
  let seed : Set ↥D := {x | x.val ∈ A}
  have hstep₁ (i : ℕ) (hi : i < f.time) :
      f.pos (i + 1) = r (f.pos i, 0 + outerVisits B f.pos i (f.pos i)) := by
    have h := f.step i hi
    rw [run_visits] at h
    exact h.symm
  let lf := liftRelease B D d₀ r A (fun _ => 0) (fun _ => 0) (fun _ => rfl)
    p hp f.pos f.time f.start hstep₁ f.before f.finish hD₁
  have hu₁ (x : ↥D) :
      run (fun _ => 0) (pathWord (fun i => encodeSite B D d₀ (f.pos i)) f.time) x =
        run (fun _ => 0) (pathWord f.pos f.time) x.val := by
    rw [encode_run B D d₀ f.pos f.time (fun i hi => hD₁ i (by omega)), run_visits]
  have hstep₂ (i : ℕ) (hi : i < g.time) :
      g.pos (i + 1) = r (g.pos i,
        run (fun _ => 0) (pathWord f.pos f.time) (g.pos i) +
          outerVisits B g.pos i (g.pos i)) := by
    have h := g.step i hi
    rw [run_visits] at h
    exact h.symm
  let lgRaw := liftRelease B D d₀ r (A ∪ {f.pos f.time})
    (run (fun _ => 0) (pathWord f.pos f.time))
    (run (fun _ => 0) (pathWord (fun i => encodeSite B D d₀ (f.pos i)) f.time))
    hu₁ q hq g.pos g.time g.start hstep₂ g.before g.finish hD₂
  let lg : ReleasePath route (seed ∪ {lf.pos lf.time})
      (run (fun _ => 0) (pathWord lf.pos lf.time)) ⟨q, hq⟩ :=
    { pos := fun i => encodeSite B D d₀ (g.pos i)
      time := g.time
      start := lgRaw.start
      step := lgRaw.step
      before := fun i hi => by
        have h := lgRaw.before i hi
        change encodeSite B D d₀ (g.pos i) ∈ {x : ↥D | x.val ∈ A ∪ {f.pos f.time}} at h
        rw [preimage_seed_insert B D d₀ A _ (hD₁ f.time le_rfl)] at h
        exact h
      finish := by
        have h := lgRaw.finish
        change encodeSite B D d₀ (g.pos g.time) ∉ {x : ↥D | x.val ∈ A ∪ {f.pos f.time}} at h
        rw [preimage_seed_insert B D d₀ A _ (hD₁ f.time le_rfl)] at h
        exact h }
  have hstep₃ (i : ℕ) (hi : i < f'.time) :
      f'.pos (i + 1) = r (f'.pos i, 0 + outerVisits B f'.pos i (f'.pos i)) := by
    have h := f'.step i hi
    rw [run_visits] at h
    exact h.symm
  let lf' := liftRelease B D d₀ r A (fun _ => 0) (fun _ => 0) (fun _ => rfl)
    q hq f'.pos f'.time f'.start hstep₃ f'.before f'.finish hD₃
  have hu₃ (x : ↥D) :
      run (fun _ => 0) (pathWord (fun i => encodeSite B D d₀ (f'.pos i)) f'.time) x =
        run (fun _ => 0) (pathWord f'.pos f'.time) x.val := by
    rw [encode_run B D d₀ f'.pos f'.time (fun i hi => hD₃ i (by omega)), run_visits]
  have hstep₄ (i : ℕ) (hi : i < g'.time) :
      g'.pos (i + 1) = r (g'.pos i,
        run (fun _ => 0) (pathWord f'.pos f'.time) (g'.pos i) +
          outerVisits B g'.pos i (g'.pos i)) := by
    have h := g'.step i hi
    rw [run_visits] at h
    exact h.symm
  let lgRaw' := liftRelease B D d₀ r (A ∪ {f'.pos f'.time})
    (run (fun _ => 0) (pathWord f'.pos f'.time))
    (run (fun _ => 0) (pathWord (fun i => encodeSite B D d₀ (f'.pos i)) f'.time))
    hu₃ p hp g'.pos g'.time g'.start hstep₄ g'.before g'.finish hD₄
  let lg' : ReleasePath route (seed ∪ {lf'.pos lf'.time})
      (run (fun _ => 0) (pathWord lf'.pos lf'.time)) d₀ :=
    { pos := fun i => encodeSite B D d₀ (g'.pos i)
      time := g'.time
      start := lgRaw'.start
      step := lgRaw'.step
      before := fun i hi => by
        have h := lgRaw'.before i hi
        change encodeSite B D d₀ (g'.pos i) ∈ {x : ↥D | x.val ∈ A ∪ {f'.pos f'.time}} at h
        rw [preimage_seed_insert B D d₀ A _ (hD₃ f'.time le_rfl)] at h
        exact h
      finish := by
        have h := lgRaw'.finish
        change encodeSite B D d₀ (g'.pos g'.time) ∉ {x : ↥D | x.val ∈ A ∪ {f'.pos f'.time}} at h
        rw [preimage_seed_insert B D d₀ A _ (hD₃ f'.time le_rfl)] at h
        exact h }
  have heq := two_release_abelian route seed d₀ ⟨q, hq⟩ lf lg lf' lg'
  ext z
  by_cases hz : z ∈ D
  · have hmem := congrArg (fun E : Set ↥D => (⟨z, hz⟩ : ↥D) ∈ E) heq
    change (z ∈ A ∨ z = f.pos f.time ∨ z = g.pos g.time) ↔
      (z ∈ A ∨ z = f'.pos f'.time ∨ z = g'.pos g'.time)
    have hv₁ := encodeSite_val B D d₀ (f.pos f.time) (hD₁ _ le_rfl)
    have hv₂ := encodeSite_val B D d₀ (g.pos g.time) (hD₂ _ le_rfl)
    have hv₃ := encodeSite_val B D d₀ (f'.pos f'.time) (hD₃ _ le_rfl)
    have hv₄ := encodeSite_val B D d₀ (g'.pos g'.time) (hD₄ _ le_rfl)
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    change ((z ∈ A ∨ (⟨z, hz⟩ : ↥D) = encodeSite B D d₀ (f.pos f.time) ∨
        (⟨z, hz⟩ : ↥D) = encodeSite B D d₀ (g.pos g.time)) =
      (z ∈ A ∨ (⟨z, hz⟩ : ↥D) = encodeSite B D d₀ (f'.pos f'.time) ∨
        (⟨z, hz⟩ : ↥D) = encodeSite B D d₀ (g'.pos g'.time))) at hmem
    simp only [Subtype.ext_iff, hv₁, hv₂, hv₃, hv₄] at hmem
    exact Iff.of_eq hmem
  · have hn₁ : z ≠ f.pos f.time := fun h => hz (h ▸ hD₁ _ le_rfl)
    have hn₂ : z ≠ g.pos g.time := fun h => hz (h ▸ hD₂ _ le_rfl)
    have hn₃ : z ≠ f'.pos f'.time := fun h => hz (h ▸ hD₃ _ le_rfl)
    have hn₄ : z ≠ g'.pos g'.time := fun h => hz (h ▸ hD₄ _ le_rfl)
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      hn₁, hn₂, hn₃, hn₄, or_false]

end
end IdlaCyl.OuterFinite

/-
Actual sequential explorers stabilize the same cylinder stacks.
Source: paper/idla-cylinder-gff.tex, tex:1331-1351,1391-1396.
-/

attribute [local instance] Classical.propDecidable
namespace IdlaCyl.OuterFinite
open IdlaCyl.Stack
open MeasureTheory
noncomputable section

private def makeRelease (B : Base) (r : OuterStacks B) (A : Set (Site B))
    (u : Site B → ℕ) (p : Site B) (X : ℕ → Site B) (hstart : X 0 = p)
    (hread : ∀ i, X (i + 1) = r (X i, u (X i) + outerVisits B X i (X i)))
    (hfinite : exitTime' B A X ≠ ⊤) :
    ReleasePath (fun x n => r (x, n)) A u p where
  pos := X
  time := (exitTime' B A X).toNat
  start := hstart
  step := by
    intro i _
    rw [run_visits]
    exact (hread i).symm
  before := by
    intro i hi
    have ht : exitTime' B A X = ((exitTime' B A X).toNat : ℕ∞) :=
      (ENat.coe_toNat hfinite).symm
    exact not_not.mp ((hittingAfter_zero_eq_coe_iff.mp ht).2 i hi)
  finish := by
    have ht : exitTime' B A X = ((exitTime' B A X).toNat : ℕ∞) :=
      (ENat.coe_toNat hfinite).symm
    exact (hittingAfter_zero_eq_coe_iff.mp ht).1

private theorem makeRelease_endpoint (B : Base) (r : OuterStacks B) (A : Set (Site B))
    (u : Site B → ℕ) (p : Site B) (X : ℕ → Site B) (hstart : X 0 = p)
    (hread : ∀ i, X (i + 1) = r (X i, u (X i) + outerVisits B X i (X i)))
    (hfinite : exitTime' B A X ≠ ⊤) :
    (makeRelease B r A u p X hstart hread hfinite).pos
      (makeRelease B r A u p X hstart hread hfinite).time = exitSite' B A X := by
  change X (exitTime' B A X).toNat = X (WithTop.untopA (exitTime' B A X))
  rw [untopA_eq_toNat hfinite]

private theorem outerStackRemainder_eq_run (B : Base) (A : Set (Site B)) (p : Site B)
    (r : OuterStacks B) (hfinite : exitTime' B A (outerStackWalk B p r) ≠ ⊤) :
    outerStackRemainder B A p r = outerUnused B
      (run (fun _ => 0) (pathWord (outerStackWalk B p r)
        (exitTime' B A (outerStackWalk B p r)).toNat)) r := by
  unfold outerStackRemainder
  rw [untopA_eq_toNat hfinite]
  have hu : outerVisits B (outerStackWalk B p r)
      (exitTime' B A (outerStackWalk B p r)).toNat =
      run (fun _ => 0) (pathWord (outerStackWalk B p r)
        (exitTime' B A (outerStackWalk B p r)).toNat) := by
    funext x
    rw [run_visits, Nat.zero_add]
  rw [hu]

/-- Genuine finite sequential releases in either order stabilize the same site stacks. -/
theorem outerStackPair_commute_of_finite (B : Base) (A : Set (Site B)) (p q : Site B)
    (r : OuterStacks B)
    (hp : exitTime' B A (outerStackWalk B p r) ≠ ⊤)
    (hq : exitTime' B (addWalk B A (outerStackWalk B p r))
      (outerStackWalk B q (outerStackRemainder B A p r)) ≠ ⊤)
    (hq' : exitTime' B A (outerStackWalk B q r) ≠ ⊤)
    (hp' : exitTime' B (addWalk B A (outerStackWalk B q r))
      (outerStackWalk B p (outerStackRemainder B A q r)) ≠ ⊤) :
    outerStackPair B A p q r = outerStackPair B A q p r := by
  let X := outerStackWalk B p r
  let Y := outerStackWalk B q (outerStackRemainder B A p r)
  let X' := outerStackWalk B q r
  let Y' := outerStackWalk B p (outerStackRemainder B A q r)
  have hread (i : ℕ) : X (i + 1) = r (X i, 0 + outerVisits B X i (X i)) := by
    simpa only [Nat.zero_add] using outerStackWalk_succ B p r i
  let f := makeRelease B r A (fun _ => 0) p X rfl hread hp
  have hf : f.pos f.time = exitSite' B A X := makeRelease_endpoint B r A _ p X rfl hread hp
  have hreadY (i : ℕ) : Y (i + 1) = r (Y i,
      run (fun _ => 0) (pathWord f.pos f.time) (Y i) + outerVisits B Y i (Y i)) := by
    have hs := outerStackWalk_succ B q (outerStackRemainder B A p r) i
    change Y (i + 1) = outerStackRemainder B A p r (Y i, outerVisits B Y i (Y i)) at hs
    rw [outerStackRemainder_eq_run B A p r hp] at hs
    exact hs
  have hqfin : exitTime' B (A ∪ {f.pos f.time}) Y ≠ ⊤ := by
    rw [hf]
    exact hq
  let g := makeRelease B r (A ∪ {f.pos f.time})
    (run (fun _ => 0) (pathWord f.pos f.time)) q Y rfl hreadY hqfin
  have hg : g.pos g.time = exitSite' B (addWalk B A X) Y := by
    have he := makeRelease_endpoint B r (A ∪ {f.pos f.time})
      (run (fun _ => 0) (pathWord f.pos f.time)) q Y rfl hreadY hqfin
    exact he.trans (congrArg (fun s => exitSite' B (A ∪ {s}) Y) hf)
  have hread' (i : ℕ) : X' (i + 1) = r (X' i, 0 + outerVisits B X' i (X' i)) := by
    simpa only [Nat.zero_add] using outerStackWalk_succ B q r i
  let f' := makeRelease B r A (fun _ => 0) q X' rfl hread' hq'
  have hf' : f'.pos f'.time = exitSite' B A X' :=
    makeRelease_endpoint B r A _ q X' rfl hread' hq'
  have hreadY' (i : ℕ) : Y' (i + 1) = r (Y' i,
      run (fun _ => 0) (pathWord f'.pos f'.time) (Y' i) + outerVisits B Y' i (Y' i)) := by
    have hs := outerStackWalk_succ B p (outerStackRemainder B A q r) i
    change Y' (i + 1) = outerStackRemainder B A q r (Y' i, outerVisits B Y' i (Y' i)) at hs
    rw [outerStackRemainder_eq_run B A q r hq'] at hs
    exact hs
  have hpfin : exitTime' B (A ∪ {f'.pos f'.time}) Y' ≠ ⊤ := by
    rw [hf']
    exact hp'
  let g' := makeRelease B r (A ∪ {f'.pos f'.time})
    (run (fun _ => 0) (pathWord f'.pos f'.time)) p Y' rfl hreadY' hpfin
  have hg' : g'.pos g'.time = exitSite' B (addWalk B A X') Y' := by
    have he := makeRelease_endpoint B r (A ∪ {f'.pos f'.time})
      (run (fun _ => 0) (pathWord f'.pos f'.time)) p Y' rfl hreadY' hpfin
    exact he.trans (congrArg (fun s => exitSite' B (A ∪ {s}) Y') hf')
  have heq := raw_two_release_abelian B r A p q f g f' g'
  have hsets : A ∪ {exitSite' B A X, exitSite' B (addWalk B A X) Y} =
      A ∪ {exitSite' B A X', exitSite' B (addWalk B A X') Y'} := by
    calc
      _ = A ∪ {f.pos f.time, g.pos g.time} :=
        congrArg₂ (fun s t => A ∪ {s, t}) hf.symm hg.symm
      _ = _ := heq
      _ = _ := congrArg₂ (fun s t => A ∪ {s, t}) hf' hg'
  ext z
  have hz := Set.ext_iff.mp hsets z
  simpa only [outerStackPair, addWalk, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, or_assoc] using hz

end
end IdlaCyl.OuterFinite
