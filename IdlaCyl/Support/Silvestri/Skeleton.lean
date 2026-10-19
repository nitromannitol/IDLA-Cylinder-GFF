import IdlaCyl.Support.Cylinder
import IdlaCyl.Support.FirstHit
import IdlaCyl.Support.Silvestri.Bridge
import Mathlib

/-!
# Skeletons of cylinder paths and their weights

A list of sites is read as the successive positions of a path, starting from a
site `p` that is not in the list. Its *skeleton* records the vertical increment
of each step, and its *horizontal list* records the base vertex after each step
that keeps the height. Conversely, a list of increments in `{-1, 0, 1}` together
with a list of base vertices of the right length rebuilds a path, which is what
`assemble` does.

The file proves the following facts, all about finite lists.

* `assemble` keeps the number of steps, its skeleton is the given list of
  increments, and its horizontal list is the given list of base vertices.
* A path all of whose steps have positive kernel entry is recovered from its
  skeleton and its horizontal list.
* The heights of an assembled path depend only on the starting height and on
  the increments.
* The last base vertex of an assembled path is the last entry of the start
  base vertex followed by the base list.
* The weight of an assembled path is the product of `cylKernel` along it. It
  is `ENNReal.ofReal` of a skeleton weight, a product of `1/2` and `1/4`, times
  a product of the lazy base kernel along the base list. This weight is the
  value of `IdlaCyl.pathWeight`.
* For a list of base vertices, the product of the lazy base kernel along it is
  `Silvestri.pathWeight` of the corresponding tuple, and the last entry of the
  list is `Silvestri.pathEnd`.

No measure theory appears in this file.
-/

namespace IdlaCyl.Silvestri

open scoped BigOperators

/-- The vertical increments of a list of sites, read as the successive positions
of a path that starts at `p`. -/
def skel {B : Base} (p : Site B) : List (Site B) → List ℤ
  | [] => []
  | q :: c => (q.2 - p.2) :: skel q c

/-- The base vertices after the steps of a list of sites, read from `p`, that keep
the height. -/
def hors {B : Base} (p : Site B) : List (Site B) → List B.V
  | [] => []
  | q :: c => if q.2 - p.2 = 0 then q.1 :: hors q c else hors q c

/-- Rebuild a list of sites from its vertical increments `τ` and its base list `ws`,
starting at `p`. A zero increment takes the next base vertex of `ws`; any other
increment keeps the base vertex of the current site. A zero increment with `ws`
exhausted keeps the base vertex of the current site as well. The statements below
assume `ws` has exactly as many entries as `τ` has zeros, so this case does not
occur for them. -/
def assemble {B : Base} (p : Site B) : List ℤ → List B.V → List (Site B)
  | [], _ => []
  | d :: τ, ws =>
    if d = 0 then
      match ws with
      | [] => (p.1, p.2) :: assemble p τ []
      | w :: ws' => (w, p.2) :: assemble (w, p.2) τ ws'
    else (p.1, p.2 + d) :: assemble (p.1, p.2 + d) τ ws

/-- The product of `1/2` for each zero increment and `1/4` for each other increment:
the weight of the vertical and horizontal steps, without their base factors. -/
noncomputable def skelWeight (τ : List ℤ) : ℝ :=
  (τ.map fun d => if d = 0 then (1 / 2 : ℝ) else 1 / 4).prod

/-- The product of the lazy base kernel along `x :: ws`. -/
noncomputable def listPathWeight (B : Base) (x : B.V) : List B.V → ℝ
  | [] => 1
  | w :: ws => B.P x w * listPathWeight B w ws

section

variable {B : Base}

/-! ### Assembling and reading back -/

/-- `assemble` keeps the number of steps. -/
theorem length_assemble (p : Site B) (τ : List ℤ) (ws : List B.V) :
    (assemble p τ ws).length = τ.length := by
  induction τ generalizing p ws with
  | nil => rfl
  | cons d τ ih =>
    by_cases hd : d = 0
    · rcases ws with _ | ⟨w, ws'⟩ <;> simp [assemble, hd, ih]
    · simp [assemble, hd, ih]

/-- The vertical increments of an assembled list are the given increments. -/
theorem skel_assemble (p : Site B) (τ : List ℤ) (ws : List B.V) :
    skel p (assemble p τ ws) = τ := by
  induction τ generalizing p ws with
  | nil => rfl
  | cons d τ ih =>
    by_cases hd : d = 0
    · rcases ws with _ | ⟨w, ws'⟩ <;> simp [assemble, skel, hd, ih]
    · simp [assemble, skel, hd, ih]

/-- The base vertices of the zero increments of an assembled list are the given base
vertices, when there is one for each zero increment. -/
theorem hors_assemble (p : Site B) (τ : List ℤ) (ws : List B.V)
    (hws : ws.length = τ.count 0) : hors p (assemble p τ ws) = ws := by
  induction τ generalizing p ws with
  | nil =>
    cases ws with
    | nil => rfl
    | cons w ws => simp at hws
  | cons d τ ih =>
    by_cases hd : d = 0
    · subst hd
      rcases ws with _ | ⟨w, ws'⟩
      · simp at hws
      · have hws' : ws'.length = τ.count 0 := by simpa using hws
        simp [assemble, hors, ih (w, p.2) ws' hws']
    · have hws' : ws.length = τ.count 0 := by simpa [hd] using hws
      simp [assemble, hors, hd, ih (p.1, p.2 + d) ws hws']

/-- A step of positive kernel entry either keeps the height or keeps the base vertex. -/
theorem base_eq_of_cylKernel_pos {p q : Site B} (h : 0 < cylKernel B p q) (hne : p.2 ≠ q.2) :
    p.1 = q.1 := by
  unfold cylKernel at h
  by_cases hA : p.1 = q.1 ∧ (p.2 - q.2).natAbs = 1
  · exact hA.1
  · simp [hA, hne] at h

/-- A list of sites all of whose steps from `p` have positive kernel entry is
recovered from its skeleton and its horizontal list. -/
theorem assemble_skel_hors (p : Site B) (c : List (Site B))
    (hc : List.IsChain (fun a b => 0 < cylKernel B a b) (p :: c)) :
    assemble p (skel p c) (hors p c) = c := by
  induction c generalizing p with
  | nil => rfl
  | cons q c ih =>
    rw [List.isChain_cons_cons] at hc
    obtain ⟨hpq, hc'⟩ := hc
    by_cases h0 : q.2 - p.2 = 0
    · have hq : (q.1, p.2) = q := Prod.ext rfl (sub_eq_zero.mp h0).symm
      have e1 : skel p (q :: c) = 0 :: skel q c := by simp [skel, h0]
      have e2 : hors p (q :: c) = q.1 :: hors q c := by simp [hors, h0]
      rw [e1, e2]
      simp only [assemble]
      simp [hq, ih q hc']
    · have hv : p.1 = q.1 := base_eq_of_cylKernel_pos hpq (fun h => h0 (by omega))
      have e1 : skel p (q :: c) = (q.2 - p.2) :: skel q c := rfl
      have e2 : hors p (q :: c) = hors q c := by simp [hors, h0]
      have hq : (p.1, p.2 + (q.2 - p.2)) = q := Prod.ext hv (by simp)
      rw [e1, e2]
      simp only [assemble, h0, if_false]
      rw [hq, ih q hc']

/-- The heights of an assembled list depend only on the starting height and on the
increments. -/
theorem map_snd_assemble (τ : List ℤ) : ∀ (p q : Site B) (ws ws' : List B.V),
    p.2 = q.2 → (assemble p τ ws).map Prod.snd = (assemble q τ ws').map Prod.snd := by
  induction τ with
  | nil => intros; rfl
  | cons d τ ih =>
    intro p q ws ws' hpq
    by_cases hd : d = 0
    · rcases ws with _ | ⟨w, ws⟩ <;> rcases ws' with _ | ⟨w', ws'⟩ <;>
        simp only [assemble, hd, ↓reduceIte, List.map_cons, hpq] <;>
        exact congrArg (List.cons _) (ih _ _ _ _ (by simp [hpq]))
    · simp only [assemble, hd, ↓reduceIte, List.map_cons, hpq]
      exact congrArg (List.cons _) (ih _ _ _ _ (by simp))

/-- The last base vertex of an assembled list is the last entry of the start base
vertex followed by the base list. -/
theorem fst_getLast_assemble (τ : List ℤ) : ∀ (p : Site B) (ws : List B.V),
    ws.length = τ.count 0 →
    ((p :: assemble p τ ws).getLast (List.cons_ne_nil _ _)).1
      = (p.1 :: ws).getLast (List.cons_ne_nil _ _) := by
  induction τ with
  | nil =>
    intro p ws hws
    cases ws with
    | nil => rfl
    | cons w ws => simp at hws
  | cons d τ ih =>
    intro p ws hws
    by_cases hd : d = 0
    · subst hd
      rcases ws with _ | ⟨w, ws'⟩
      · simp at hws
      · have hws' : ws'.length = τ.count 0 := by simpa using hws
        have := ih (w, p.2) ws' hws'
        simpa [assemble] using this
    · have hws' : ws.length = τ.count 0 := by simpa [hd] using hws
      have := ih (p.1, p.2 + d) ws hws'
      simpa [assemble, hd] using this


/-! ### Weights -/

/-- A list read at an index inside its length does not depend on the default value. -/
theorem getD_congr_default {α : Type*} (l : List α) {i : ℕ} (hi : i < l.length) (d d' : α) :
    l.getD i d = l.getD i d' := by
  simp [hi]

/-- The skeleton weight splits off the first increment. -/
theorem skelWeight_cons (d : ℤ) (τ : List ℤ) :
    skelWeight (d :: τ) = (if d = 0 then 1 / 2 else 1 / 4) * skelWeight τ := by
  simp [skelWeight]

/-- The kernel entry of a step that keeps the height and moves the base vertex to `w`. -/
theorem cylKernel_hor (p : Site B) (w : B.V) : cylKernel B p (w, p.2) = 1 / 2 * B.P p.1 w := by
  simp [cylKernel]

/-- The kernel entry of a vertical step of size one, which keeps the base vertex. -/
theorem cylKernel_ver (p : Site B) {d : ℤ} (hd : d = -1 ∨ d = 1) :
    cylKernel B p (p.1, p.2 + d) = 1 / 4 := by
  have h : (p.2 - (p.2 + d)).natAbs = 1 := by
    rcases hd with rfl | rfl <;> simp
  unfold cylKernel
  rw [if_pos ⟨rfl, h⟩]

/-- The product of the kernel entries along `p :: q :: c`, indexed as in
`IdlaCyl.pathWeight`, splits off the first step. -/
theorem prod_getD_cons (p q : Site B) (c : List (Site B)) :
    ∏ i ∈ Finset.range (c.length + 1),
        cylKernel B ((p :: q :: c).getD i p) ((p :: q :: c).getD (i + 1) p)
      = cylKernel B p q * ∏ i ∈ Finset.range c.length,
          cylKernel B ((q :: c).getD i q) ((q :: c).getD (i + 1) q) := by
  rw [Finset.prod_range_succ', mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  have h1 : i < (q :: c).length := by simp; omega
  have h2 : i + 1 < (q :: c).length := by simp; omega
  show cylKernel B ((q :: c).getD i p) ((q :: c).getD (i + 1) p)
    = cylKernel B ((q :: c).getD i q) ((q :: c).getD (i + 1) q)
  rw [getD_congr_default (q :: c) h1 p q, getD_congr_default (q :: c) h2 p q]

/-- The kernel product along an assembled list is the skeleton weight times the base
chain weight along the base list. -/
theorem prod_cylKernel_assemble (τ : List ℤ) (p : Site B) (ws : List B.V)
    (hτ : ∀ d ∈ τ, d = -1 ∨ d = 0 ∨ d = 1) (hws : ws.length = τ.count 0) :
    ∏ i ∈ Finset.range (assemble p τ ws).length,
        cylKernel B ((p :: assemble p τ ws).getD i p) ((p :: assemble p τ ws).getD (i + 1) p)
      = skelWeight τ * listPathWeight B p.1 ws := by
  induction τ generalizing p ws with
  | nil =>
    cases ws with
    | nil => simp [assemble, skelWeight, listPathWeight]
    | cons w ws => simp at hws
  | cons d τ ih =>
    have hτ' : ∀ e ∈ τ, e = -1 ∨ e = 0 ∨ e = 1 := fun e he => hτ e (by simp [he])
    by_cases hd : d = 0
    · subst hd
      rcases ws with _ | ⟨w, ws'⟩
      · simp at hws
      · have hws' : ws'.length = τ.count 0 := by simpa using hws
        have ih' := ih (w, p.2) ws' hτ' hws'
        simp only [assemble, ↓reduceIte, List.length_cons]
        rw [prod_getD_cons, ih', cylKernel_hor, skelWeight_cons]
        simp only [listPathWeight, if_true]
        ring
    · have hd' : d = -1 ∨ d = 1 := by
        rcases hτ d (by simp) with h | h | h <;> omega
      have hws' : ws.length = τ.count 0 := by simpa [hd] using hws
      simp only [assemble, hd, ↓reduceIte, List.length_cons]
      rw [prod_getD_cons, ih (p.1, p.2 + d) ws hτ' hws', cylKernel_ver p hd', skelWeight_cons]
      simp only [if_false, hd]
      ring

/-- The weight of an assembled list is `ENNReal.ofReal` of the skeleton weight times
the base chain weight, written as a product of `ENNReal.ofReal` of kernel entries. -/
theorem prod_ofReal_assemble (τ : List ℤ) (p : Site B) (ws : List B.V)
    (hτ : ∀ d ∈ τ, d = -1 ∨ d = 0 ∨ d = 1) (hws : ws.length = τ.count 0) :
    ∏ i ∈ Finset.range (assemble p τ ws).length,
        ENNReal.ofReal (cylKernel B ((p :: assemble p τ ws).getD i p)
          ((p :: assemble p τ ws).getD (i + 1) p))
      = ENNReal.ofReal (skelWeight τ * listPathWeight B p.1 ws) := by
  rw [← prod_cylKernel_assemble τ p ws hτ hws, ENNReal.ofReal_prod_of_nonneg]
  exact fun i _ => cylKernel_nonneg _ _

/-- The `IdlaCyl.pathWeight` of a path that follows `p :: c` is the product of
`ENNReal.ofReal` of the kernel entries along `p :: c`. -/
theorem pathWeight_eq_prod (p : Site B) (c : List (Site B)) (f : ℕ → Site B)
    (hf : ∀ i ≤ c.length, f i = (p :: c).getD i p) :
    IdlaCyl.pathWeight B c.length f
      = ∏ i ∈ Finset.range c.length,
          ENNReal.ofReal (cylKernel B ((p :: c).getD i p) ((p :: c).getD (i + 1) p)) := by
  unfold IdlaCyl.pathWeight
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [hf i (by omega), hf (i + 1) (by omega)]

/-- The `IdlaCyl.pathWeight` of an assembled list is the skeleton weight times the base
chain weight, as an `ENNReal.ofReal`. -/
theorem pathWeight_assemble (p : Site B) (τ : List ℤ) (ws : List B.V) (f : ℕ → Site B)
    (hτ : ∀ d ∈ τ, d = -1 ∨ d = 0 ∨ d = 1) (hws : ws.length = τ.count 0)
    (hf : ∀ i ≤ (assemble p τ ws).length, f i = (p :: assemble p τ ws).getD i p) :
    IdlaCyl.pathWeight B (assemble p τ ws).length f
      = ENNReal.ofReal (skelWeight τ * listPathWeight B p.1 ws) := by
  rw [pathWeight_eq_prod p _ f hf, prod_ofReal_assemble τ p ws hτ hws]

/-- The `IdlaCyl.pathWeight` of an assembled list, indexed by the increment count `τ.length`. -/
theorem pathWeight_assemble_length (p : Site B) (τ : List ℤ) (ws : List B.V) (f : ℕ → Site B)
    (hτ : ∀ d ∈ τ, d = -1 ∨ d = 0 ∨ d = 1) (hws : ws.length = τ.count 0)
    (hf : ∀ i ≤ τ.length, f i = (p :: assemble p τ ws).getD i p) :
    IdlaCyl.pathWeight B τ.length f
      = ENNReal.ofReal (skelWeight τ * listPathWeight B p.1 ws) := by
  have h := pathWeight_assemble p τ ws f hτ hws (by rw [length_assemble]; exact hf)
  rw [length_assemble] at h
  exact h

/-! ### The base chain along a list of base vertices -/

/-- Appending one base vertex multiplies the base chain weight by the last step. -/
theorem listPathWeight_append_singleton (x : B.V) (ws : List B.V) (v : B.V) :
    listPathWeight B x (ws ++ [v])
      = listPathWeight B x ws * B.P ((x :: ws).getLast (List.cons_ne_nil _ _)) v := by
  induction ws generalizing x with
  | nil => simp [listPathWeight]
  | cons w ws ih =>
    simp only [List.cons_append, listPathWeight, ih, List.getLast_cons_cons]
    ring

/-- The last entry of `x :: List.ofFn w` is the endpoint of the path `w` from `x`. -/
theorem getLast_cons_ofFn (x : B.V) {s : ℕ} (w : Fin s → B.V) :
    (x :: List.ofFn w).getLast (List.cons_ne_nil _ _) = pathEnd B x s w := by
  cases s with
  | zero => simp [pathEnd]
  | succ s =>
    rw [List.ofFn_succ']
    simp [pathEnd]

/-- The base chain weight along `ofFn w` is the path weight of `w`, the product of the
one-step probabilities. -/
theorem listPathWeight_ofFn (x : B.V) {s : ℕ} (w : Fin s → B.V) :
    listPathWeight B x (List.ofFn w) = pathWeight B x s w := by
  induction s generalizing x with
  | zero => simp [listPathWeight, pathWeight]
  | succ s ih =>
    rw [List.ofFn_succ', List.concat_eq_append, listPathWeight_append_singleton, ih,
      getLast_cons_ofFn]
    rfl

end

end IdlaCyl.Silvestri
