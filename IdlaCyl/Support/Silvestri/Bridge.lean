import IdlaCyl.Support.Spectral
import Mathlib

/-!
# Path weights and bridges of the lazy base chain

Fix a base `B` and write `B.P` for its lazy simple random walk kernel. A path
of `s` steps from a vertex `x` is a tuple `w : Fin s → B.V`, read as the visited
vertices `w 0, …, w (s - 1)` after the start `x`. Its weight `pathWeight B x s w`
is the product of the one-step probabilities `B.P` along `x, w 0, …, w (s - 1)`.

The file proves the following facts. Every sum is a finite sum over the paths
of a fixed length.

* Path weights are nonnegative, and over all paths of length `s` they sum to `1`.
* Summed over the paths that end at `e`, the path weights give the `s`-step
  transition probability `basePow B s x e`.
* `bridgeWeight B s x e` is the path weight divided by `basePow B s x e`, on the
  paths from `x` to `e`. Its total mass is `1` whenever `basePow B s x e ≠ 0`.
* Mixing the bridges with the weights `basePow B s x e` gives back the path
  weight: `∑ e, basePow B s x e * bridgeWeight B s x e w = pathWeight B x s w`.

Only the nonnegativity and the row sums of `B.P` are used.
-/

namespace IdlaCyl.Silvestri

open scoped BigOperators

/-- The last vertex of a path of `s` steps from `x`: the start `x` when `s = 0`,
and the last visited vertex `w (s - 1)` otherwise. -/
def pathEnd (B : Base) (x : B.V) : (s : ℕ) → (Fin s → B.V) → B.V
  | 0, _ => x
  | _ + 1, w => w (Fin.last _)

/-- The weight of the path `x, w 0, …, w (s - 1)`: the product of the one-step
probabilities `B.P` along it. The last factor is `B.P` from the endpoint of the
first `s` steps to `w (s - 1)`. -/
noncomputable def pathWeight (B : Base) (x : B.V) : (s : ℕ) → (Fin s → B.V) → ℝ
  | 0, _ => 1
  | s + 1, w => pathWeight B x s (Fin.init w) * B.P (pathEnd B x s (Fin.init w)) (w (Fin.last s))

/-- The bridge weight of a path of `s` steps from `x` to `e`: the path weight divided
by `basePow B s x e`, on the paths that end at `e`, and `0` on the others. It is also
`0` on every path when `basePow B s x e = 0`. -/
noncomputable def bridgeWeight (B : Base) (s : ℕ) (x e : B.V) (w : Fin s → B.V) : ℝ :=
  if pathEnd B x s w = e then
    (if basePow B s x e = 0 then 0 else pathWeight B x s w / basePow B s x e)
  else 0

section

variable (B : Base)

/-- The endpoint of a path of `s + 1` steps is its last vertex. -/
theorem pathEnd_snoc {s : ℕ} (x : B.V) (w : Fin s → B.V) (v : B.V) :
    pathEnd B x (s + 1) (Fin.snoc (α := fun _ => B.V) w v) = v := by
  simp [pathEnd]

/-- Appending a vertex multiplies the weight by the last one-step probability. -/
theorem pathWeight_snoc {s : ℕ} (x : B.V) (w : Fin s → B.V) (v : B.V) :
    pathWeight B x (s + 1) (Fin.snoc (α := fun _ => B.V) w v)
      = pathWeight B x s w * B.P (pathEnd B x s w) v := by
  simp [pathWeight]

/-- Splitting a sum over the paths of `s + 1` steps at the last vertex. -/
theorem sum_succ_paths {s : ℕ} (f : (Fin (s + 1) → B.V) → ℝ) :
    ∑ w, f w = ∑ w' : Fin s → B.V, ∑ v : B.V, f (Fin.snoc (α := fun _ => B.V) w' v) := by
  calc ∑ w, f w
      = ∑ p : B.V × (Fin s → B.V), f (Fin.snoc (α := fun _ => B.V) p.2 p.1) :=
        ((Fin.snocEquiv (fun _ : Fin (s + 1) => B.V)).sum_comp f).symm
    _ = ∑ v : B.V, ∑ w' : Fin s → B.V, f (Fin.snoc (α := fun _ => B.V) w' v) := by
        rw [Fintype.sum_prod_type]
    _ = ∑ w' : Fin s → B.V, ∑ v : B.V, f (Fin.snoc (α := fun _ => B.V) w' v) :=
        Finset.sum_comm

/-- The `s`-step transition probabilities are nonnegative. -/
theorem basePow_nonneg (x : B.V) (s : ℕ) : ∀ e : B.V, 0 ≤ basePow B s x e := by
  induction s with
  | zero =>
    intro e
    simp only [basePow]
    split_ifs <;> norm_num
  | succ s ih =>
    intro e
    simp only [basePow]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih z) (B.P_nonneg z e)

/-- Path weights are nonnegative. -/
theorem pathWeight_nonneg (x : B.V) (s : ℕ) : ∀ w : Fin s → B.V, 0 ≤ pathWeight B x s w := by
  induction s with
  | zero =>
    intro w
    simp [pathWeight]
  | succ s ih =>
    intro w
    simp only [pathWeight]
    exact mul_nonneg (ih _) (B.P_nonneg _ _)

/-- The path weights over all paths of `s` steps sum to `1`, because each row of
`B.P` sums to `1`. -/
theorem sum_pathWeight (x : B.V) (s : ℕ) : ∑ w : Fin s → B.V, pathWeight B x s w = 1 := by
  induction s with
  | zero => simp [pathWeight]
  | succ s ih =>
    rw [sum_succ_paths]
    simp only [pathWeight_snoc, ← Finset.mul_sum, B.P_row_sum, mul_one]
    exact ih

/-- Summed over the paths that end at `e`, the path weights give the `s`-step
transition probability `basePow B s x e`. -/
theorem sum_paths_end_eq_basePow (x : B.V) (s : ℕ) : ∀ e : B.V,
    ∑ w : Fin s → B.V, (if pathEnd B x s w = e then pathWeight B x s w else 0)
      = basePow B s x e := by
  induction s with
  | zero =>
    intro e
    simp [pathEnd, pathWeight, basePow]
  | succ s ih =>
    intro e
    rw [sum_succ_paths]
    simp only [pathEnd_snoc, pathWeight_snoc, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    show _ = ∑ z : B.V, basePow B s x z * B.P z e
    simp only [← ih, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    simp

/-- A path weight is at most the transition probability to its endpoint. -/
theorem pathWeight_le_basePow (x : B.V) (s : ℕ) : ∀ w : Fin s → B.V,
    pathWeight B x s w ≤ basePow B s x (pathEnd B x s w) := by
  induction s with
  | zero =>
    intro w
    simp [pathWeight, pathEnd, basePow]
  | succ s ih =>
    intro w
    calc pathWeight B x (s + 1) w
        = pathWeight B x s (Fin.init w) * B.P (pathEnd B x s (Fin.init w)) (w (Fin.last s)) := rfl
      _ ≤ basePow B s x (pathEnd B x s (Fin.init w))
            * B.P (pathEnd B x s (Fin.init w)) (w (Fin.last s)) :=
          mul_le_mul_of_nonneg_right (ih _) (B.P_nonneg _ _)
      _ ≤ ∑ z : B.V, basePow B s x z * B.P z (w (Fin.last s)) :=
          Finset.single_le_sum (f := fun z => basePow B s x z * B.P z (w (Fin.last s)))
            (fun z _ => mul_nonneg (basePow_nonneg B x s z) (B.P_nonneg _ _))
            (Finset.mem_univ _)
      _ = basePow B (s + 1) x (pathEnd B x (s + 1) w) := rfl

/-- Bridge weights are nonnegative. -/
theorem bridgeWeight_nonneg (x e : B.V) (s : ℕ) (w : Fin s → B.V) :
    0 ≤ bridgeWeight B s x e w := by
  unfold bridgeWeight
  split_ifs <;> first
    | exact le_rfl
    | exact div_nonneg (pathWeight_nonneg B x s w) (basePow_nonneg B x s e)

/-- The bridge weights from `x` to `e` sum to `1` when `basePow B s x e ≠ 0`. -/
theorem sum_bridgeWeight (x e : B.V) (s : ℕ) (h : basePow B s x e ≠ 0) :
    ∑ w : Fin s → B.V, bridgeWeight B s x e w = 1 := by
  have hw : ∀ w : Fin s → B.V, bridgeWeight B s x e w
      = (if pathEnd B x s w = e then pathWeight B x s w else 0) / basePow B s x e := by
    intro w
    unfold bridgeWeight
    by_cases hp : pathEnd B x s w = e <;> simp [hp, h]
  simp only [hw]
  rw [← Finset.sum_div, sum_paths_end_eq_basePow, div_self h]

/-- Mixing the bridges with the weights `basePow B s x e` gives back the path weight. -/
theorem bridge_mixture (x : B.V) (s : ℕ) (w : Fin s → B.V) :
    ∑ e : B.V, basePow B s x e * bridgeWeight B s x e w = pathWeight B x s w := by
  rw [Finset.sum_eq_single (pathEnd B x s w)]
  · simp only [bridgeWeight, if_true]
    split_ifs with h
    · linarith [pathWeight_le_basePow B x s w, pathWeight_nonneg B x s w]
    · field_simp
  · intro b _ hb
    simp [bridgeWeight, Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

end

end IdlaCyl.Silvestri
