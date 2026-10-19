import Mathlib

set_option autoImplicit false

/-!
# Finite horizontal kernels

The normalized counting measure is stationary. A nonconstant eigenvalue has
mean-zero eigenfunctions. The lazy kernel is constructed from a finite regular
simple graph and its explicit degree count; regularity is not inferred from
vertex transitivity in this file.
-/

namespace IdlaCyl

open scoped BigOperators

variable {V : Type*} [Fintype V]

structure SymmetricKernel (V : Type*) [Fintype V] where
  weight : V → V → ℝ
  nonneg : ∀ x y, 0 ≤ weight x y
  row_sum : ∀ x, ∑ y, weight x y = 1
  symmetric : ∀ x y, weight x y = weight y x

namespace SymmetricKernel

variable (P : SymmetricKernel V)

noncomputable def applyFn (f : V → ℝ) (x : V) : ℝ := ∑ y, P.weight x y * f y

theorem col_sum (y : V) : ∑ x, P.weight x y = 1 := by
  calc
    ∑ x, P.weight x y = ∑ x, P.weight y x := by
      apply Finset.sum_congr rfl
      intro x _
      exact P.symmetric x y
    _ = 1 := P.row_sum y

@[simp] theorem applyFn_const (c : ℝ) (x : V) :
    P.applyFn (fun _ => c) x = c := by
  unfold applyFn
  rw [← Finset.sum_mul, P.row_sum]
  ring

@[simp] theorem applyFn_zero (x : V) : P.applyFn (fun _ => 0) x = 0 := by
  exact P.applyFn_const 0 x

theorem applyFn_add (f g : V → ℝ) (x : V) :
    P.applyFn (fun y => f y + g y) x = P.applyFn f x + P.applyFn g x := by
  simp [applyFn, mul_add, Finset.sum_add_distrib]

theorem applyFn_mul_const (f : V → ℝ) (c : ℝ) (x : V) :
    P.applyFn (fun y => f y * c) x = P.applyFn f x * c := by
  simp only [applyFn, mul_assoc, Finset.sum_mul]

theorem applyFn_const_mul (f : V → ℝ) (c : ℝ) (x : V) :
    P.applyFn (fun y => c * f y) x = c * P.applyFn f x := by
  simp only [applyFn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Preservation of the counting integral, hence also the normalized one. -/
theorem sum_applyFn (f : V → ℝ) : ∑ x, P.applyFn f x = ∑ x, f x := by
  unfold applyFn
  rw [Finset.sum_comm]
  calc
    (∑ y, ∑ x, P.weight x y * f y) =
        ∑ y, (∑ x, P.weight x y) * f y := by
      simp only [Finset.sum_mul]
    _ = ∑ y, f y := by simp only [P.col_sum, one_mul]

theorem eigenfunction_sum_zero (f : V → ℝ) {lam : ℝ} (hlam : lam ≠ 1)
    (heig : ∀ x, P.applyFn f x = lam * f x) : ∑ x, f x = 0 := by
  have hs : (∑ x, f x) = lam * (∑ x, f x) := by
    calc
      (∑ x, f x) = ∑ x, P.applyFn f x := (P.sum_applyFn f).symm
      _ = ∑ x, lam * f x := by
        apply Finset.sum_congr rfl
        intro x _
        exact heig x
      _ = lam * (∑ x, f x) := (Finset.mul_sum _ _ _).symm
  have hprod : (1 - lam) * (∑ x, f x) = 0 := by nlinarith
  rcases mul_eq_zero.mp hprod with h | h
  · exact False.elim (hlam (by linarith))
  · exact h

end SymmetricKernel

section RegularGraph

variable [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Exactly formula (1): diagonal 1/2 and weight 1/(2d) on each edge. -/
noncomputable def lazyWeight (d : ℕ) (x y : V) : ℝ :=
  (if y = x then (1 : ℝ) / 2 else 0) +
    (if G.Adj x y then (1 : ℝ) / (2 * (d : ℝ)) else 0)

omit [Fintype V] in
@[simp] theorem lazyWeight_self (d : ℕ) (x : V) :
    lazyWeight G d x x = 1 / 2 := by
  simp [lazyWeight]

omit [Fintype V] in
theorem lazyWeight_of_adj (d : ℕ) {x y : V} (h : G.Adj x y) :
    lazyWeight G d x y = 1 / (2 * (d : ℝ)) := by
  have hne : y ≠ x := by
    intro he
    subst y
    exact G.loopless.irrefl x h
  simp [lazyWeight, hne, h]

/-- Construct the symmetric stochastic kernel, rather than postulating it. -/
noncomputable def lazyKernel (d : ℕ) (hd : 0 < d)
    (hregular : ∀ x, (Finset.univ.filter (G.Adj x)).card = d) :
    SymmetricKernel V where
  weight := lazyWeight G d
  nonneg := by
    intro x y
    unfold lazyWeight
    split_ifs <;> positivity
  row_sum := by
    intro x
    have hcount :
        (∑ y, if G.Adj x y then (1 : ℝ) / (2 * (d : ℝ)) else 0) =
          (d : ℝ) * (1 / (2 * (d : ℝ))) := by
      calc
        (∑ y, if G.Adj x y then (1 : ℝ) / (2 * (d : ℝ)) else 0) =
            ∑ y ∈ Finset.univ.filter (G.Adj x),
              (1 : ℝ) / (2 * (d : ℝ)) := by
          rw [Finset.sum_filter]
        _ = (d : ℝ) * (1 / (2 * (d : ℝ))) := by simp [hregular]
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    change (∑ y, ((if y = x then (1 : ℝ) / 2 else 0) +
      if G.Adj x y then (1 : ℝ) / (2 * (d : ℝ)) else 0)) = 1
    have hdiag : (∑ y : V, if y = x then (1 : ℝ) / 2 else 0) = 1 / 2 := by
      simp
    rw [Finset.sum_add_distrib, hcount, hdiag]
    field_simp [hd']; ring
  symmetric := by
    intro x y
    have ha : G.Adj x y ↔ G.Adj y x := G.adj_comm x y
    simp only [lazyWeight, ha, eq_comm]

end RegularGraph
end IdlaCyl
