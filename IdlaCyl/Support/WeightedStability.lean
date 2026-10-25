module

public import IdlaCyl.Support.Stability

@[expose] public section

set_option autoImplicit false

/-!
# Weighted consequences of trajectory stability

The main bound is equation (27) in the paper, supplied as a deterministic
inequality. Taking expectations and Efron--Stein are separate steps.
-/

namespace IdlaCyl

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- Finite discrepancy weightedPairing. -/
noncomputable def weightedPairing (A B : Finset α) (f : α → ℝ) : ℝ :=
  (∑ x ∈ A, f x) - ∑ x ∈ B, f x

theorem diff_parts_disjoint (A B : Finset α) : Disjoint (A \ B) (B \ A) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hy).1

theorem pairing_eq_directed (A B : Finset α) (f : α → ℝ) :
    weightedPairing A B f = (∑ x ∈ A \ B, f x) - ∑ x ∈ B \ A, f x := by
  have hIA : A ∩ B ⊆ A := by
    intro x hx
    exact (Finset.mem_inter.mp hx).1
  have hIB : A ∩ B ⊆ B := by
    intro x hx
    exact (Finset.mem_inter.mp hx).2
  have hdA : A \ (A ∩ B) = A \ B := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hdB : B \ (A ∩ B) = B \ A := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hA := Finset.sum_sdiff (f := f) hIA
  have hB := Finset.sum_sdiff (f := f) hIB
  rw [hdA] at hA
  rw [hdB] at hB
  unfold weightedPairing
  linarith

/-- On the symmetric difference the sign is +1 on A and -1 on B. -/
noncomputable def discrepancySign (A : Finset α) (x : α) : ℝ :=
  if x ∈ A then 1 else -1

@[simp] theorem discrepancySign_sq (A : Finset α) (x : α) :
    discrepancySign A x ^ 2 = 1 := by
  unfold discrepancySign
  split_ifs <;> norm_num

theorem pairing_eq_signed_support (A B : Finset α) (f : α → ℝ) :
    weightedPairing A B f = ∑ x ∈ differenceSupport A B, discrepancySign A x * f x := by
  rw [pairing_eq_directed]
  unfold differenceSupport
  rw [Finset.sum_union (diff_parts_disjoint A B)]
  have hA : (∑ x ∈ A \ B, discrepancySign A x * f x) = ∑ x ∈ A \ B, f x := by
    apply Finset.sum_congr rfl
    intro x hx
    simp [discrepancySign, (Finset.mem_sdiff.mp hx).1]
  have hB : (∑ x ∈ B \ A, discrepancySign A x * f x) = - ∑ x ∈ B \ A, f x := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    simp [discrepancySign, (Finset.mem_sdiff.mp hx).2]
  rw [hA, hB]
  ring

/-- Cauchy--Schwarz with the *cardinality* of the changed set, not its volume. -/
theorem pairing_sq_le_card_mul (A B : Finset α) (f : α → ℝ) :
    weightedPairing A B f ^ 2 ≤ (differenceSupport A B).card *
      ∑ x ∈ differenceSupport A B, f x ^ 2 := by
  rw [pairing_eq_signed_support]
  have h := Finset.sum_mul_sq_le_sq_mul_sq (differenceSupport A B)
    (discrepancySign A) f
  simpa only [discrepancySign_sq, Finset.sum_const, nsmul_eq_mul, mul_one] using h

theorem pairing_sq_le_two (A B : Finset α) (f : α → ℝ)
    (hcard : (differenceSupport A B).card ≤ 2) :
    weightedPairing A B f ^ 2 ≤ 2 * ∑ x ∈ differenceSupport A B, f x ^ 2 := by
  have hn : 0 ≤ ∑ x ∈ differenceSupport A B, f x ^ 2 :=
    Finset.sum_nonneg (fun x _ => sq_nonneg (f x))
  have hc : ((differenceSupport A B).card : ℝ) ≤ 2 := by exact_mod_cast hcard
  exact (pairing_sq_le_card_mul A B f).trans (mul_le_mul_of_nonneg_right hc hn)

namespace EscapingPath

variable {seed : Set α}

/-- Equation (27), derived from first-exit dynamics and finite Cauchy--Schwarz. -/
theorem one_change_weighted_sq (A : Finset α)
    (pre post : List (EscapingPath seed)) (p q : EscapingPath seed) (f : α → ℝ) :
    weightedPairing (grow A (pre ++ p :: post)) (grow A (pre ++ q :: post)) f ^ 2 ≤
      2 * ∑ x ∈ differenceSupport (grow A (pre ++ p :: post))
        (grow A (pre ++ q :: post)), f x ^ 2 := by
  exact pairing_sq_le_two _ _ f (one_change_stability A pre post p q)

end EscapingPath

/-- For nonnegative weights, the unsigned support sum bounds the discrepancy. -/
theorem abs_pairing_le_support_sum (A B : Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    |weightedPairing A B f| ≤ ∑ x ∈ differenceSupport A B, f x := by
  rw [pairing_eq_directed]
  unfold differenceSupport
  rw [Finset.sum_union (diff_parts_disjoint A B)]
  have hA : 0 ≤ ∑ x ∈ A \ B, f x := Finset.sum_nonneg (fun x _ => hf x)
  have hB : 0 ≤ ∑ x ∈ B \ A, f x := Finset.sum_nonneg (fun x _ => hf x)
  apply abs_le.mpr
  constructor <;> linarith

theorem abs_pairing_le_slab_sum (A B F : Finset α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hF : differenceSupport A B ⊆ F) :
    |weightedPairing A B f| ≤ ∑ x ∈ F, f x := by
  have hs := Finset.sum_sdiff (f := f) hF
  have hn : 0 ≤ ∑ x ∈ F \ differenceSupport A B, f x :=
    Finset.sum_nonneg (fun x _ => hf x)
  have hbound := abs_pairing_le_support_sum A B f hf
  linarith

end IdlaCyl
