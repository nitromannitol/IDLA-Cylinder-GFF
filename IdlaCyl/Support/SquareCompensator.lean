import IdlaCyl.Support.FiniteProcess

set_option autoImplicit false

/-!
# Optional versus predictable quadratic variation

The conditional variance of X^2 is computed, not postulated. Its fourth-moment
bound feeds the constructed finite-process square-energy identity. The local
clock-update condition is explicitly stated; no IDLA or CLT conclusion occurs
in any assumption.
-/
namespace IdlaCyl
open scoped BigOperators
noncomputable section

namespace FiniteLaw
variable {S : Type*} [Fintype S]

/-- Centering X^2 makes a mean-zero increment even when X is not centered. -/
theorem square_centered_mean (μ : FiniteLaw S) (X : S → ℝ) :
    μ.expect (fun x => X x ^ 2 - μ.expect (fun y => X y ^ 2)) = 0 := by
  rw [expect_sub, expect_const]
  ring

theorem square_centered_energy (μ : FiniteLaw S) (X : S → ℝ) :
    μ.expect (fun x => (X x ^ 2 - μ.expect (fun y => X y ^ 2)) ^ 2) =
      μ.expect (fun x => X x ^ 4) - (μ.expect (fun x => X x ^ 2)) ^ 2 := by
  rw [expect_centered_sq]
  unfold variance
  congr 1
  apply μ.expect_congr
  intro x
  ring

theorem fourth_moment_le (μ : FiniteLaw S) (X : S → ℝ) (ε : ℝ)
    (hbound : ∀ x, 0 < μ.weight x → |X x| ≤ ε) :
    μ.expect (fun x => X x ^ 4) ≤ ε^2 * μ.expect (fun x => X x^2) := by
  rw [← expect_const_mul]
  apply μ.expect_mono_support
  intro x hx
  have h := hbound x hx
  have hp : 0 ≤ ε := (abs_nonneg _).trans h
  have hs : X x ^ 2 ≤ ε^2 := by
    nlinarith [sq_abs (X x), abs_nonneg (X x), mul_le_mul h h (abs_nonneg (X x)) hp]
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg (X x))]

theorem square_centered_energy_le (μ : FiniteLaw S) (X : S → ℝ) (ε : ℝ)
    (hbound : ∀ x, 0 < μ.weight x → |X x| ≤ ε) :
    μ.expect (fun x => (X x^2 - μ.expect (fun y => X y^2))^2) ≤
      ε^2 * μ.expect (fun x => X x^2) := by
  rw [square_centered_energy]
  exact (sub_le_self _ (sq_nonneg _)).trans (fourth_moment_le μ X ε hbound)

/-- A deterministic pointwise quadratic cap makes the discrepancy estimate useful. -/
theorem tail_of_square_bound (μ : FiniteLaw S) (D : S → ℝ) (b C : ℝ)
    (hb : 0 < b) (henergy : μ.expect (fun x => D x^2) ≤ C) :
    μ.event (fun x => b ≤ |D x|) ≤ C / b^2 := by
  classical
  have hpoint : b^2 * μ.event (fun x => b ≤ |D x|) ≤
      μ.expect (fun x => D x^2) := by
    calc
      _ = μ.expect (fun x => b^2 * if b ≤ |D x| then 1 else 0) := by
        rw [expect_const_mul]; rfl
      _ ≤ _ := by
        apply μ.expect_mono
        intro x
        by_cases h : b ≤ |D x|
        · simp only [h, if_true, mul_one]
          nlinarith [sq_abs (D x)]
        · simp [h, sq_nonneg]
  apply (le_div_iff₀ (sq_pos_of_pos hb)).mpr
  simpa only [mul_comm] using hpoint.trans henergy

end FiniteLaw

namespace FiniteProcess
variable {S : Type*} [Fintype S]

/-- Clock error energy, derived from centered squares of the actual transition variable. -/
theorem compensator_error_energy (P : FiniteProcess S)
    (D : ℕ → S → ℝ) (X : ℕ → S → S → ℝ) (ε : ℝ) (n : ℕ)
    (hzero : ∀ x, 0 < P.initial.weight x → D 0 x = 0)
    (hupdate : ∀ k < n, ∀ x, P.reachable k x → ∀ y,
      0 < (P.transition k x).weight y →
      D (k+1) y-D k x = X k x y^2 -
        (P.transition k x).expect (fun z => X k x z^2))
    (hbound : ∀ k < n, ∀ x, P.reachable k x → ∀ y,
      0 < (P.transition k x).weight y → |X k x y| ≤ ε) :
    (P.law n).expect (fun x => D n x^2) ≤
      ε^2 * ∑ k ∈ Finset.range n, (P.law k).expect (fun x =>
        (P.transition k x).expect (fun y => X k x y^2)) := by
  have hm : ∀ k < n, ∀ x, P.reachable k x →
      (P.transition k x).expect (fun y => D (k+1) y-D k x) = 0 := by
    intro k hk x hx
    calc
      _ = (P.transition k x).expect (fun y => X k x y^2 -
          (P.transition k x).expect (fun z => X k x z^2)) := by
        apply FiniteLaw.expect_congr_support
        exact hupdate k hk x hx
      _ = 0 := FiniteLaw.square_centered_mean _ _
  have he := P.square_energy D n hm
  have hz : P.initial.expect (fun x => D 0 x^2) = 0 := by
    calc
      _ = P.initial.expect (fun _ => 0) := by
        apply FiniteLaw.expect_congr_support
        intro x hx
        simp [hzero x hx]
      _ = 0 := FiniteLaw.expect_const _ _
  rw [hz, zero_add] at he
  rw [he, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  rw [← FiniteLaw.expect_const_mul]
  apply FiniteLaw.expect_mono_support
  intro x hx
  calc
    _ = (P.transition k x).expect (fun y => (X k x y^2 -
        (P.transition k x).expect (fun z => X k x z^2))^2) := by
      apply FiniteLaw.expect_congr_support
      intro y hy
      rw [hupdate k (Finset.mem_range.mp hk) x hx y hy]
    _ ≤ _ := FiniteLaw.square_centered_energy_le _ _ ε
      (hbound k (Finset.mem_range.mp hk) x hx)

end FiniteProcess
end
end IdlaCyl
