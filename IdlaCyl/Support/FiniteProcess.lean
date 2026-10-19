import IdlaCyl.Support.FiniteLawOperations

set_option autoImplicit false

/-! # Time-inhomogeneous finite chains, constructed by binding kernels -/
namespace IdlaCyl
open scoped BigOperators
noncomputable section

structure FiniteProcess (S : Type*) [Fintype S] where
  initial : FiniteLaw S
  transition : ℕ → S → FiniteLaw S

namespace FiniteProcess
variable {S : Type*} [Fintype S]

/-- A law, not an abstract expectation operator. -/
def law (P : FiniteProcess S) : ℕ → FiniteLaw S
  | 0 => P.initial
  | n + 1 => (P.law n).bind (P.transition n)

@[simp] theorem law_zero (P : FiniteProcess S) : P.law 0 = P.initial := rfl

@[simp] theorem expect_succ (P : FiniteProcess S) (n : ℕ) (f : S → ℝ) :
    (P.law (n+1)).expect f =
      (P.law n).expect (fun x => (P.transition n x).expect f) := by
  exact FiniteLaw.expect_bind _ _ _

/-- Adjacent-state joint law, with the right next-state marginal. -/
def stepLaw (P : FiniteProcess S) (n : ℕ) : FiniteLaw (S × S) :=
  (P.law n).joint (P.transition n)

@[simp] theorem expect_stepLaw (P : FiniteProcess S) (n : ℕ) (f : S × S → ℝ) :
    (P.stepLaw n).expect f =
      (P.law n).expect (fun x => (P.transition n x).expect (fun y => f (x,y))) := by
  exact FiniteLaw.expect_joint _ _ _

/-- Reachability is determined by the actual propagated probability weights. -/
def reachable (P : FiniteProcess S) (n : ℕ) (x : S) : Prop := 0 < (P.law n).weight x

/-- Telescoping of conditional drifts, obtained by rearranging finite sums. -/
theorem expect_telescope (P : FiniteProcess S) (F : ℕ → S → ℝ) (n : ℕ) :
    (P.law n).expect (F n) - P.initial.expect (F 0) =
      ∑ k ∈ Finset.range n, (P.law k).expect
        (fun x => (P.transition k x).expect (F (k+1)) - F k x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih, FiniteLaw.expect_sub, expect_succ]
      ring

/-- A local mean-zero increment implies a global mean identity. -/
theorem mean_constant (P : FiniteProcess S) (M : ℕ → S → ℝ) (n : ℕ)
    (hmean : ∀ k < n, ∀ x, P.reachable k x →
      (P.transition k x).expect (fun y => M (k+1) y - M k x) = 0) :
    (P.law n).expect (M n) = P.initial.expect (M 0) := by
  have hz : ∑ k ∈ Finset.range n, (P.law k).expect
      (fun x => (P.transition k x).expect (M (k+1)) - M k x) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    calc
      _ = (P.law k).expect (fun _ => 0) := by
        apply (P.law k).expect_congr_support
        intro x hx
        simpa only [FiniteLaw.expect_sub, FiniteLaw.expect_const] using
          hmean k (Finset.mem_range.mp hk) x hx
      _ = 0 := FiniteLaw.expect_const _ _
  have h := P.expect_telescope M n
  rw [hz] at h
  linarith

/-- Squared-martingale energy, without a conditional-expectation library. -/
theorem square_energy (P : FiniteProcess S) (M : ℕ → S → ℝ) (n : ℕ)
    (hmean : ∀ k < n, ∀ x, P.reachable k x →
      (P.transition k x).expect (fun y => M (k+1) y - M k x) = 0) :
    (P.law n).expect (fun x => M n x ^ 2) =
      P.initial.expect (fun x => M 0 x ^ 2) +
      ∑ k ∈ Finset.range n, (P.law k).expect (fun x =>
        (P.transition k x).expect (fun y => (M (k+1) y - M k x) ^ 2)) := by
  have hloc (k : ℕ) (hk : k < n) (x : S) (hx : P.reachable k x) :
      (P.transition k x).expect (fun y => M (k+1) y ^ 2) - M k x ^ 2 =
      (P.transition k x).expect (fun y => (M (k+1) y - M k x) ^ 2) := by
    have hm := hmean k hk x hx
    have he := (P.transition k x).expect_congr (fun y =>
      show M (k+1) y ^ 2 = (M (k+1) y - M k x) ^ 2 +
        (2 * M k x) * (M (k+1) y - M k x) + M k x ^ 2 by ring)
    rw [FiniteLaw.expect_add, FiniteLaw.expect_add,
      FiniteLaw.expect_const_mul, FiniteLaw.expect_const, hm] at he
    linarith
  have ht := P.expect_telescope (fun k x => M k x ^ 2) n
  have hs : (∑ k ∈ Finset.range n, (P.law k).expect
      (fun x => (P.transition k x).expect (fun y => M (k+1) y ^ 2) - M k x ^ 2)) =
      ∑ k ∈ Finset.range n, (P.law k).expect (fun x =>
        (P.transition k x).expect (fun y => (M (k+1) y - M k x) ^ 2)) := by
    apply Finset.sum_congr rfl
    intro k hk
    apply (P.law k).expect_congr_support
    intro x hx
    exact hloc k (Finset.mem_range.mp hk) x hx
  rw [hs] at ht
  linarith

end FiniteProcess
end
end IdlaCyl
