import IdlaCyl.Support.FiniteProcess

set_option autoImplicit false

/-!
# Adaptive bounded-variable concentration from finite sums

There is no independence hypothesis: the next law is the constructed kernel of
`FiniteProcess`. Local hypotheses are imposed only on positive-probability
states and transitions. The conditional exponential bound is proved by the
chord inequality, not assumed as a field of a concentration structure.
-/
namespace IdlaCyl
open scoped BigOperators
noncomputable section

namespace FiniteLaw
variable {S : Type*} [Fintype S]

/-- The chord joining the exponential at 0 and at lam, also for negative lam. -/
theorem exp_chord (s lam : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Real.exp (lam * s) ≤ 1 + s * (Real.exp lam - 1) := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ lam)
    (show 0 ≤ 1-s by linarith) hs0 (show 1-s+s=1 by ring)
  have hh : Real.exp (s*lam) ≤ (1-s)+s*Real.exp lam := by
    simpa only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] using h
  calc
    Real.exp (lam*s) = Real.exp (s*lam) := by rw [mul_comm]
    _ ≤ (1-s)+s*Real.exp lam := hh
    _ = 1+s*(Real.exp lam-1) := by ring

/-- Exponential domination of any [0,1]-valued variable by its Bernoulli chord. -/
theorem bounded_laplace (μ : FiniteLaw S) (Y : S → ℝ) (p lam : ℝ)
    (hbound : ∀ x, 0 < μ.weight x → 0 ≤ Y x ∧ Y x ≤ 1)
    (hmean : μ.expect Y = p) :
    μ.expect (fun x => Real.exp (lam * (Y x - p))) ≤
      Real.exp (p * (Real.exp lam - 1 - lam)) := by
  have hchord : μ.expect (fun x => Real.exp (lam * Y x)) ≤
      1 + p * (Real.exp lam - 1) := by
    calc
      _ ≤ μ.expect (fun x => 1 + Y x * (Real.exp lam - 1)) := by
        apply μ.expect_mono_support
        intro x hx
        exact exp_chord (Y x) lam (hbound x hx).1 (hbound x hx).2
      _ = _ := by rw [expect_add, expect_const, expect_mul_const, hmean]
  have hline : 1 + p * (Real.exp lam - 1) ≤ Real.exp (p * (Real.exp lam - 1)) := by
    simpa only [add_comm] using Real.add_one_le_exp (p * (Real.exp lam - 1))
  calc
    _ = Real.exp (-lam*p) * μ.expect (fun x => Real.exp (lam * Y x)) := by
      rw [← expect_const_mul]
      apply μ.expect_congr
      intro x
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-lam*p) * Real.exp (p * (Real.exp lam - 1)) :=
      mul_le_mul_of_nonneg_left (hchord.trans hline) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- An explicit remainder estimate, derived from the exponential power series. -/
theorem exp_remainder_le_square (lam : ℝ) (hlam : |lam| ≤ 1) :
    Real.exp lam - 1 - lam ≤ lam ^ 2 := by
  have hc : ‖(lam : ℂ)‖ ≤ 1 := by simpa using hlam
  have h := Complex.norm_exp_sub_one_sub_id_le hc
  have ha : |Real.exp lam - 1 - lam| ≤ lam ^ 2 := by
    simpa only [← Complex.ofReal_exp, ← Complex.ofReal_one,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h
  exact (le_abs_self _).trans ha

end FiniteLaw

namespace FiniteProcess
variable {S : Type*} [Fintype S]

/-- Iteration of an explicitly checked one-step weighted inequality. -/
theorem iterate_nonnegative_factor (P : FiniteProcess S) (F : ℕ → S → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (n : ℕ)
    (hzero : P.initial.expect (F 0) ≤ 1)
    (hstep : ∀ k < n, ∀ x, P.reachable k x →
      (P.transition k x).expect (F (k+1)) ≤ c * F k x) :
    (P.law n).expect (F n) ≤ c ^ n := by
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      have hn := ih (fun k hk x hx => hstep k (Nat.lt_trans hk (Nat.lt_succ_self n)) x hx)
      calc
        _ = (P.law n).expect (fun x => (P.transition n x).expect (F (n+1))) :=
          P.expect_succ n _
        _ ≤ (P.law n).expect (fun x => c * F n x) := by
          apply (P.law n).expect_mono_support
          intro x hx
          exact hstep n (Nat.lt_succ_self n) x hx
        _ = c * (P.law n).expect (F n) := FiniteLaw.expect_const_mul _ _ _
        _ ≤ c * c ^ n := mul_le_mul_of_nonneg_left hn hc
        _ = c ^ (n+1) := by rw [pow_succ]; ring

/-- The exact Bernoulli-cumulant bound for adaptive [0,1] increments. -/
theorem adaptive_laplace (P : FiniteProcess S) (A : ℕ → S → ℝ)
    (p lam : ℝ) (n : ℕ)
    (hzero : ∀ x, 0 < P.initial.weight x → A 0 x = 0)
    (hbound : ∀ k < n, ∀ x, P.reachable k x → ∀ y,
      0 < (P.transition k x).weight y →
      0 ≤ A (k+1) y - A k x ∧ A (k+1) y - A k x ≤ 1)
    (hmean : ∀ k < n, ∀ x, P.reachable k x →
      (P.transition k x).expect (fun y => A (k+1) y - A k x) = p) :
    (P.law n).expect (fun x => Real.exp (lam * (A n x - (n:ℝ)*p))) ≤
      Real.exp ((n:ℝ)*p*(Real.exp lam - 1 - lam)) := by
  let F : ℕ → S → ℝ := fun k x => Real.exp (lam*(A k x-(k:ℝ)*p))
  let c := Real.exp (p*(Real.exp lam-1-lam))
  have h0 : P.initial.expect (F 0) = 1 := by
    calc
      _ = P.initial.expect (fun _ => 1) := by
        apply P.initial.expect_congr_support
        intro x hx
        simp [F, hzero x hx]
      _ = 1 := FiniteLaw.expect_const _ _
  have hs : ∀ k < n, ∀ x, P.reachable k x →
      (P.transition k x).expect (F (k+1)) ≤ c*F k x := by
    intro k hk x hx
    have hb := FiniteLaw.bounded_laplace (P.transition k x)
      (fun y => A (k+1) y-A k x) p lam (hbound k hk x hx) (hmean k hk x hx)
    calc
      _ = F k x * (P.transition k x).expect
          (fun y => Real.exp (lam*((A (k+1) y-A k x)-p))) := by
        rw [← FiniteLaw.expect_const_mul]
        apply FiniteLaw.expect_congr
        intro y
        simp only [F, ← Real.exp_add, Nat.cast_add, Nat.cast_one]
        congr 1
        ring
      _ ≤ F k x * c := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
      _ = c*F k x := mul_comm _ _
  have h := P.iterate_nonnegative_factor F c (Real.exp_nonneg _) n h0.le hs
  convert h using 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- The small-parameter estimate works for either sign of lam. -/
theorem adaptive_laplace_square (P : FiniteProcess S) (A : ℕ → S → ℝ)
    (p lam : ℝ) (hp : 0 ≤ p) (hlam : |lam| ≤ 1) (n : ℕ)
    (hzero : ∀ x, 0 < P.initial.weight x → A 0 x = 0)
    (hbound : ∀ k < n, ∀ x, P.reachable k x → ∀ y,
      0 < (P.transition k x).weight y →
      0 ≤ A (k+1) y - A k x ∧ A (k+1) y - A k x ≤ 1)
    (hmean : ∀ k < n, ∀ x, P.reachable k x →
      (P.transition k x).expect (fun y => A (k+1) y - A k x) = p) :
    (P.law n).expect (fun x => Real.exp (lam * (A n x - (n:ℝ)*p))) ≤
      Real.exp ((n:ℝ)*p*lam^2) := by
  apply (P.adaptive_laplace A p lam n hzero hbound hmean).trans
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (FiniteLaw.exp_remainder_le_square lam hlam)
    (mul_nonneg (Nat.cast_nonneg n) hp)

/-- An explicit optimized upper tail; no Gaussian or concentration theorem is imported. -/
theorem adaptive_upper_tail (P : FiniteProcess S) (A : ℕ → S → ℝ)
    (p r : ℝ) (n : ℕ) (hp : 0 ≤ p) (hμ : 0 < (n:ℝ)*p)
    (hr : 0 ≤ r) (hrmax : r ≤ 2*((n:ℝ)*p))
    (hzero : ∀ x, 0 < P.initial.weight x → A 0 x = 0)
    (hbound : ∀ k < n, ∀ x, P.reachable k x → ∀ y,
      0 < (P.transition k x).weight y →
      0 ≤ A (k+1) y - A k x ∧ A (k+1) y - A k x ≤ 1)
    (hmean : ∀ k < n, ∀ x, P.reachable k x →
      (P.transition k x).expect (fun y => A (k+1) y - A k x) = p) :
    (P.law n).event (fun x => r ≤ A n x-(n:ℝ)*p) ≤
      Real.exp (-r^2/(4*((n:ℝ)*p))) := by
  let lam := r/(2*((n:ℝ)*p))
  have hl0 : 0 ≤ lam := div_nonneg hr (by positivity)
  have hl1 : lam ≤ 1 := (div_le_one (by positivity)).mpr hrmax
  have hlabs : |lam| ≤ 1 := by rwa [abs_of_nonneg hl0]
  have hm := P.adaptive_laplace_square A p lam hp hlabs n hzero hbound hmean
  calc
    _ ≤ Real.exp (-lam*r) * (P.law n).expect
        (fun x => Real.exp (lam*(A n x-(n:ℝ)*p))) :=
      (P.law n).upper_laplace _ r lam hl0
    _ ≤ Real.exp (-lam*r) * Real.exp ((n:ℝ)*p*lam^2) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      dsimp [lam]
      field_simp [ne_of_gt hμ]
      ring

/-- The same optimized lower tail, applying exponential Markov with -lam. -/
theorem adaptive_lower_tail (P : FiniteProcess S) (A : ℕ → S → ℝ)
    (p r : ℝ) (n : ℕ) (hp : 0 ≤ p) (hμ : 0 < (n:ℝ)*p)
    (hr : 0 ≤ r) (hrmax : r ≤ 2*((n:ℝ)*p))
    (hzero : ∀ x, 0 < P.initial.weight x → A 0 x = 0)
    (hbound : ∀ k < n, ∀ x, P.reachable k x → ∀ y,
      0 < (P.transition k x).weight y →
      0 ≤ A (k+1) y - A k x ∧ A (k+1) y - A k x ≤ 1)
    (hmean : ∀ k < n, ∀ x, P.reachable k x →
      (P.transition k x).expect (fun y => A (k+1) y - A k x) = p) :
    (P.law n).event (fun x => A n x-(n:ℝ)*p ≤ -r) ≤
      Real.exp (-r^2/(4*((n:ℝ)*p))) := by
  let lam := r/(2*((n:ℝ)*p))
  have hl0 : 0 ≤ lam := div_nonneg hr (by positivity)
  have hl1 : lam ≤ 1 := (div_le_one (by positivity)).mpr hrmax
  have hlabs : |-lam| ≤ 1 := by rwa [abs_neg, abs_of_nonneg hl0]
  have hm := P.adaptive_laplace_square A p (-lam) hp hlabs n hzero hbound hmean
  have hevent : (fun x => A n x-(n:ℝ)*p ≤ -r) =
      (fun x => r ≤ -(A n x-(n:ℝ)*p)) := by
    funext x
    apply propext
    constructor <;> intro h <;> linarith
  rw [hevent]
  calc
    _ ≤ Real.exp (-lam*r) * (P.law n).expect
        (fun x => Real.exp (lam*(-(A n x-(n:ℝ)*p)))) :=
      (P.law n).upper_laplace _ r lam hl0
    _ = Real.exp (-lam*r) * (P.law n).expect
        (fun x => Real.exp ((-lam)*(A n x-(n:ℝ)*p))) := by
      congr 1
      apply FiniteLaw.expect_congr
      intro x
      congr 1
      ring
    _ ≤ Real.exp (-lam*r) * Real.exp ((n:ℝ)*p*(-lam)^2) :=
      mul_le_mul_of_nonneg_left hm (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      dsimp [lam]
      field_simp [ne_of_gt hμ]
      ring

end FiniteProcess
end
end IdlaCyl
