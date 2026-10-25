module

public import IdlaCyl.Support.FiniteComplex
public import IdlaCyl.Support.ExponentialMartingale

@[expose] public section

set_option autoImplicit false

/-!
# The local characteristic-function calculation

The cubic exponential error comes from the library's proved exponential power
series. Centering cancels the linear term. Multiplying by exp(t²v/2) cancels
the conditional quadratic term up to an explicit error O(εv).
-/
namespace IdlaCyl
open scoped BigOperators
noncomputable section

namespace Characteristic

def phase (t x : ℝ) : ℂ := Complex.I * (t:ℂ) * (x:ℂ)

@[simp] theorem norm_phase (t x : ℝ) : ‖phase t x‖ = |t|  * |x| := by
  simp [phase, Complex.norm_real, Real.norm_eq_abs]

theorem phase_square (t x : ℝ) : (phase t x)^2 = -((t^2*x^2 : ℝ):ℂ) := by
  simp only [phase, mul_pow, Complex.I_sq, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

/-- Explicit Taylor remainder; the weaker coefficient one is intentional. -/
theorem exp_cubic_remainder (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z-(1+z+z^2/2)‖ ≤ ‖z‖^3 := by
  have h := Complex.exp_bound hz (n := 3) (by decide)
  have hp : (∑ m ∈ Finset.range 3, z^m/(m.factorial:ℂ)) = 1+z+z^2/2 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hp] at h
  calc
    _ ≤ ‖z‖^3 * ((4:ℝ)*(6*3)⁻¹) := by simpa [Nat.factorial] using h
    _ ≤ ‖z‖^3 := by nlinarith [pow_nonneg (norm_nonneg z) 3]

theorem real_exp_remainder_abs (x : ℝ) (hx : |x| ≤ 1) :
    |Real.exp x-1-x| ≤ x^2 := by
  have h := Complex.norm_exp_sub_one_sub_id_le
    (x := (x:ℂ)) (by simpa using hx)
  simpa only [← Complex.ofReal_exp, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

theorem real_exp_sub_one_abs (x : ℝ) (hx : |x| ≤ 1) :
    |Real.exp x-1| ≤ 2 * |x| := by
  have h := Complex.norm_exp_sub_one_le (x := (x:ℂ)) (by simpa using hx)
  simpa only [← Complex.ofReal_exp, ← Complex.ofReal_one,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h

/-- The compensation error is quadratic in the conditional variance. -/
theorem scalar_compensation (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    |Real.exp b*(1-b)-1| ≤ 3*b^2 := by
  have hab : |b| ≤ 1 := by rwa [abs_of_nonneg hb0]
  have h1 := real_exp_remainder_abs b hab
  have h2 := real_exp_sub_one_abs b hab
  calc
    _ = |(Real.exp b-1-b)-b*(Real.exp b-1)| := by congr 1; ring
    _ ≤ |Real.exp b-1-b| + |b*(Real.exp b-1)| := abs_sub _ _
    _ = |Real.exp b-1-b| + b * |Real.exp b-1| := by rw [abs_mul, abs_of_nonneg hb0]
    _ ≤ b^2+b*(2 * |b|) := add_le_add h1 (mul_le_mul_of_nonneg_left h2 hb0)
    _ = 3*b^2 := by rw [abs_of_nonneg hb0]; ring

end Characteristic

namespace FiniteLaw
open Characteristic
variable {S : Type*} [Fintype S]

/-- Centered characteristic expansion with a cubic, not quadratic, error. -/
theorem characteristic_second_order (μ : FiniteLaw S) (X : S → ℝ) (t ε : ℝ)
    (_hε : 0 ≤ ε) (hsmall : |t| *ε ≤ 1)
    (hbound : ∀ x, 0 < μ.weight x → |X x| ≤ ε)
    (hmean : μ.expect X = 0) :
    ‖μ.cexpect (fun x => Complex.exp (phase t (X x))) -
      (1-((t^2/2 * μ.expect (fun x => X x^2):ℝ):ℂ))‖ ≤
      (|t|^3*ε) * μ.expect (fun x => X x^2) := by
  let poly : S → ℂ := fun x => 1+phase t (X x)+(phase t (X x))^2/2
  have hpoly (x : S) : poly x =
      1 + Complex.I*(t:ℂ)*(X x:ℂ) - ((t^2/2 * X x^2:ℝ):ℂ) := by
    dsimp [poly]
    rw [phase_square]
    dsimp [phase]
    push_cast
    ring
  have hp : μ.cexpect poly =
      1-((t^2/2 * μ.expect (fun x => X x^2):ℝ):ℂ) := by
    have hpolyfun : poly = fun x =>
        1 + Complex.I*(t:ℂ)*(X x:ℂ) - ((t^2/2 * X x^2:ℝ):ℂ) := funext hpoly
    rw [hpolyfun]
    simp only [cexpect_sub, cexpect_add, cexpect_const,
      cexpect_const_mul, cexpect_ofReal, expect_const_mul, hmean]
    push_cast
    ring
  have hlocal (x : S) (hx : 0 < μ.weight x) :
      ‖Complex.exp (phase t (X x))-poly x‖ ≤ (|t|^3*ε)*X x^2 := by
    have hxi := hbound x hx
    have hz : ‖phase t (X x)‖ ≤ 1 := by
      rw [norm_phase]
      exact (mul_le_mul_of_nonneg_left hxi (abs_nonneg t)).trans hsmall
    calc
      _ ≤ ‖phase t (X x)‖^3 := exp_cubic_remainder _ hz
      _ = (|t|^3 * |X x|)*X x^2 := by
        rw [norm_phase, mul_pow, ← sq_abs (X x)]
        ring
      _ ≤ _ := by
        have hmul := mul_le_mul_of_nonneg_left hxi (pow_nonneg (abs_nonneg t) 3)
        exact mul_le_mul_of_nonneg_right hmul (sq_nonneg _)
  calc
    _ = ‖μ.cexpect (fun x => Complex.exp (phase t (X x))-poly x)‖ := by
      rw [cexpect_sub, hp]
    _ ≤ μ.expect (fun x => (|t|^3*ε)*X x^2) := norm_cexpect_le_support _ _ _ hlocal
    _ = _ := expect_const_mul _ _ _

/-- The local error coefficient used by the compensated exponential. -/
def characteristicError (t : ℝ) : ℝ := Real.exp 1 * |t|^3 + 3*t^4/4

theorem characteristicError_nonneg (t : ℝ) : 0 ≤ characteristicError t := by
  unfold characteristicError
  positivity

/-- One-step compensated characteristic estimate, completely in finite-law algebra. -/
theorem compensated_characteristic (μ : FiniteLaw S) (X : S → ℝ) (t ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hsmall : |t| *ε ≤ 1)
    (hbound : ∀ x, 0 < μ.weight x → |X x| ≤ ε)
    (hmean : μ.expect X = 0) :
    ‖((Real.exp (t^2/2 * μ.expect (fun x => X x^2)):ℝ):ℂ) *
        μ.cexpect (fun x => Complex.exp (phase t (X x))) - 1‖ ≤
      characteristicError t * ε * μ.expect (fun x => X x^2) := by
  let v := μ.expect (fun x => X x^2)
  let b := t^2/2*v
  let F := μ.cexpect (fun x => Complex.exp (phase t (X x)))
  have hv0 : 0 ≤ v := μ.expect_nonneg (fun x => sq_nonneg _)
  have hvε : v ≤ ε^2 := by
    calc
      _ ≤ μ.expect (fun _ => ε^2) := by
        apply μ.expect_mono_support
        intro x hx
        have hh := hbound x hx
        rw [← sq_abs (X x)]
        exact pow_le_pow_left₀ (abs_nonneg _) hh 2
      _ = _ := μ.expect_const _
  have hvε' : v ≤ ε := by nlinarith
  have htε : t^2*ε^2 ≤ 1 := by
    have he : (|t| *ε)^2 = t^2*ε^2 := by rw [mul_pow, sq_abs]
    have hp : 0 ≤ |t| *ε := mul_nonneg (abs_nonneg t) hε0
    nlinarith
  have htv : t^2*v ≤ t^2*ε^2 := mul_le_mul_of_nonneg_left hvε (sq_nonneg t)
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b]; nlinarith
  have hh : ‖F-(1-(b:ℂ))‖ ≤ (|t|^3*ε)*v :=
    characteristic_second_order μ X t ε hε0 hsmall hbound hmean
  have hcomp := scalar_compensation b hb0 hb1
  have hpow : v^2 ≤ ε*v := by nlinarith
  have hpower : 3*b^2 ≤ (3*t^4/4)*ε*v := by
    have h := mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ 3*t^4/4 by positivity)
    dsimp [b]
    nlinarith
  have he : Real.exp b ≤ Real.exp 1 := Real.exp_le_exp.mpr hb1
  change ‖((Real.exp b:ℝ):ℂ)*F-1‖ ≤ characteristicError t*ε*v
  calc
    _ = ‖((Real.exp b:ℝ):ℂ)*(F-(1-(b:ℂ))) +
        ((Real.exp b*(1-b)-1:ℝ):ℂ)‖ := by congr 1; push_cast; ring
    _ ≤ ‖((Real.exp b:ℝ):ℂ)*(F-(1-(b:ℂ)))‖ +
        ‖((Real.exp b*(1-b)-1:ℝ):ℂ)‖ := norm_add_le _ _
    _ = Real.exp b*‖F-(1-(b:ℂ))‖ + |Real.exp b*(1-b)-1| := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
    _ ≤ Real.exp 1*((|t|^3*ε)*v)+3*b^2 := by
      apply add_le_add _ hcomp
      exact mul_le_mul he hh (norm_nonneg _) (Real.exp_nonneg _)
    _ ≤ Real.exp 1*((|t|^3*ε)*v)+(3*t^4/4)*ε*v := add_le_add le_rfl hpower
    _ = _ := by unfold characteristicError; ring

end FiniteLaw
end
end IdlaCyl
