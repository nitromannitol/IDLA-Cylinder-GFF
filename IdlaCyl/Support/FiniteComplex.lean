import IdlaCyl.Support.FiniteProcess

set_option autoImplicit false

/-! # Complex expectation and drift telescoping over the constructed finite law -/
namespace IdlaCyl
open scoped BigOperators
noncomputable section
namespace FiniteLaw
variable {S T : Type*} [Fintype S] [Fintype T]

def cexpect (μ : FiniteLaw S) (f : S → ℂ) : ℂ :=
  ∑ x, (μ.weight x : ℂ) * f x

@[simp] theorem cexpect_ofReal (μ : FiniteLaw S) (f : S → ℝ) :
    μ.cexpect (fun x => (f x : ℂ)) = (μ.expect f : ℂ) := by
  simp [cexpect, expect]

theorem cexpect_congr (μ : FiniteLaw S) {f g : S → ℂ} (h : ∀ x, f x=g x) :
    μ.cexpect f=μ.cexpect g := by simp only [cexpect, h]

theorem cexpect_congr_support (μ : FiniteLaw S) {f g : S → ℂ}
    (h : ∀ x, 0 < μ.weight x → f x=g x) : μ.cexpect f=μ.cexpect g := by
  unfold cexpect
  apply Finset.sum_congr rfl
  intro x _
  rcases eq_or_lt_of_le (μ.nonneg x) with hx | hx
  · simp [← hx]
  · rw [h x hx]

@[simp] theorem cexpect_const (μ : FiniteLaw S) (z : ℂ) :
    μ.cexpect (fun _ => z) = z := by
  unfold cexpect
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, μ.total]
  simp

@[simp] theorem cexpect_add (μ : FiniteLaw S) (f g : S → ℂ) :
    μ.cexpect (fun x => f x+g x)=μ.cexpect f+μ.cexpect g := by
  simp [cexpect, mul_add, Finset.sum_add_distrib]

@[simp] theorem cexpect_sub (μ : FiniteLaw S) (f g : S → ℂ) :
    μ.cexpect (fun x => f x-g x)=μ.cexpect f-μ.cexpect g := by
  simp [cexpect, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem cexpect_const_mul (μ : FiniteLaw S) (z : ℂ) (f : S → ℂ) :
    μ.cexpect (fun x => z*f x)=z*μ.cexpect f := by
  simp only [cexpect, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

@[simp] theorem cexpect_mul_const (μ : FiniteLaw S) (f : S → ℂ) (z : ℂ) :
    μ.cexpect (fun x => f x*z)=μ.cexpect f*z := by
  simp only [cexpect, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

@[simp] theorem cexpect_bind (μ : FiniteLaw S) (κ : S → FiniteLaw T) (f : T → ℂ) :
    (μ.bind κ).cexpect f = μ.cexpect (fun x => (κ x).cexpect f) := by
  simp only [cexpect, bind, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- The finite-integral triangle inequality, including null weights. -/
theorem norm_cexpect_le (μ : FiniteLaw S) (f : S → ℂ) :
    ‖μ.cexpect f‖ ≤ μ.expect (fun x => ‖f x‖) := by
  calc
    _ ≤ ∑ x, ‖(μ.weight x : ℂ)*f x‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      simp [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (μ.nonneg x)]

theorem norm_cexpect_le_support (μ : FiniteLaw S) (f : S → ℂ) (g : S → ℝ)
    (h : ∀ x, 0 < μ.weight x → ‖f x‖ ≤ g x) :
    ‖μ.cexpect f‖ ≤ μ.expect g :=
  (norm_cexpect_le μ f).trans (μ.expect_mono_support h)

end FiniteLaw

namespace FiniteProcess
variable {S : Type*} [Fintype S]

@[simp] theorem cexpect_succ (P : FiniteProcess S) (n : ℕ) (f : S → ℂ) :
    (P.law (n+1)).cexpect f =
      (P.law n).cexpect (fun x => (P.transition n x).cexpect f) := by
  exact FiniteLaw.cexpect_bind _ _ _

/-- Complex drift telescoping, proved by the same explicit bind algebra. -/
theorem cexpect_telescope (P : FiniteProcess S) (F : ℕ → S → ℂ) (n : ℕ) :
    (P.law n).cexpect (F n)-P.initial.cexpect (F 0) =
      ∑ k ∈ Finset.range n, (P.law k).cexpect
        (fun x => (P.transition k x).cexpect (F (k+1))-F k x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih, FiniteLaw.cexpect_sub, cexpect_succ]
      ring

/-- Sum of local complex drift bounds. There is no independence assertion here. -/
theorem norm_cexpect_telescope_le (P : FiniteProcess S) (F : ℕ → S → ℂ)
    (rate : ℕ → S → ℝ) (C : ℝ) (n : ℕ)
    (h : ∀ k < n, ∀ x, P.reachable k x →
      ‖(P.transition k x).cexpect (F (k+1))-F k x‖ ≤ C*rate k x) :
    ‖(P.law n).cexpect (F n)-P.initial.cexpect (F 0)‖ ≤
      C * ∑ k ∈ Finset.range n, (P.law k).expect (rate k) := by
  rw [P.cexpect_telescope, Finset.mul_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range n, ‖(P.law k).cexpect
        (fun x => (P.transition k x).cexpect (F (k+1))-F k x)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← FiniteLaw.expect_const_mul]
      exact FiniteLaw.norm_cexpect_le_support _ _ _
        (h k (Finset.mem_range.mp hk))

end FiniteProcess
end
end IdlaCyl
