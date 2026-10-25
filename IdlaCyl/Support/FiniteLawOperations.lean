module

public import IdlaCyl.Support.FiniteProbability

@[expose] public section

set_option autoImplicit false

/-!
# Constructed finite kernels and events

These are finite sums, not axioms about conditional probabilities. `bind` is
constructed from the transition weights. Null-weight states are handled
explicitly: a local assertion is needed only on the support of its law.
-/
namespace IdlaCyl
open scoped BigOperators
noncomputable section
namespace FiniteLaw
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Probability of a predicate, including null events. -/
def event (μ : FiniteLaw α) (E : α → Prop) : ℝ := by
  classical
  exact μ.expect (fun x => if E x then 1 else 0)

theorem expect_congr_support (μ : FiniteLaw α) {f g : α → ℝ}
    (h : ∀ x, 0 < μ.weight x → f x = g x) : μ.expect f = μ.expect g := by
  unfold expect
  apply Finset.sum_congr rfl
  intro x _
  rcases eq_or_lt_of_le (μ.nonneg x) with hx | hx
  · simp [← hx]
  · rw [h x hx]

theorem expect_mono_support (μ : FiniteLaw α) {f g : α → ℝ}
    (h : ∀ x, 0 < μ.weight x → f x ≤ g x) : μ.expect f ≤ μ.expect g := by
  unfold expect
  apply Finset.sum_le_sum
  intro x _
  rcases eq_or_lt_of_le (μ.nonneg x) with hx | hx
  · simp [← hx]
  · exact mul_le_mul_of_nonneg_left (h x hx) hx.le

def bind (μ : FiniteLaw α) (κ : α → FiniteLaw β) : FiniteLaw β where
  weight y := ∑ x, μ.weight x * (κ x).weight y
  nonneg y := Finset.sum_nonneg (fun x _ => mul_nonneg (μ.nonneg x) ((κ x).nonneg y))
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, FiniteLaw.total, mul_one]

@[simp] theorem expect_bind (μ : FiniteLaw α) (κ : α → FiniteLaw β) (f : β → ℝ) :
    (μ.bind κ).expect f = μ.expect (fun x => (κ x).expect f) := by
  simp only [expect, bind, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Finite dependent joint law: draw x, then draw y using κ x. -/
def joint (μ : FiniteLaw α) (κ : α → FiniteLaw β) : FiniteLaw (α × β) where
  weight z := μ.weight z.1 * (κ z.1).weight z.2
  nonneg z := mul_nonneg (μ.nonneg z.1) ((κ z.1).nonneg z.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, FiniteLaw.total, mul_one]

@[simp] theorem expect_joint (μ : FiniteLaw α) (κ : α → FiniteLaw β)
    (f : α × β → ℝ) :
    (μ.joint κ).expect f = μ.expect (fun x => (κ x).expect (fun y => f (x,y))) := by
  simp only [expect, joint, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- The deterministic law is normalized by construction. -/
def point (a : α) : FiniteLaw α := by
  classical
  exact {
    weight := fun x => if x = a then 1 else 0
    nonneg := by intro x; split_ifs <;> norm_num
    total := by simp }

@[simp] theorem expect_point (a : α) (f : α → ℝ) : (point a).expect f = f a := by
  classical
  simp [point, expect]

def map (μ : FiniteLaw α) (f : α → β) : FiniteLaw β := μ.bind (fun x => point (f x))

@[simp] theorem expect_map (μ : FiniteLaw α) (f : α → β) (g : β → ℝ) :
    (μ.map f).expect g = μ.expect (fun x => g (f x)) := by
  simp [map]

theorem event_nonneg (μ : FiniteLaw α) (E : α → Prop) : 0 ≤ μ.event E := by
  classical
  apply μ.expect_nonneg
  intro x
  split_ifs <;> norm_num

theorem event_le_one (μ : FiniteLaw α) (E : α → Prop) : μ.event E ≤ 1 := by
  classical
  calc
    μ.event E ≤ μ.expect (fun _ => 1) := by
      apply μ.expect_mono
      intro x
      split_ifs <;> norm_num
    _ = 1 := μ.expect_const 1

theorem event_mono (μ : FiniteLaw α) {E F : α → Prop}
    (h : ∀ x, E x → F x) : μ.event E ≤ μ.event F := by
  classical
  apply μ.expect_mono
  intro x
  by_cases he : E x
  · simp [he, h x he]
  · simp only [he, if_false]
    split_ifs <;> norm_num

theorem event_or_le (μ : FiniteLaw α) (E F : α → Prop) :
    μ.event (fun x => E x ∨ F x) ≤ μ.event E + μ.event F := by
  classical
  simp only [event]
  rw [← expect_add]
  apply μ.expect_mono
  intro x
  by_cases he : E x <;> by_cases hf : F x <;> simp [he, hf]

theorem event_false (μ : FiniteLaw α) : μ.event (fun _ => False) = 0 := by
  classical
  simp [event]

theorem event_not (μ : FiniteLaw α) (E : α → Prop) :
    μ.event (fun x => ¬ E x) = 1 - μ.event E := by
  classical
  calc
    μ.event (fun x => ¬ E x) = μ.expect (fun x => 1 - if E x then 1 else 0) := by
      apply μ.expect_congr
      intro x
      by_cases h : E x <;> simp [h]
    _ = 1 - μ.event E := by rw [expect_sub, expect_const]; rfl

omit [Fintype β] in
/-- The finite union bound, with no independence requirement. -/
theorem event_exists_le (μ : FiniteLaw α) (s : Finset β) (E : β → α → Prop) :
    μ.event (fun x => ∃ b ∈ s, E b x) ≤ ∑ b ∈ s, μ.event (E b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [event]
  | @insert b s hb ih =>
      have heq : (fun x => ∃ z ∈ insert b s, E z x) =
          (fun x => E b x ∨ ∃ z ∈ s, E z x) := by
        funext x
        simp
      rw [heq, Finset.sum_insert hb]
      exact (μ.event_or_le _ _).trans (add_le_add le_rfl ih)

/-- Markov's inequality in multiplication form, so the zero-threshold case is honest. -/
theorem event_mul_le_expect (μ : FiniteLaw α) (f : α → ℝ) (b : ℝ)
    (hf : ∀ x, 0 ≤ f x) : b * μ.event (fun x => b ≤ f x) ≤ μ.expect f := by
  classical
  calc
    b * μ.event (fun x => b ≤ f x) =
        μ.expect (fun x => b * if b ≤ f x then 1 else 0) := by rw [expect_const_mul]; rfl
    _ ≤ μ.expect f := by
      apply μ.expect_mono
      intro x
      by_cases h : b ≤ f x
      · simp [h]
      · simpa [h] using hf x

/-- Exponential Markov bound without division or a positive-threshold restriction. -/
theorem upper_laplace (μ : FiniteLaw α) (f : α → ℝ) (b lam : ℝ) (hlam : 0 ≤ lam) :
    μ.event (fun x => b ≤ f x) ≤
      Real.exp (-lam * b) * μ.expect (fun x => Real.exp (lam * f x)) := by
  classical
  have h : Real.exp (lam * b) * μ.event (fun x => b ≤ f x) ≤
      μ.expect (fun x => Real.exp (lam * f x)) := by
    calc
      _ = μ.expect (fun x => Real.exp (lam * b) * if b ≤ f x then 1 else 0) := by
        rw [expect_const_mul]; rfl
      _ ≤ _ := by
        apply μ.expect_mono
        intro x
        by_cases hx : b ≤ f x
        · simp only [hx, if_true, mul_one]
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx hlam)
        · simp [hx, (Real.exp_pos (lam * f x)).le]
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (-lam * b)).le
  have he : Real.exp (-lam * b) * Real.exp (lam * b) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  simpa only [← mul_assoc, he, one_mul] using hm

end FiniteLaw
end
end IdlaCyl
