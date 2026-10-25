module

public import IdlaCyl.Support.FiniteProbability

@[expose] public section

set_option autoImplicit false

/-!
# Efron--Stein by induction on the number of finite independent coordinates

`resamplingCost` is the sum of squared changes under one-coordinate independent
resampling, expressed recursively. The variance bound is proved from the finite
sum identities in `FiniteProbability`; it is not imported or assumed.
-/

namespace IdlaCyl

noncomputable section

universe u

/-- Right-associated products keep coordinate induction explicit. -/
def ProductSpace (α : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => α × ProductSpace α n

instance productSpaceFintype (α : Type u) [Fintype α] (n : ℕ) :
    Fintype (ProductSpace α n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit.{u + 1})
  | succ n ih =>
      letI : Fintype (ProductSpace α n) := ih
      exact inferInstanceAs (Fintype (α × ProductSpace α n))

namespace FiniteLaw

variable {α : Type u} [Fintype α]

def unitLaw : FiniteLaw PUnit.{u + 1} where
  weight _ := 1
  nonneg _ := zero_le_one
  total := by simp

def productLaw (μ : FiniteLaw α) : (n : ℕ) → FiniteLaw (ProductSpace α n)
  | 0 => unitLaw
  | n + 1 => μ.prod (productLaw μ n)

/-- Sum over coordinates of the independent-copy squared difference. -/
def resamplingCost (μ : FiniteLaw α) :
    (n : ℕ) → (ProductSpace α n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, f =>
      (μ.productLaw n).expect (fun y => μ.expect (fun x => μ.expect (fun x' =>
        (f (x, y) - f (x', y)) ^ 2))) +
      μ.expect (fun x => resamplingCost μ n (fun y => f (x, y)))

@[simp] theorem variance_unit (f : PUnit.{u + 1} → ℝ) : unitLaw.variance f = 0 := by
  simp [variance, expect, unitLaw]

/-- Twice the variance is bounded by the total independent-resampling cost. -/
theorem efron_stein_twice (μ : FiniteLaw α) (n : ℕ)
    (f : ProductSpace α n → ℝ) :
    2 * (μ.productLaw n).variance f ≤ μ.resamplingCost n f := by
  induction n with
  | zero =>
      show 2 * unitLaw.variance f ≤ (0 : ℝ)
      rw [variance_unit]
      norm_num
  | succ n ih =>
      let ν := μ.productLaw n
      have hind : 2 * μ.expect (fun x => ν.variance (fun y => f (x, y))) ≤
          μ.expect (fun x => μ.resamplingCost n (fun y => f (x, y))) := by
        rw [← expect_const_mul]
        apply μ.expect_mono
        intro x
        exact ih (fun y => f (x, y))
      have havg : μ.variance (fun x => ν.expect (fun y => f (x, y))) ≤
          ν.expect (fun y => μ.variance (fun x => f (x, y))) :=
        μ.variance_expect_le ν (fun x y => f (x, y))
      have hcost : ν.expect (fun y => μ.expect (fun x => μ.expect (fun x' =>
          (f (x, y) - f (x', y)) ^ 2))) =
          2 * ν.expect (fun y => μ.variance (fun x => f (x, y))) := by
        simp_rw [iid_difference_eq]
        exact ν.expect_const_mul 2 _
      change 2 * (μ.prod ν).variance f ≤
        ν.expect (fun y => μ.expect (fun x => μ.expect (fun x' =>
          (f (x, y) - f (x', y)) ^ 2))) +
        μ.expect (fun x => μ.resamplingCost n (fun y => f (x, y)))
      have hvar := μ.variance_prod ν (fun x y => f (x, y))
      have hf : (fun z : α × ProductSpace α n => f (z.1, z.2)) = f := by
        funext z
        cases z
        rfl
      rw [hf] at hvar
      rw [hvar, hcost]
      linarith

/-- The usual factor 1/2, proved including the degenerate case. -/
theorem efron_stein (μ : FiniteLaw α) (n : ℕ)
    (f : ProductSpace α n → ℝ) :
    (μ.productLaw n).variance f ≤ μ.resamplingCost n f / 2 := by
  have h := μ.efron_stein_twice n f
  linarith

end FiniteLaw
end
end IdlaCyl
