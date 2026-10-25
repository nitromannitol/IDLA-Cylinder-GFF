module

/-
Discrete harmonic functions on the cylinder and the exponential modes.

`tex:679-684` defines `ψ` discrete harmonic by
`E[ψ(S_1) | S_0 = p] = ψ(p)`.  Unfolding `cylKernel` (`tex:246-255`) gives
exactly the three-term operator below: the vertical neighbours get weight
`1/4` each and the horizontal layer gets weight `1/2` times the base kernel
`P_N`.

`tex:716-723` (`pr:hextension`) builds the harmonic extension of a test
function from the eigenmodes `f_k` with rate `q_k` solving `cosh q_k = 2 - λ_k`.
This file lands the harmonic-operator core of that proposition, on the
canonical `Site B` / `Base.P`: closure properties of the operator, the
exponential modes and their upward/downward shifts, the harmonicity of a mode
from the eigen-equation and `cosh q = 2 - λ`, the finite linear combination, the
zero horizontal average of a mean-zero mode, and the downward exponential decay
needed for optional stopping.

Everything is a finite sum; there is no `tsum` or `finsum` and hence no junk
branch.  The integral form `∫ ψ d(cylMeasure p) = ψ p` is proved in
`Support/HarmonicIntegral.lean`.
-/
public import IdlaCyl.Support.Cylinder

@[expose] public section

namespace IdlaCyl

open scoped BigOperators

variable (B : Base)

/-! ### The harmonic operator -/

/-- The one-step operator of the cylinder walk (`tex:246-255`, `tex:681-684`):
`(1/4)` to each vertical neighbour plus `(1/2)` times the base kernel on the
horizontal layer. -/
noncomputable def cylinderOp (ψ : Site B → ℝ) (p : Site B) : ℝ :=
  (1 / 4) * ψ (p.1, p.2 + 1) + (1 / 4) * ψ (p.1, p.2 - 1)
    + (1 / 2) * ∑ x' : B.V, B.P p.1 x' * ψ (x', p.2)

/-- `ψ` is discrete harmonic (`tex:679-684`): its value is its one-step
expectation under the cylinder kernel. -/
def DiscreteHarmonic (ψ : Site B → ℝ) : Prop :=
  ∀ p : Site B, cylinderOp B ψ p = ψ p

@[simp]
theorem cylinderOp_const (c : ℝ) (p : Site B) :
    cylinderOp B (fun _ => c) p = c := by
  have hrow : (∑ x' : B.V, B.P p.1 x' * c) = c := by
    rw [← Finset.sum_mul, B.P_row_sum p.1, one_mul]
  unfold cylinderOp
  rw [hrow]
  ring

theorem cylinderOp_add (F H : Site B → ℝ) (p : Site B) :
    cylinderOp B (fun q => F q + H q) p = cylinderOp B F p + cylinderOp B H p := by
  simp only [cylinderOp]
  rw [show (∑ x' : B.V, B.P p.1 x' * (F (x', p.2) + H (x', p.2)))
      = ∑ x' : B.V, (B.P p.1 x' * F (x', p.2) + B.P p.1 x' * H (x', p.2)) by
        apply Finset.sum_congr rfl
        intro x' _
        ring]
  rw [Finset.sum_add_distrib]
  ring

theorem cylinderOp_const_mul (c : ℝ) (F : Site B → ℝ) (p : Site B) :
    cylinderOp B (fun q => c * F q) p = c * cylinderOp B F p := by
  have hsum : (∑ x' : B.V, B.P p.1 x' * (c * F (x', p.2)))
      = c * ∑ x' : B.V, B.P p.1 x' * F (x', p.2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x' _
    ring
  unfold cylinderOp
  rw [hsum]
  ring

theorem discreteHarmonic_const (c : ℝ) : DiscreteHarmonic B (fun _ => c) :=
  fun p => cylinderOp_const B c p

theorem discreteHarmonic_add {F H : Site B → ℝ} (hF : DiscreteHarmonic B F)
    (hH : DiscreteHarmonic B H) : DiscreteHarmonic B (fun q => F q + H q) :=
  fun p => by rw [cylinderOp_add, hF p, hH p]

theorem discreteHarmonic_const_mul (c : ℝ) {F : Site B → ℝ}
    (hF : DiscreteHarmonic B F) : DiscreteHarmonic B (fun q => c * F q) :=
  fun p => by rw [cylinderOp_const_mul, hF p]

theorem discreteHarmonic_finset_sum {I : Type*} (s : Finset I) (F : I → Site B → ℝ)
    (hF : ∀ i ∈ s, DiscreteHarmonic B (F i)) :
    DiscreteHarmonic B (fun q => ∑ i ∈ s, F i q) := by
  classical
  revert hF
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa using discreteHarmonic_const B 0
  | @insert i s hi ih =>
      intro hF
      have h1 : DiscreteHarmonic B (F i) := hF i (by simp)
      have hs : ∀ j ∈ s, DiscreteHarmonic B (F j) := by
        intro j hj
        exact hF j (by simp [hj])
      simpa only [Finset.sum_insert hi] using discreteHarmonic_add B h1 (ih hs)

/-! ### The exponential modes -/

/-- A single mode with reference height `h` (`tex:740-746`):
`f(x) e^{q(y-h)}`.  `h` is real so that `T/N` is allowed. -/
noncomputable def exponentialMode (f : B.V → ℝ) (q h : ℝ) (p : Site B) : ℝ :=
  f p.1 * Real.exp (q * ((p.2 : ℝ) - h))

theorem exponentialMode_up (f : B.V → ℝ) (q h : ℝ) (x : B.V) (y : ℤ) :
    exponentialMode B f q h (x, y + 1) = exponentialMode B f q h (x, y) * Real.exp q := by
  unfold exponentialMode
  simp only [Int.cast_add, Int.cast_one]
  rw [show q * ((y : ℝ) + 1 - h) = q * ((y : ℝ) - h) + q by ring, Real.exp_add]
  ring

theorem exponentialMode_down (f : B.V → ℝ) (q h : ℝ) (x : B.V) (y : ℤ) :
    exponentialMode B f q h (x, y - 1) = exponentialMode B f q h (x, y) * Real.exp (-q) := by
  unfold exponentialMode
  simp only [Int.cast_sub, Int.cast_one]
  rw [show q * ((y : ℝ) - 1 - h) = q * ((y : ℝ) - h) + (-q) by ring, Real.exp_add]
  ring

@[simp]
theorem exponentialMode_boundary (f : B.V → ℝ) (q : ℝ) (h : ℤ) (x : B.V) :
    exponentialMode B f q (h : ℝ) (x, h) = f x := by
  simp [exponentialMode]

/-- A mode is harmonic when `f` is an eigenvector with eigenvalue `lam` and
`q` satisfies `(e^q + e^{-q})/2 = 2 - lam` (`tex:738-746`). -/
theorem exponentialMode_harmonic_of_exp (f : B.V → ℝ) (lam q h : ℝ)
    (heig : ∀ x : B.V, ∑ x' : B.V, B.P x x' * f x' = lam * f x)
    (hq : (Real.exp q + Real.exp (-q)) / 2 = 2 - lam) :
    DiscreteHarmonic B (exponentialMode B f q h) := by
  intro p
  rcases p with ⟨x, y⟩
  have hh : (∑ x' : B.V, B.P x x' * exponentialMode B f q h (x', y))
      = lam * exponentialMode B f q h (x, y) := by
    unfold exponentialMode
    rw [show (∑ x' : B.V, B.P x x' * (f x' * Real.exp (q * ((y : ℝ) - h))))
        = (∑ x' : B.V, B.P x x' * f x') * Real.exp (q * ((y : ℝ) - h)) by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x' _
          ring]
    rw [heig x]
    ring
  change (1 / 4) * exponentialMode B f q h (x, y + 1)
      + (1 / 4) * exponentialMode B f q h (x, y - 1)
      + (1 / 2) * (∑ x' : B.V, B.P x x' * exponentialMode B f q h (x', y))
      = exponentialMode B f q h (x, y)
  rw [exponentialMode_up, exponentialMode_down, hh]
  calc
    (1 / 4) * (exponentialMode B f q h (x, y) * Real.exp q)
        + (1 / 4) * (exponentialMode B f q h (x, y) * Real.exp (-q))
        + (1 / 2) * (lam * exponentialMode B f q h (x, y))
        = exponentialMode B f q h (x, y) *
            (((Real.exp q + Real.exp (-q)) / 2 + lam) / 2) := by ring
    _ = exponentialMode B f q h (x, y) := by rw [hq]; ring

/-- `pr:hextension`'s harmonicity clause for one mode (`tex:716-723`). -/
theorem exponentialMode_harmonic (f : B.V → ℝ) (lam q h : ℝ)
    (heig : ∀ x : B.V, ∑ x' : B.V, B.P x x' * f x' = lam * f x)
    (hq : Real.cosh q = 2 - lam) :
    DiscreteHarmonic B (exponentialMode B f q h) :=
  exponentialMode_harmonic_of_exp B f lam q h heig (by simpa only [Real.cosh_eq] using hq)

/-- The finite linear combination in `pr:hextension` (`tex:716-723`). -/
theorem finiteMode_harmonic {I : Type*} (s : Finset I) (f : I → B.V → ℝ)
    (lam q c : I → ℝ) (h : ℝ)
    (heig : ∀ i ∈ s, ∀ x : B.V, ∑ x' : B.V, B.P x x' * f i x' = lam i * f i x)
    (hq : ∀ i ∈ s, Real.cosh (q i) = 2 - lam i) :
    DiscreteHarmonic B (fun p => ∑ i ∈ s, c i * exponentialMode B (f i) (q i) h p) := by
  apply discreteHarmonic_finset_sum
  intro i hi
  exact discreteHarmonic_const_mul B (c i)
    (exponentialMode_harmonic B (f i) (lam i) (q i) h (heig i hi) (hq i hi))

/-- A mean-zero mode stays mean zero on every horizontal layer, i.e. it has the
zero horizontal average property (`tex:356-361`). -/
theorem exponentialMode_sum_zero (f : B.V → ℝ) (q h : ℝ)
    (hf : ∑ x : B.V, f x = 0) (y : ℤ) :
    ∑ x : B.V, exponentialMode B f q h (x, y) = 0 := by
  unfold exponentialMode
  rw [show (∑ x : B.V, f (x, y).1 * Real.exp (q * (((x, y).2 : ℝ) - h)))
      = ∑ x : B.V, f x * Real.exp (q * ((y : ℝ) - h)) from
        Finset.sum_congr rfl fun x _ => rfl]
  rw [← Finset.sum_mul, hf, zero_mul]

/-! ### Exponential decay as `y → -∞` -/

/-- Exponential decay downwards (`tex:689`, `tex:700`): the admissibility
condition of `pr:hextension` and `le:martingale`. -/
def ExpDecayBelow (ψ : Site B → ℝ) : Prop :=
  ∃ C c : ℝ, 0 < c ∧ ∀ p : Site B, p.2 ≤ 0 → |ψ p| ≤ C * Real.exp (c * (p.2 : ℝ))

/-- A mode with `q ≥ 0` decays downwards at rate `q` (up to the fixed factor
`|f x|`), `tex:689`. -/
theorem abs_exponentialMode_le (f : B.V → ℝ) (q h : ℝ) (hq : 0 ≤ q) (p : Site B)
    (hp : (p.2 : ℝ) ≤ h) :
    |exponentialMode B f q h p| ≤ |f p.1| := by
  have ht : q * ((p.2 : ℝ) - h) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hq (sub_nonpos.mpr hp)
  have he : Real.exp (q * ((p.2 : ℝ) - h)) ≤ 1 := by
    calc
      Real.exp (q * ((p.2 : ℝ) - h)) ≤ Real.exp 0 := Real.exp_le_exp.mpr ht
      _ = 1 := Real.exp_zero
  unfold exponentialMode
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  simpa using mul_le_mul_of_nonneg_left he (abs_nonneg (f p.1))

/-- A concrete bound on a stopped mode below the reference height. -/
theorem exponentialMode_bounded_below (f : B.V → ℝ) (q h : ℝ) (hq : 0 ≤ q) (p : Site B)
    (hp : (p.2 : ℝ) ≤ h) :
    |exponentialMode B f q h p| ≤ ∑ x : B.V, |f x| := by
  classical
  exact (abs_exponentialMode_le B f q h hq p hp).trans
    (Finset.single_le_sum (fun x _ => abs_nonneg (f x)) (Finset.mem_univ p.1))

end IdlaCyl
