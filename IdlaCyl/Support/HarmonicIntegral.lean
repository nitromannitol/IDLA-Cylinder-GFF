module

/-
The integral form of discrete harmonicity.

`tex:679-684` defines `ψ` discrete harmonic by the one-step expectation under
the cylinder kernel.  The canonical one-step law is `cylMeasure B p`, a
`Measure.sum` of Dirac masses weighted by `cylKernel`.  This file proves that
the one-step expectation *is* the integral against `cylMeasure`,

  `∫ q, ψ q ∂(cylMeasure B p) = (1/4)ψ(p.1,p.2+1) + (1/4)ψ(p.1,p.2-1)
      + (1/2) ∑ x', B.P p.1 x' ψ(x',p.2)`,

and hence `DiscreteHarmonic B ψ ↔ ∀ p, ∫ ψ ∂(cylMeasure B p) = ψ p`.  This is
the bridge that lets the optional-stopping and martingale arguments (which work
with the walk law) consume the operator form of harmonicity.

The integral against a sum of weighted Diracs is Mathlib's
`MeasureTheory.integral_sum_dirac` (no summability hypothesis for `E = ℝ`); the
kernel has finite support, so the resulting `tsum` is a finite sum over the
three-layer set `V_N × {p.2-1, p.2, p.2+1}`.
-/
public import IdlaCyl.Support.Harmonic
public import IdlaCyl.Support.Canonical
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

@[expose] public section

namespace IdlaCyl

open MeasureTheory
open scoped BigOperators

variable (B : Base)

/-- **The one-step integral** (`tex:679-684`): the integral of `ψ` against the
canonical one-step law `cylMeasure B p` is the `tsum` of `cylKernel` times `ψ`. -/
theorem integral_cylMeasure (p : Site B) (ψ : Site B → ℝ) :
    ∫ q, ψ q ∂(cylMeasure B p) = ∑' q : Site B, cylKernel B p q * ψ q := by
  rw [cylMeasure, integral_sum_dirac (fun q => ENNReal.ofReal_ne_top)]
  congr 1 with q
  rw [ENNReal.toReal_ofReal (cylKernel_nonneg p q), smul_eq_mul]

/-- The `tsum` of the kernel against `ψ` has finite support, and expands to the
paper's three-term operator. -/
theorem tsum_cylKernel_mul (p : Site B) (ψ : Site B → ℝ) :
    (∑' q : Site B, cylKernel B p q * ψ q) = cylinderOp B ψ p := by
  classical
  have hsupp : ∀ q ∉ (Finset.univ ×ˢ ({p.2 - 1, p.2, p.2 + 1} : Finset ℤ) : Finset (Site B)),
      cylKernel B p q * ψ q = 0 := by
    intro q hq
    have hk0 : cylKernel B p q = 0 := by
      simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, not_or] at hq
      obtain ⟨hq1, hq2, hq3⟩ := hq
      unfold cylKernel
      split_ifs with h1 h2
      · exfalso
        obtain ⟨-, h1'⟩ := h1
        rcases Int.natAbs_eq (p.2 - q.2) with hd | hd <;> rw [h1'] at hd <;> omega
      · exact absurd h2.symm hq2
      · rfl
    rw [hk0, zero_mul]
  rw [tsum_eq_sum hsupp, Finset.sum_product]
  have hbot : ∀ x : B.V, cylKernel B p (x, p.2 - 1) * ψ (x, p.2 - 1)
      = (if p.1 = x then (1 / 4 : ℝ) else 0) * ψ (x, p.2 - 1) := by
    intro x
    rw [show cylKernel B p (x, p.2 - 1) = if p.1 = x then (1 / 4 : ℝ) else 0 from by
      unfold cylKernel
      have hne : p.2 ≠ p.2 - 1 := by omega
      simp [hne]]
  have hmid : ∀ x : B.V, cylKernel B p (x, p.2) * ψ (x, p.2)
      = (1 / 2) * B.P p.1 x * ψ (x, p.2) := by
    intro x
    rw [show cylKernel B p (x, p.2) = (1 / 2) * B.P p.1 x from by
      unfold cylKernel
      simp]
  have htop : ∀ x : B.V, cylKernel B p (x, p.2 + 1) * ψ (x, p.2 + 1)
      = (if p.1 = x then (1 / 4 : ℝ) else 0) * ψ (x, p.2 + 1) := by
    intro x
    rw [show cylKernel B p (x, p.2 + 1) = if p.1 = x then (1 / 4 : ℝ) else 0 from by
      unfold cylKernel
      have hne : p.2 ≠ p.2 + 1 := by omega
      simp [hne]]
  have hsplit : ∀ x : B.V, (∑ y ∈ ({p.2 - 1, p.2, p.2 + 1} : Finset ℤ),
      cylKernel B p (x, y) * ψ (x, y))
      = cylKernel B p (x, p.2 - 1) * ψ (x, p.2 - 1)
        + cylKernel B p (x, p.2) * ψ (x, p.2)
        + cylKernel B p (x, p.2 + 1) * ψ (x, p.2 + 1) := by
    intro x
    have h1 : p.2 - 1 ∉ ({p.2, p.2 + 1} : Finset ℤ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have h2 : p.2 ∉ ({p.2 + 1} : Finset ℤ) := by
      simp only [Finset.mem_singleton]
      omega
    rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
    ring
  simp_rw [hsplit, hbot, hmid, htop]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [ite_mul, zero_mul, Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  rw [show (∑ x : B.V, (1 / 2) * B.P p.1 x * ψ (x, p.2))
      = (1 / 2) * ∑ x : B.V, B.P p.1 x * ψ (x, p.2) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring]
  rw [cylinderOp]
  ring

/-- **Harmonicity as an integral identity** (`tex:679-684`): discrete harmonicity is the one-step integral
identity. -/
theorem discreteHarmonic_iff_integral (ψ : Site B → ℝ) :
    DiscreteHarmonic B ψ ↔ ∀ p : Site B, ∫ q, ψ q ∂(cylMeasure B p) = ψ p := by
  constructor
  · intro h p
    rw [integral_cylMeasure, tsum_cylKernel_mul]
    exact h p
  · intro h p
    rw [← tsum_cylKernel_mul B p ψ, ← integral_cylMeasure B p ψ]
    exact h p

end IdlaCyl
