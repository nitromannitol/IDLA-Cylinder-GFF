import IdlaCyl.Definitions.TestFunction
import IdlaCyl.Definitions.RectangularMass
import IdlaCyl.Support.LeReplaceInputs

/-!
The mode expansion, cancellation, and layer norm in the replacement lemma
(`tex:794-826`). The coefficient below uses the existing unscaled rate
`S.qk k`, so its exponent is exactly the exponent in `harmAt`.
-/

namespace IdlaCyl.Replace

open Defs
open scoped BigOperators

variable (B : Base)

/-- The coefficient `β_k(y)` of `tex:805-810`. -/
noncomputable def beta (S : SpectralData B) (a : ℝ) (h : ℤ)
    (α : ℕ → ℝ → ℝ) (y : ℤ) (k : ℕ) : ℝ :=
  α k ((y : ℝ) / a) - α k ((h : ℝ) / a) *
    Real.exp (S.qk k * ((y : ℝ) - (h : ℝ)))

/-- The coefficient vanishes on the reference layer, including at scale zero. -/
theorem beta_at_height (S : SpectralData B) (a : ℝ) (h : ℤ)
    (α : ℕ → ℝ → ℝ) (k : ℕ) : beta B S a h α h k = 0 := by
  simp only [beta, sub_self, mul_zero, Real.exp_zero, mul_one]

/-- The literal difference of the test and harmonic extension is the beta mode sum. -/
theorem testAt_sub_harmAt (S : SpectralData B) (a : ℝ) (h : ℤ) (K : ℕ)
    (α : ℕ → ℝ → ℝ) (p : Site B) :
    testAt B S a K α p - harmAt B S a h K α p =
      ∑ k ∈ Finset.Icc 2 K, beta B S a h α p.2 k * S.f k p.1 := by
  unfold testAt harmAt beta
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Every nonconstant eigenmode has zero horizontal sum. -/
theorem sum_eigenmode_eq_zero (S : SpectralData B) (k : ℕ)
    (hk : 2 ≤ k) (hkN : k ≤ B.card) : ∑ x : B.V, S.f k x = 0 := by
  have hh := S.orthonormal 1 k (by omega) (by omega) (by omega) hkN
  have hN : (B.card : ℝ) ≠ 0 := by
    exact_mod_cast (show B.card ≠ 0 by change Fintype.card B.V ≠ 0; have := B.nontrivial; omega)
  simp only [S.f_one, one_mul, if_neg (show 1 ≠ k by omega)] at hh
  exact (mul_eq_zero.mp hh).resolve_left (one_div_ne_zero hN)

/-- The test function has zero horizontal average on every layer. -/
theorem testAt_zeroHorizontalAverage (S : SpectralData B) (a : ℝ) (K : ℕ)
    (α : ℕ → ℝ → ℝ) (hK : K ≤ B.card) :
    ZeroHorizontalAverage B (testAt B S a K α) := by
  intro y
  unfold testAt
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  change (∑ x : B.V, α k ((y : ℝ) / a) * S.f k x) = 0
  rw [← Finset.mul_sum, sum_eigenmode_eq_zero B S k
    (Finset.mem_Icc.mp hk).1 ((Finset.mem_Icc.mp hk).2.trans hK), mul_zero]

/-- The test-minus-harmonic error has zero horizontal average on every layer. -/
theorem error_zeroHorizontalAverage (S : SpectralData B) (a : ℝ) (h : ℤ) (K : ℕ)
    (α : ℕ → ℝ → ℝ) (hK : K ≤ B.card) :
    ZeroHorizontalAverage B (fun p => testAt B S a K α p - harmAt B S a h K α p) := by
  intro y
  simp_rw [testAt_sub_harmAt]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  rw [← Finset.mul_sum, sum_eigenmode_eq_zero B S k
    (Finset.mem_Icc.mp hk).1 ((Finset.mem_Icc.mp hk).2.trans hK), mul_zero]

/-- Parseval's identity for the replacement error, with the normalized layer norm. -/
theorem error_layerMeanSquare (S : SpectralData B) (a : ℝ) (h : ℤ) (K : ℕ)
    (α : ℕ → ℝ → ℝ) (hK : K ≤ B.card) (y : ℤ) :
    layerMeanSquare B (fun p => testAt B S a K α p - harmAt B S a h K α p) y =
      ∑ k ∈ Finset.Icc 2 K, beta B S a h α y k ^ 2 := by
  have horth : CountingOrthonormalOn B (Finset.Icc 2 K) S.f := by
    intro i hi j hj
    exact SpectralData.countingOrthonormalOn B S i
      (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hi).1; omega,
        (Finset.mem_Icc.mp hi).2.trans hK⟩) j
      (Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hj).1; omega,
        (Finset.mem_Icc.mp hj).2.trans hK⟩)
  have hnorm := modeSumOn_norm B (Finset.Icc 2 K) S.f horth (beta B S a h α y)
  have hN : (B.card : ℝ) ≠ 0 := by
    exact_mod_cast (show B.card ≠ 0 by change Fintype.card B.V ≠ 0; have := B.nontrivial; omega)
  unfold layerMeanSquare
  simp_rw [testAt_sub_harmAt]
  change (B.card : ℝ)⁻¹ * (∑ x : B.V,
    modeSumOn B (Finset.Icc 2 K) S.f (beta B S a h α y) x ^ 2) = _
  rw [hnorm, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

end IdlaCyl.Replace
