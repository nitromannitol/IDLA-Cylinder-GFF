module

public import IdlaCyl.Support.Spectral

@[expose] public section

/-!
The test function in the replacement lemma (`tex:784-789`), evaluated at the
rescaled integer height (`tex:805-810`).
-/

namespace IdlaCyl.Defs

open scoped BigOperators

/-- The literal rescaled test function `∑_{k=2}^K α_k(y/a_N) f_k^N(x)`
(`tex:787`, `tex:805-810`). -/
noncomputable def testAt (B : Base) (S : SpectralData B) (a : ℝ)
    (K : ℕ) (α : ℕ → ℝ → ℝ) (p : Site B) : ℝ :=
  ∑ k ∈ Finset.Icc 2 K, α k ((p.2 : ℝ) / a) * S.f k p.1

/-- Zero coefficients give the zero test function on every base and scale. -/
theorem testAt_zero (B : Base) (S : SpectralData B) (a : ℝ) (K : ℕ) (p : Site B) :
    testAt B S a K (fun _ _ => 0) p = 0 := by
  simp only [testAt, zero_mul, Finset.sum_const_zero]

end IdlaCyl.Defs
