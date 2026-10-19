/-
Nonvacuity of the cycle spectral statements. Source: tex:475-483,
`paper/idla-cylinder-gff.tex`. Existence uses the proved spectral theorem.
-/
import IdlaCyl.Support.Cycle.Ordering
import IdlaCyl.Support.Obligations

namespace IdlaCyl

/-- Every admissible cycle has lawful spectral data. -/
theorem cycle_spectralData_exists (N : ℕ) (hN : 3 ≤ N) :
    Nonempty (SpectralData (cycleBase N hN)) :=
  spectralData_exists (cycleBase N hN)

/-- An actual four-cycle spectral witness, with the low eigenvalue and the
Nyquist eigenvalue calculated from the basis-independent formula. -/
theorem cycle_four_nonvacuous :
    ∃ S : SpectralData (cycleBase 4 (by norm_num)), S.lam 2 = 1 / 2 ∧ S.lam 4 = 0 := by
  obtain ⟨S⟩ := cycle_spectralData_exists 4 (by norm_num)
  refine ⟨S, ?_, ?_⟩
  · rw [cycle_lam_eq 4 (by norm_num) S 2 (by norm_num) (by norm_num)]
    norm_num only [Nat.reduceDiv, Nat.cast_one, Nat.cast_ofNat, mul_one]
    rw [show 2 * Real.pi / 4 = Real.pi / 2 by ring, Real.cos_pi_div_two]
    norm_num
  · rw [cycle_lam_eq 4 (by norm_num) S 4 (by norm_num) (by norm_num)]
    norm_num only [Nat.reduceDiv, Nat.cast_ofNat]
    rw [show 2 * Real.pi * 2 / 4 = Real.pi by ring, Real.cos_pi]
    norm_num

end IdlaCyl
