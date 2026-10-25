module

/-
The lazy cycle kernel and its Fourier spectrum. Source: tex:474-484,
`paper/idla-cylinder-gff.tex`. The kernel normalization is tex:229-237.
-/
public import Mathlib
public import IdlaCyl.Support.CycleBase
public import IdlaCyl.Support.Spectral

@[expose] public section

namespace IdlaCyl
open scoped BigOperators

namespace CycleSpectrum

/-- The additive character on `Fin N` transported from `ZMod N`. -/
noncomputable def character (N : ℕ) [NeZero N] : AddChar (Fin N) ℂ :=
  ZMod.stdAddChar.compAddMonoidHom (ZMod.finEquiv N).toAddEquiv.toAddMonoidHom

lemma character_injective (N : ℕ) [NeZero N] :
    Function.Injective (character N) :=
  ZMod.injective_stdAddChar.comp (ZMod.finEquiv N).injective

/-- Complex Fourier columns. -/
noncomputable def fourier (N : ℕ) [NeZero N] : Matrix (Fin N) (Fin N) ℂ :=
  fun x j => character N (j * x)

open scoped Fin.CommRing in
lemma fourier_isUnit (N : ℕ) [NeZero N] : IsUnit (fourier N) := by
  apply Matrix.linearIndependent_cols_iff_isUnit.mp
  apply (AddChar.linearIndependent (Fin N) ℂ).comp (fun j => (character N).mulShift j)
  intro j k h
  apply character_injective N
  have h' := congrArg (fun ψ : AddChar (Fin N) ℂ => ψ 1) h
  simpa only [AddChar.mulShift_apply, mul_one] using h'

lemma kernel (N : ℕ) [NeZero N] (hN : 3 ≤ N) (x y : Fin N) :
    (cycleBase N hN).P x y =
      (if y = x then 1 / 2 else 0) +
      (if y = x + 1 then 1 / 4 else 0) +
      (if y = x - 1 then 1 / 4 else 0) := by
  have h1val : (1 : Fin N).val = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < N)]
  have h1 : (1 : Fin N) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    rw [h1val, Fin.val_zero] at this
    omega
  have h2 : (1 : Fin N) + 1 ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    rw [Fin.val_add, h1val, Fin.val_zero, Nat.mod_eq_of_lt (by omega : 1 + 1 < N)] at this
    omega
  have hp : x + 1 ≠ x := by
    intro h
    apply h1
    exact add_left_cancel (h.trans (add_zero x).symm)
  have hm : x - 1 ≠ x := by
    intro h
    exact hp ((sub_eq_iff_eq_add.mp h).symm)
  have hpm : x + 1 ≠ x - 1 := by
    intro h
    apply h2
    calc (1 : Fin N) + 1 = (x + 1) - (x - 1) := by abel
         _ = 0 := sub_eq_zero.mpr h
  have hadj : (cycleBase N hN).graph.Adj x y ↔ y = x + 1 ∨ y = x - 1 := by
    change (SimpleGraph.cycleGraph N).Adj x y ↔ _
    rw [SimpleGraph.cycleGraph_adj']
    have hone : (1 : Fin N).val = 1 := by
      rw [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < N)]
    rw [← hone, Fin.val_inj, Fin.val_inj]
    constructor
    · rintro (h | h)
      · right; exact (eq_sub_iff_add_eq.mpr ((add_comm y 1).trans (sub_eq_iff_eq_add.mp h).symm))
      · left; exact sub_eq_iff_eq_add.mp h |>.trans (add_comm 1 x)
    · rintro (rfl | rfl)
      · right; simp only [add_sub_cancel_left]
      · left; simp only [sub_sub_cancel]
  unfold Base.P
  rw [cycleBase_deg]
  simp only [hadj]
  by_cases h0 : y = x
  · subst y
    simp [Ne.symm hp, Ne.symm hm]
  · by_cases hplus : y = x + 1
    · subst y
      simp [hp, hpm]
      norm_num
    · by_cases hminus : y = x - 1
      · subst y
        simp [hm, Ne.symm hpm]
        norm_num
      · simp only [hplus, hminus, or_self, ite_false, h0, zero_add]
        exact if_neg (Ne.symm h0)

lemma kernel_apply (N : ℕ) [NeZero N] (hN : 3 ≤ N) (v : Fin N → ℂ) (x : Fin N) :
    ∑ y, ((cycleBase N hN).P x y : ℂ) * v y =
      v x / 2 + v (x + 1) / 4 + v (x - 1) / 4 := by
  change ∑ y : Fin N, ((cycleBase N hN).P x y : ℂ) * v y = _
  simp only [kernel, Complex.ofReal_add]
  simp only [apply_ite (fun r : ℝ => (r : ℂ)), Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_zero]
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

lemma character_exp (N : ℕ) [NeZero N] (j : Fin N) :
    character N j = Complex.exp ((2 * Real.pi * (j.val : ℝ) / N : ℝ) * Complex.I) := by
  have hj : (ZMod.finEquiv N) j = (j.val : ZMod N) := by
    cases N with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => exact (Fin.cast_val_eq_self j).symm
  change ZMod.stdAddChar ((ZMod.finEquiv N) j) = _
  rw [hj]
  have hcast : (j.val : ZMod N) = ((j.val : ℤ) : ZMod N) := by simp only [Int.cast_natCast]
  rw [hcast, ZMod.stdAddChar_coe]
  push_cast
  congr 1
  ring

/-- The Fourier eigenvalue at frequency `j`, before sorting. -/
noncomputable def value (N : ℕ) (j : ℕ) : ℝ :=
  (1 + Real.cos (2 * Real.pi * j / N)) / 2

lemma character_pair (N : ℕ) [NeZero N] (j : Fin N) :
    character N j + character N (-j) = (2 * Real.cos (2 * Real.pi * j.val / N) : ℝ) := by
  rw [AddChar.map_neg_eq_conj, character_exp]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.conj_re, Complex.exp_ofReal_mul_I_re,
      Complex.ofReal_re]
    ring
  · simp only [Complex.add_im, Complex.conj_im, add_neg_cancel, Complex.ofReal_im]

open scoped Fin.CommRing in
lemma fourier_eigen (N : ℕ) [NeZero N] (hN : 3 ≤ N) (j x : Fin N) :
    ∑ y : Fin N, ((cycleBase N hN).P x y : ℂ) * fourier N y j =
      (value N j.val : ℂ) * fourier N x j := by
  refine (kernel_apply N hN (fun y => fourier N y j) x).trans ?_
  simp only [fourier, mul_add, mul_sub, mul_one]
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  have hpair := character_pair N j
  have hc : (value N j.val : ℂ) = (2 + character N j + character N (-j)) / 4 := by
    rw [show (2 + character N j + character N (-j)) = 2 +
      (character N j + character N (-j)) by ring, hpair]
    unfold value
    push_cast
    ring
  rw [hc]
  ring

lemma charpoly_conjugate {n : ℕ} {K : Type*} [Field K]
    (A F : Matrix (Fin n) (Fin n) K) (hF : IsUnit F) :
    A.charpoly = (F⁻¹ * A * F).charpoly := by
  have hd : IsUnit F.det := (Matrix.isUnit_iff_isUnit_det F).mp hF
  symm
  rw [Matrix.charpoly_mul_comm, ← mul_assoc, Matrix.mul_nonsing_inv F hd, one_mul]

/-- The real matrix whose columns are the supplied eigenfunctions. -/
noncomputable def vectors (N : ℕ) (hN : 3 ≤ N) (S : SpectralData (cycleBase N hN)) :
    Matrix (Fin N) (Fin N) ℝ := fun x i => S.f (i.val + 1) x

lemma vectors_left_inv (N : ℕ) (hN : 3 ≤ N) (S : SpectralData (cycleBase N hN)) :
    ((N : ℝ)⁻¹ • (vectors N hN S).transpose) * vectors N hN S = 1 := by
  rw [Matrix.smul_mul]
  ext i j
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    vectors, smul_eq_mul, Matrix.one_apply]
  have h := S.orthonormal (i.val + 1) (j.val + 1) (by omega)
    (by rw [cycleBase_card]; omega) (by omega) (by rw [cycleBase_card]; omega)
  rw [cycleBase_card, one_div] at h
  have hij : i.val + 1 = j.val + 1 ↔ i = j := by simp only [Nat.add_right_cancel_iff, Fin.val_inj]
  simp only [hij] at h
  exact h

lemma vectors_isUnit (N : ℕ) (hN : 3 ≤ N) (S : SpectralData (cycleBase N hN)) :
    IsUnit (vectors N hN S) := by
  have h := congrArg Matrix.det (vectors_left_inv N hN S)
  rw [Matrix.det_mul, Matrix.det_one] at h
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  intro hz
  rw [hz, mul_zero] at h
  exact zero_ne_one h

/-- The cycle kernel as a real matrix. -/
noncomputable def transition (N : ℕ) (hN : 3 ≤ N) : Matrix (Fin N) (Fin N) ℝ :=
  (cycleBase N hN).P

lemma vectors_eigen (N : ℕ) (hN : 3 ≤ N) (S : SpectralData (cycleBase N hN)) :
    transition N hN * vectors N hN S =
      vectors N hN S * Matrix.diagonal (fun i => S.lam (i.val + 1)) := by
  ext x i
  rw [Matrix.mul_diagonal]
  change (∑ y : Fin N, (cycleBase N hN).P x y * S.f (i.val + 1) y) =
    S.f (i.val + 1) x * S.lam (i.val + 1)
  exact (S.eigen (i.val + 1) (by omega) (by rw [cycleBase_card]; omega) x).trans
    (mul_comm _ _)

lemma spectral_charpoly (N : ℕ) (hN : 3 ≤ N) (S : SpectralData (cycleBase N hN)) :
    (transition N hN).charpoly =
      (Matrix.diagonal (fun i : Fin N => S.lam (i.val + 1))).charpoly := by
  have hF := vectors_isUnit N hN S
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hF
  rw [charpoly_conjugate (transition N hN) (vectors N hN S) hF,
    mul_assoc, vectors_eigen, ← mul_assoc, Matrix.nonsing_inv_mul _ hd, one_mul]

lemma fourier_charpoly (N : ℕ) [NeZero N] (hN : 3 ≤ N) :
    ((transition N hN).map Complex.ofRealHom).charpoly =
      (Matrix.diagonal (fun j : Fin N => (value N j.val : ℂ))).charpoly := by
  have hF := fourier_isUnit N
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hF
  have heig : (transition N hN).map Complex.ofRealHom * fourier N =
      fourier N * Matrix.diagonal (fun j : Fin N => (value N j.val : ℂ)) := by
    ext x j
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, Matrix.map_apply, transition, Complex.ofRealHom_eq_coe]
    exact (fourier_eigen N hN j x).trans (mul_comm _ _)
  rw [charpoly_conjugate _ (fourier N) hF, mul_assoc, heig,
    ← mul_assoc, Matrix.nonsing_inv_mul _ hd, one_mul]

end CycleSpectrum
end IdlaCyl
