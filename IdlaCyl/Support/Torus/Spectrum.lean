/-
The Fourier spectrum of the lazy nearest-neighbour torus. Source: tex:229-237,
tex:502-520, `paper/idla-cylinder-gff.tex`.
-/
import Mathlib
import IdlaCyl.Support.TorusBase
import IdlaCyl.Support.Spectral

namespace IdlaCyl.TorusSpectrum
open scoped BigOperators

/-- The character with frequency vector `m`, on the actual torus carrier. -/
noncomputable def character (d n : ℕ) [NeZero n] (m : Fin d → ZMod n) :
    AddChar (Fin d → ZMod n) ℂ :=
  ZMod.stdAddChar.compAddMonoidHom
    { toFun := fun x => ∑ i, m i * x i
      map_zero' := by simp
      map_add' := by intros; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] }

lemma character_single (d n : ℕ) [NeZero n] (m : Fin d → ZMod n) (i : Fin d) (a : ZMod n) :
    character d n m (Pi.single i a) = ZMod.stdAddChar (m i * a) := by
  simp [character, Pi.single_apply]

lemma character_injective (d n : ℕ) [NeZero n] : Function.Injective (character d n) := by
  intro m l h
  funext i
  apply ZMod.injective_stdAddChar
  have hi := congrArg (fun ψ : AddChar (Fin d → ZMod n) ℂ => ψ (Pi.single i 1)) h
  simpa only [character_single, mul_one] using hi

/-- Unsorted eigenvalue, including all frequency multiplicities. -/
noncomputable def value (d n : ℕ) [NeZero n] (m : Fin d → ZMod n) : ℝ :=
  (1 + (∑ i, Real.cos (2 * Real.pi * (m i).val / n)) / d) / 2

lemma neighborFinset (d n : ℕ) [NeZero n] (hn : 3 ≤ n) (x : Fin d → ZMod n) :
    (torusGraph d n hn).neighborFinset x =
      Finset.univ.image (fun p => x + torusDir d n p) := by
  have ht (y : Fin d → ZMod n) : torusAdj d n x y ↔ torusAdj d n 0 (y - x) := by
    simpa only [sub_add_cancel, zero_add] using
      (torusAdj_add x (0 : Fin d → ZMod n) (y - x))
  ext y
  rw [SimpleGraph.mem_neighborFinset]
  change torusAdj d n x y ↔ _
  rw [ht, ← show (torusGraph d n hn).Adj 0 (y - x) ↔ torusAdj d n 0 (y - x) from Iff.rfl,
    ← SimpleGraph.mem_neighborFinset, torusGraph_neighborFinset_zero]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, by rw [hp]; abel⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, by rw [← hp]; abel⟩

lemma base_kernel_apply (B : Base) (v : B.V → ℂ) (x : B.V) :
    ∑ y, (B.P x y : ℂ) * v y =
      v x / 2 + (∑ y ∈ B.graph.neighborFinset x, v y) / (2 * B.deg : ℂ) := by
  classical
  have hsplit : (∑ y : B.V, (B.P x y : ℂ) * v y) =
      (∑ y ∈ B.graph.neighborFinset x, (B.P x y : ℂ) * v y) + (B.P x x : ℂ) * v x := by
    rw [← Finset.sum_subset (Finset.subset_univ (insert x (B.graph.neighborFinset x)))]
    · rw [Finset.sum_insert (by simp [SimpleGraph.mem_neighborFinset])]
      ring
    · intro y _ hy
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or] at hy
      simp only [Base.P, if_neg hy.2, if_neg (Ne.symm hy.1), Complex.ofReal_zero, zero_mul]
  have hnb : (∑ y ∈ B.graph.neighborFinset x, (B.P x y : ℂ) * v y) =
      (∑ y ∈ B.graph.neighborFinset x, v y) / (2 * B.deg : ℂ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro y hy
    have hadj : B.graph.Adj x y := by simpa only [SimpleGraph.mem_neighborFinset] using hy
    simp only [Base.P, if_pos hadj, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast]
    ring
  have hxx : B.P x x = 1 / 2 := by simp [Base.P]
  rw [hsplit, hnb, hxx]
  push_cast
  ring

lemma kernel_apply (d n : ℕ) [NeZero n] (hd : 1 ≤ d) (hn : 3 ≤ n)
    (v : (Fin d → ZMod n) → ℂ) (x : Fin d → ZMod n) :
    ∑ y, ((torusBase d n hd hn).P x y : ℂ) * v y =
      v x / 2 + (∑ p : Fin d × Bool, v (x + torusDir d n p)) / (4 * d) := by
  classical
  have h := base_kernel_apply (torusBase d n hd hn) v x
  rw [torusBase_deg] at h
  change (∑ y, ((torusBase d n hd hn).P x y : ℂ) * v y) =
    v x / 2 + (∑ y ∈ (torusGraph d n hn).neighborFinset x, v y) / (2 * (2 * d : ℕ) : ℂ) at h
  rw [neighborFinset, Finset.sum_image] at h
  · push_cast at h
    convert h using 1; ring
  · intro p _ q _ hpq
    exact torusDir_injective d n hn (add_left_cancel hpq)

lemma character_exp (n : ℕ) [NeZero n] (a : ZMod n) :
    ZMod.stdAddChar a = Complex.exp ((2 * Real.pi * (a.val : ℝ) / n : ℝ) * Complex.I) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [show (a.val : ZMod n) = ((a.val : ℤ) : ZMod n) by simp only [Int.cast_natCast],
    ZMod.stdAddChar_coe]
  push_cast
  congr 1
  ring

lemma character_pair (d n : ℕ) [NeZero n] (m : Fin d → ZMod n) (i : Fin d) :
    character d n m (Pi.single i 1) + character d n m (Pi.single i (-1)) =
      (2 * Real.cos (2 * Real.pi * (m i).val / n) : ℝ) := by
  simp only [character_single, mul_one, mul_neg_one]
  rw [AddChar.map_neg_eq_conj, character_exp]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.conj_re, Complex.exp_ofReal_mul_I_re,
      Complex.ofReal_re]
    ring
  · simp only [Complex.add_im, Complex.conj_im, add_neg_cancel, Complex.ofReal_im]

lemma character_eigen (d n : ℕ) [NeZero n] (hd : 1 ≤ d) (hn : 3 ≤ n)
    (m x : Fin d → ZMod n) :
    ∑ y, ((torusBase d n hd hn).P x y : ℂ) * character d n m y =
      (value d n m : ℂ) * character d n m x := by
  rw [kernel_apply]
  simp only [AddChar.map_add_eq_mul, Fintype.sum_prod_type, torusDir,
    Fintype.sum_bool, cond_true, cond_false, character_pair,
    ← Finset.mul_sum]
  unfold value
  simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast]
  rw [← Finset.mul_sum]
  ring

/-- Fourier columns, indexed by the torus frequencies themselves. -/
noncomputable def fourier (d n : ℕ) [NeZero n] :
    Matrix (Fin d → ZMod n) (Fin d → ZMod n) ℂ := fun x m => character d n m x

lemma fourier_isUnit (d n : ℕ) [NeZero n] : IsUnit (fourier d n) := by
  apply Matrix.linearIndependent_cols_iff_isUnit.mp
  change LinearIndependent ℂ (fun m : Fin d → ZMod n => fun x => character d n m x)
  apply (AddChar.linearIndependent (Fin d → ZMod n) ℂ).comp (character d n)
  exact character_injective d n

lemma charpoly_conjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : Type*} [Field K] (A F : Matrix ι ι K) (hF : IsUnit F) :
    A.charpoly = (F⁻¹ * A * F).charpoly := by
  have hd := (Matrix.isUnit_iff_isUnit_det F).mp hF
  symm
  rw [Matrix.charpoly_mul_comm, ← mul_assoc, Matrix.mul_nonsing_inv F hd, one_mul]

lemma diagonal_roots {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    (Matrix.diagonal v).charpoly.roots = Finset.univ.val.map v := by
  rw [Matrix.charpoly_diagonal]
  have hp : (∏ i, (Polynomial.X - Polynomial.C (v i))) =
      ((Finset.univ.val.map v).map (fun a => Polynomial.X - Polynomial.C a)).prod := by
    rw [Multiset.map_map, Finset.prod_map_val]
    rfl
  rw [hp, Polynomial.roots_multiset_prod_X_sub_C]

/-- A bijective one-based enumeration of the torus, used only for the given eigenbasis. -/
noncomputable def eigenIndex (d n : ℕ) [NeZero n] (j : Fin d → ZMod n) : ℕ :=
  (Fintype.equivFin (Fin d → ZMod n) j).val + 1

lemma eigenIndex_pos (d n : ℕ) [NeZero n] (j : Fin d → ZMod n) :
    1 ≤ eigenIndex d n j := Nat.le_add_left 1 _

lemma eigenIndex_le (d n : ℕ) [NeZero n] (j : Fin d → ZMod n) :
    eigenIndex d n j ≤ n ^ d := by
  have h := (Fintype.equivFin (Fin d → ZMod n) j).isLt
  exact (Nat.succ_le_iff.mpr h).trans_eq (torus_card d n)

lemma eigenIndex_injective (d n : ℕ) [NeZero n] :
    Function.Injective (eigenIndex d n) := by
  intro i j h
  exact (Fintype.equivFin _).injective (Fin.ext (Nat.add_right_cancel h))

/-- The real matrix of any supplied lawful orthonormal eigenbasis. -/
noncomputable def vectors (d n : ℕ) [NeZero n] (hd : 1 ≤ d) (hn : 3 ≤ n)
    (S : SpectralData (torusBase d n hd hn)) :
    Matrix (Fin d → ZMod n) (Fin d → ZMod n) ℝ := by
  exact fun x j => S.f (eigenIndex d n j) x

lemma vectors_left_inv (d n : ℕ) [NeZero n] (hd : 1 ≤ d) (hn : 3 ≤ n)
    (S : SpectralData (torusBase d n hd hn)) :
    (((n ^ d : ℕ) : ℝ)⁻¹ • (vectors d n hd hn S).transpose) * vectors d n hd hn S = 1 := by
  rw [Matrix.smul_mul]
  ext i j
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    vectors, smul_eq_mul, Matrix.one_apply]
  have h := S.orthonormal (eigenIndex d n i) (eigenIndex d n j)
    (eigenIndex_pos d n i) (by rw [torusBase_card]; exact eigenIndex_le d n i)
    (eigenIndex_pos d n j) (by rw [torusBase_card]; exact eigenIndex_le d n j)
  rw [torusBase_card, one_div] at h
  simp only [(eigenIndex_injective d n).eq_iff] at h
  convert h using 1
  congr 1

lemma vectors_isUnit (d n : ℕ) [NeZero n] (hd : 1 ≤ d) (hn : 3 ≤ n)
    (S : SpectralData (torusBase d n hd hn)) : IsUnit (vectors d n hd hn S) := by
  have h := congrArg Matrix.det (vectors_left_inv d n hd hn S)
  rw [Matrix.det_mul, Matrix.det_one] at h
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  intro hz
  rw [hz, mul_zero] at h
  exact zero_ne_one h

/-- The lazy torus transition matrix. -/
noncomputable def transition (d n : ℕ) (hd : 1 ≤ d) (hn : 3 ≤ n) :
    Matrix (Fin d → ZMod n) (Fin d → ZMod n) ℝ := (torusBase d n hd hn).P

lemma spectral_charpoly (d n : ℕ) [NeZero n] (hd : 1 ≤ d) (hn : 3 ≤ n)
    (S : SpectralData (torusBase d n hd hn)) :
    (transition d n hd hn).charpoly =
      (Matrix.diagonal (fun j => S.lam (eigenIndex d n j))).charpoly := by
  have hF := vectors_isUnit d n hd hn S
  have hdF := (Matrix.isUnit_iff_isUnit_det _).mp hF
  have heig : transition d n hd hn * vectors d n hd hn S =
      vectors d n hd hn S * Matrix.diagonal (fun j => S.lam (eigenIndex d n j)) := by
    ext x j
    rw [Matrix.mul_diagonal]
    exact (S.eigen _ (eigenIndex_pos d n j)
      (by rw [torusBase_card]; exact eigenIndex_le d n j) x).trans (mul_comm _ _)
  rw [charpoly_conjugate _ _ hF, mul_assoc, heig, ← mul_assoc,
    Matrix.nonsing_inv_mul _ hdF, one_mul]

lemma fourier_charpoly (d n : ℕ) [NeZero n] (hd : 1 ≤ d) (hn : 3 ≤ n) :
    ((transition d n hd hn).map Complex.ofRealHom).charpoly =
      (Matrix.diagonal (fun m => (value d n m : ℂ))).charpoly := by
  have hF := fourier_isUnit d n
  have hdF := (Matrix.isUnit_iff_isUnit_det _).mp hF
  have heig : (transition d n hd hn).map Complex.ofRealHom * fourier d n =
      fourier d n * Matrix.diagonal (fun m => (value d n m : ℂ)) := by
    ext x m
    rw [Matrix.mul_diagonal]
    exact (character_eigen d n hd hn m x).trans (mul_comm _ _)
  rw [charpoly_conjugate _ _ hF, mul_assoc, heig, ← mul_assoc,
    Matrix.nonsing_inv_mul _ hdF, one_mul]

/-- Exact multiplicity-preserving identification with the Fourier values. -/
theorem spectral_values (d n : ℕ) [NeZero n] (hd : 1 ≤ d) (hn : 3 ≤ n)
    (S : SpectralData (torusBase d n hd hn)) :
    (List.ofFn (fun j : Fin (n ^ d) => S.lam (j.val + 1)) : Multiset ℝ) =
      (Finset.univ : Finset (Fin d → ZMod n)).val.map (value d n) := by
  have h := congrArg (fun p : Polynomial ℝ => p.map Complex.ofRealHom)
    (spectral_charpoly d n hd hn S)
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map,
    Matrix.diagonal_map (map_zero Complex.ofRealHom), fourier_charpoly d n hd hn] at h
  have hr := congrArg Polynomial.roots h
  rw [diagonal_roots, diagonal_roots] at hr
  have hre := congrArg (Multiset.map Complex.re) hr
  simp only [Multiset.map_map, Function.comp_apply, Complex.ofRealHom_eq_coe,
    Complex.ofReal_re] at hre
  rw [← hre.symm]
  let e : (Fin d → ZMod n) ≃ Fin (n ^ d) :=
    (Fintype.equivFin _).trans (finCongr (torus_card d n))
  have he := congrArg (Multiset.map (fun j : Fin (n ^ d) => S.lam (j.val + 1)))
    (Multiset.map_univ_val_equiv e)
  rw [Multiset.map_map, Fin.univ_val_map] at he
  exact he.symm

/-- The supplied eigenvalues are exactly the Fourier multiset sorted in descending order. -/
theorem sorted_spectral_values (d n : ℕ) [NeZero n] (hd : 1 ≤ d) (hn : 3 ≤ n)
    (S : SpectralData (torusBase d n hd hn)) :
    List.ofFn (fun j : Fin (n ^ d) => S.lam (j.val + 1)) =
      ((Finset.univ : Finset (Fin d → ZMod n)).val.map (value d n)).sort (· ≥ ·) := by
  have hs : (List.ofFn (fun j : Fin (n ^ d) => S.lam (j.val + 1))).SortedGE := by
    apply List.Pairwise.sortedGE
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact S.antitone _ _ (by omega) (by have := hij.le; omega)
      (by rw [torusBase_card]; have := j.isLt; omega)
  have hp := spectral_values d n hd hn S
  have hperm := Multiset.coe_eq_coe.mp
    (hp.trans (Multiset.sort_eq _ (· ≥ ·)).symm)
  exact hperm.eq_of_sortedGE hs (Multiset.pairwise_sort _ _).sortedGE

end IdlaCyl.TorusSpectrum
