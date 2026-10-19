/-
Sorting the Fourier frequencies of the lazy cycle. Source: tex:475-483,
`paper/idla-cylinder-gff.tex`: the eigenvalue in slot `k` uses `⌊k/2⌋`.
-/
import IdlaCyl.Support.Cycle.Spectrum

namespace IdlaCyl
namespace CycleSpectrum
open scoped BigOperators

/-- Frequencies in the order `0, N-1, 1, N-2, 2, …`. -/
def orderFrequency (N : ℕ) (i : Fin N) : Fin N :=
  ⟨if i.val % 2 = 0 then i.val / 2 else N - 1 - i.val / 2, by
    have := i.isLt
    split_ifs <;> omega⟩

lemma orderFrequency_injective (N : ℕ) : Function.Injective (orderFrequency N) := by
  intro i j h
  have hval := congrArg Fin.val h
  change (if i.val % 2 = 0 then i.val / 2 else N - 1 - i.val / 2) =
    (if j.val % 2 = 0 then j.val / 2 else N - 1 - j.val / 2) at hval
  have := i.isLt
  have := j.isLt
  apply Fin.ext
  split_ifs at hval <;> omega

/-- The permutation that sorts the Fourier eigenvalues. -/
noncomputable def orderPerm (N : ℕ) : Equiv.Perm (Fin N) :=
  Equiv.ofBijective (orderFrequency N)
    ⟨orderFrequency_injective N, Finite.surjective_of_injective (orderFrequency_injective N)⟩

lemma value_reflect (N m : ℕ) (hN : 0 < N) (hm : m ≤ N) :
    value N (N - m) = value N m := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold value
  rw [Nat.cast_sub hm]
  have ha : 2 * Real.pi * ((N : ℝ) - m) / N =
      2 * Real.pi - 2 * Real.pi * m / N := by field_simp
  rw [ha, Real.cos_two_pi_sub]

lemma value_orderPerm (N : ℕ) (hN : 0 < N) (i : Fin N) :
    value N (orderPerm N i).val = value N ((i.val + 1) / 2) := by
  change value N (if i.val % 2 = 0 then i.val / 2 else N - 1 - i.val / 2) = _
  have := i.isLt
  split_ifs with h
  · congr 1; omega
  · rw [show N - 1 - i.val / 2 = N - (i.val + 1) / 2 by omega]
    exact value_reflect N _ hN (by omega)

lemma sorted_values_antitone (N : ℕ) (hN : 0 < N) :
    Antitone (fun i : Fin N => value N ((i.val + 1) / 2)) := by
  intro i j hij
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hm : (j.val + 1) / 2 * 2 ≤ N := by have := j.isLt; omega
  have hmR : (((j.val + 1) / 2 : ℕ) : ℝ) * 2 ≤ (N : ℝ) := by exact_mod_cast hm
  have hijR : (((i.val + 1) / 2 : ℕ) : ℝ) ≤ ((j.val + 1) / 2 : ℕ) := by
    exact_mod_cast (show (i.val + 1) / 2 ≤ (j.val + 1) / 2 by exact Nat.div_le_div_right (by have := hij; omega))
  unfold value
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  apply add_le_add_right
  apply Real.cos_le_cos_of_nonneg_of_le_pi
  · positivity
  · apply (div_le_iff₀ hNr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmR Real.pi_pos.le]
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hijR (by positivity)) hNr.le

lemma diagonal_roots {N : ℕ} (v : Fin N → ℂ) :
    (Matrix.diagonal v).charpoly.roots = (List.ofFn v : Multiset ℂ) := by
  rw [Matrix.charpoly_diagonal]
  have hp : (∏ i : Fin N, (Polynomial.X - Polynomial.C (v i))) =
      ((List.ofFn v : Multiset ℂ).map (fun a => Polynomial.X - Polynomial.C a)).prod := by
    rw [Multiset.map_coe, ← List.ofFn_comp', Multiset.prod_coe, Fin.prod_ofFn]
  rw [hp, Polynomial.roots_multiset_prod_X_sub_C]

lemma spectral_values_perm (N : ℕ) (hN : 3 ≤ N) (S : SpectralData (cycleBase N hN)) :
    (List.ofFn (fun i : Fin N => S.lam (i.val + 1))).Perm
      (List.ofFn (fun i : Fin N => value N i.val)) := by
  haveI : NeZero N := ⟨by omega⟩
  have h := congrArg (fun p : Polynomial ℝ => p.map Complex.ofRealHom) (spectral_charpoly N hN S)
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, Matrix.diagonal_map (map_zero Complex.ofRealHom),
    fourier_charpoly N hN] at h
  have hr := congrArg Polynomial.roots h
  rw [diagonal_roots, diagonal_roots] at hr
  have hre := congrArg (Multiset.map Complex.re) hr
  simp only [Multiset.map_coe, ← List.ofFn_comp',
    Complex.ofRealHom_eq_coe, Complex.ofReal_re] at hre
  exact Multiset.coe_eq_coe.mp hre.symm

lemma values_orderPerm_perm (N : ℕ) :
    (List.ofFn (fun i : Fin N => value N i.val)).Perm
      (List.ofFn (fun i : Fin N => value N (orderPerm N i).val)) := by
  apply Multiset.coe_eq_coe.mp
  rw [← Fin.univ_val_map, ← Fin.univ_val_map]
  have h := congrArg (Multiset.map (fun i : Fin N => value N i.val))
    (Multiset.map_univ_val_equiv (orderPerm N))
  simpa only [Multiset.map_map, Function.comp_apply] using h.symm

end CycleSpectrum

/-- The lazy cycle eigenvalues, in the paper's one-based descending order,
independently of the choice of orthonormal eigenbasis (`tex:475-483`). -/
theorem cycle_lam_eq (N : ℕ) (hN : 3 ≤ N) (S : SpectralData (cycleBase N hN))
    (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    S.lam k = (1 + Real.cos (2 * Real.pi * (k / 2 : ℕ) / N)) / 2 := by
  have hp := (CycleSpectrum.spectral_values_perm N hN S).trans
    (CycleSpectrum.values_orderPerm_perm N)
  have hvalues : (fun i : Fin N => CycleSpectrum.value N (CycleSpectrum.orderPerm N i).val) =
      (fun i : Fin N => CycleSpectrum.value N ((i.val + 1) / 2)) := by
    funext i
    exact CycleSpectrum.value_orderPerm N (by omega) i
  rw [hvalues] at hp
  have hs : (List.ofFn (fun i : Fin N => S.lam (i.val + 1))).SortedGE := by
    apply List.Pairwise.sortedGE
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact S.antitone _ _ (by omega) (by have := hij.le; omega)
      (by rw [cycleBase_card]; omega)
  have ht : (List.ofFn (fun i : Fin N => CycleSpectrum.value N ((i.val + 1) / 2))).SortedGE := by
    apply List.Pairwise.sortedGE
    apply List.pairwise_ofFn.mpr
    intro i j hij
    exact CycleSpectrum.sorted_values_antitone N (by omega) hij.le
  have heq := List.ofFn_injective (hp.eq_of_sortedGE hs ht)
  have h := congrFun heq (⟨k - 1, by omega⟩ : Fin N)
  simpa only [Nat.sub_add_cancel hk, CycleSpectrum.value] using h

end IdlaCyl
