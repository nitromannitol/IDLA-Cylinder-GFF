module

/-
Counting levels in the exact torus spectrum. Source: tex:502-507,
`paper/idla-cylinder-gff.tex`. The inequalities below deliberately ignore
any ordering within a repeated eigenvalue.
-/
public import IdlaCyl.Support.Torus.Spectrum

@[expose] public section

namespace IdlaCyl.TorusSpectrum
open scoped BigOperators

lemma spectral_count (d n : ℕ) [NeZero n] (hd : 1 ≤ d) (hn : 3 ≤ n)
    (S : SpectralData (torusBase d n hd hn)) (p : ℝ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun j : Fin (n ^ d) => p (S.lam (j.val + 1)))).card =
      (Finset.univ.filter (fun m : Fin d → ZMod n => p (value d n m))).card := by
  have h := congrArg (fun s : Multiset ℝ => (s.filter p).card) (spectral_values d n hd hn S)
  rw [← Fin.univ_val_map] at h
  simpa only [Multiset.filter_map, Multiset.card_map, Function.comp_def, Finset.card, Finset.filter_val] using h

lemma le_of_count_le {q : ℕ} (a : Fin q → ℝ) (ha : Monotone a) (j : Fin q) (u : ℝ)
    (hcount : j.val + 1 ≤ (Finset.univ.filter (fun i => a i ≤ u)).card) : a j ≤ u := by
  classical
  by_contra h
  have hs : Finset.univ.filter (fun i => a i ≤ u) ⊆ Finset.Iio j := by
    intro i hi
    have hiu := (Finset.mem_filter.mp hi).2
    apply Finset.mem_Iio.mpr
    by_contra hij
    exact h ((ha (le_of_not_gt hij)).trans hiu)
  have hc := Finset.card_le_card hs
  rw [Fin.card_Iio] at hc
  omega

lemma le_of_count_lt {q : ℕ} (a : Fin q → ℝ) (ha : Monotone a) (j : Fin q) (l : ℝ)
    (hcount : (Finset.univ.filter (fun i => a i < l)).card < j.val + 1) : l ≤ a j := by
  classical
  by_contra h
  have hs : Finset.Iic j ⊆ Finset.univ.filter (fun i => a i < l) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,
      lt_of_le_of_lt (ha (Finset.mem_Iic.mp hi)) (lt_of_not_ge h)⟩
  have hc := Finset.card_le_card hs
  rw [Fin.card_Iic] at hc
  omega

end IdlaCyl.TorusSpectrum
