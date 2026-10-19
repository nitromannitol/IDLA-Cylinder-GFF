import IdlaCyl.Support.CanonicalExchange

/-!
The Cauchy–Schwarz step for a canonical trajectory replacement
(`tex:828-835`, `eq:CS`). The symmetric difference is a genuine finite set,
identified with the set whose extended cardinality is bounded by exchange.
-/

namespace IdlaCyl.Replace

open scoped BigOperators

/-- A finite sum changes in square by at most the size of its symmetric
 difference times the square mass there. -/
theorem sum_sub_sq_le {ι : Type*} [DecidableEq ι] (s t : Finset ι) (f : ι → ℝ) :
    ((∑ p ∈ s, f p) - ∑ p ∈ t, f p) ^ 2 ≤
      ((symmDiff s t).card : ℝ) * ∑ p ∈ symmDiff s t, f p ^ 2 := by
  let g : ι → ℝ := fun p => if p ∈ s then f p else -f p
  have hdis : Disjoint (s \ t) (t \ s) := Finset.disjoint_left.mpr
    (fun p hp hq => (Finset.mem_sdiff.mp hp).2 (Finset.mem_sdiff.mp hq).1)
  have hsum : (∑ p ∈ symmDiff s t, g p) = (∑ p ∈ s, f p) - ∑ p ∈ t, f p := by
    rw [Finset.symmDiff_def, Finset.sum_union hdis]
    have hs : ∑ p ∈ s \ t, g p = ∑ p ∈ s \ t, f p :=
      Finset.sum_congr rfl (fun p hp => if_pos (Finset.mem_sdiff.mp hp).1)
    have ht : ∑ p ∈ t \ s, g p = -∑ p ∈ t \ s, f p := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun p hp => if_neg (Finset.mem_sdiff.mp hp).2)
    rw [hs, ht, ← sub_eq_add_neg, Finset.sum_sdiff_sub_sum_sdiff]
  have hsq (p : ι) : g p ^ 2 = f p ^ 2 := by
    dsimp only [g]
    split_ifs <;> simp only [neg_sq]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (symmDiff s t) (fun _ => (1 : ℝ)) g
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    hsum, hsq] using hcs

/-- Resampling any one trajectory changes a canonical cluster sum in square
by at most twice the square mass on the symmetric difference (`eq:CS`). -/
theorem cluster_sum_swap_sq_le (B : Base) (ω ω' : TrajSeq B) (T j : ℕ)
    (hshared : ∀ i, i < T → i ≠ j → ω i = ω' i) (f : Site B → ℝ) :
    ((∑ p ∈ clusterPlusFinset B ω T, f p) -
      ∑ p ∈ clusterPlusFinset B ω' T, f p) ^ 2 ≤
      2 * ∑ p ∈ symmDiff (clusterPlusFinset B ω T) (clusterPlusFinset B ω' T), f p ^ 2 := by
  classical
  have he := CanonicalExchange.clusterPlusTraj_symmDiff_encard_le_two B ω ω' T j hshared
  have hc : ((symmDiff (clusterPlusFinset B ω T) (clusterPlusFinset B ω' T)).card : ℝ) ≤ 2 := by
    rw [← coe_clusterPlusFinset B ω T, ← coe_clusterPlusFinset B ω' T,
      ← Finset.coe_symmDiff, Set.encard_coe_eq_coe_finsetCard] at he
    exact_mod_cast he
  exact (sum_sub_sq_le _ _ f).trans
    (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun p _ => sq_nonneg (f p)))

end IdlaCyl.Replace
