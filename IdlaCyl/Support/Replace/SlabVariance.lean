module

public import IdlaCyl.Support.Replace.CanonicalEfronStein
public import IdlaCyl.Support.Replace.SwapAverage

@[expose] public section

/-!
The variance estimate for the canonical truncated replacement statistic
(`tex:828-848`, `eq:varSN`). The only upper bound supplied is the deterministic
layer mean square of the fixed test function.
-/

namespace IdlaCyl.Replace

open MeasureTheory ProbabilityTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable (B : Base)

private theorem sum_truncated (A : Finset (Site B)) (Y : Finset ℤ) (f : Site B → ℝ) :
    (∑ p ∈ A, if p.2 ∈ Y then f p else 0) =
      ∑ y ∈ Y, ∑ x : B.V, if (x, y) ∈ A then f (x, y) else 0 := by
  let Q : Finset (Site B) := Finset.univ.product Y
  have htest (p : Site B) : (if p.2 ∈ Y then f p else 0) =
      (if p ∈ Q then f p else 0) := by
    rcases p with ⟨x, y⟩
    simp only [Q, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_univ, true_and]
  calc
    _ = ∑ p ∈ A ∩ Q, f p := by simp_rw [htest]; rw [Finset.sum_ite_mem]
    _ = ∑ p ∈ Q ∩ A, f p := by rw [Finset.inter_comm]
    _ = ∑ p ∈ Q, if p ∈ A then f p else 0 := by rw [Finset.sum_ite_mem]
    _ = _ := by
      exact (Finset.sum_product (Finset.univ : Finset B.V) Y
        (fun p : Site B => if p ∈ A then f p else 0)).trans Finset.sum_comm

/-- The fixed slab occupation sum is the positive-cluster sum of the
slab-truncated field, for a slab strictly above the seed. -/
theorem slabSum_eq_clusterSum (T : ℕ) (Y : Finset ℤ)
    (hY : ∀ y ∈ Y, 1 ≤ y) (f : Site B → ℝ) (ω : TrajSeq B) :
    slabSum B T Y f ω =
      ∑ p ∈ clusterPlusFinset B ω T, if p.2 ∈ Y then f p else 0 := by
  rw [sum_truncated B]
  unfold slabSum
  apply Finset.sum_congr rfl
  intro y hy
  exact Finset.sum_congr rfl fun x _ => by
    simp only [mem_clusterPlusFinset_iff_cluster B ω T (p := (x, y)) (hY y hy)]

/-- Pathwise squared change of the slab sum under one-coordinate replacement. -/
theorem slabSum_swap_sq_le (T j : ℕ) (Y : Finset ℤ)
    (hY : ∀ y ∈ Y, 1 ≤ y) (f : Site B → ℝ)
    (z : TrajSeq B × (ℕ → Site B)) :
    (slabSum B T Y f z.1 - slabSum B T Y f (swapped B j z)) ^ 2 ≤
      2 * swapSlabMass B T j Y f z := by
  have hshared (i : ℕ) (_ : i < T) (hi : i ≠ j) : z.1 i = swapped B j z i := by
    simp only [swapped, Function.update_of_ne hi]
  rw [slabSum_eq_clusterSum B T Y hY f z.1,
    slabSum_eq_clusterSum B T Y hY f (swapped B j z)]
  have h := cluster_sum_swap_sq_le B z.1 (swapped B j z) T j hshared
    (fun p => if p.2 ∈ Y then f p else 0)
  have he : (∑ p ∈ swapSites B T j z, (if p.2 ∈ Y then f p else 0) ^ 2) =
      swapSlabMass B T j Y f z := by
    have hsq (p : Site B) : (if p.2 ∈ Y then f p else 0) ^ 2 =
        if p.2 ∈ Y then f p ^ 2 else 0 := by split_ifs <;> simp only [zero_pow (by norm_num : 2 ≠ 0)]
    simp_rw [hsq]
    exact sum_truncated B (swapSites B T j z) Y (fun p => f p ^ 2)
  change _ ≤ 2 * (∑ p ∈ swapSites B T j z, (if p.2 ∈ Y then f p else 0) ^ 2) at h
  rwa [he] at h

private theorem integrable_slabSwapSq (T j : ℕ) (Y : Finset ℤ) (f : Site B → ℝ) :
    Integrable (fun z : TrajSeq B × (ℕ → Site B) =>
      (slabSum B T Y f z.1 - slabSum B T Y f (swapped B j z)) ^ 2) (swapLaw B) := by
  let C : ℝ := ∑ y ∈ Y, ∑ x : B.V, |f (x, y)|
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hm : Measurable (fun z : TrajSeq B × (ℕ → Site B) =>
      (slabSum B T Y f z.1 - slabSum B T Y f (swapped B j z)) ^ 2) :=
    (((measurable_slabSum B T Y f).comp measurable_fst).sub
      ((measurable_slabSum B T Y f).comp (measurable_swapped B j))).pow_const 2
  refine Integrable.of_bound hm.aestronglyMeasurable (4 * C ^ 2) (.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hb := (abs_sub _ _).trans
    (add_le_add (slabSum_abs_le B T Y f z.1) (slabSum_abs_le B T Y f (swapped B j z)))
  have hs := (sq_le_sq₀ (abs_nonneg _) (show 0 ≤ C + C by linarith)).mpr hb
  rw [sq_abs] at hs
  nlinarith only [hs]

/-- The expected squared effect of resampling any one canonical trajectory
is at most four times the maximal layer mean square. -/
theorem integral_slabSwapSq_le (T j : ℕ) (Y : Finset ℤ)
    (hY : ∀ y ∈ Y, 1 ≤ y) (f : Site B → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ y ∈ Y, layerMeanSquare B f y ≤ M) :
    (∫ ω, ∫ X, (slabSum B T Y f ω -
      slabSum B T Y f (Function.update ω j X)) ^ 2
        ∂walkLawUniform B ∂idlaMeasure B) ≤ 4 * M := by
  have hi := integrable_slabSwapSq B T j Y f
  calc
    _ = ∫ z, (slabSum B T Y f z.1 - slabSum B T Y f (swapped B j z)) ^ 2
        ∂swapLaw B := (integral_prod _ hi).symm
    _ ≤ ∫ z, 2 * swapSlabMass B T j Y f z ∂swapLaw B :=
      integral_mono hi ((integrable_swapSlabMass B T j Y f).const_mul 2)
        (slabSum_swap_sq_le B T j Y hY f)
    _ = 2 * ∫ z, swapSlabMass B T j Y f z ∂swapLaw B := integral_const_mul _ _
    _ ≤ 4 * M := by
      have h := integral_swapSlabMass_le B T j Y f M hM hbound
      linarith

/-- The variance estimate `eq:varSN` on the canonical process. -/
theorem variance_slabSum_le (T : ℕ) (Y : Finset ℤ)
    (hY : ∀ y ∈ Y, 1 ≤ y) (f : Site B → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ y ∈ Y, layerMeanSquare B f y ≤ M) :
    variance (slabSum B T Y f) (idlaMeasure B) ≤ 2 * T * M := by
  have h := efron_stein_slabSum_update B T Y f
  have hc : (∑ i : Fin T, ∫ ω, ∫ X,
      (slabSum B T Y f ω - slabSum B T Y f (Function.update ω (i : ℕ) X)) ^ 2
        ∂walkLawUniform B ∂idlaMeasure B) ≤ (T : ℝ) * (4 * M) := by
    calc
      _ ≤ ∑ _i : Fin T, 4 * M := Finset.sum_le_sum fun i _ =>
        integral_slabSwapSq_le B T i Y hY f M hM hbound
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

end IdlaCyl.Replace
