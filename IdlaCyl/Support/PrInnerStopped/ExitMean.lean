/-
The uniform-start exit mean of the hitting probability (`paper/idla-cylinder-gff.tex:1198-1202`).

A cylinder walk started uniformly on `V_N × {0}` exits a set `S` with `R_0 ⊆ S ⊆ R_{ζ_2 - 1}` at a
site where the hitting probability `H_ζ` has mean `1/N`.  The fixed-start identity is
`hitProb_exit_mean`, applied at every base point of layer `0`; the layer average is
`hitProb_layer_sum` at layer `0`.
-/
import IdlaCyl.Support.ExitIntegral
import IdlaCyl.Support.FirstHit
import IdlaCyl.Support.Recurrence.Discharge

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable (B : Base)

/-- **Uniform-start exit mean of `H_ζ`** (`tex:1198-1202`).  For a set `S` with
`R_0 ⊆ S ⊆ R_{ζ_2 - 1}`, the expectation of `H_ζ` at the exit site of a cylinder walk started
uniformly on `V_N × {0}` is `1/N`. -/
theorem integral_hitProb_exitSite_uniform (ζ : Site B) (S : Set (Site B))
    (hS : S ⊆ R B ((ζ.2 : ℝ) - 1)) (hS0 : R B 0 ⊆ S) :
    ∫ X, hitProb B ζ (exitSite' B S X) ∂(walkLawUniform B) = 1 / (B.card : ℝ) := by
  have hcard_pos : 0 < B.card := lt_of_lt_of_le (by norm_num) B.nontrivial
  have hcard_ne : (B.card : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hcard_pos.ne'
  -- the base point of layer `0` lies in `R_0 ⊆ S ⊆ R_{ζ_2 - 1}`, so `0 ≤ ζ_2`
  have hmem0 : ((B.pt, (0 : ℤ)) : Site B) ∈ R B 0 := by
    rw [mem_R]
    simp
  have hζ : (0 : ℤ) ≤ ζ.2 := by
    have h1 := hS (hS0 hmem0)
    rw [mem_R] at h1
    have h2 : ((0 : ℤ) : ℝ) ≤ (ζ.2 : ℝ) - 1 := h1
    have h3 : (1 : ℤ) ≤ ζ.2 := by
      have h4 : (1 : ℝ) ≤ (ζ.2 : ℝ) := by
        push_cast at h2
        linarith
      exact_mod_cast h4
    omega
  have hbound : ∀ X : ℕ → Site B, ‖hitProb B ζ (exitSite' B S X)‖ ≤ 1 := by
    intro X
    rw [Real.norm_eq_abs, abs_of_nonneg (hitProb_nonneg B ζ _)]
    exact hitProb_le_one B ζ _
  have hmeas : Measurable fun X : ℕ → Site B => hitProb B ζ (exitSite' B S X) :=
    (measurable_of_countable (hitProb B ζ)).comp (measurable_exitSite' B S)
  have hint : Integrable (fun X : ℕ → Site B => hitProb B ζ (exitSite' B S X))
      ((walkPathKernel B).comp (layerKernel B) ()) := by
    rw [walkPathKernel_comp_layerKernel]
    exact Integrable.of_bound hmeas.aestronglyMeasurable 1 (Filter.Eventually.of_forall hbound)
  have hcomp : ∫ X, hitProb B ζ (exitSite' B S X) ∂(walkLawUniform B)
      = ∫ p, (∫ X, hitProb B ζ (exitSite' B S X) ∂(walkPathLaw B p)) ∂(layerLawAt B 0) := by
    rw [← walkPathKernel_comp_layerKernel]
    rw [Kernel.integral_comp hint]
    simp only [walkPathKernel_apply, layerKernel_apply]
  -- the fixed-start identity at every base point of layer `0`
  have hstart : ∀ x : B.V, ∫ X, hitProb B ζ (exitSite' B S X) ∂(walkPathLaw B (x, 0))
      = hitProb B ζ (x, 0) := fun x =>
    hitProb_exit_mean B ζ S hS (x, 0)
      (hS0 (show ((x, 0) : Site B) ∈ R B 0 by rw [mem_R]; simp))
      External.lazyRwRecurrent_holds
  have hconv : ((B.card : ℝ≥0∞)⁻¹).toReal = 1 / (B.card : ℝ) := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
  rw [hcomp]
  unfold layerLawAt
  rw [Measure.sum_fintype]
  have hInt : ∀ x ∈ (Finset.univ : Finset B.V),
      Integrable (fun p : Site B => ∫ X, hitProb B ζ (exitSite' B S X) ∂(walkPathLaw B p))
        ((B.card : ℝ≥0∞)⁻¹ • Measure.dirac ((x, 0) : Site B)) := by
    intro x _
    refine (integrable_dirac ?_).smul_measure (ENNReal.inv_ne_top.mpr hcard_ne)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_lt_top
  rw [integral_finsetSum_measure hInt]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul, hstart, hconv]
  rw [← Finset.mul_sum, hitProb_layer_sum B ζ 0 hζ External.lazyRwRecurrent_holds, mul_one]

end IdlaCyl
