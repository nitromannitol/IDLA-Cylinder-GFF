import IdlaCyl.Support.Replace.SlabVariance
import IdlaCyl.Support.Replace.SlabReduction

/-!
Chebyshev and the shape-event decomposition in the replacement lemma
(`tex:791-803`, `tex:846-863`, `eq:Zn-decomp`).
-/

namespace IdlaCyl.Replace

open MeasureTheory ProbabilityTheory Defs
open scoped BigOperators

variable (B : Base)

/-- The pairing tail is bounded by the bad-shape probability and the
canonical slab variance estimate. -/
theorem pairing_tail_le (T : ℕ) (d : ℝ)
    (hL : 0 ≤ ⌊(T : ℝ) / (B.card : ℝ) - d⌋) (f : Site B → ℝ)
    (hf : ZeroHorizontalAverage B f) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ y ∈ slabHeights B T d, layerMeanSquare B f y ≤ M)
    (c ε : ℝ) (hε : 0 < ε) :
    (idlaMeasure B).real {ω | ε ≤ |c * pairingTraj B ω T f|} ≤
      (idlaMeasure B).real (eventAt B T d)ᶜ + c ^ 2 * (2 * T * M) / ε ^ 2 := by
  let Y := slabHeights B T d
  have hY (y : ℤ) (hy : y ∈ Y) : 1 ≤ y := by
    have hh := (Finset.mem_Ioc.mp hy).1
    omega
  let S := fun ω => c * slabSum B T Y f ω
  have hlp : MemLp (slabSum B T Y f) 2 (idlaMeasure B) :=
    MemLp.of_bound (measurable_slabSum B T Y f).aestronglyMeasurable
      (∑ y ∈ Y, ∑ x : B.V, |f (x, y)|) (.of_forall fun ω => by
        simpa only [Real.norm_eq_abs] using slabSum_abs_le B T Y f ω)
  have hSlp : MemLp S 2 (idlaMeasure B) := hlp.const_mul c
  have hmean : (∫ ω, S ω ∂idlaMeasure B) = 0 := by
    rw [integral_const_mul, integral_slabSum_eq_zero B T Y f hf, mul_zero]
  have hcheb : (idlaMeasure B).real {ω | ε ≤ |S ω|} ≤
      variance S (idlaMeasure B) / ε ^ 2 := by
    have he := meas_ge_le_variance_div_sq hSlp hε
    rw [hmean] at he
    simp only [sub_zero] at he
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
    change ((idlaMeasure B) {ω | ε ≤ |S ω|}).toReal ≤ _
    simpa only [ENNReal.toReal_ofReal
      (div_nonneg (variance_nonneg S (idlaMeasure B)) (sq_nonneg ε))] using ht
  have hvar : variance S (idlaMeasure B) ≤ c ^ 2 * (2 * T * M) := by
    rw [variance_const_mul]
    exact mul_le_mul_of_nonneg_left (variance_slabSum_le B T Y hY f M hM hbound)
      (sq_nonneg c)
  have hsub : {ω : TrajSeq B | ε ≤ |c * pairingTraj B ω T f|} ⊆
      (eventAt B T d)ᶜ ∪ {ω | ε ≤ |S ω|} := by
    intro ω hω
    by_cases hshape : ω ∈ eventAt B T d
    · right
      change ε ≤ |c * slabSum B T Y f ω|
      rw [← pairing_eq_slabSum_on_event B ω T d hL hshape f hf]
      exact hω
    · exact Or.inl hshape
  calc
    _ ≤ (idlaMeasure B).real (eventAt B T d)ᶜ +
        (idlaMeasure B).real {ω | ε ≤ |S ω|} :=
      (measureReal_mono hsub).trans (measureReal_union_le _ _)
    _ ≤ (idlaMeasure B).real (eventAt B T d)ᶜ +
        variance S (idlaMeasure B) / ε ^ 2 := add_le_add le_rfl hcheb
    _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_right hvar (sq_nonneg ε))

end IdlaCyl.Replace
