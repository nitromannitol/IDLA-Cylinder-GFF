import IdlaCyl.Support.LeReplaceLayerAvg

/-!
Exact cancellation of the mean of a finite-slab sum in the replacement lemma
(`tex:853-861`). All sums have fixed finite carriers. Horizontal invariance is
used at the level of the canonical trajectory law.
-/

namespace IdlaCyl.Replace

attribute [local instance] Classical.propDecidable

open MeasureTheory
open scoped BigOperators

variable (B : Base)

/-- Sum a test function over occupied sites in a fixed finite slab. -/
noncomputable def slabSum (T : ℕ) (Y : Finset ℤ) (f : Site B → ℝ) (ω : TrajSeq B) : ℝ :=
  ∑ y ∈ Y, ∑ x : B.V, if (x, y) ∈ clusterTraj B ω T then f (x, y) else 0

/-- Every fixed-site occupation term is integrable under the canonical law. -/
theorem integrable_occupation (T : ℕ) (p : Site B) (c : ℝ) :
    Integrable (fun ω : TrajSeq B => if p ∈ clusterTraj B ω T then c else 0)
      (idlaMeasure B) := by
  exact (integrable_const c).indicator (measurableSet_mem_clusterTraj B T p)

/-- A slab sum is measurable, with no regularity required of the fixed test function. -/
theorem measurable_slabSum (T : ℕ) (Y : Finset ℤ) (f : Site B → ℝ) :
    Measurable (slabSum B T Y f) := by
  exact Finset.measurable_sum _ fun y _ => Finset.measurable_sum _ fun x _ =>
    Measurable.ite (measurableSet_mem_clusterTraj B T (x, y)) measurable_const measurable_const

/-- A slab sum is integrable under the canonical trajectory law. -/
theorem integrable_slabSum (T : ℕ) (Y : Finset ℤ) (f : Site B → ℝ) :
    Integrable (slabSum B T Y f) (idlaMeasure B) := by
  exact integrable_finsetSum _ fun y _ => integrable_finsetSum _ fun x _ =>
    integrable_occupation B T (x, y) (f (x, y))

/-- The expected slab sum is the sum of the layer probabilities times the
complete horizontal sums (`tex:853-861`). -/
theorem integral_slabSum (T : ℕ) (Y : Finset ℤ) (f : Site B → ℝ) (x₀ : B.V) :
    (∫ ω, slabSum B T Y f ω ∂idlaMeasure B) =
      ∑ y ∈ Y, (idlaMeasure B).real {ω | (x₀, y) ∈ clusterTraj B ω T} *
        ∑ x : B.V, f (x, y) := by
  unfold slabSum
  rw [integral_finsetSum _ (fun y _ => integrable_finsetSum _ (fun x _ =>
    integrable_occupation B T (x, y) (f (x, y))))]
  apply Finset.sum_congr rfl
  intro y _
  rw [integral_finsetSum _ (fun x _ => integrable_occupation B T (x, y) (f (x, y))),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  change (∫ ω, {ω : TrajSeq B | (x, y) ∈ clusterTraj B ω T}.indicator
    (fun _ => f (x, y)) ω ∂idlaMeasure B) = _
  rw [integral_indicator_const _ (measurableSet_mem_clusterTraj B T (x, y)), smul_eq_mul,
    layer_constancy B T x x₀ y]

/-- The truncated replacement sum has mean exactly zero whenever each layer
of the test function has zero horizontal average. -/
theorem integral_slabSum_eq_zero (T : ℕ) (Y : Finset ℤ) (f : Site B → ℝ)
    (hf : ZeroHorizontalAverage B f) :
    (∫ ω, slabSum B T Y f ω ∂idlaMeasure B) = 0 := by
  rw [integral_slabSum B T Y f B.pt]
  exact Finset.sum_eq_zero fun y _ => by rw [hf y, mul_zero]

end IdlaCyl.Replace
