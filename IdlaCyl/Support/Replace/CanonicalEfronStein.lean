import IdlaCyl.Support.Replace.InfiniteCoordinate
import IdlaCyl.Support.Replace.SlabMean

/-!
Efron–Stein on the canonical product of cylinder walk laws (`tex:828-848`).
The statistic is the fixed finite-slab occupation sum; it depends on exactly
the consumed prefix of trajectories and is bounded on every trajectory family.
-/

namespace IdlaCyl.Replace

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable (B : Base)

attribute [local instance] Classical.propDecidable

/-- A deterministic bound on any finite-slab occupation sum. -/
theorem slabSum_abs_le (T : ℕ) (Y : Finset ℤ) (f : Site B → ℝ) (ω : TrajSeq B) :
    |slabSum B T Y f ω| ≤ ∑ y ∈ Y, ∑ x : B.V, |f (x, y)| := by
  unfold slabSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  split_ifs
  · exact le_rfl
  · simpa only [abs_zero] using abs_nonneg (f (x, y))

/-- A canonical occupation sum ignores all trajectories after time `T`. -/
theorem slabSum_finiteDependence (T : ℕ) (Y : Finset ℤ) (f : Site B → ℝ)
    (ω ω' : TrajSeq B) (h : ∀ i, i < T → ω i = ω' i) :
    slabSum B T Y f ω = slabSum B T Y f ω' := by
  unfold slabSum
  rw [clusterTraj_congr B h]

/-- Efron–Stein for the actual canonical walk product, with no finite-support
restriction on any walk law and no variance or concentration hypothesis. -/
theorem efron_stein_slabSum (T : ℕ) (Y : Finset ℤ) (f : Site B → ℝ) :
    variance (slabSum B T Y f) (idlaMeasure B) ≤
      ProductEfronStein.cost (fun _ => walkLawUniform B) T
        (fun z => slabSum B T Y f
          (ProductEfronStein.extend T z (fun _ _ => (B.pt, 0)))) / 2 := by
  exact ProductEfronStein.efron_stein_finiteDependence
    (fun _ => walkLawUniform B) T (fun _ _ => (B.pt, 0)) (slabSum B T Y f)
    (measurable_slabSum B T Y f) (slabSum_finiteDependence B T Y f)
    (∑ y ∈ Y, ∑ x : B.V, |f (x, y)|)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (slabSum_abs_le B T Y f)

/-- Canonical Efron–Stein in the usual explicit sum over resampled trajectories. -/
theorem efron_stein_slabSum_update (T : ℕ) (Y : Finset ℤ) (f : Site B → ℝ) :
    variance (slabSum B T Y f) (idlaMeasure B) ≤
      (∑ i : Fin T, ∫ ω, ∫ X,
        (slabSum B T Y f ω - slabSum B T Y f (Function.update ω (i : ℕ) X)) ^ 2
          ∂walkLawUniform B ∂idlaMeasure B) / 2 := by
  exact ProductEfronStein.efron_stein_infinitePi_update
    (fun _ => walkLawUniform B) T (fun _ _ => (B.pt, 0)) (slabSum B T Y f)
    (measurable_slabSum B T Y f) (slabSum_finiteDependence B T Y f)
    (∑ y ∈ Y, ∑ x : B.V, |f (x, y)|)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (slabSum_abs_le B T Y f)

end IdlaCyl.Replace
