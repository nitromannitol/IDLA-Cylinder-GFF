/-
Gluing the actual canonical flat-cluster laws along a deterministic trace.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.
-/
import IdlaCyl.Support.Reduction.CountableGlue

namespace IdlaCyl.Reduction

open MeasureTheory
open scoped BigOperators

/-- Adjacent literal cluster couplings compose with the sum of their allowances. -/
theorem glue_flat_trace (B : Base) (R : ℕ) (t : Fin (R + 1) → ℕ)
    (ℓ : Fin R → ℕ) (ε : Fin R → ℝ) (hε : ∀ i, 0 ≤ ε i)
    (hc : ∀ i : Fin R, ClusterCoupling B
      (flatClusterLaw B (t i.castSucc)) (flatClusterLaw B (t i.succ)) (ℓ i) (ε i)) :
    ClusterCoupling B (flatClusterLaw B (t 0)) (flatClusterLaw B (t (Fin.last R)))
      (∑ i, ℓ i) (∑ i, ε i) := by
  exact glue_cluster_couplings B R (fun i => flatClusterLaw B (t i))
    (fun _ => layerGrowthLaw_isProbability _ _ _ _) ℓ ε hε hc

end IdlaCyl.Reduction
