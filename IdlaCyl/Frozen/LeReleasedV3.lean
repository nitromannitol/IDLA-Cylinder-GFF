/-
Height of a balanced release in any order (`le:released`, all enumerations).
Source: paper/idla-cylinder-gff.tex, tex:1331-1337 ("releasing exactly m particles from each
site of V_N × {0}, in any order"; the lemma gives C₃, K₁ and the bound N^{-(ν+2)}).

`le_released_v2` (`LeReleasedV2.lean`) fixes the enumeration `balancedIndex`. This file
states the bound for every enumeration `σ` of the N·m releases. The constants are the ones of
`le_released_v2`, chosen before `B`, `m` and `σ`. The proof rewrites each order-`σ` law as the
`balancedIndex` law by `balancedLaw_cluster_order_invariant`
(`IdlaCyl/Support/Outer/BalancedReleaseOrder.lean`).
-/
import IdlaCyl.Frozen.LeReleasedV2
import IdlaCyl.Support.Outer.BalancedReleaseOrder

namespace IdlaCyl.Frozen

open IdlaCyl MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

-- FROZEN-STATEMENT-BEGIN
theorem le_released_v3 (ν : ℝ) (hν : 0 < ν) :
    ∃ C₃ K₁ : ℝ, 0 < C₃ ∧ 0 < K₁ ∧ ∃ N₀ : ℕ,
      ∀ B : Base, N₀ ≤ B.card → ∀ m : ℕ,
        K₁ * Real.log (B.card : ℝ) ≤ (m : ℝ) →
        ∀ σ : Fin (B.card * m) ≃ B.V × Fin m,
          balancedLaw B m {ω : BalancedDriver B m |
            ¬ (balancedClusterOf B m σ ω ⊆ R B (C₃ * (m : ℝ)))} ≤
              ENNReal.ofReal ((B.card : ℝ) ^ (-(ν + 2)))
-- FROZEN-STATEMENT-END
  := by
  obtain ⟨C₃, K₁, hC₃, hK₁, N₀, hbound⟩ := le_released_v2 ν hν
  refine ⟨C₃, K₁, hC₃, hK₁, N₀, fun B hB m hm σ => ?_⟩
  rw [balancedLaw_cluster_order_invariant B m σ (C₃ * (m : ℝ))]
  exact hbound B hB m hm

end
end IdlaCyl.Frozen
