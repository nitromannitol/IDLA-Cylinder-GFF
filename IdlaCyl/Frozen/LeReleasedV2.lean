/-
Height of a balanced release (`le:released`).
Source: paper/idla-cylinder-gff.tex, tex:1328-1372 (Lemma `le:released` and its proof).

The printed lemma (tex:1328-1331): for every `ν > 0` there exist constants `C₃ = C₃(ν) < ∞` and
`K₁ = K₁(ν) < ∞` such that, for every integer `m ≥ K₁ log N`, `ℙ(Ã^{(m)} ⊄ R_{C₃ m}) ≤ N^{-(ν+2)}`
for `N` large enough, where `Ã^{(m)}` is the cluster of `m` particles released from each site of
`V_N × {0}` in any order.

The Lean reads it as: for `ν > 0` there are `C₃ > 0` and `K₁ > 0` and `N₀` such that for every
base `B` with `N₀ ≤ B.card` and every `m` with `K₁ log B.card ≤ m`, the balanced law of the
cluster leaving `R B (C₃ m)` is at most `N^{-(ν+2)}`.

Status: PROVED. The proof reduces to `IdlaCyl.le_released_v2_of_fixed_comparison` applied to
`IdlaCyl.le_released_v2_fixed` (IdlaCyl/Support/Outer/LeReleasedV2Assembly.lean).
-/
import IdlaCyl.Support.Outer.BalancedRelease
import IdlaCyl.Support.Outer.LeReleasedV2Assembly

namespace IdlaCyl.Frozen

open IdlaCyl MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

-- FROZEN-STATEMENT-BEGIN
theorem le_released_v2 (ν : ℝ) (hν : 0 < ν) :
    ∃ C₃ K₁ : ℝ, 0 < C₃ ∧ 0 < K₁ ∧ ∃ N₀ : ℕ,
      ∀ B : Base, N₀ ≤ B.card → ∀ m : ℕ,
        K₁ * Real.log (B.card : ℝ) ≤ (m : ℝ) →
        balancedLaw B m {ω : BalancedDriver B m |
          ¬ (balancedCluster B m ω ⊆ R B (C₃ * (m : ℝ)))} ≤
            ENNReal.ofReal ((B.card : ℝ) ^ (-(ν + 2)))
-- FROZEN-STATEMENT-END
  := by
  exact IdlaCyl.le_released_v2_of_fixed_comparison IdlaCyl.le_released_v2_fixed ν hν

end
end IdlaCyl.Frozen
