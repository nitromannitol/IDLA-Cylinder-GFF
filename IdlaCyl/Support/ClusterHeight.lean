/-
The canonical cluster is contained in a half-cylinder.

This is the missing interface between the conditional expectation
(`Support/CondExpZero.lean`) and the walk optional stopping
(`Support/ExitIntegral.lean`): the latter only gives the zero exit integral for
sets already contained in some half-cylinder `R B h`, and `clusterTraj B ω k` is
exactly such a set.  The unbounded-`S` hypothesis `hint_zero` of
`condExp_settleSite_eq_zero` is not the honest interface; this file supplies the
height cap it needs.
-/
import IdlaCyl.Support.CanonicalIdla
import IdlaCyl.Support.CanonicalGrowth

namespace IdlaCyl

variable (B : Base)

/-- Every cluster `A(k)` is contained in a half-cylinder (`tex:263-265`): it is
`R_0` together with the finitely many settling sites, so the maximum of their
heights caps it. -/
theorem clusterTraj_subset_R (ω : TrajSeq B) (k : ℕ) :
    ∃ H : ℤ, clusterTraj B ω k ⊆ R B (H : ℝ) := by
  refine ⟨max 0 (∑ j ∈ Finset.range k, |(settleSite B ω j).2|), ?_⟩
  intro p hp
  rw [clusterTraj_eq_union] at hp
  simp only [Set.mem_union, Finset.coe_image, Set.mem_image, mem_R] at hp ⊢
  rcases hp with hp | ⟨j, hj, rfl⟩
  · have hH : (0 : ℝ) ≤
        ((max 0 (∑ j ∈ Finset.range k, |(settleSite B ω j).2|) : ℤ) : ℝ) := by
      exact_mod_cast (le_max_left (0 : ℤ) _)
    linarith
  · have hle_sum : |(settleSite B ω j).2|
        ≤ ∑ i ∈ Finset.range k, |(settleSite B ω i).2| :=
      Finset.single_le_sum (f := fun i => |(settleSite B ω i).2|)
        (fun i _ => abs_nonneg _) hj
    have h1 : (settleSite B ω j).2
        ≤ max 0 (∑ i ∈ Finset.range k, |(settleSite B ω i).2|) :=
      le_trans (le_abs_self _) (le_trans hle_sum (le_max_right _ _))
    exact_mod_cast h1

end IdlaCyl
