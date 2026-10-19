/-
Lemma `le:mono-init` (`tex:1400-1405`), with its proof at `tex:1407-1419`.

The paper's words:

  "Let $\mathcal{B}_1 \subseteq \mathcal{B}_2 \subsetneq V_N \times \bbZ$ be two
   proper subsets of the cylinder, and let $\o = (\o_1, \o_2, \ldots)$ be a
   sequence of infinite cylinder walks with prescribed starting sites. For each
   $i \in \{1, 2\}$ and $k \geq 0$, let $\Phi_k(\mathcal{B}_i)$ denote the cluster
   obtained from $\mathcal{B}_i$ after the first $k$ walks have been released and
   settled according to the usual IDLA rule (the $j$-th walk settles at the first
   site of $\o_j$ outside the current cluster). Assume that for each
   $i \in \{1, 2\}$ and each $k \geq 0$, the first exit time of $\o_{k+1}$ from
   $\Phi_k(\mathcal{B}_i)$ is almost surely finite. Then
   \[
     \Phi_k(\mathcal{B}_1) \;\subseteq\; \Phi_k(\mathcal{B}_2)
       \qquad \text{for every } k \geq 0\,.
   \]"

The Lean statement reads this as an almost-sure statement, for any probability
law `μ` of the walk sequences, that `clusterFrom B A₁ ω k ⊆ clusterFrom B A₂ ω k`
holds for every `k`, with the finiteness premise assumed almost surely for each
starting set and each `k`.
-/

import IdlaCyl.Support.CanonicalExit
import IdlaCyl.Support.Exit

open MeasureTheory

namespace IdlaCyl.Frozen

-- FROZEN-STATEMENT-BEGIN
theorem le_mono_init_v2 (B : Base) (A₁ A₂ : Set (Site B)) (hsub : A₁ ⊆ A₂)
    (hp₁ : A₁ ≠ (Set.univ : Set (Site B)))
    (hp₂ : A₂ ≠ (Set.univ : Set (Site B)))
    (μ : Measure (TrajSeq B)) [IsProbabilityMeasure μ]
    (hfinite : ∀ A ∈ ({A₁, A₂} : Set (Set (Site B))), ∀ k,
      ∀ᵐ ω ∂μ, exitTime' B (clusterFrom B A ω k) (ω k) ≠ ⊤) :
    ∀ᵐ ω ∂μ, ∀ k, clusterFrom B A₁ ω k ⊆ clusterFrom B A₂ ω k
-- FROZEN-STATEMENT-END
  := by
  -- The printed properness premises are kept in the statement but not used by the induction.
  have _ := hp₁
  have _ := hp₂
  -- Only the larger set's finiteness is used: `exitTime'_mono` gives the smaller one.
  have hA₂ : ∀ k, ∀ᵐ ω ∂μ, exitTime' B (clusterFrom B A₂ ω k) (ω k) ≠ ⊤ :=
    fun k => hfinite A₂ (by simp) k
  filter_upwards [ae_all_iff.mpr hA₂] with ω hω
  intro k
  induction k with
  | zero => simpa only [clusterFrom_zero] using hsub
  | succ k ih =>
    simp only [clusterFrom_succ]
    refine Set.union_subset ?_ ?_
    · exact ih.trans Set.subset_union_left
    · exact Set.singleton_subset_iff.mpr (exitSite'_mem_of_subset B ih (hω k))

/-- Nonvacuity: the premises of `le_mono_init_v2` are satisfiable.  For the canonical
law `idlaMeasure B` and `A₁ = A₂ = R B 0`, the set is proper because `(B.pt, 1)` lies
outside it, and the finiteness premise is `exitTraj_ae_finite`, since `clusterTraj B ω k`
is by definition `clusterFrom B (R B 0) ω k`. -/
example (B : Base) :
    ∀ᵐ ω ∂idlaMeasure B, ∀ k, clusterFrom B (R B 0) ω k ⊆ clusterFrom B (R B 0) ω k := by
  have hR0 : R B 0 ≠ (Set.univ : Set (Site B)) := by
    intro h
    have hmem : ((B.pt, (1 : ℤ)) : Site B) ∈ R B 0 := by
      rw [h]
      exact Set.mem_univ _
    rw [mem_R] at hmem
    norm_num at hmem
  have hfin : ∀ A ∈ ({R B 0, R B 0} : Set (Set (Site B))), ∀ k,
      ∀ᵐ ω ∂idlaMeasure B, exitTime' B (clusterFrom B A ω k) (ω k) ≠ ⊤ := by
    intro A hA k
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl <;> exact exitTraj_ae_finite B k
  exact le_mono_init_v2 B (R B 0) (R B 0) Set.Subset.rfl hR0 hR0 (idlaMeasure B) hfin

end IdlaCyl.Frozen
