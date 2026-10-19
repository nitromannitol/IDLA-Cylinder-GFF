/-
The deterministic slab bound behind `clm:Q-W` (`tex:1011-1030`).

On the good event `E`, the cluster satisfies
`R_{T/N - d} ⊆ A(T) ⊆ R_{T/N + d}`, so the symmetric difference
`A(T) △ R_{T/N}` is contained in the slab `R_{T/N + d} \ R_{⌊T/N - d⌋}`, and
hence the two quadratic masses differ by at most the mass of that slab:

  `|∑_{A_+(T)} |ψ|² − ∑_{R_{T/N}∖R_0} |ψ|²| ≤ ∑_{p ∈ slab} |ψ|²`.

This file is the canonical (Finset-level, no `finsum`/`tsum`) form of the
deterministic half of `clm:Q-W`; the analytic half (`eqn:psi squared` and the
`(2Δ_N+1)/a_N` estimate) is proved separately.

## Note on the slab

The paper's slab is `R_{T/N + Δ_N} \ R_{⌊T/N - Δ_N⌋}`, i.e. the integer vertical
levels `⌊T/N - d⌋ + 1, …, ⌊T/N + d⌋`, where `d = Δ_N`; this is
`slabFinset B T d` below.  It is **not** the rectangle
`{p | 1 ≤ p.2 ≤ ⌊T/N⌋}`: with `d > 0` the cluster may occupy a site above
`⌊T/N⌋`, and a `ψ` supported on such a site (and vanishing on the rectangle)
makes the difference of the two quadratic masses positive while the rectangle
mass is `0`, so the inequality with the rectangle on the right is false.  The
main theorem therefore bounds by the paper's slab; the general slab form
`quadratic_mass_difference_le_of_slab` is stated for any slab containing the
symmetric difference, so a caller may use whichever Finset it has.
-/
import IdlaCyl.Support.Discrepancy
import IdlaCyl.Support.ShapeSlab
import IdlaCyl.Support.QuadraticMass

namespace IdlaCyl

open scoped BigOperators

variable (B : Base)

/-- The slab `R_{T/N+d} \ R_{⌊T/N-d⌋}` above level `0`, as a `Finset`:
`V_N × {⌊T/N-d⌋+1, …, ⌊T/N+d⌋}`. -/
noncomputable def slabFinset (T : ℕ) (d : ℝ) : Finset (Site B) :=
  Finset.univ.product
    (Finset.Icc (⌊(T : ℝ) / (B.card : ℝ) - d⌋ + 1)
      ⌊(T : ℝ) / (B.card : ℝ) + d⌋)

/-- Membership in the slab. -/
theorem mem_slabFinset_iff (T : ℕ) (d : ℝ) (p : Site B) :
    p ∈ slabFinset B T d ↔
      ⌊(T : ℝ) / (B.card : ℝ) - d⌋ + 1 ≤ p.2 ∧
        p.2 ≤ ⌊(T : ℝ) / (B.card : ℝ) + d⌋ := by
  simp [slabFinset, Finset.mem_product]

/-- **`clm:Q-W`, slab form.**  If the symmetric difference of `A_+(T)` and the
rectangle `V_N × {1, …, ⌊T/N⌋}` is contained in `slab`, then the two quadratic
masses differ by at most `∑_{slab} ψ²`.  The `Finset` form of
`quadratic_mass_difference_le_slab`, with `L = A ∩ R` and `U = A ∪ R`, so that
`U \ L = A △ R`. -/
theorem quadratic_mass_difference_le_of_slab (ω : TrajSeq B) (T : ℕ)
    (slab : Finset (Site B))
    (hslab : (clusterPlusFinset B ω T \ rectangleFinset B T) ∪
        (rectangleFinset B T \ clusterPlusFinset B ω T) ⊆ slab)
    (ψ : Site B → ℝ) :
    |(∑ p ∈ clusterPlusFinset B ω T, ψ p ^ 2)
        - (∑ p ∈ rectangleFinset B T, ψ p ^ 2)|
      ≤ ∑ p ∈ slab, ψ p ^ 2 := by
  set A := clusterPlusFinset B ω T
  set R := rectangleFinset B T
  have hmain := quadratic_mass_difference_le_slab A R (A ∩ R) (A ∪ R)
    Finset.inter_subset_left Finset.subset_union_left
    Finset.inter_subset_right Finset.subset_union_right ψ
  refine hmain.trans ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    apply hslab
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at hp ⊢
    tauto
  · intro p _ _
    exact sq_nonneg (ψ p)

/-- **The canonical `clm:Q-W` deterministic bound** (`tex:1011-1030`).  If
`R_{T/N-d} ⊆ A(T) ⊆ R_{T/N+d}` with `d ≥ 0`, then the difference between the
quadratic masses over `A_+(T)` and over the rectangle `V_N × {1,…,⌊T/N⌋}` is at
most the quadratic mass of the paper's slab
`V_N × {⌊T/N-d⌋+1, …, ⌊T/N+d⌋}`. -/
theorem clm_q_w_bound (ω : TrajSeq B) (T : ℕ) (d : ℝ) (hd : 0 ≤ d)
    (hsub : R B ((T : ℝ) / (B.card : ℝ) - d) ⊆ clusterTraj B ω T)
    (hsup : clusterTraj B ω T ⊆ R B ((T : ℝ) / (B.card : ℝ) + d))
    (ψ : Site B → ℝ) :
    |(∑ p ∈ clusterPlusFinset B ω T, ψ p ^ 2)
        - (∑ p ∈ rectangleFinset B T, ψ p ^ 2)|
      ≤ ∑ p ∈ slabFinset B T d, ψ p ^ 2 := by
  apply quadratic_mass_difference_le_of_slab B ω T (slabFinset B T d)
  intro p hp
  rw [mem_slabFinset_iff]
  rw [Finset.mem_union] at hp
  rcases hp with hp | hp
  · -- `p ∈ A_+(T) \ rectangle`: above `⌊T/N⌋`, at most `⌊T/N+d⌋`.
    rw [Finset.mem_sdiff] at hp
    obtain ⟨hpA, hpR⟩ := hp
    have hA2 : 1 ≤ p.2 := ((mem_clusterPlusFinset_iff B ω T p).mp hpA).2
    have hcl : p ∈ clusterTraj B ω T := mem_clusterPlusFinset_cluster B ω T hpA
    refine ⟨?_, ?_⟩
    · have hnotR : ¬ (p.2 ≤ ⌊(T : ℝ) / (B.card : ℝ)⌋) := by
        intro hle
        exact hpR ((mem_rectangleFinset_iff B T p).mpr ⟨hA2, hle⟩)
      have hlt : ⌊(T : ℝ) / (B.card : ℝ)⌋ < p.2 := lt_of_not_ge hnotR
      have hmono : ⌊(T : ℝ) / (B.card : ℝ) - d⌋ ≤ ⌊(T : ℝ) / (B.card : ℝ)⌋ :=
        Int.floor_mono (by linarith)
      omega
    · have hR : (p.2 : ℝ) ≤ (T : ℝ) / (B.card : ℝ) + d := mem_R.mp (hsup hcl)
      exact (Int.le_floor).mpr hR
  · -- `p ∈ rectangle \ A_+(T)`: at least `⌊T/N-d⌋+1`, at most `⌊T/N⌋`.
    rw [Finset.mem_sdiff] at hp
    obtain ⟨hpR, hpA⟩ := hp
    have hRm := (mem_rectangleFinset_iff B T p).mp hpR
    have hR2 : 1 ≤ p.2 := hRm.1
    have hcl : p ∉ clusterTraj B ω T := by
      intro h
      exact hpA ((mem_clusterPlusFinset_iff_cluster B ω T hR2).mpr h)
    refine ⟨?_, hRm.2.trans (Int.floor_mono (show (T : ℝ) / (B.card : ℝ) ≤
      (T : ℝ) / (B.card : ℝ) + d by linarith))⟩
    have hnotRlo : ¬ ((p.2 : ℝ) ≤ (T : ℝ) / (B.card : ℝ) - d) := by
      intro h
      exact hcl (hsub (mem_R.mpr h))
    have hlt : (T : ℝ) / (B.card : ℝ) - d < (p.2 : ℝ) := lt_of_not_ge hnotRlo
    have := (Int.floor_lt).mpr hlt
    omega

end IdlaCyl
