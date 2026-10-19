/-
Block filling of the stopped cluster: with `2NH` particles stopped at height `H`, the stopped
cluster fills the layer `R_H` except with probability `N H e^{-H/8}`.
Source: paper/idla-cylinder-gff.tex, tex:1227-1251.
The per-site estimate of `PrInnerStopped/BoundaryMeasure.lean` is applied at the stopping layer
of each site, the monotonicity in the stopping height lifts it to the top layer, and a union
bound over the `N H` sites of the block closes the estimate.
-/
import IdlaCyl.Support.PrInnerStopped.BoundaryMeasure

/-!
# Block filling of the stopped cluster

For a base `B` with `N = B.card` vertices, `H ≥ 1`, and `T = 2 N H` particles, the stopped cluster
`stoppedCluster B H ω T` contains the layer `R_H` except on an event of probability at most
`N H e^{-H/8}`.  The bound persists at every time `M ≥ 2 N H`, by the monotonicity of the stopped
cluster in time.
-/

namespace IdlaCyl.Reduction

open MeasureTheory
open scoped ENNReal

variable (B : Base)

/-- A single site of the block `1 ≤ ζ.2 ≤ H` is missed by the stopped cluster at height `H` after
`2 N H` steps with probability at most `e^{-H/8}`. -/
theorem site_not_mem_stoppedCluster_block (H : ℕ) (hH : 1 ≤ H) (ζ : Site B)
    (hζ1 : 1 ≤ ζ.2) (hζH : ζ.2 ≤ (H : ℤ)) :
    idlaMeasure B {ω : TrajSeq B | ζ ∉ stoppedCluster B (H : ℤ) ω (2 * B.card * H)}
      ≤ ENNReal.ofReal (Real.exp (-(H : ℝ) / 8)) := by
  have hN0 : 0 < B.card := lt_of_lt_of_le (by norm_num) B.nontrivial
  have hNR : (0 : ℝ) < B.card := by exact_mod_cast hN0
  have hHR : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hT : 1 ≤ 2 * B.card * H := Nat.mul_pos (Nat.mul_pos two_pos hN0) (by omega)
  have hTR : ((2 * B.card * H : ℕ) : ℝ) = 2 * (B.card : ℝ) * H := by push_cast; ring
  have hRHS : ((2 * B.card * H : ℕ) : ℝ) / (B.card : ℝ) = 2 * H := by
    rw [hTR]
    field_simp
  have hℓ : (H : ℝ) ≤ ((2 * B.card * H : ℕ) : ℝ) / (2 * (B.card : ℝ)) := by
    rw [hTR]
    field_simp
    linarith
  have hζR : ((ζ.2 : ℤ) : ℝ) ≤ (H : ℝ) := by exact_mod_cast hζH
  have hℓh : ((ζ.2 : ℤ) : ℝ) + (H : ℝ) ≤ ((2 * B.card * H : ℕ) : ℝ) / (B.card : ℝ) := by
    rw [hRHS]
    linarith
  have hsite := measure_not_mem_stoppedCluster_le_exp B ζ.2 hζ1 ζ rfl (2 * B.card * H) hT
    (H : ℝ) (by positivity) hℓ hℓh
  have hexp : (H : ℝ) ^ 2 * (B.card : ℝ) / (4 * ((2 * B.card * H : ℕ) : ℝ)) = H / 8 := by
    rw [hTR]
    field_simp
    ring
  rw [hexp, ← neg_div] at hsite
  refine (measure_mono_ae ?_).trans hsite
  filter_upwards [idlaMeasure_ae_stopped_hyp B] with ω hω
  intro hnot hmem
  exact hnot (stoppedCluster_mono_height B hζH ω
    (fun t => hω.2.2.1 t (H : ℤ) (by exact_mod_cast hH)) (2 * B.card * H) hmem)

/-- **Block filling** (`tex:1227-1251`).  With `T = 2 N H` particles, the stopped cluster at
height `H` contains the layer `R_H` except on an event of probability at most `N H e^{-H/8}`. -/
theorem stopped_block_fill (H : ℕ) (hH : 1 ≤ H) :
    idlaMeasure B {ω : TrajSeq B | ¬ R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) ω (2 * B.card * H)}
      ≤ ENNReal.ofReal ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8)) := by
  classical
  let S : Finset (Site B) := (Finset.univ : Finset B.V) ×ˢ Finset.Icc (1 : ℤ) (H : ℤ)
  have hS : S.card = B.card * H := by
    simp [S, Finset.card_product, Int.card_Icc, IdlaCyl.Base.card]
  calc idlaMeasure B {ω : TrajSeq B | ¬ R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) ω (2 * B.card * H)}
      ≤ idlaMeasure B (⋃ ζ ∈ S,
          {ω : TrajSeq B | ζ ∉ stoppedCluster B (H : ℤ) ω (2 * B.card * H)}) := by
        refine measure_mono fun ω hω => ?_
        have hω' : ¬ R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) ω (2 * B.card * H) := hω
        obtain ⟨p, hpR, hpA⟩ := Set.not_subset.mp hω'
        have hpH : p.2 ≤ (H : ℤ) := by exact_mod_cast mem_R.mp hpR
        have hp1 : 1 ≤ p.2 := by
          by_contra hlt
          exact hpA (subset_R_zero_stoppedCluster B (H : ℤ) ω (2 * B.card * H)
            (mem_R.mpr (by exact_mod_cast (show p.2 ≤ 0 by omega))))
        have hpS : p ∈ S := Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_Icc.mpr ⟨hp1, hpH⟩⟩
        exact Set.mem_iUnion₂.mpr ⟨p, hpS, hpA⟩
    _ ≤ ∑ ζ ∈ S, idlaMeasure B {ω : TrajSeq B | ζ ∉ stoppedCluster B (H : ℤ) ω (2 * B.card * H)} :=
        measure_biUnion_finset_le S _
    _ ≤ ∑ _ζ ∈ S, ENNReal.ofReal (Real.exp (-(H : ℝ) / 8)) := by
        refine Finset.sum_le_sum fun ζ hζ => ?_
        have hζI := Finset.mem_Icc.mp (Finset.mem_product.mp hζ).2
        exact site_not_mem_stoppedCluster_block B H hH ζ hζI.1 hζI.2
    _ = ENNReal.ofReal ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8)) := by
        rw [Finset.sum_const, hS, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        push_cast
        ring

/-- **Block filling at every later time** (`tex:1227-1251`).  For `M ≥ 2 N H` the same bound holds
at time `M`, since the stopped cluster is nondecreasing in time. -/
theorem stopped_block_fill_ge (H : ℕ) (hH : 1 ≤ H) (M : ℕ) (hM : 2 * B.card * H ≤ M) :
    idlaMeasure B {ω : TrajSeq B | ¬ R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) ω M}
      ≤ ENNReal.ofReal ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8)) :=
  (measure_mono fun ω (hω : ¬ R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) ω M)
      (hsub : R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) ω (2 * B.card * H)) =>
    hω (Set.Subset.trans hsub (stoppedCluster_monotone B (H : ℤ) ω hM))).trans
    (stopped_block_fill B H hH)

end IdlaCyl.Reduction
