import IdlaCyl.Support.PrInnerInclusion

/-!
# The slab union bound of `pr:inner`

This module proves the union-bound step of the second inequality of `pr:inner`
(`paper/idla-cylinder-gff.tex:1176-1179`) for the canonical driver `idlaMeasure` and the actual
stopped process `stoppedCluster`, and its composition with the height reduction
`pr_inner_ineq_reduction` (`tex:1182-1183`).

The finite slab `V_N × {1, …, h}` is the part of `R_h ∖ R_0` that can be missing from `Ā_h(T)`:
the stopped cluster always contains `R_0`, so a site of `R_h` that is missing has height in
`[1, h]`. The union bound is subadditivity of the outer measure (`measure_biUnion_finset_le`). It
uses no hypothesis on `h`, `T` or the driver, and no measurability.

This module does not prove the per-site estimate `P(ζ ∉ Ā_h(T)) ≤ e^{-(ν+4) L_T}`
(`tex:1227-1251`). That estimate is the remaining step of the second inequality of `tex:1164`.
-/

namespace IdlaCyl.PrInnerTail

open MeasureTheory

/-- The finite slab `V_N × {1, …, h}` of `R_h ∖ R_0` (`tex:1176-1179`). -/
noncomputable def slab (B : Base) (h : ℤ) : Finset (Site B) :=
  (Finset.univ : Finset B.V) ×ˢ Finset.Icc (1 : ℤ) h

/-- A site lies in the slab exactly when its height lies in `[1, h]`. -/
theorem mem_slab (B : Base) (h : ℤ) (ζ : Site B) :
    ζ ∈ slab B h ↔ 1 ≤ ζ.2 ∧ ζ.2 ≤ h := by
  simp [slab]

/-- The stopped cluster contains `R_0` at every time: it starts equal to `R_0` and only grows by
the recursion of `stoppedCluster` (`tex:1147-1151`). -/
theorem R_zero_subset_stoppedCluster (B : Base) (h : ℤ) (ω : TrajSeq B) (T : ℕ) :
    R B 0 ⊆ stoppedCluster B h ω T := by
  induction T with
  | zero => exact subset_rfl
  | succ n ih =>
    rw [show stoppedCluster B h ω (n + 1)
        = stoppedCluster B h ω n ∪
          {exitSite' B (stoppedCluster B h ω n ∩ R B ((h : ℝ) - 1)) (ω n)} from rfl]
    exact ih.trans Set.subset_union_left

/-- The union bound over the slab (`tex:1176-1179`). If `Ā_h(T)` misses a site of `R_h`, then it
misses a site of the slab, because every site of `R_0` is in `Ā_h(T)`. So the probability that
`Ā_h(T)` misses `R_h` is at most the sum over the slab of the probabilities that it misses each
site. -/
theorem pr_inner_slab_union_le (B : Base) (h : ℤ) (T : ℕ) :
    idlaMeasure B {ω | ¬ R B (h : ℝ) ⊆ stoppedCluster B h ω T}
      ≤ ∑ ζ ∈ slab B h, idlaMeasure B {ω | ζ ∉ stoppedCluster B h ω T} := by
  have hsub : {ω | ¬ R B (h : ℝ) ⊆ stoppedCluster B h ω T}
      ⊆ ⋃ ζ ∈ slab B h, {ω | ζ ∉ stoppedCluster B h ω T} := by
    intro ω hω
    have hω' : ¬ R B (h : ℝ) ⊆ stoppedCluster B h ω T := hω
    obtain ⟨p, hpR, hpA⟩ := Set.not_subset.mp hω'
    have hph : p.2 ≤ h := by
      have hle : (p.2 : ℝ) ≤ (h : ℝ) := hpR
      exact_mod_cast hle
    rcases le_or_gt 1 p.2 with h1 | h1
    · exact Set.mem_iUnion₂.mpr ⟨p, (mem_slab B h p).mpr ⟨h1, hph⟩, hpA⟩
    · have hp0 : p ∈ R B 0 := by
        show (p.2 : ℝ) ≤ 0
        exact_mod_cast (show p.2 ≤ 0 by omega)
      exact absurd (R_zero_subset_stoppedCluster B h ω T hp0) hpA
  exact (measure_mono hsub).trans (measure_biUnion_finset_le _ _)

/-- The union bound composed with the height reduction (`tex:1182-1183`). Each slab site `ζ` is
replaced by its own stopping height `ζ₂`, which lies in `[1, h]`, so
`P(ζ ∉ Ā_h(T)) ≤ P(ζ ∉ Ā_{ζ₂}(T))` by `pr_inner_ineq_reduction`. -/
theorem pr_inner_slab_reduced_le (B : Base) (h : ℤ) (T : ℕ) :
    idlaMeasure B {ω | ¬ R B (h : ℝ) ⊆ stoppedCluster B h ω T}
      ≤ ∑ ζ ∈ slab B h, idlaMeasure B {ω | ζ ∉ stoppedCluster B ζ.2 ω T} := by
  refine (pr_inner_slab_union_le B h T).trans (Finset.sum_le_sum fun ζ hζ => ?_)
  obtain ⟨h1, h2⟩ := (mem_slab B h ζ).mp hζ
  exact pr_inner_ineq_reduction B ζ h1 h2 T

end IdlaCyl.PrInnerTail
