/-
Upward translation of canonical finite cluster codes, retaining the entire seed.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.
-/
import IdlaCyl.Support.Reduction.CouplingBasic

attribute [local instance] Classical.propDecidable

namespace IdlaCyl.Reduction

open MeasureTheory

/-- The positive part of a shifted cluster includes all intervening full layers. -/
noncomputable def shiftFinite (B : Base) (L : ℕ) (F : ResumeFinite B) : ResumeFinite B :=
  ⟨(Finset.univ ×ˢ Finset.Icc (1 : ℤ) (L : ℤ)) ∪ F.val.image (outerShift B (L : ℤ)), by
    intro z hz hz0
    have hz0' : z.2 ≤ 0 := by exact_mod_cast (mem_R.mp hz0)
    rcases Finset.mem_union.mp hz with hz | hz
    · have hh := (Finset.mem_Icc.mp (Finset.mem_product.mp hz).2).1
      omega
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      have hw0 : 0 < w.2 := by
        have h := F.property w hw
        have h' : ¬ (w.2 : ℝ) ≤ 0 := h
        exact_mod_cast (lt_of_not_ge h')
      change w.2 + (L : ℤ) ≤ 0 at hz0'
      omega⟩

/-- Translation of the finite code represents translation of the whole occupied set. -/
theorem resumeSeed_shiftFinite (B : Base) (L : ℕ) (F : ResumeFinite B) :
    resumeSeed B (shiftFinite B L F) = outerShift B (L : ℤ) '' resumeSeed B F := by
  simp only [resumeSeed, Set.image_union, outerShift_image_R, zero_add]
  ext z
  simp only [shiftFinite, Finset.mem_coe, Finset.mem_union, Finset.mem_product,
    Finset.mem_univ, true_and, Finset.mem_Icc, Finset.mem_image, Set.mem_union,
    Set.mem_image, mem_R]
  have hzR : (z.2 : ℝ) ≤ (L : ℝ) ↔ z.2 ≤ (L : ℤ) := by exact_mod_cast Iff.rfl
  simp only [Int.cast_natCast] at *
  rw [hzR]
  constructor
  · rintro (hzero | hrect | hshift)
    · left
      have hz : z.2 ≤ 0 := by exact_mod_cast hzero
      omega
    · exact Or.inl hrect.2
    · exact Or.inr hshift
  · rintro (hrect | hshift)
    · by_cases hz : z.2 ≤ 0
      · left
        exact_mod_cast hz
      · exact Or.inr (Or.inl ⟨by omega, hrect⟩)
    · exact Or.inr (Or.inr hshift)

/-- The empty shifted seed is the literal full rectangle. -/
theorem resumeSeed_shiftFinite_empty (B : Base) (L : ℕ) :
    resumeSeed B (shiftFinite B L (resumeEmpty B)) = R B (L : ℝ) := by
  rw [resumeSeed_shiftFinite, resumeSeed_empty, outerShift_image_R, zero_add, Int.cast_natCast]

/-- Translating both cluster coordinates preserves equality and its failure allowance. -/
theorem clusterCoupling_shiftFinite (B : Base) (L : ℕ)
    (P Q : Measure (ResumeFinite B)) (ε : ℝ) (hc : ClusterCoupling B P Q 0 ε) :
    ClusterCoupling B (P.map (shiftFinite B L)) (Q.map (shiftFinite B L)) 0 ε := by
  obtain ⟨μ, hf, hs, he⟩ := hc
  let e := fun p : ResumeFinite B × ResumeFinite B =>
    (shiftFinite B L p.1, shiftFinite B L p.2)
  have hm : Measurable e := measurable_of_countable _
  refine ⟨μ.map e, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hm]
    exact (Measure.map_map (measurable_of_countable _) measurable_fst).symm.trans
      (congrArg (Measure.map (shiftFinite B L)) hf)
  · rw [Measure.map_map measurable_snd hm]
    exact (Measure.map_map (measurable_of_countable _) measurable_snd).symm.trans
      (congrArg (Measure.map (shiftFinite B L)) hs)
  · rw [Measure.map_apply hm (Set.to_countable _).measurableSet]
    apply (measure_mono (show e ⁻¹' (matchShift B 0)ᶜ ⊆ (matchShift B 0)ᶜ from ?_)).trans he
    intro p hp hgood
    apply hp
    rw [mem_matchShift_zero] at hgood ⊢
    exact congrArg (shiftFinite B L) hgood

end IdlaCyl.Reduction
