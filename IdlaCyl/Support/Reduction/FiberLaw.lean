module

/-
Explicit conditioning on countably many measurable cluster fibers.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.
Zero-mass fibers use the original probability law. Every inverse is used
only after its positive finite mass is established.
-/
public import IdlaCyl.Support.Reduction.CouplingBasic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

@[expose] public section

attribute [local instance] Classical.propDecidable

namespace IdlaCyl.Reduction

open MeasureTheory
open scoped ENNReal

/-- A countable measurable bind is the explicit sum of its atomic input mixtures. -/
theorem countable_bind_eq_sum {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α] (μ : Measure α) (κ : α → Measure β) :
    μ.bind κ = Measure.sum (fun a => μ {a} • κ a) := by
  calc
    _ = (Measure.sum (fun a => μ {a} • Measure.dirac a)).bind κ := by
      rw [Measure.sum_smul_dirac]
    _ = Measure.sum (fun a => (μ {a} • Measure.dirac a).bind κ) :=
      Measure.bind_sum _ _ (measurable_of_countable κ).aemeasurable
    _ = _ := by
      simp only [Measure.bind_smul, Measure.dirac_bind (measurable_of_countable κ)]

/-- Normalize the actual fiber when it has positive mass, and use μ at zero atoms. -/
noncomputable def fiberLaw {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    (μ : Measure Ω) (f : Ω → C) (c : C) : Measure Ω :=
  if μ (f ⁻¹' {c}) = 0 then μ else (μ (f ⁻¹' {c}))⁻¹ • μ.restrict (f ⁻¹' {c})

instance fiberLaw_isProbability {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → C) (c : C) :
    IsProbabilityMeasure (fiberLaw μ f c) := by
  unfold fiberLaw
  split_ifs with hc
  · infer_instance
  · constructor
    rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      smul_eq_mul, ENNReal.inv_mul_cancel hc (measure_ne_top _ _)]

/-- A positive-mass fiber conditional is concentrated on that same fiber. -/
theorem fiberLaw_ae {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    [MeasurableSingletonClass C] (μ : Measure Ω) (f : Ω → C) (hf : Measurable f)
    (c : C) (hc : μ (f ⁻¹' {c}) ≠ 0) : ∀ᵐ ω ∂fiberLaw μ f c, f ω = c := by
  rw [ae_iff, fiberLaw, if_neg hc, Measure.smul_apply]
  change (μ (f ⁻¹' {c}))⁻¹ • (μ.restrict (f ⁻¹' {c})) (f ⁻¹' {c})ᶜ = 0
  rw [Measure.restrict_apply (hf (measurableSet_singleton c)).compl,
    Set.compl_inter_self, measure_empty, smul_zero]

/-- A conditional over a positive-mass fiber maps to the specified atom. -/
theorem fiberLaw_map {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    [MeasurableSingletonClass C] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → C) (hf : Measurable f) (c : C) (hc : μ (f ⁻¹' {c}) ≠ 0) :
    (fiberLaw μ f c).map f = Measure.dirac c := by
  rw [Measure.map_congr (fiberLaw_ae μ f hf c hc), Measure.map_const, measure_univ, one_smul]

/-- Weighting by the actual fiber mass recovers its unnormalized restriction, also at zero atoms. -/
theorem fiberLaw_weight {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → C) (c : C) :
    μ (f ⁻¹' {c}) • fiberLaw μ f c = μ.restrict (f ⁻¹' {c}) := by
  by_cases hc : μ (f ⁻¹' {c}) = 0
  · rw [hc, zero_smul, (Measure.restrict_eq_zero.mpr hc)]
  · rw [fiberLaw, if_neg hc, smul_smul,
      ENNReal.mul_inv_cancel hc (measure_ne_top _ _), one_smul]

/-- The countable fibers form a measurable partition of the entire original probability space. -/
theorem sum_restrict_fibers {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    [Countable C] [MeasurableSingletonClass C] (μ : Measure Ω) (f : Ω → C)
    (hf : Measurable f) : Measure.sum (fun c => μ.restrict (f ⁻¹' {c})) = μ := by
  have hd : Pairwise (fun c d : C => Disjoint (f ⁻¹' {c}) (f ⁻¹' {d})) := by
    intro c d hcd
    apply Set.disjoint_left.mpr
    intro ω hc hd
    exact hcd (hc.symm.trans hd)
  have hu : (⋃ c : C, f ⁻¹' {c}) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, exists_eq',
      Set.mem_univ]
  have h := Measure.restrict_iUnion (μ := μ) hd (fun c => hf (measurableSet_singleton c))
  rw [hu, Measure.restrict_univ] at h
  exact h.symm

/-- Mixing the explicit countable fiber conditionals restores the WHOLE driving law. -/
theorem fiberLaw_reconstruct {Ω C : Type*} [MeasurableSpace Ω] [MeasurableSpace C]
    [Countable C] [MeasurableSingletonClass C] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → C) (hf : Measurable f) :
    (μ.map f).bind (fiberLaw μ f) = μ := by
  rw [countable_bind_eq_sum]
  have hw : (fun c => (μ.map f) {c} • fiberLaw μ f c) =
      (fun c => μ.restrict (f ⁻¹' {c})) := by
    funext c
    rw [Measure.map_apply hf (measurableSet_singleton c), fiberLaw_weight]
  rw [hw]
  exact sum_restrict_fibers μ f hf

end IdlaCyl.Reduction
