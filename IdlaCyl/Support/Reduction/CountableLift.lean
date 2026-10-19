/-
Lift a countable-state coupling by explicit normalized fiber laws.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.
Both original laws are restored on their full measurable spaces, and the
entire coupled output law is preserved, not just one selected event.
-/
import IdlaCyl.Support.Reduction.FiberLaw

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Mix independent fiber conditionals against the supplied joint output law. -/
noncomputable def fiberLift {Ω Ω' C D : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace C] [MeasurableSpace D] (μ : Measure Ω) (ν : Measure Ω')
    (f : Ω → C) (g : Ω' → D) (ρ : Measure (C × D)) : Measure (Ω × Ω') :=
  ρ.bind (fun cd => (fiberLaw μ f cd.1).prod (fiberLaw ν g cd.2))

/-- The first full marginal of the explicit fiber lift is the original law. -/
theorem fiberLift_fst {Ω Ω' C D : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace C] [MeasurableSpace D] [Countable C] [Countable D]
    [MeasurableSingletonClass C] [MeasurableSingletonClass D]
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → C) (g : Ω' → D) (hf : Measurable f) (ρ : Measure (C × D))
    (hρ : ρ.map Prod.fst = μ.map f) : (fiberLift μ ν f g ρ).map Prod.fst = μ := by
  rw [fiberLift, resume_map_bind _ _ _ (measurable_of_countable _) measurable_fst]
  simp_rw [Measure.map_fst_prod, measure_univ, one_smul]
  rw [← resume_bind_map _ _ _ measurable_fst (measurable_of_countable _), hρ,
    fiberLaw_reconstruct μ f hf]

/-- The second full marginal of the explicit fiber lift is the original law. -/
theorem fiberLift_snd {Ω Ω' C D : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace C] [MeasurableSpace D] [Countable C] [Countable D]
    [MeasurableSingletonClass C] [MeasurableSingletonClass D]
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → C) (g : Ω' → D) (hg : Measurable g) (ρ : Measure (C × D))
    (hρ : ρ.map Prod.snd = ν.map g) : (fiberLift μ ν f g ρ).map Prod.snd = ν := by
  rw [fiberLift, resume_map_bind _ _ _ (measurable_of_countable _) measurable_snd]
  simp_rw [Measure.map_snd_prod, measure_univ, one_smul]
  rw [← resume_bind_map _ _ _ measurable_snd (measurable_of_countable _), hρ,
    fiberLaw_reconstruct ν g hg]

/-- The lift preserves the supplied WHOLE joint output law, including all positive atoms. -/
theorem fiberLift_map {Ω Ω' C D : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace C] [MeasurableSpace D] [Countable C] [Countable D]
    [MeasurableSingletonClass C] [MeasurableSingletonClass D]
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → C) (g : Ω' → D) (hf : Measurable f) (hg : Measurable g)
    (ρ : Measure (C × D)) (hρf : ρ.map Prod.fst = μ.map f)
    (hρg : ρ.map Prod.snd = ν.map g) :
    (fiberLift μ ν f g ρ).map (Prod.map f g) = ρ := by
  rw [fiberLift, resume_map_bind _ _ _ (measurable_of_countable _) (hf.prodMap hg),
    countable_bind_eq_sum]
  conv_rhs => rw [← Measure.sum_smul_dirac ρ]
  congr 1
  funext cd
  by_cases hp : ρ {cd} = 0
  · rw [hp, zero_smul, zero_smul]
  · have hfirst : ρ {cd} ≤ μ (f ⁻¹' {cd.1}) := by
      rw [← Measure.map_apply hf (measurableSet_singleton cd.1), ← hρf,
        Measure.map_apply measurable_fst (measurableSet_singleton cd.1)]
      exact measure_mono (Set.singleton_subset_iff.mpr rfl)
    have hsecond : ρ {cd} ≤ ν (g ⁻¹' {cd.2}) := by
      rw [← Measure.map_apply hg (measurableSet_singleton cd.2), ← hρg,
        Measure.map_apply measurable_snd (measurableSet_singleton cd.2)]
      exact measure_mono (Set.singleton_subset_iff.mpr rfl)
    have hc : μ (f ⁻¹' {cd.1}) ≠ 0 := by
      intro hzero
      exact hp (le_zero_iff.mp (hfirst.trans_eq hzero))
    have hd : ν (g ⁻¹' {cd.2}) ≠ 0 := by
      intro hzero
      exact hp (le_zero_iff.mp (hsecond.trans_eq hzero))
    rw [← Measure.map_prod_map _ _ hf hg, fiberLaw_map μ f hf cd.1 hc,
      fiberLaw_map ν g hg cd.2 hd, Measure.dirac_prod_dirac, Prod.eta]

/-- A countable joint output distribution lifts to a coupling of the entire input spaces. -/
theorem countable_coupling_lift {Ω Ω' C D : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace C] [MeasurableSpace D]
    [Countable C] [Countable D] [MeasurableSingletonClass C] [MeasurableSingletonClass D]
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → C) (g : Ω' → D) (hf : Measurable f) (hg : Measurable g)
    (ρ : Measure (C × D)) (hρf : ρ.map Prod.fst = μ.map f)
    (hρg : ρ.map Prod.snd = ν.map g) :
    ∃ η : Measure (Ω × Ω'), η.map Prod.fst = μ ∧ η.map Prod.snd = ν ∧
      η.map (Prod.map f g) = ρ :=
  ⟨fiberLift μ ν f g ρ, fiberLift_fst μ ν f g hf ρ hρf,
    fiberLift_snd μ ν f g hg ρ hρg, fiberLift_map μ ν f g hf hg ρ hρf hρg⟩

end IdlaCyl.Reduction
