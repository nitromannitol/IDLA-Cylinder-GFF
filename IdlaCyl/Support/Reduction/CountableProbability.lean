module

/-
Probability instances for the literal countable kernels in the reduction.
Source: paper/idla-cylinder-gff.tex, tex:246-265,1440-1453.
-/
public import IdlaCyl.Support.Reduction.Laws

@[expose] public section

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Binding a measurable countable probability kernel preserves total mass one. -/
instance countableBind_isProbability {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : α → Measure β) [∀ a, IsProbabilityMeasure (κ a)] : IsProbabilityMeasure (μ.bind κ) :=
  isProbabilityMeasure_bind (measurable_of_countable κ).aemeasurable
    (Filter.Eventually.of_forall (fun _ => inferInstance))

/-- Every flat finite-cluster law is a probability measure. -/
instance flatClusterLaw_isProbability (B : Base) (t : ℕ) :
    IsProbabilityMeasure (flatClusterLaw B t) :=
  layerGrowthLaw_isProbability B (resumeEmpty B) 0 t

end IdlaCyl.Reduction
