/-
Countable mixtures of actual endpoint couplings preserve both marginals and the allowance.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.
Finite prescribed-start mixtures are special cases. No future success event
is used as a conditioning variable.
-/
import IdlaCyl.Support.Reduction.CouplingBasic

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Mix complete couplings, preserving their actual marginals on every branch. -/
theorem mix_cluster_couplings {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (B : Base) (σ : Measure S)
    [IsProbabilityMeasure σ] (P Q : S → Measure (ResumeFinite B))
    (k : ℕ) (ε : ℝ) (hc : ∀ s, ClusterCoupling B (P s) (Q s) k ε) :
    ClusterCoupling B (σ.bind P) (σ.bind Q) k ε := by
  let J := fun s => Classical.choose (hc s)
  have hJ (s : S) : (J s).map Prod.fst = P s ∧ (J s).map Prod.snd = Q s ∧
      J s (matchShift B k)ᶜ ≤ ENNReal.ofReal ε := Classical.choose_spec (hc s)
  refine ⟨σ.bind J, ?_, ?_, ?_⟩
  · rw [resume_map_bind _ _ _ (measurable_of_countable _) measurable_fst]
    exact congrArg (Measure.bind σ) (funext (fun s => (hJ s).1))
  · rw [resume_map_bind _ _ _ (measurable_of_countable _) measurable_snd]
    exact congrArg (Measure.bind σ) (funext (fun s => (hJ s).2.1))
  · rw [Measure.bind_apply (Set.to_countable _).measurableSet
      (measurable_of_countable J).aemeasurable]
    calc
      _ ≤ ∫⁻ _s, ENNReal.ofReal ε ∂σ := lintegral_mono (fun s => (hJ s).2.2)
      _ = _ := by rw [lintegral_const, measure_univ, mul_one]

end IdlaCyl.Reduction
