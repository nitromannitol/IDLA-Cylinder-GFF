/-
Countable mixtures with almost-sure eligible starting vectors.
Source: paper/idla-cylinder-gff.tex, tex:246-265,1440-1453;
Ineligible vectors have independent correct marginals.
-/
import IdlaCyl.Support.Reduction.MixCouplings

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Mix almost-everywhere available couplings, using independent correct fallback laws. -/
theorem mix_cluster_couplings_ae {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (B : Base) (σ : Measure S)
    [IsProbabilityMeasure σ] (P Q : S → Measure (ResumeFinite B))
    [∀ s, IsProbabilityMeasure (P s)] [∀ s, IsProbabilityMeasure (Q s)]
    (k : ℕ) (ε : ℝ) (hc : ∀ᵐ s ∂σ, ClusterCoupling B (P s) (Q s) k ε) :
    ClusterCoupling B (σ.bind P) (σ.bind Q) k ε := by
  classical
  let J := fun s => if h : ClusterCoupling B (P s) (Q s) k ε then
    Classical.choose h else (P s).prod (Q s)
  have hJ (s : S) : (J s).map Prod.fst = P s ∧ (J s).map Prod.snd = Q s := by
    dsimp only [J]
    split_ifs with h
    · exact ⟨(Classical.choose_spec h).1, (Classical.choose_spec h).2.1⟩
    · simp only [Measure.map_fst_prod, Measure.map_snd_prod, measure_univ, one_smul,
        and_self]
  have hbound : ∀ᵐ s ∂σ, J s (matchShift B k)ᶜ ≤ ENNReal.ofReal ε := by
    filter_upwards [hc] with s hs
    dsimp only [J]
    rw [dif_pos hs]
    exact (Classical.choose_spec hs).2.2
  refine ⟨σ.bind J, ?_, ?_, ?_⟩
  · rw [resume_map_bind _ _ _ (measurable_of_countable _) measurable_fst]
    exact congrArg (Measure.bind σ) (funext (fun s => (hJ s).1))
  · rw [resume_map_bind _ _ _ (measurable_of_countable _) measurable_snd]
    exact congrArg (Measure.bind σ) (funext (fun s => (hJ s).2))
  · rw [Measure.bind_apply (Set.to_countable _).measurableSet
      (measurable_of_countable J).aemeasurable]
    calc
      _ ≤ ∫⁻ _s, ENNReal.ofReal ε ∂σ := lintegral_mono_ae hbound
      _ = _ := by rw [lintegral_const, measure_univ, mul_one]

/-- The layer law assigns no mass to a different height. -/
theorem layerLawAt_ae_height (B : Base) (L : ℤ) :
    ∀ᵐ z ∂layerLawAt B L, z.2 = L := by
  rw [ae_iff, layerLawAt, Measure.sum_apply _ (Set.to_countable _).measurableSet]
  simp [Measure.smul_apply, Measure.dirac_apply', (Set.to_countable _).measurableSet]

/-- Every coordinate of the finite independent layer vector has its prescribed height. -/
theorem layer_vector_ae_height (B : Base) (L : ℤ) (T : ℕ) :
    ∀ᵐ s ∂Measure.pi (fun _ : Fin T => layerLawAt B L), ∀ i, (s i).2 = L := by
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval (fun _ : Fin T => layerLawAt B L) i).quasiMeasurePreserving.ae
    (layerLawAt_ae_height B L)

end IdlaCyl.Reduction
