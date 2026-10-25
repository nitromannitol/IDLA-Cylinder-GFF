module

/-
Uniform starts on a layer mixed over the start vector, and the finite-prefix restriction.
Source: paper/idla-cylinder-gff.tex, tex:265, tex:1330-1331, tex:1402.
The height-zero disintegration is `idlaMeasure_eq_bind_prescribed` in `CanonicalIdla`.
-/
public import IdlaCyl.Support.CanonicalIdla
public import IdlaCyl.Support.Reduction.Laws

@[expose] public section

namespace IdlaCyl.Reduction

open MeasureTheory ProbabilityTheory

/-- Pushing a measure forward and then binding a kernel is the same as binding the kernel
along the map. -/
theorem bind_map_eq_bind_comp {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass β] (μ : Measure α) {f : α → β}
    {κ : β → Measure γ} (hf : Measurable f) (hκ : Measurable κ) :
    (μ.map f).bind κ = μ.bind (fun a => κ (f a)) := by
  have hd : Measurable (fun x => Measure.dirac (f x)) := Measure.measurable_dirac.comp hf
  rw [← Measure.bind_dirac_eq_map μ hf, Measure.bind_bind hd.aemeasurable hκ.aemeasurable]
  refine Measure.bind_congr_right (Filter.Eventually.of_forall fun a => ?_)
  exact Measure.dirac_bind hκ (f a)

/-- Mapping a mixture forward is the mixture of the mapped kernels. -/
theorem map_bind_eq_bind_map {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ] (μ : Measure α) {κ : α → Measure β}
    {g : β → γ} (hκ : Measurable κ) (hg : Measurable g) :
    (μ.bind κ).map g = μ.bind (fun a => (κ a).map g) := by
  have hd : Measurable (fun y => Measure.dirac (g y)) := Measure.measurable_dirac.comp hg
  rw [← Measure.bind_dirac_eq_map (μ.bind κ) hg, Measure.bind_bind hκ.aemeasurable hd.aemeasurable]
  refine Measure.bind_congr_right (Filter.Eventually.of_forall fun a => ?_)
  exact Measure.bind_dirac_eq_map (κ a) hg

/-- The independent walks released uniformly on layer `L` are the mixture, over independent
uniform starting sites on layer `L`, of the prescribed walk laws. This is the height-`L`
form of `idlaMeasure_eq_bind_prescribed`. -/
theorem layerDrivingLaw_eq_bind_prescribed (B : Base) (L : ℤ) :
    Measure.infinitePi (fun _ : ℕ => walkLawUniformAt B L)
      = (Measure.infinitePi fun _ : ℕ => layerLawAt B L).bind (prescribedMeasure B) := by
  symm
  apply Measure.eq_infinitePi
  intro s t ht
  have hmeas_pi : MeasurableSet (Set.pi s t) :=
    MeasurableSet.pi s.countable_toSet fun i _ => ht i
  rw [Measure.bind_apply hmeas_pi (measurable_prescribedMeasure B).aemeasurable]
  have hpt : ∀ start : ℕ → Site B,
      prescribedMeasure B start (Set.pi s t) = ∏ i ∈ s, walkPathLaw B (start i) (t i) :=
    fun start => Measure.infinitePi_pi (fun j => walkPathLaw B (start j)) (fun i _ => ht i)
  simp_rw [hpt]
  have hIndep : iIndepFun (fun i (start : ℕ → Site B) => walkPathLaw B (start i) (t i))
      (Measure.infinitePi fun _ : ℕ => layerLawAt B L) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => layerLawAt B L)
      (X := fun i (x : Site B) => walkPathLaw B x (t i))
      (fun i => measurable_of_countable _)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun s
    (fun i (start : ℕ → Site B) => walkPathLaw B (start i) (t i)) hIndep
    (fun i => (measurable_of_countable fun x : Site B => walkPathLaw B x (t i)).comp
      (measurable_pi_apply i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [(measurePreserving_eval_infinitePi (fun _ : ℕ => layerLawAt B L) i).lintegral_comp
      (measurable_of_countable fun x : Site B => walkPathLaw B x (t i)),
    ← Measure.bind_apply (ht i) (measurable_of_countable (walkPathLaw B)).aemeasurable]
  exact congrArg (fun μ => μ (t i)) (walkLawUniformAt_eq_bind B L).symm

/-- Restricting the infinite product of layer-`L` starting laws to its first `T` coordinates
gives the finite product of the same laws on `Fin T`. -/
theorem infinitePi_map_take_eq_pi (B : Base) (L : ℤ) (T : ℕ) :
    (Measure.infinitePi fun _ : ℕ => layerLawAt B L).map
        (fun a : ℕ → Site B => fun i : Fin T => a i)
      = Measure.pi fun _ : Fin T => layerLawAt B L := by
  let e : Fin T ≃ ↥(Finset.range T) :=
    Fin.equivSubtype.trans (Equiv.subtypeEquivRight fun x => Finset.mem_range.symm)
  have hpi := measurePreserving_piCongrLeft (α := fun _ : Fin T => Site B)
    (fun _ : Fin T => layerLawAt B L) e.symm
  have hfun : (fun a : ℕ → Site B => fun i : Fin T => a i)
      = (MeasurableEquiv.piCongrLeft (fun _ : Fin T => Site B) e.symm) ∘
          (Finset.range T).restrict := by
    funext a i
    rfl
  rw [hfun, ← Measure.map_map (MeasurableEquiv.piCongrLeft (fun _ : Fin T => Site B) e.symm).measurable
    (Finset.measurable_restrict _),
    Measure.infinitePi_map_restrict]
  exact hpi.map_eq

/-- **The uniform-start mixture identity.** Mixing the finite prescribed-start release over
independent uniform starts on layer `L` gives the growth law of `T` releases on that layer. -/
theorem uniform_start_mixture (B : Base) (F : ResumeFinite B) (L : ℤ) (T : ℕ) :
    (Measure.pi (fun _ : Fin T => layerLawAt B L)).bind
        (fun s => resumeRun B F (List.ofFn s)) = layerGrowthLaw B F L T := by
  have hres : Measurable (fun a : ℕ → Site B => fun i : Fin T => a i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hkappa : Measurable (fun s : Fin T → Site B => resumeRun B F (List.ofFn s)) :=
    measurable_of_countable _
  unfold layerGrowthLaw layerDrivingLaw
  rw [layerDrivingLaw_eq_bind_prescribed B L,
    map_bind_eq_bind_map _ (measurable_prescribedMeasure B) (measurable_resumeGrow B F T)]
  simp only [prescribedMeasure_map_resumeGrow]
  rw [← infinitePi_map_take_eq_pi B L T]
  exact bind_map_eq_bind_comp _ hres hkappa

end IdlaCyl.Reduction
