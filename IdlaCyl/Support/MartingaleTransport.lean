module

/-
Martingales pulled back along a measure-preserving map.

For `π : Ω' → Ω` with `MeasurePreserving π μ' μ`, the filtration `i ↦ π⁻¹ ℱ_i` on `Ω'`
makes `f i ∘ π` a martingale whenever `f` is a martingale for `ℱ` under `μ`.
The conditional expectation transports along `π` because `π` pushes `μ'` forward to `μ`,
and every `comap π m`-measurable set has the form `π⁻¹ A` with `A` `m`-measurable.

This is the transport step for product-space constructions: when several processes are
realised on one product space and each coordinate map is measure preserving, a martingale
property on the factor space holds on the product space.
-/
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Trim
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.Filtration

@[expose] public section

open MeasureTheory

namespace IdlaCyl

/-- The filtration `i ↦ π⁻¹ ℱ_i` on `Ω'`. -/
def filtrationComap {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} [mΩ' : MeasurableSpace Ω'] {π : Ω' → Ω}
    (hπ : Measurable π) (ℱ : Filtration ℕ mΩ) : Filtration ℕ mΩ' where
  seq i := MeasurableSpace.comap π (ℱ i)
  mono' _ _ hij := MeasurableSpace.comap_mono (ℱ.mono hij)
  le' i := (MeasurableSpace.comap_mono (ℱ.le i)).trans hπ.comap_le

/-- The `i`-th σ-algebra of the pulled-back filtration is `π⁻¹ ℱ_i`. -/
theorem filtrationComap_apply {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace Ω']
    {π : Ω' → Ω} (hπ : Measurable π) (ℱ : Filtration ℕ mΩ) (i : ℕ) :
    filtrationComap hπ ℱ i = MeasurableSpace.comap π (ℱ i) :=
  rfl

/-- Conditional expectation commutes with a measure-preserving map: conditioning `g ∘ π` on
`π⁻¹ m` gives `μ[g | m] ∘ π`, almost everywhere for `μ'`. -/
theorem condExp_comp_measurePreserving {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω}
    [MeasurableSpace Ω'] {μ : Measure Ω} {μ' : Measure Ω'} [IsFiniteMeasure μ]
    {π : Ω' → Ω} (hπ : MeasurePreserving π μ' μ)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {g : Ω → ℝ} (hg : Integrable g μ) :
    μ'[g ∘ π | MeasurableSpace.comap π m] =ᵐ[μ'] μ[g | m] ∘ π := by
  letI : MeasurableSpace Ω := mΩ
  have hfin : μ' Set.univ < ⊤ := by
    have h := hπ.measure_preimage MeasurableSet.univ.nullMeasurableSet
    rw [Set.preimage_univ] at h
    rw [h]
    exact measure_lt_top μ Set.univ
  haveI : IsFiniteMeasure μ' := ⟨hfin⟩
  have hπm : MeasurableSpace.comap π m ≤ ‹MeasurableSpace Ω'› :=
    (MeasurableSpace.comap_mono hm).trans hπ.measurable.comap_le
  haveI : SigmaFinite (μ'.trim hπm) := inferInstance
  have hcm : Integrable (μ[g | m] ∘ π) μ' := hπ.integrable_comp_of_integrable integrable_condExp
  have hgm : AEStronglyMeasurable[MeasurableSpace.comap π m] (μ[g | m] ∘ π) μ' :=
    ((stronglyMeasurable_condExp (μ := μ) (f := g) (m := m)).comp_measurable
      (comap_measurable π)).aestronglyMeasurable
  have hset : ∀ s : Set Ω', MeasurableSet[MeasurableSpace.comap π m] s →
      ∫ x in s, (μ[g | m] ∘ π) x ∂μ' = ∫ x in s, (g ∘ π) x ∂μ' := by
    intro s hs
    obtain ⟨A, hA, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have hA' : MeasurableSet A := hm A hA
    have key : ∀ h : Ω → ℝ, AEStronglyMeasurable h μ →
        ∫ y in A, h y ∂μ = ∫ x in π ⁻¹' A, h (π x) ∂μ' := by
      intro h hh
      have h' := setIntegral_map (μ := μ') (g := π) (f := h) hA'
        (by rw [hπ.map_eq]; exact hh) hπ.measurable.aemeasurable
      rw [hπ.map_eq] at h'
      exact h'
    have hcond : AEStronglyMeasurable (μ[g | m]) μ :=
      (stronglyMeasurable_condExp.mono hm).aestronglyMeasurable
    have h1 := key (μ[g | m]) hcond
    have h2 := key g hg.aestronglyMeasurable
    have h3 := setIntegral_condExp hm hg hA
    exact h1.symm.trans (h3.trans h2)
  have hcond : μ[g | m] ∘ π =ᵐ[μ'] μ'[g ∘ π | MeasurableSpace.comap π m] :=
    ae_eq_condExp_of_forall_setIntegral_eq hπm (hπ.integrable_comp_of_integrable hg)
      (fun s _ _ => hcm.integrableOn) (fun s hs _ => hset s hs) hgm
  exact hcond.symm

/-- A martingale composed with a measure-preserving map is a martingale for the pulled-back
filtration. -/
theorem martingale_comp_measurePreserving {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω}
    [MeasurableSpace Ω'] {μ : Measure Ω} {μ' : Measure Ω'} [IsFiniteMeasure μ]
    {π : Ω' → Ω} (hπ : MeasurePreserving π μ' μ)
    {ℱ : Filtration ℕ mΩ} {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ μ) :
    Martingale (fun i => f i ∘ π) (filtrationComap hπ.measurable ℱ) μ' := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · exact (hf.1 i).comp_measurable (comap_measurable π)
  · show μ'[f j ∘ π | MeasurableSpace.comap π (ℱ i)] =ᵐ[μ'] f i ∘ π
    have hae : ∀ᵐ x ∂μ, μ[f j | ℱ i] x = f i x := hf.2 i j hij
    have hpull : μ[f j | ℱ i] ∘ π =ᵐ[μ'] f i ∘ π := hπ.quasiMeasurePreserving.ae hae
    by_cases hint : Integrable (f j) μ
    · exact (condExp_comp_measurePreserving hπ (ℱ.le i) hint).trans hpull
    · have h0 : μ[f j | ℱ i] = 0 := condExp_of_not_integrable hint
      have hnot : ¬Integrable (f j ∘ π) μ' := by
        intro h
        apply hint
        have hmeas : AEStronglyMeasurable (f j) μ :=
          ((hf.1 j).mono (ℱ.le j)).aestronglyMeasurable
        exact (hπ.integrable_comp hmeas).mp h
      rw [condExp_of_not_integrable hnot]
      rw [h0] at hpull
      filter_upwards [hpull] with x hx
      exact hx

end IdlaCyl
