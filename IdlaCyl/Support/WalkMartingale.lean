module

/-
The cylinder walk evaluated at a discrete harmonic function is a martingale
(`tex:681-691`, the core of the optional-stopping identity `tex:696-698`).

`walkPathLaw B x` is Ionescu-Tulcea's law of the whole walk (`Support/Canonical.lean`),
so the one-step disintegration `Kernel.condExp_traj` and the one-step pushforward
`Kernel.map_traj_succ_self` compute the conditional expectation of `ψ (X (n+1))`
given the first `n + 1` coordinates: continuing from time `n` with an independent
step and averaging against the one-step law `cylMeasure B (X n)`.  Discrete
harmonicity `discreteHarmonic_iff_integral` then collapses that average to
`ψ (X n)`.  The one-step relation on the `ℕ`-indexed filtration upgrades to the
full martingale property by `martingale_nat`.

Integrability is not a hypothesis: the walk cannot move vertically more than one
level per step (`CylAdmissible.ver_step`), so at the finite time `n` it is
supported in the finite set `V_N × [x.2 - n, x.2 + n]` and `ψ (X n)` is a.e.
bounded.  `walkPathLaw_ae_start` and `walkPathLaw_ae_admissible` supply the two
ingredients.
-/
public import IdlaCyl.Support.StrongMarkov
public import IdlaCyl.Support.Admissible
public import IdlaCyl.Support.HarmonicIntegral
public import Mathlib.Probability.Martingale.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace IdlaCyl

variable (B : Base)

/-- **The walk filtration is the product filtration of the first coordinates.**
Both sides record the information in `X 0, …, X i`; the left one through the
`iSup` of the coordinate `σ`-algebras, the right one through `Filtration.piLE`
(equivalently, the comap of `Preorder.restrictLe i`). -/
theorem walkFiltration_eq_piLE (i : ℕ) :
    walkFiltration B i = Filtration.piLE (X := fun _ : ℕ => Site B) i := by
  change (⨆ k ≤ i, MeasurableSpace.comap (fun X : ℕ → Site B => X k) inferInstance)
    = MeasurableSpace.comap (Preorder.restrictLe i) MeasurableSpace.pi
  have h1 : MeasurableSpace.comap (Preorder.restrictLe i) MeasurableSpace.pi
      = ⨆ a : Set.Iic i, MeasurableSpace.comap (fun X : ℕ → Site B => X a) inferInstance :=
    MeasurableSpace.comap_process_pi (fun (a : Set.Iic i) (b : ℕ → Site B) => b a)
  rw [h1]
  exact iSup_subtype' (p := fun k : ℕ => k ≤ i)
    (f := fun k (_ : k ≤ i) => MeasurableSpace.comap (fun X : ℕ → Site B => X k) inferInstance)

/-- **`ψ (X n)` is integrable under `walkPathLaw B x`.**  The walk stays within
vertical distance `n` of its start, so at time `n` it lies in the finite set
`V_N × [x.2 - n, x.2 + n]` on which `ψ` is bounded. -/
theorem integrable_psi_walk (B : Base) (x : Site B) (ψ : Site B → ℝ) (n : ℕ) :
    Integrable (fun X : ℕ → Site B => ψ (X n)) (walkPathLaw B x) := by
  classical
  set F : Finset (Site B) :=
    (Finset.univ : Finset B.V) ×ˢ (Finset.Icc (x.2 - (n : ℤ)) (x.2 + (n : ℤ))) with hF
  refine Integrable.of_bound
    (((measurable_of_countable ψ).comp (measurable_pi_apply n)).aestronglyMeasurable)
    (∑ p ∈ F, ‖ψ p‖) ?_
  filter_upwards [walkPathLaw_ae_start B x, walkPathLaw_ae_admissible B x] with X hX0 hXadm
  have hbound : ∀ m : ℕ, x.2 - (m : ℤ) ≤ (X m).2 ∧ (X m).2 ≤ x.2 + (m : ℤ) := by
    intro m
    induction m with
    | zero => rw [hX0]; simp
    | succ k ih =>
      have hs := hXadm.ver_step B k
      rcases hs with h | h | h <;> omega
  have hmem : X n ∈ F := by
    rw [hF]
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_Icc.mpr (hbound n)⟩
  exact Finset.single_le_sum (fun p _ => norm_nonneg _) hmem

/-- **`tex:685-691`.**  If `ψ` is discrete harmonic, then `ψ (X n)` is a
martingale under the law of one cylinder walk.  This is the core of the
optional stopping at `tex:696-698`. -/
theorem walkMartingale_of_discreteHarmonic (B : Base) (x : Site B) (ψ : Site B → ℝ)
    (hharm : DiscreteHarmonic B ψ) :
    Martingale (fun s (X : ℕ → Site B) => ψ (X s)) (walkFiltration B) (walkPathLaw B x) := by
  classical
  -- the one-step relation `E[ψ (X (n+1)) | ℱ_n] = ψ (X n)`
  have hstep (n : ℕ) :
      (walkPathLaw B x)[fun X : ℕ → Site B => ψ (X (n + 1)) | walkFiltration B n]
        =ᵐ[walkPathLaw B x] (fun X : ℕ → Site B => ψ (X n)) := by
    have hint : Integrable (fun X : ℕ → Site B => ψ (X (n + 1)))
        ((Kernel.traj (cylITKernel B) 0)
          ((MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => Site B)).symm x)) := by
      rw [← walkPathLaw_eq_traj B x]
      exact integrable_psi_walk B x ψ (n + 1)
    have hcond := Kernel.condExp_traj (κ := cylITKernel B) (a := 0) (b := n)
      (x₀ := (MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => Site B)).symm x)
      (f := fun X : ℕ → Site B => ψ (X (n + 1))) (Nat.zero_le n) hint
    rw [walkPathLaw_eq_traj B x, walkFiltration_eq_piLE B n]
    refine hcond.trans ?_
    filter_upwards with X
    have hmi : ∫ y : ℕ → Site B, ψ (y (n + 1))
          ∂((Kernel.traj (cylITKernel B) n) (Preorder.frestrictLe n X))
        = ∫ z : Site B, ψ z
          ∂(((Kernel.traj (cylITKernel B) n) (Preorder.frestrictLe n X)).map
              (fun y : ℕ → Site B => y (n + 1))) :=
      (integral_map (μ := (Kernel.traj (cylITKernel B) n) (Preorder.frestrictLe n X))
        (φ := fun y : ℕ → Site B => y (n + 1)) (f := ψ)
        (measurable_pi_apply (n + 1)).aemeasurable
        (measurable_of_countable ψ).aestronglyMeasurable).symm
    rw [hmi]
    have hmapν : ((Kernel.traj (cylITKernel B) n) (Preorder.frestrictLe n X)).map
          (fun y : ℕ → Site B => y (n + 1)) = cylMeasure B (X n) := by
      rw [← Kernel.map_apply (Kernel.traj (cylITKernel B) n)
            (measurable_pi_apply (n + 1)) (Preorder.frestrictLe n X),
        Kernel.map_traj_succ_self]
      rfl
    rw [hmapν]
    exact (discreteHarmonic_iff_integral B ψ).mp hharm (X n)
  -- adaptedness
  have hadp : StronglyAdapted (walkFiltration B) (fun s (X : ℕ → Site B) => ψ (X s)) := by
    intro i
    have hgi : Measurable[walkFiltration B i] (fun X : ℕ → Site B => X i) := by
      rw [measurable_iff_comap_le]
      exact le_iSup₂ (f := fun k (_ : k ≤ i) =>
        MeasurableSpace.comap (fun X : ℕ → Site B => X k) inferInstance) i le_rfl
    exact ((measurable_of_countable ψ).comp hgi).stronglyMeasurable
  -- integrability at every time
  have hint : ∀ i, Integrable (fun X : ℕ → Site B => ψ (X i)) (walkPathLaw B x) :=
    fun i => integrable_psi_walk B x ψ i
  exact martingale_nat hadp hint fun i => (hstep i).symm

end IdlaCyl
