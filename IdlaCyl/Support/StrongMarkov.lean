/-
The strong Markov property of the cylinder walk, and the one-step case.

The former `External.StrongMarkov` stated only the one-step
Markov property (`Kernel.map_traj_succ_self` at `a = 0`) while being consumed by
`le-wellspread` (`tex:1277`) and `pr:outer` (`tex:1392`), both of which condition
at a *random* freezing time.  Here `walkPathLaw_map_succ` keeps the one-step case
as a standalone theorem, and `External.StrongMarkov` is restated for stopping
times.
-/
import IdlaCyl.Support.Canonical
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Process.Filtration

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IdlaCyl

variable (B : Base)

/-- The natural filtration of the cylinder walk. -/
noncomputable def walkFiltration (B : Base) :
    Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Site B)) where
  seq n := ⨆ k ≤ n, MeasurableSpace.comap (fun X : ℕ → Site B => X k) inferInstance
  mono' := by
    intro i j hij
    refine iSup_le fun k => iSup_le fun hk => ?_
    exact le_iSup_of_le k (le_iSup_of_le (le_trans hk hij) le_rfl)
  le' := by
    intro n
    refine iSup_le fun k => iSup_le fun _ => ?_
    exact (measurable_pi_apply k).comap_le

/-- One-step Markov: the law of `X 1` under `walkPathLaw B x` is `cylMeasure`.
This is `Kernel.map_traj_succ_self` at `a = 0` and is discharged directly. -/
theorem walkPathLaw_map_succ (B : Base) (x : Site B) :
    (walkPathLaw B x).map (fun X : ℕ → Site B => X 1) = cylMeasure B x := by
  have hstep : (Kernel.traj (cylITKernel B) 0).map (fun X : ℕ → Site B => X 1)
      = cylITKernel B 0 := by
    have h := Kernel.map_traj_succ_self (X := fun _ : ℕ => Site B) (κ := cylITKernel B) (a := 0)
    simpa using h
  unfold walkPathLaw Kernel.trajMeasure
  rw [Measure.map_comp _ _ (measurable_pi_apply 1), hstep,
    Measure.map_dirac' (by fun_prop),
    Measure.dirac_bind (cylITKernel B 0).measurable]
  rfl

namespace External

/-- `ext-strong-markov` (`tex:1277`, `tex:1383`): conditionally on the walk up to
a finite stopping time `τ`, the shifted trajectory `n ↦ X (τ X + n)` is an
independent cylinder walk from the stopped position `X (τ X)`. -/
def StrongMarkov : Prop :=
  ∀ (B : Base) (x : Site B) (τ : (ℕ → Site B) → ℕ)
    (_hτ : ∀ n, MeasurableSet[walkFiltration B n] {X : ℕ → Site B | τ X ≤ n}),
    (condDistrib (fun X : ℕ → Site B => fun n => X (τ X + n))
        (fun X : ℕ → Site B => X (τ X)) (walkPathLaw B x))
      =ᵐ[(walkPathLaw B x).map (fun X : ℕ → Site B => X (τ X))]
      Kernel.ofFunOfCountable (walkPathLaw B)

end External

end IdlaCyl
