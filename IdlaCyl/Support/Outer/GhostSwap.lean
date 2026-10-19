/-
Exchange of an independent fresh walk with one prescribed site-ghost coordinate.
Source: paper/idla-cylinder-gff.tex, tex:1271-1280.

This is the finite-product permutation step used when a stopped prefix selects
a site ghost. The fresh coordinate has exactly the selected ghost's law.
-/
import IdlaCyl.Support.Outer.GhostMarkov

attribute [local instance] Classical.propDecidable

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

private def ghostOptionEquiv (ι α : Type*) [MeasurableSpace α] :
    (α × (ι → α)) ≃ᵐ (Option ι → α) where
  toFun p o := match o with | none => p.1 | some i => p.2 i
  invFun f := (f none, fun i => f (some i))
  left_inv _ := rfl
  right_inv f := by funext o; cases o <;> rfl
  measurable_toFun := measurable_pi_iff.mpr fun o => by
    cases o with
    | none => exact measurable_fst
    | some i => exact (measurable_pi_apply i).comp measurable_snd
  measurable_invFun := (measurable_pi_apply none).prodMk
    (measurable_pi_iff.mpr fun i => measurable_pi_apply (some i))

/-- Swap a fresh coordinate with a specified site coordinate. -/
def ghostCoordinateSwap {ι α : Type*} [DecidableEq ι] (i : ι) (p : α × (ι → α)) :
    α × (ι → α) :=
  (p.2 i, Function.update p.2 i p.1)

/-- Swapping two equal-law independent coordinates preserves their complete joint law. -/
theorem measurePreserving_ghostCoordinateSwap {ι α : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace α] (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (ghostCoordinateSwap (α := α) i) ((μ i).prod (Measure.pi μ))
      ((μ i).prod (Measure.pi μ)) := by
  let ν : Option ι → Measure α := fun o => match o with | none => μ i | some j => μ j
  let e := ghostOptionEquiv ι α
  have hν : ∀ o, IsProbabilityMeasure (ν o) := by
    intro o
    cases o <;> dsimp only [ν] <;> infer_instance
  have he : MeasurePreserving e ((μ i).prod (Measure.pi μ)) (Measure.pi ν) := by
    refine ⟨e.measurable, ?_⟩
    symm
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply e.measurable (MeasurableSet.univ_pi hs)]
    have hpre : e ⁻¹' Set.univ.pi s = (s none) ×ˢ Set.univ.pi (fun j => s (some j)) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_prod]
      change (∀ o : Option ι, (match o with | none => p.1 | some j => p.2 j) ∈ s o) ↔
        p.1 ∈ s none ∧ ∀ j, p.2 j ∈ s (some j)
      constructor
      · intro h
        exact ⟨h none, fun j => h (some j)⟩
      · rintro ⟨h0, hj⟩ o
        cases o with
        | none => exact h0
        | some j => exact hj j
    rw [hpre, Measure.prod_prod, Measure.pi_pi, Fintype.prod_option]
  let σ : Option ι ≃ Option ι := Equiv.swap none (some i)
  have hνσ : (fun o => ν (σ o)) = ν := by
    funext o
    by_cases h0 : o = none
    · subst o
      simp only [σ, Equiv.swap_apply_left, ν]
    · by_cases hi : o = some i
      · subst o
        simp only [σ, Equiv.swap_apply_right, ν]
      · rw [Equiv.swap_apply_of_ne_of_ne h0 hi]
  have hσ : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : Option ι => α) σ)
      (Measure.pi ν) (Measure.pi ν) := by
    have h := measurePreserving_piCongrLeft (α := fun _ : Option ι => α) ν σ
    rw [hνσ] at h
    exact h
  have hσinv := MeasurePreserving.symm
    (MeasurableEquiv.piCongrLeft (fun _ : Option ι => α) σ) hσ
  have hcomp := (MeasurePreserving.symm e he).comp (hσinv.comp he)
  have heq : e.symm ∘ ((MeasurableEquiv.piCongrLeft (fun _ : Option ι => α) σ).symm ∘ e) =
      ghostCoordinateSwap (α := α) i := by
    funext p
    apply Prod.ext
    · change (Equiv.piCongrLeft (fun _ : Option ι => α) σ).symm (e p) none = p.2 i
      rw [Equiv.piCongrLeft_symm_apply]
      rw [show σ none = some i from Equiv.swap_apply_left _ _]
      rfl
    · funext j
      change (Equiv.piCongrLeft (fun _ : Option ι => α) σ).symm (e p) (some j) =
        Function.update p.2 i p.1 j
      rw [Equiv.piCongrLeft_symm_apply]
      by_cases hj : j = i
      · subst j
        rw [show σ (some i) = none from Equiv.swap_apply_right _ _, Function.update_self]
        rfl
      · rw [show σ (some j) = some j from
          Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa only [ne_eq, Option.some.injEq] using hj),
          Function.update_of_ne hj]
        rfl
  rw [heq] at hcomp
  exact hcomp

/-- Replacing one coordinate of an independent stream by an independent sample
with that coordinate's law preserves the stream law. -/
theorem measurePreserving_ghostOverwrite {ι α : Type*} [DecidableEq ι] [MeasurableSpace α]
    (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (fun p : (ι → α) × α => Function.update p.1 i p.2)
      ((Measure.infinitePi μ).prod (μ i)) (Measure.infinitePi μ) := by
  have hm : Measurable (fun p : (ι → α) × α => Function.update p.1 i p.2) := by
    apply measurable_pi_iff.mpr
    intro j
    by_cases hj : j = i
    · subst j
      simp only [Function.update_self]
      exact measurable_snd
    · simp only [Function.update_of_ne hj]
      exact (measurable_pi_apply j).comp measurable_fst
  refine ⟨hm, Measure.eq_infinitePi μ ?_⟩
  intro s t ht
  rw [Measure.map_apply hm (MeasurableSet.pi s.countable_toSet (fun j _ => ht j))]
  by_cases hi : i ∈ s
  · have hpre : (fun p : (ι → α) × α => Function.update p.1 i p.2) ⁻¹' Set.pi s t =
        (Set.pi (s.erase i) t) ×ˢ t i := by
      ext p
      constructor
      · intro hp
        refine ⟨fun j hj => ?_, ?_⟩
        · have hmem := hp j (Finset.mem_of_mem_erase hj)
          simpa only [Function.update_of_ne (Finset.mem_erase.mp hj).1] using hmem
        · simpa only [Function.update_self] using hp i hi
      · rintro ⟨hp, hpi⟩ j hj
        by_cases hji : j = i
        · subst j
          simpa only [Function.update_self] using hpi
        · simpa only [Function.update_of_ne hji] using hp j (Finset.mem_erase.mpr ⟨hji, hj⟩)
    rw [hpre, Measure.prod_prod, Measure.infinitePi_pi _ (fun j _ => ht j)]
    exact Finset.prod_erase_mul _ _ hi
  · have hpre : (fun p : (ι → α) × α => Function.update p.1 i p.2) ⁻¹' Set.pi s t =
        (Set.pi s t) ×ˢ Set.univ := by
      ext p
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
      constructor
      · intro hp j hj
        have hji : j ≠ i := fun heq => hi (heq ▸ hj)
        simpa only [Function.update_of_ne hji] using hp j hj
      · intro hp j hj
        have hji : j ≠ i := fun heq => hi (heq ▸ hj)
        simpa only [Function.update_of_ne hji] using hp j hj
    rw [hpre, Measure.prod_prod, measure_univ, mul_one,
      Measure.infinitePi_pi _ (fun j _ => ht j)]

example : MeasurePreserving (ghostCoordinateSwap (α := ℕ) (0 : Fin 2))
    ((Measure.dirac (0 : ℕ)).prod (Measure.pi fun i : Fin 2 => Measure.dirac (i : ℕ)))
    ((Measure.dirac (0 : ℕ)).prod (Measure.pi fun i : Fin 2 => Measure.dirac (i : ℕ))) :=
  measurePreserving_ghostCoordinateSwap (fun i : Fin 2 => Measure.dirac (i : ℕ)) 0

example : MeasurePreserving (fun p : (Fin 2 → ℕ) × ℕ => Function.update p.1 0 p.2)
    ((Measure.infinitePi fun i : Fin 2 => Measure.dirac (i : ℕ)).prod (Measure.dirac 0))
    (Measure.infinitePi fun i : Fin 2 => Measure.dirac (i : ℕ)) :=
  measurePreserving_ghostOverwrite (fun i : Fin 2 => Measure.dirac (i : ℕ)) 0

end
end IdlaCyl
