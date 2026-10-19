import IdlaCyl.Support.Replace.ProductEfronStein
import Mathlib.Probability.Independence.InfinitePi

/-!
Restriction of an infinite independent family to the finite product used by
Efron–Stein in the replacement lemma (`tex:828-848`). The coordinate laws are
arbitrary probability measures, rather than finite-support approximations.
-/

namespace ProbabilityTheory.ProductEfronStein

open MeasureTheory

universe u
variable {α : Type u} [MeasurableSpace α]

/-- Assemble a finite vector into the right-associated product. -/
def collect : (n : ℕ) → (Fin n → α) → Space α n
  | 0, _ => PUnit.unit
  | n + 1, x => (x 0, collect n (fun i => x i.succ))

/-- The finite-vector assembly map is measurable. -/
theorem measurable_collect (n : ℕ) : Measurable (collect (α := α) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_pi_apply 0).prodMk
      (ih.comp (measurable_pi_lambda _ fun i => measurable_pi_apply i.succ))

/-- The finite-vector assembly carries the usual finite product law to `law`. -/
theorem measurePreserving_collect (μ : ℕ → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (n : ℕ) :
    MeasurePreserving (collect (α := α) n) (Measure.pi fun i : Fin n => μ i) (law μ n) := by
  induction n generalizing μ with
  | zero =>
    refine ⟨measurable_collect 0, ?_⟩
    simp only [collect, law, Measure.map_const, measure_univ, one_smul]
  | succ n ih =>
    have htail := ih (fun i => μ (i + 1))
    have hp := ((MeasurePreserving.id (μ 0)).prod htail).comp
      (measurePreserving_piFinSuccAbove (fun i : Fin (n + 1) => μ i) 0)
    have hfun : (Prod.map id (collect (α := α) n)) ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0) = collect (n + 1) := by
      funext x
      change (x 0, collect n (fun i => x ((0 : Fin (n + 1)).succAbove i))) =
        (x 0, collect n (fun i => x i.succ))
      simp only [Fin.succAbove_zero]
    rw [hfun] at hp
    exact hp

/-- The first `n` coordinates of an infinite sequence, as a finite product. -/
def take (n : ℕ) (ω : ℕ → α) : Space α n := collect n (fun i => ω i)

/-- Prefix restriction is measurable. -/
theorem measurable_take (n : ℕ) : Measurable (take (α := α) n) :=
  (measurable_collect n).comp (measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ))

/-- Prefix restriction sends the infinite product to its genuine finite marginal law. -/
theorem measurePreserving_take (μ : ℕ → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (n : ℕ) :
    MeasurePreserving (take (α := α) n) (Measure.infinitePi μ) (law μ n) := by
  have hm : MeasurePreserving (fun ω : ℕ → α => fun i : Fin n => ω i)
      (Measure.infinitePi μ) (Measure.pi fun i : Fin n => μ i) := by
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]
  exact (measurePreserving_collect μ n).comp hm

/-- Product Efron–Stein for a bounded statistic of a finite prefix of an infinite
independent family. The right side resamples each of the consumed coordinates. -/
theorem efron_stein_infinitePi (μ : ℕ → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (n : ℕ) (f : Space α n → ℝ) (hf : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ z, |f z| ≤ C) :
    variance (fun ω => f (take n ω)) (Measure.infinitePi μ) ≤ cost μ n f / 2 := by
  rw [(measurePreserving_take μ n).variance_fun_comp hf.aemeasurable]
  exact efron_stein μ n f hf C hC hbound

end ProbabilityTheory.ProductEfronStein
