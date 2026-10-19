import IdlaCyl.Support.Replace.InfiniteProduct

/-!
Efron–Stein for finite-dependent observables on an infinite product, as
needed for the first `T` trajectories in the replacement lemma (`tex:828-848`).
-/

namespace ProbabilityTheory.ProductEfronStein

open MeasureTheory

universe u
variable {α : Type u} [MeasurableSpace α]

/-- Attach a fixed unused tail to a finite product. -/
def extend : (n : ℕ) → Space α n → (ℕ → α) → (ℕ → α)
  | 0, _, tail => tail
  | n + 1, z, tail => fun j => Nat.casesOn j z.1 (fun i => extend n z.2 tail i)

/-- Attaching a fixed tail is measurable as a function of the finite coordinates. -/
theorem measurable_extend (n : ℕ) (tail : ℕ → α) :
    Measurable (fun z => extend (α := α) n z tail) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    apply measurable_pi_lambda
    intro j
    cases j with
    | zero => exact measurable_fst
    | succ j => exact (measurable_pi_apply j).comp (ih.comp measurable_snd)

omit [MeasurableSpace α] in
/-- Prefix restriction at a successor separates the first coordinate. -/
theorem take_succ (n : ℕ) (ω : ℕ → α) :
    take (n + 1) ω = (ω 0, take n (fun i => ω (i + 1))) := rfl

omit [MeasurableSpace α] in
/-- Prefix restriction recovers all the supplied finite coordinates. -/
theorem take_extend (n : ℕ) (z : Space α n) (tail : ℕ → α) :
    take n (extend n z tail) = z := by
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    rw [take_succ]
    change (z.1, take n (extend n z.2 tail)) = z
    rw [ih]

omit [MeasurableSpace α] in
/-- Replacing an unused tail preserves every consumed coordinate. -/
theorem extend_take_eq (n : ℕ) (ω tail : ℕ → α) (i : ℕ) (hi : i < n) :
    extend n (take n ω) tail i = ω i := by
  induction n generalizing ω i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change extend n (take n (fun j => ω (j + 1))) tail i = ω (i + 1)
      exact ih _ _ (by omega)

/-- Product Efron–Stein for any bounded measurable observable depending on
only the first `n` coordinates of an infinite independent family. -/
theorem efron_stein_finiteDependence (μ : ℕ → Measure α) [∀ i, IsProbabilityMeasure (μ i)]
    (n : ℕ) (tail : ℕ → α) (f : (ℕ → α) → ℝ) (hf : Measurable f)
    (hdep : ∀ ω ω', (∀ i, i < n → ω i = ω' i) → f ω = f ω')
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ ω, |f ω| ≤ C) :
    variance f (Measure.infinitePi μ) ≤
      cost μ n (fun z => f (extend n z tail)) / 2 := by
  have heq (ω : ℕ → α) : f ω = f (extend n (take n ω) tail) :=
    hdep _ _ (fun i hi => (extend_take_eq n ω tail i hi).symm)
  calc
    _ = variance (fun ω => f (extend n (take n ω) tail)) (Measure.infinitePi μ) :=
      variance_congr (.of_forall heq)
    _ ≤ _ := efron_stein_infinitePi μ n (fun z => f (extend n z tail))
      (hf.comp (measurable_extend n tail)) C hC (fun z => hbound _)

end ProbabilityTheory.ProductEfronStein
