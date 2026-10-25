module

/-
Fresh batches fill a canonical buffer.
Source: paper/idla-cylinder-gff.tex, tex:246-265,595-610,1440-1453.
Induction conditions on the actual finite occupied set, including all extra
sites above its filled rectangle. No successful-coupling conditioning occurs.
-/
public import IdlaCyl.Support.Reduction.CouponGrowth

@[expose] public section

namespace IdlaCyl.Reduction

open MeasureTheory
open scoped ENNReal

/-- Zero additions leave the entire seed unchanged, in law. -/
theorem layerGrowthLaw_zero (B : Base) (F : ResumeFinite B) (h : ℤ) :
    layerGrowthLaw B F h 0 = Measure.dirac F := by
  simp only [layerGrowthLaw, resumeGrow, Measure.map_const, measure_univ, one_smul]

/-- One-step growth uses an independent next canonical walk. -/
theorem layerGrowthLaw_succ (B : Base) (F : ResumeFinite B) (h : ℤ) (n : ℕ) :
    layerGrowthLaw B F h (n + 1) = (layerGrowthLaw B F h n).bind
      (fun G => (walkLawUniformAt B h).map
        (fun X => resumeInsert B G (exitSite' B (resumeSeed B G) X))) :=
  resumeGrow_law_step B F (fun _ => walkLawUniformAt B h) n

/-- A finite block followed by fresh additions has exactly the ordinary growth law. -/
theorem layerGrowthLaw_add (B : Base) (F : ResumeFinite B) (h : ℤ) (m n : ℕ) :
    layerGrowthLaw B F h (m + n) =
      (layerGrowthLaw B F h m).bind (fun G => layerGrowthLaw B G h n) := by
  induction n with
  | zero => simp only [Nat.add_zero, layerGrowthLaw_zero, Measure.bind_dirac]
  | succ n ih =>
      rw [Nat.add_succ, layerGrowthLaw_succ, ih,
        Measure.bind_bind (measurable_of_countable _).aemeasurable
          (measurable_of_countable _).aemeasurable]
      congr 1
      funext G
      exact (layerGrowthLaw_succ B G h n).symm

/-- A uniform conditional failure bound costs that bound plus the bad-past probability. -/
theorem bind_failure_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α]
    (μ : Measure α) [IsProbabilityMeasure μ] (κ : α → Measure β)
    [∀ a, IsProbabilityMeasure (κ a)] (A : Set α) (E : Set β)
    (hA : MeasurableSet A) (hE : MeasurableSet E) (δ : ℝ≥0∞)
    (hgood : ∀ a ∈ A, κ a E ≤ δ) :
    (μ.bind κ) E ≤ μ Aᶜ + δ := by
  rw [Measure.bind_apply hE (measurable_of_countable κ).aemeasurable]
  calc
    _ ≤ ∫⁻ a, δ + Aᶜ.indicator (fun _ => (1 : ℝ≥0∞)) a ∂μ := by
      apply lintegral_mono
      intro a
      change κ a E ≤ δ + Aᶜ.indicator (fun _ => (1 : ℝ≥0∞)) a
      by_cases ha : a ∈ A
      · rw [Set.indicator_of_notMem (show a ∉ Aᶜ from not_not.mpr ha), add_zero]
        exact hgood a ha
      · rw [Set.indicator_of_mem (show a ∈ Aᶜ from ha)]
        exact (prob_le_one (μ := κ a) (s := E)).trans (le_add_self : 1 ≤ δ + 1)
    _ = μ Aᶜ + δ := by
      rw [lintegral_add_left measurable_const, lintegral_const,
        lintegral_indicator_const hA.compl, measure_univ, mul_one, one_mul, add_comm]

/-- The full canonical buffer bound, with arbitrary additional occupied sites. -/
theorem canonical_buffer_fill (B : Base) (F : ResumeFinite B)
    (h L : ℤ) (hh : h ≤ L) (hF : R B (L : ℝ) ⊆ resumeSeed B F)
    (M β : ℕ) (q : ℝ)
    (hM : (q + 1) * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (M : ℝ)) :
    layerGrowthLaw B F h (M * β) (filled B (L + (β : ℤ)))ᶜ ≤
      ENNReal.ofReal ((β : ℝ) * (B.card : ℝ) ^ (-q)) := by
  induction β with
  | zero =>
      rw [Nat.mul_zero, Nat.cast_zero, add_zero, layerGrowthLaw_zero]
      have hmem : F ∉ (filled B L)ᶜ := not_not.mpr hF
      rw [Measure.dirac_apply' _ (Set.to_countable _).measurableSet,
        Set.indicator_of_notMem hmem, Nat.cast_zero, zero_mul, ENNReal.ofReal_zero]
  | succ β ih =>
      have hlevel : L + ((β + 1 : ℕ) : ℤ) = (L + (β : ℤ)) + 1 := by omega
      rw [Nat.mul_succ, hlevel, layerGrowthLaw_add]
      have hgood (G : ResumeFinite B) (hG : G ∈ filled B (L + (β : ℤ))) :
          layerGrowthLaw B G h M (filled B (L + (β : ℤ) + 1))ᶜ ≤
            ENNReal.ofReal ((B.card : ℝ) ^ (-q)) := by
        apply canonical_one_layer_fill B G h (L + (β : ℤ) + 1) (by omega) _ M q hM
        have heq : (((L + (β : ℤ) + 1 : ℤ) : ℝ) - 1) = ((L + (β : ℤ) : ℤ) : ℝ) := by
          push_cast
          ring
        rw [heq]
        exact hG
      calc
        _ ≤ layerGrowthLaw B F h (M * β) (filled B (L + (β : ℤ)))ᶜ +
            ENNReal.ofReal ((B.card : ℝ) ^ (-q)) :=
          bind_failure_le _ _ _ _ (Set.to_countable _).measurableSet
            (Set.to_countable _).measurableSet _ hgood
        _ ≤ ENNReal.ofReal ((β : ℝ) * (B.card : ℝ) ^ (-q)) +
            ENNReal.ofReal ((B.card : ℝ) ^ (-q)) := add_le_add ih le_rfl
        _ = ENNReal.ofReal (((β + 1 : ℕ) : ℝ) * (B.card : ℝ) ^ (-q)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          push_cast
          ring

/-- Subsequent canonical additions cannot destroy a filled buffer. -/
theorem layerGrowthLaw_failure_mono (B : Base) (F : ResumeFinite B) (h j : ℤ)
    (m n : ℕ) (hmn : m ≤ n) :
    layerGrowthLaw B F h n (filled B j)ᶜ ≤ layerGrowthLaw B F h m (filled B j)ᶜ := by
  rw [layerGrowthLaw, layerGrowthLaw,
    Measure.map_apply (measurable_resumeGrow B F n) (Set.to_countable _).measurableSet,
    Measure.map_apply (measurable_resumeGrow B F m) (Set.to_countable _).measurableSet]
  apply measure_mono
  intro ω hbad hfill
  have hfilled : R B (j : ℝ) ⊆ resumeSeed B (resumeGrow B F ω m) := hfill
  apply hbad
  intro z hz
  rw [resumeSeed_grow] at hfilled ⊢
  exact clusterFrom_mono B _ ω hmn (hfilled hz)

end IdlaCyl.Reduction
