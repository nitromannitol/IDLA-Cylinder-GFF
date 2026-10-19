/-
The literal aborted layered exploration, freshly completed, has the ordinary law.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396,1440-1453.
This unconditional identity includes every failed-layer branch.
The remaining-count premise is a deterministic accounting constraint only.
-/
import IdlaCyl.Support.Reduction.FreezeFinish

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Consuming a batch and then every remaining release gives the correct completion kernel. -/
theorem freezeBatch_finishUniform (B : Base) (j M : ℕ) (s : ResumeState B)
    (hF : R B (j : ℝ) ⊆ resumeSeed B s.1) (r : ℕ) (hr : M ≤ r) :
    (freezeBatch B (j + 1 : ℕ) M s).bind (fun t => finishUniform B t (r - M)) =
      finishUniform B s r := by
  unfold finishUniform
  rw [← Measure.bind_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable, freezeBatch_finish B j M s.1 s.2 hF,
    Measure.bind_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
  congr 1
  funext F
  rw [← layerGrowthLaw_add, Nat.add_sub_of_le hr]

/-- An arbitrary interrupted layered schedule may be completed with no bias.
The input queue is retained and the next starts are never inspected in advance. -/
theorem layeredPause_finishUniform (B : Base) (M n j : ℕ) (s : ResumeState B)
    (r : ℕ) (hr : M * n ≤ r) :
    (layeredPause B M n j s r).bind (fun t => finishUniform B t.1 t.2) =
      finishUniform B s r := by
  induction n generalizing j s r with
  | zero =>
      exact Measure.dirac_bind (measurable_of_countable
        (fun t : ResumeState B × ℕ => finishUniform B t.1 t.2)) (s, r)
  | succ n ih =>
      have hbudget : M * n ≤ r - M := by
        rw [Nat.mul_succ] at hr
        omega
      have hM : M ≤ r := by
        rw [Nat.mul_succ] at hr
        omega
      unfold layeredPause
      split_ifs with hF
      · rw [Measure.bind_bind (measurable_of_countable _).aemeasurable
          (measurable_of_countable _).aemeasurable]
        have heq : (fun t : ResumeState B =>
            (layeredPause B M n (j + 1) t (r - M)).bind
              (fun u => finishUniform B u.1 u.2)) =
            (fun t => finishUniform B t (r - M)) := by
          funext t
          exact ih (j + 1) t (r - M) hbudget
        rw [heq]
        exact freezeBatch_finishUniform B j M s hF r hM
      · exact Measure.dirac_bind (measurable_of_countable
          (fun t : ResumeState B × ℕ => finishUniform B t.1 t.2)) (s, r)

/-- The initial empty queue followed by ordinary releases is exactly flat-start IDLA. -/
theorem finishUniform_empty (B : Base) (r : ℕ) :
    finishUniform B (resumeEmpty B, []) r = flatClusterLaw B r := by
  unfold finishUniform resumeRun
  rw [Measure.dirac_bind (measurable_of_countable _)]
  rfl

/-- Completing the actual multi-layer exploration, including fallback, gives ordinary IDLA. -/
theorem layeredPause_finish (B : Base) (M ℓ ρ : ℕ) :
    (layeredPause B M ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ)).bind
        (fun s => finishUniform B s.1 s.2) =
      flatClusterLaw B (M * ℓ + ρ) := by
  rw [layeredPause_finishUniform B M ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ) (by omega),
    finishUniform_empty]

end IdlaCyl.Reduction
