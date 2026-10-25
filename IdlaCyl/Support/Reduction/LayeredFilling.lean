module

/-
The genuine aborted layered exploration fills all layers with the finite union bound.
Source: paper/idla-cylinder-gff.tex, tex:595-610,1385-1396,1440-1453.
The success event also verifies the unreleased-particle count.
-/
public import IdlaCyl.Support.Reduction.FreezeBatchLaw

@[expose] public section

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Every fresh batch costs at most one coupon allowance, with the actual failure fallback. -/
theorem layeredPause_fill_bound (B : Base) (M n j : ℕ) (s : ResumeState B)
    (hF : R B (j : ℝ) ⊆ resumeSeed B s.1) (ρ : ℕ) (q : ℝ)
    (hM : (q + 1) * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (M : ℝ)) :
    layeredPause B M n j s (M * n + ρ)
        {t | R B ((j + n : ℕ) : ℝ) ⊆ resumeSeed B t.1.1 ∧ t.2 = ρ}ᶜ ≤
      ENNReal.ofReal ((n : ℝ) * (B.card : ℝ) ^ (-q)) := by
  induction n generalizing j s with
  | zero =>
      have hnot : (s, ρ) ∉ {t : ResumeState B × ℕ |
          R B ((j + 0 : ℕ) : ℝ) ⊆ resumeSeed B t.1.1 ∧ t.2 = ρ}ᶜ :=
        not_not.mpr ⟨hF, rfl⟩
      simp only [Nat.mul_zero, Nat.zero_add, layeredPause, Nat.cast_zero, zero_mul,
        ENNReal.ofReal_zero]
      rw [Measure.dirac_apply' _ (Set.to_countable _).measurableSet,
        Set.indicator_of_notMem hnot]
  | succ n ih =>
      have hremain : M * (n + 1) + ρ - M = M * n + ρ := by
        rw [Nat.mul_succ]
        omega
      rw [layeredPause, if_pos hF, hremain]
      have hgood (t : ResumeState B) (ht : R B ((j + 1 : ℕ) : ℝ) ⊆ resumeSeed B t.1) :
          layeredPause B M n (j + 1) t (M * n + ρ)
              {u | R B ((j + (n + 1) : ℕ) : ℝ) ⊆ resumeSeed B u.1.1 ∧ u.2 = ρ}ᶜ ≤
            ENNReal.ofReal ((n : ℝ) * (B.card : ℝ) ^ (-q)) := by
        have h := ih (j + 1) t ht
        rwa [show j + 1 + n = j + (n + 1) by omega] at h
      calc
        _ ≤ freezeBatch B (j + 1 : ℕ) M s
              {t | R B ((j + 1 : ℕ) : ℝ) ⊆ resumeSeed B t.1}ᶜ +
            ENNReal.ofReal ((n : ℝ) * (B.card : ℝ) ^ (-q)) :=
          bind_failure_le _ _ _ _ (Set.to_countable _).measurableSet
            (Set.to_countable _).measurableSet _ hgood
        _ ≤ ENNReal.ofReal ((B.card : ℝ) ^ (-q)) +
            ENNReal.ofReal ((n : ℝ) * (B.card : ℝ) ^ (-q)) := by
          apply add_le_add _ le_rfl
          apply freezeBatch_fill B (j + 1 : ℕ) s _ M q hM
          simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one,
            Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hF
        _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * (B.card : ℝ) ^ (-q)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          push_cast
          ring

/-- The initial layered phase has an unconditional failure bound. -/
theorem layeredPause_flat_fill (B : Base) (M ℓ ρ : ℕ) (q : ℝ)
    (hM : (q + 1) * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (M : ℝ)) :
    layeredPause B M ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ)
        {t | R B (ℓ : ℝ) ⊆ resumeSeed B t.1.1 ∧ t.2 = ρ}ᶜ ≤
      ENNReal.ofReal ((ℓ : ℝ) * (B.card : ℝ) ^ (-q)) := by
  have hF : R B ((0 : ℕ) : ℝ) ⊆ resumeSeed B (resumeEmpty B) := by
    rw [Nat.cast_zero, resumeSeed_empty]
  simpa only [Nat.zero_add] using
    layeredPause_fill_bound B M ℓ 0 (resumeEmpty B, []) hF ρ q hM

end IdlaCyl.Reduction
