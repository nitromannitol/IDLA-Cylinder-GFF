module

public import IdlaCyl.Support.FirstHit

@[expose] public section

/-!
# Assembly of the lazy-walk recurrence

`IdlaCyl.External.LazyRwRecurrent` (`tex:600-604`) follows from four ingredients about the
probability `f(x, y)` that the cylinder walk started at `(x, y)` stays strictly below height `k`
forever: `f` vanishes at height `≥ k`, `f` is harmonic below `k`, `f` does not depend on the
horizontal start `x`, and a bounded harmonic function on a half-line vanishing at `k` vanishes.
This file discharges `LazyRwRecurrent` from those four hypotheses.

Paper: `paper/idla-cylinder-gff.tex`.
-/

namespace IdlaCyl.Recurrence

open MeasureTheory

theorem lazyRwRecurrent_of
    (h1 : ∀ (B : Base) (k : ℤ) (p : Site B), k ≤ p.2 →
      walkPathLaw B p {X : ℕ → Site B | ∀ n, (X n).2 < k} = 0)
    (h2 : ∀ (B : Base) (k : ℤ) (p : Site B), p.2 < k →
      (1/4 : ℝ) * (walkPathLaw B (p.1, p.2 + 1) {X : ℕ → Site B | ∀ n, (X n).2 < k}).toReal
        + (1/4 : ℝ) * (walkPathLaw B (p.1, p.2 - 1) {X : ℕ → Site B | ∀ n, (X n).2 < k}).toReal
        + (1/2 : ℝ) * ∑ x' : B.V, B.P p.1 x' *
            (walkPathLaw B (x', p.2) {X : ℕ → Site B | ∀ n, (X n).2 < k}).toReal
        = (walkPathLaw B p {X : ℕ → Site B | ∀ n, (X n).2 < k}).toReal)
    (h3 : ∀ (B : Base) (k : ℤ) (x x' : B.V) (y : ℤ),
      walkPathLaw B (x, y) {X : ℕ → Site B | ∀ n, (X n).2 < k}
        = walkPathLaw B (x', y) {X : ℕ → Site B | ∀ n, (X n).2 < k})
    (h4 : ∀ (g : ℤ → ℝ) (k : ℤ), g k = 0 → (∀ y ≤ k, 0 ≤ g y ∧ g y ≤ 1) →
      (∀ y < k, 2 * g y = g (y + 1) + g (y - 1)) → ∀ y ≤ k, g y = 0) :
    External.LazyRwRecurrent := by
  intro B p k
  rw [MeasureTheory.ae_iff]
  have hset : {X : ℕ → Site B | ¬ ∃ n, k ≤ (X n).2}
      = {X : ℕ → Site B | ∀ n, (X n).2 < k} := by
    ext X
    simp only [Set.mem_setOf_eq, not_exists, not_le]
  rw [hset]
  -- the height-`y` never-reach probability, read off at the base point
  obtain ⟨g, hg⟩ : ∃ g : ℤ → ℝ, ∀ y : ℤ,
      g y = (walkPathLaw B (B.pt, y) {X : ℕ → Site B | ∀ n, (X n).2 < k}).toReal :=
    ⟨fun y => (walkPathLaw B (B.pt, y) {X : ℕ → Site B | ∀ n, (X n).2 < k}).toReal,
      fun _ => rfl⟩
  have hx : ∀ (x : B.V) (y : ℤ),
      (walkPathLaw B (x, y) {X : ℕ → Site B | ∀ n, (X n).2 < k}).toReal = g y := fun x y => by
    rw [hg y, h3 B k x B.pt y]
  have hgk : g k = 0 := by
    rw [hg k, h1 B k (B.pt, k) le_rfl]
    rfl
  have hbd : ∀ y ≤ k, 0 ≤ g y ∧ g y ≤ 1 := fun y _ => by
    rw [hg y]
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have hle : walkPathLaw B (B.pt, y) {X : ℕ → Site B | ∀ n, (X n).2 < k} ≤ 1 := prob_le_one
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hle
  have hharm : ∀ y < k, 2 * g y = g (y + 1) + g (y - 1) := fun y hy => by
    have h := h2 B k (B.pt, y) hy
    simp only [hx] at h
    rw [← Finset.sum_mul, B.P_row_sum B.pt, one_mul] at h
    linarith
  have hzero := h4 g k hgk hbd hharm
  by_cases hp : k ≤ p.2
  · exact h1 B k p hp
  · have hlt : p.2 < k := not_le.mp hp
    have hreal : (walkPathLaw B p {X : ℕ → Site B | ∀ n, (X n).2 < k}).toReal = 0 := by
      have := hx p.1 p.2
      rw [hzero p.2 hlt.le] at this
      exact this
    rcases (ENNReal.toReal_eq_zero_iff _).mp hreal with h0 | htop
    · exact h0
    · exact absurd htop (measure_ne_top _ _)

end IdlaCyl.Recurrence
