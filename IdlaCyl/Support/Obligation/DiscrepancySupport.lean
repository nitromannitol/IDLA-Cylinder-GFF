module

/-
The discrepancy function has finite support.

`paper/idla-cylinder-gff.tex:348-353` (`tex:348-353`): the symmetric difference
`A(t) △ R_{t/N}` is always finite, so the pairing `⟪D_t, f⟫` is a finite sum.
This file proves it, for every driver, from `A(0) = R_0`, monotonicity of the
cluster, and the fact that the cluster gains one site per step.  It discharges
the obligation `IdlaCyl.discrepancy_support_finite`.
-/
public import IdlaCyl.Support.Idla

@[expose] public section

namespace IdlaCyl.Obligation

open IdlaCyl

/-- The cluster at time `t` is `R_0` together with finitely many sites: each
step adds the single site `exitSite`. -/
theorem discrepancy_support_finite_cluster_subset (B : Base) (ω : Driver) (t : ℕ) :
    ∃ F : Finset (Site B), cluster B ω t ⊆ R B 0 ∪ (F : Set (Site B)) := by
  induction t with
  | zero => exact ⟨∅, by simp⟩
  | succ n ih =>
    obtain ⟨F, hF⟩ := ih
    refine ⟨insert (exitSite B (cluster B ω n) (ω n)) F, ?_⟩
    rw [cluster_succ]
    intro p hp
    rcases hp with hp | hp
    · rcases hF hp with h | h
      · exact Or.inl h
      · exact Or.inr (by simp [h])
    · exact Or.inr (by simp [Set.mem_singleton_iff.mp hp])

/-- A site at which `D_t` does not vanish lies in exactly one of `A(t)` and
`R_{t/N}`. -/
theorem discrepancy_support_finite_mem_or (B : Base) (ω : Driver) (t : ℕ) (p : Site B)
    (hp : discrepancy B ω t p ≠ 0) :
    (p ∈ cluster B ω t ∧ p ∉ R B ((t : ℝ) / B.card)) ∨
      (p ∉ cluster B ω t ∧ p ∈ R B ((t : ℝ) / B.card)) := by
  unfold discrepancy at hp
  by_cases h1 : p ∈ cluster B ω t <;> by_cases h2 : p ∈ R B ((t : ℝ) / B.card)
  · exact absurd (by simp [h1, h2]) hp
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (by simp [h1, h2]) hp

theorem discrepancy_support_finite (B : Base) (ω : Driver) (t : ℕ) :
    (Function.support (discrepancy B ω t)).Finite := by
  obtain ⟨F, hF⟩ := discrepancy_support_finite_cluster_subset B ω t
  have hR : R B 0 ⊆ cluster B ω t := by
    simpa using cluster_mono B ω (Nat.zero_le t)
  have hnn : (0 : ℝ) ≤ (t : ℝ) / B.card := by positivity
  have hsub : Function.support (discrepancy B ω t) ⊆
      (F : Set (Site B)) ∪ (Set.univ ×ˢ Set.Icc (1 : ℤ) ⌊(t : ℝ) / B.card⌋) := by
    intro p hp
    rcases discrepancy_support_finite_mem_or B ω t p hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      have h3 : p ∉ R B 0 := fun h => h2 (R_mono hnn h)
      rcases hF h1 with h | h
      · exact absurd h h3
      · exact h
    · right
      have h3 : p ∉ R B 0 := fun h => h1 (hR h)
      have h4 : ¬ ((p.2 : ℝ) ≤ 0) := by simpa using h3
      have h5 : (p.2 : ℝ) ≤ (t : ℝ) / B.card := by simpa using h2
      refine ⟨Set.mem_univ _, ?_, Int.le_floor.mpr h5⟩
      have h6 : ¬ p.2 ≤ 0 := fun h => h4 (by exact_mod_cast h)
      omega
  exact ((Finset.finite_toSet F).union
    (Set.finite_univ.prod (Set.finite_Icc _ _))).subset hsub

end IdlaCyl.Obligation
