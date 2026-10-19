import IdlaCyl.Support.PausedPaths
import IdlaCyl.Support.FiniteLawOperations

set_option autoImplicit false

/-!
# The exact stopped harmonic score, with no ghost trajectories

The score is constructed from the actual settled set and the LIST of paused
particles. Each processed trajectory adds its exit score. When the interior
rectangle is filled and the boundary values are a Kronecker delta, the paused
multiplicity at the target is exactly a centered score plus a deterministic
number. This is an identity, not an independence assumption.
-/
namespace IdlaCyl
open scoped BigOperators
noncomputable section
variable {α : Type*} [DecidableEq α] {seed : Set α}

namespace PausedState
open EscapingPath

/-- All paused copies are counted, even when their start sites coincide. -/
def weightedMass (s : PausedState seed) (H : α → ℝ) : ℝ :=
  (∑ z ∈ s.settled, H z) + (s.pending.map (fun p => H (p.position 0))).sum

/-- Accumulated first-exit score in the actual ordered paused recursion. -/
def exitScore (boundary : Set α) (H : α → ℝ) (s : PausedState seed) :
    List (EscapingPath seed) → ℝ
  | [] => 0
  | w :: ws => H (w.exitSite s.settled) + exitScore boundary H (s.pauseOne boundary w) ws

theorem weightedMass_pauseOne (boundary : Set α) (H : α → ℝ)
    (s : PausedState seed) (w : EscapingPath seed) :
    (s.pauseOne boundary w).weightedMass H =
      s.weightedMass H + H (w.exitSite s.settled) := by
  classical
  by_cases hb : w.exitSite s.settled ∈ boundary
  · have hb' : w.position (w.exitTime s.settled) ∈ boundary := hb
    simp [pauseOne, hb', weightedMass, List.map_append, List.sum_append,
      exitSite, add_assoc]
  · simp [pauseOne, hb, weightedMass, settle, w.exit_fresh s.settled,
      add_assoc, add_left_comm, add_comm]

theorem weightedMass_pauseAll (boundary : Set α) (H : α → ℝ)
    (s : PausedState seed) (ws : List (EscapingPath seed)) :
    (s.pauseAll boundary ws).weightedMass H =
      s.weightedMass H + exitScore boundary H s ws := by
  induction ws generalizing s with
  | nil => simp [pauseAll, exitScore]
  | cons w ws ih =>
      rw [pauseAll, ih, weightedMass_pauseOne]
      simp [exitScore, add_assoc]

/-- The boundary delta sums to the literal list multiplicity. -/
theorem pending_delta_sum (ws : List (EscapingPath seed)) (H : α → ℝ) (ζ : α)
    (hdelta : ∀ p ∈ ws, H (p.position 0) = if p.position 0 = ζ then 1 else 0) :
    (ws.map (fun p => H (p.position 0))).sum =
      (((ws.map (fun p => p.position 0)).count ζ : ℕ) : ℝ) := by
  induction ws with
  | nil => simp
  | cons p ps ih =>
      have hp := hdelta p (by simp)
      have hps : ∀ q ∈ ps, H (q.position 0) = if q.position 0 = ζ then 1 else 0 := by
        intro q hq
        exact hdelta q (by simp [hq])
      have ht := ih hps
      by_cases h : p.position 0 = ζ
      · rw [h] at hp
        simp [hp, h, ht, Nat.cast_add, add_comm]
      · simp [hp, h, ht]

/-- Exact frozen-count identity on a filled interior of harmonic mass m. -/
theorem frozen_count_identity (s : PausedState seed) (H : α → ℝ)
    (ζ : α) (μ m : ℝ)
    (hdelta : ∀ p ∈ s.pending, H (p.position 0) = if p.position 0 = ζ then 1 else 0)
    (hfilled : (∑ z ∈ s.settled, H z) = m) :
    (s.multiplicity ζ : ℝ) = (s.weightedMass H - μ) + μ - m := by
  have hp := pending_delta_sum s.pending H ζ hdelta
  unfold weightedMass
  rw [hfilled, hp]
  change _ = m + (s.multiplicity ζ : ℝ) - μ + μ - m
  ring

/-- The actual upper-tail event reduces to the one centered score. -/
theorem frozen_upper_event (s : PausedState seed) (H : α → ℝ)
    (ζ : α) (μ m r : ℝ)
    (hdelta : ∀ p ∈ s.pending, H (p.position 0) = if p.position 0 = ζ then 1 else 0)
    (hfilled : (∑ z ∈ s.settled, H z) = m)
    (hlarge : μ-m+r ≤ (s.multiplicity ζ : ℝ)) :
    r ≤ s.weightedMass H-μ := by
  rw [frozen_count_identity s H ζ μ m hdelta hfilled] at hlarge
  linarith

/-- If no paused copy reaches the target, only distinct interior sites contribute. -/
theorem no_target_lower_event (s : PausedState seed) (H : α → ℝ)
    (ζ : α) (μ m : ℝ)
    (hdelta : ∀ p ∈ s.pending, H (p.position 0) = if p.position 0 = ζ then 1 else 0)
    (hnone : s.multiplicity ζ = 0)
    (hmass : (∑ z ∈ s.settled, H z) ≤ m) :
    s.weightedMass H-μ ≤ m-μ := by
  have hp := pending_delta_sum s.pending H ζ hdelta
  change _ = (s.multiplicity ζ : ℝ) at hp
  rw [hnone] at hp
  unfold weightedMass
  simp only [hp, Nat.cast_zero, add_zero]
  linarith

/-- Support inclusion is valid for original labelled paths, unlike resumption equality. -/
theorem pauseOne_support_subset (boundary : Set α) (s : PausedState seed)
    (A : Finset α) (w : EscapingPath seed)
    (hs : s.settled ⊆ A) (hp : ∀ p ∈ s.pending, p.position 0 ∈ A) :
    (s.pauseOne boundary w).settled ⊆ settle A w ∧
      ∀ p ∈ (s.pauseOne boundary w).pending, p.position 0 ∈ settle A w := by
  classical
  have hx : w.exitSite s.settled ∈ settle A w :=
    settle_mono w hs (Finset.mem_insert_self _ _)
  by_cases hb : w.exitSite s.settled ∈ boundary
  · simp only [pauseOne, if_pos hb]
    refine ⟨fun z hz => subset_settle A w (hs hz), ?_⟩
    intro p hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact subset_settle A w (hp p hmem)
    · have he : p = w.suffix (w.exitTime s.settled) := by simpa using hmem
      subst p
      simpa [suffix_start, exitSite] using hx
  · simp only [pauseOne, if_neg hb]
    exact ⟨settle_mono w hs, fun p hmem => subset_settle A w (hp p hmem)⟩

theorem pauseAll_support_subset (boundary : Set α) (s : PausedState seed)
    (A : Finset α) (ws : List (EscapingPath seed))
    (hs : s.settled ⊆ A) (hp : ∀ p ∈ s.pending, p.position 0 ∈ A) :
    (s.pauseAll boundary ws).settled ⊆ grow A ws ∧
      ∀ p ∈ (s.pauseAll boundary ws).pending, p.position 0 ∈ grow A ws := by
  induction ws generalizing s A with
  | nil => exact ⟨hs, hp⟩
  | cons w ws ih =>
      have h := pauseOne_support_subset boundary s A w hs hp
      exact ih (s.pauseOne boundary w) (settle A w) h.1 h.2

end PausedState

/-- Summing normalized hitting kernels over h complete positive layers gives h. -/
theorem complete_layer_score {V : Type*} [Fintype V]
    (H : V × ℤ → ℝ) (h : ℕ)
    (hrow : ∀ j < h, (∑ x : V, H (x,(j:ℤ)+1)) = 1) :
    (∑ j ∈ Finset.range h, ∑ x : V, H (x,(j:ℤ)+1)) = (h:ℝ) := by
  calc
    _ = ∑ _j ∈ Finset.range h, (1:ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hrow j (Finset.mem_range.mp hj)
    _ = _ := by simp

end
end IdlaCyl
