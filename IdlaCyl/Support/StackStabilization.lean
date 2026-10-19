import IdlaCyl.Support.StackPrefix

set_option autoImplicit false

/-!
# Constructed two-stage stabilization

This file combines the termination and least-action arguments. In particular,
neither a paused stable schedule nor a resumed stable schedule is supplied as
an assumption. Both are constructed from the explicit exiting-tail condition.
For arbitrary finite instruction tables, completion supplies that condition.
-/

namespace IdlaCyl.Stack

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem exitingTails_mono_active (route : Routing V) (cutoff : V → ℕ)
    {small large : Set V} (hsub : small ⊆ large)
    (h : ExitingTails route large cutoff) : ExitingTails route small cutoff := by
  intro x hx n hn hdest
  exact h x (hsub hx) n hn (hsub hdest)

/-- Pausing, finishing, and ordinary stabilization all exist and agree. -/
theorem two_stage_stabilization_exists (route : Routing V) (initial capacity : V → ℤ)
    {paused full : Set V} (hregion : paused ⊆ full) (cutoff u : V → ℕ)
    (htail : ExitingTails route full cutoff)
    (hcap : ∀ x ∈ full, 0 ≤ capacity x)
    (hu : ∀ x, 0 ≤ particles route initial u x) :
    ∃ pfx continuation ordinary : List V,
      LegalFrom route initial capacity paused u pfx ∧
      Stable route initial capacity paused (run u pfx) ∧
      LegalFrom route initial capacity full (run u pfx) continuation ∧
      Stable route initial capacity full (run (run u pfx) continuation) ∧
      LegalFrom route initial capacity full u ordinary ∧
      Stable route initial capacity full (run u ordinary) ∧
      run (run u pfx) continuation = run u ordinary ∧
      particles route initial (run (run u pfx) continuation) =
        particles route initial (run u ordinary) := by
  have hcapSmall : ∀ x ∈ paused, 0 ≤ capacity x :=
    fun x hx => hcap x (hregion hx)
  obtain ⟨pfx, hp, hps⟩ := exists_legal_stabilization route initial capacity
    paused cutoff u (exitingTails_mono_active route cutoff hregion htail) hcapSmall hu
  have hnonneg := legalFrom_nonneg route initial capacity paused u pfx hcapSmall hu hp
  obtain ⟨continuation, hc, hcs⟩ := exists_legal_stabilization route initial capacity
    full cutoff (run u pfx) htail hcap hnonneg
  obtain ⟨ordinary, ho, hos⟩ := exists_legal_stabilization route initial capacity
    full cutoff u htail hcap hu
  exact ⟨pfx, continuation, ordinary, hp, hps, hc, hcs, ho, hos,
    pause_resume_odometer route initial capacity hregion u pfx continuation ordinary
      hp hc ho hcs hos,
    pause_resume_particles route initial capacity hregion u pfx continuation ordinary
      hp hc ho hcs hos⟩

/-- Arbitrary finite pfxes have a fully constructed abelian paused completion. -/
theorem completed_two_stage_stabilization_exists (route : Routing V)
    (initial capacity : V → ℤ) {paused full : Set V} (hregion : paused ⊆ full)
    (cutoff : V → ℕ) (sink : V) (hsink : sink ∉ full)
    (hcap : ∀ x ∈ full, 0 ≤ capacity x) (hinit : ∀ x, 0 ≤ initial x) :
    ∃ pfx continuation ordinary : List V,
      LegalFrom (completeRoute route cutoff sink) initial capacity paused (fun _ => 0) pfx ∧
      Stable (completeRoute route cutoff sink) initial capacity paused
        (run (fun _ => 0) pfx) ∧
      LegalFrom (completeRoute route cutoff sink) initial capacity full
        (run (fun _ => 0) pfx) continuation ∧
      Stable (completeRoute route cutoff sink) initial capacity full
        (run (run (fun _ => 0) pfx) continuation) ∧
      LegalFrom (completeRoute route cutoff sink) initial capacity full (fun _ => 0) ordinary ∧
      Stable (completeRoute route cutoff sink) initial capacity full
        (run (fun _ => 0) ordinary) ∧
      run (run (fun _ => 0) pfx) continuation = run (fun _ => 0) ordinary ∧
      particles (completeRoute route cutoff sink) initial
          (run (run (fun _ => 0) pfx) continuation) =
        particles (completeRoute route cutoff sink) initial (run (fun _ => 0) ordinary) := by
  apply two_stage_stabilization_exists (completeRoute route cutoff sink) initial capacity
    hregion cutoff (fun _ => 0)
    (completeRoute_exitingTails route full cutoff sink hsink) hcap
  intro x
  simpa using hinit x

end IdlaCyl.Stack
