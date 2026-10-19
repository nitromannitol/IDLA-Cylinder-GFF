import IdlaCyl.Support.Silvestri.TimeShift
import IdlaCyl.Support.Outer.ResumeGrowth
import IdlaCyl.Support.CanonicalIdla

/-!
# Pathwise success of a pair of walks, and the deterministic induction

Two infinite paths `ω`, `ω' : ℕ → Site B` are merged below a height `H` when they agree
after finitely many steps, and each of them stays in the half-cylinder `R B H` before the
time at which it joins the other. `pairGood B H ω ω'` adds that both paths reach every
integer height, so that both exit every finite extension of the flat seed.

The file proves the following.

* `MergedBelow.mono` and `pairGood.mono`: both predicates are monotone in the height.
* `resumeGrow_eq_of_success`: if the seed contains `R B H`, and for every walker `t < T`
  the paths `ω t` and `ω' t` are good, then the finite extensions of the seed built from
  `ω` and from `ω'` agree up to time `T`. The induction uses only the exit sites of the
  two paths from the same occupied set, so no measure theory enters.
-/

namespace IdlaCyl.Silvestri

/-- The two paths `ω`, `ω'` are merged below the height `H`: after the shifts `a` and `b`
they coincide, and each path stays in `R B H` before its shift time. -/
def MergedBelow (B : Base) (H : ℝ) (ω ω' : ℕ → Site B) : Prop :=
  ∃ a b : ℕ, (∀ n, ω (a + n) = ω' (b + n)) ∧ (∀ k < a, ω k ∈ R B H) ∧
    (∀ k < b, ω' k ∈ R B H)

/-- The pathwise success event of a pair of walks below the height `H`: the paths are merged
below `H`, and both of them reach every integer height. The unboundedness clauses make each
path leave every finite extension of the seed. -/
def pairGood (B : Base) (H : ℝ) (ω ω' : ℕ → Site B) : Prop :=
  MergedBelow B H ω ω' ∧ (∀ M : ℤ, ∃ n, M < (ω n).2) ∧ (∀ M : ℤ, ∃ n, M < (ω' n).2)

/-- Merging below a height persists when the height increases. -/
theorem MergedBelow.mono {B : Base} {H H' : ℝ} (hH : H ≤ H') {ω ω' : ℕ → Site B}
    (h : MergedBelow B H ω ω') : MergedBelow B H' ω ω' := by
  obtain ⟨a, b, hshift, hpre, hpre'⟩ := h
  exact ⟨a, b, hshift, fun k hk => R_mono hH (hpre k hk), fun k hk => R_mono hH (hpre' k hk)⟩

/-- The pathwise success event persists when the height increases. -/
theorem pairGood.mono {B : Base} {H H' : ℝ} (hH : H ≤ H') {ω ω' : ℕ → Site B}
    (h : pairGood B H ω ω') : pairGood B H' ω ω' := by
  obtain ⟨hm, hu, hu'⟩ := h
  exact ⟨hm.mono hH, hu, hu'⟩

/-- **Deterministic induction.** If the seed `F` contains the half-cylinder `R B H`, and for
every walker `t < T` the paths `ω t` and `ω' t` are good below `H`, then the finite
extensions of the seed built by the two families of paths agree at every time `t ≤ T`.
At each step the seed contains `R B H`, both paths leave that seed at the same site by the
time shift, and the two extensions are then the same by the induction hypothesis. -/
theorem resumeGrow_eq_of_success (B : Base) (T : ℕ) (F : ResumeFinite B) (H : ℝ)
    (hF : R B H ⊆ resumeSeed B F) (ω ω' : TrajSeq B)
    (hgood : ∀ t < T, pairGood B H (ω t) (ω' t)) :
    ∀ t ≤ T, resumeGrow B F ω t = resumeGrow B F ω' t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have ih' : resumeGrow B F ω t = resumeGrow B F ω' t := ih (by omega)
    obtain ⟨⟨a, b, hshift, hpre, hpre'⟩, hub, -⟩ := hgood t (by omega)
    -- the seed at time `t` contains the half-cylinder `R B H`
    have hsub : R B H ⊆ resumeSeed B (resumeGrow B F ω t) := by
      rw [resumeSeed_grow]
      have h0 : resumeSeed B F ⊆ clusterFrom B (resumeSeed B F) ω t :=
        clusterFrom_mono B (resumeSeed B F) ω (Nat.zero_le t)
      exact hF.trans h0
    -- the seed is bounded, and the first path leaves it, so the exit time is finite
    obtain ⟨M, hM⟩ := resumeSeed_subset_bounded B (resumeGrow B F ω t)
    have hfin : exitTime' B (resumeSeed B (resumeGrow B F ω t)) (ω t) ≠ ⊤ :=
      exitTime'_ne_top_of_unbounded B hM (hub M)
    have hpreS : ∀ k < a, ω t k ∈ resumeSeed B (resumeGrow B F ω t) :=
      fun k hk => hsub (hpre k hk)
    have hpreS' : ∀ k < b, ω' t k ∈ resumeSeed B (resumeGrow B F ω t) :=
      fun k hk => hsub (hpre' k hk)
    have hsite : exitSite' B (resumeSeed B (resumeGrow B F ω t)) (ω t) =
        exitSite' B (resumeSeed B (resumeGrow B F ω t)) (ω' t) :=
      exitSite'_eq_of_shift B hpreS hpreS' hshift hfin
    show resumeInsert B (resumeGrow B F ω t)
        (exitSite' B (resumeSeed B (resumeGrow B F ω t)) (ω t)) =
      resumeInsert B (resumeGrow B F ω' t)
        (exitSite' B (resumeSeed B (resumeGrow B F ω' t)) (ω' t))
    rw [hsite, ih']

end IdlaCyl.Silvestri
