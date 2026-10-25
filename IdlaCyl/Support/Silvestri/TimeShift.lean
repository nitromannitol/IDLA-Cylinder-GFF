module

public import IdlaCyl.Support.Exit
public import IdlaCyl.Support.Outer.ResumeKernels

@[expose] public section

/-!
# Exit sites are invariant under time shifts

Two trajectories `ω` and `ω'` that satisfy `ω (a + n) = ω' (b + n)` for all `n`, and that
stay inside an occupied set `S` before the times `a` and `b`, leave `S` at the same site
as soon as `ω` exits `S`.  The two walks first leave `S` at the times `a + n₀` and `b + n₀`
for the same index `n₀` of the shared continuation, so their exit sites coincide.

The file also records two facts about the finite extensions of the flat seed `R₀`:
`resumeSeed B G` lies below a height bound that depends on the finite set `G`, and a
trajectory that climbs above such a bound leaves `resumeSeed B G`.

Main results: `resumeSeed_subset_bounded`, `exitTime'_ne_top_of_unbounded`,
`exitSite'_eq_of_shift`.
-/

namespace IdlaCyl.Silvestri

open MeasureTheory

variable (B : Base)

/-- Every finite extension of the flat seed lies below a common integer height. -/
theorem resumeSeed_subset_bounded (G : ResumeFinite B) :
    ∃ M : ℤ, ∀ p ∈ resumeSeed B G, p.2 ≤ M := by
  refine ⟨∑ p ∈ G.1, |p.2|, fun p hp => ?_⟩
  rcases (show p ∈ R B 0 ∨ p ∈ (G.1 : Set (Site B)) from hp) with hp | hp
  · have h0 : ((p.2 : ℤ) : ℝ) ≤ 0 := hp
    have h0' : p.2 ≤ 0 := by exact_mod_cast h0
    exact h0'.trans (Finset.sum_nonneg fun q _ => abs_nonneg _)
  · exact (le_abs_self p.2).trans
      (Finset.single_le_sum (f := fun q : Site B => |q.2|) (fun q _ => abs_nonneg _) hp)

/-- A walk that reaches a height above a bound `M` on `S` leaves `S`. -/
theorem exitTime'_ne_top_of_unbounded {S : Set (Site B)} {M : ℤ} (hS : ∀ p ∈ S, p.2 ≤ M)
    {X : ℕ → Site B} (hX : ∃ n, M < (X n).2) : exitTime' B S X ≠ ⊤ := by
  obtain ⟨n, hn⟩ := hX
  intro htop
  have hmem : X n ∈ S := not_not.mp (hittingAfter_eq_top_iff.mp htop n (Nat.zero_le n))
  exact absurd (hS _ hmem) (not_le.mpr hn)

/-- If a walk first leaves `S` at time `i` and stayed in `S` before, its exit time is `i`. -/
theorem exitTime'_eq_of_first {S : Set (Site B)} {X : ℕ → Site B} {i : ℕ}
    (hout : X i ∉ S) (hin : ∀ j < i, X j ∈ S) : exitTime' B S X = (i : ℕ∞) := by
  refine le_antisymm (hittingAfter_le_of_mem (u := fun (k : ℕ) (Y : ℕ → Site B) => Y k)
    (s := Sᶜ) (n := 0) (i := i) (ω := X) (Nat.zero_le i) hout) ?_
  by_contra hlt
  obtain ⟨j, ⟨-, hji⟩, hj⟩ := hittingAfter_lt_iff.mp (not_le.mp hlt)
  exact absurd (hin j hji) hj

/-- **Exit sites do not see time shifts.**  If `ω (a + n) = ω' (b + n)` for all `n`, both
walks stay in `S` before times `a` and `b`, and `ω` exits `S`, then both walks leave `S`
at the same site.  The prefix conditions are needed because a visit outside `S` before
the shift is read as the exit.  The finiteness of the exit is needed because otherwise
`exitSite'` reads the junk index `untopA ⊤`, where nothing forces the two walks to agree. -/
theorem exitSite'_eq_of_shift {S : Set (Site B)} {ω ω' : ℕ → Site B} {a b : ℕ}
    (hpre : ∀ k < a, ω k ∈ S) (hpre' : ∀ k < b, ω' k ∈ S)
    (hshift : ∀ n : ℕ, ω (a + n) = ω' (b + n)) (hfin : exitTime' B S ω ≠ ⊤) :
    exitSite' B S ω = exitSite' B S ω' := by
  classical
  -- `ω` leaves `S` somewhere, necessarily at or after time `a`
  have hex : ∃ j, ω j ∉ S := by
    by_contra h
    push Not at h
    exact hfin (hittingAfter_eq_top_iff.mpr fun j _ hj => hj (h j))
  obtain ⟨j, hj⟩ := hex
  have haj : a ≤ j := not_lt.mp fun hlt => hj (hpre j hlt)
  -- the first exit of the shifted continuation, which both walks share
  have hP : ∃ n, ω' (b + n) ∉ S :=
    ⟨j - a, by rw [← hshift, Nat.add_sub_of_le haj]; exact hj⟩
  have hspec := Nat.find_spec hP
  have hmin : ∀ m < Nat.find hP, ω' (b + m) ∈ S :=
    fun m hm => not_not.mp (Nat.find_min hP hm)
  have hA : exitTime' B S ω = ((a + Nat.find hP : ℕ) : ℕ∞) := by
    refine exitTime'_eq_of_first B ?_ ?_
    · rw [hshift]
      exact hspec
    · intro k hk
      by_cases hka : k < a
      · exact hpre k hka
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hka)
        rw [hshift]
        exact hmin m (by omega)
  have hB : exitTime' B S ω' = ((b + Nat.find hP : ℕ) : ℕ∞) := by
    refine exitTime'_eq_of_first B hspec ?_
    intro k hk
    by_cases hkb : k < b
    · exact hpre' k hkb
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hkb)
      exact hmin m (by omega)
  show ω (WithTop.untopA (exitTime' B S ω)) = ω' (WithTop.untopA (exitTime' B S ω'))
  rw [hA, hB]
  exact hshift _

end IdlaCyl.Silvestri
