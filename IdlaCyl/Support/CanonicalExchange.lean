import IdlaCyl.Support.Discrepancy

/-!
The deterministic contraction engine for `pr:exchange`, `tex:770-782`.

A shared trajectory preserves containment up to one exceptional site in each
direction. This uses first-exit times in the original labelled order. If a
trajectory never exits, its selected stopped value is already occupied and
the cluster stays unchanged.
-/

namespace IdlaCyl.CanonicalExchange

variable (B : Base)

/-- A never-exiting trajectory has its selected stopped value in the set. -/
theorem exitSite_mem_of_top {A : Set (Site B)} {X : ℕ → Site B}
    (h : exitTime' B A X = ⊤) : exitSite' B A X ∈ A := by
  have hall := MeasureTheory.hittingAfter_eq_top_iff.mp h
  exact not_not.mp (hall (WithTop.untopA (exitTime' B A X)) (Nat.zero_le _))

/-- The canonical growth step adds nothing on a never-exiting trajectory. -/
theorem step_eq_self_of_top {A : Set (Site B)} {X : ℕ → Site B}
    (h : exitTime' B A X = ⊤) : A ∪ {exitSite' B A X} = A := by
  exact Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr (exitSite_mem_of_top B h))

/-- The earlier of two first exits lies in the set exited later, even if
the latter exit time is infinite. -/
theorem exitSite_mem_of_lt {A C : Set (Site B)} {X : ℕ → Site B}
    (h : exitTime' B A X < exitTime' B C X) : exitSite' B A X ∈ C := by
  by_contra hn
  have hle : exitTime' B C X ≤ ((WithTop.untopA (exitTime' B A X) : ℕ) : ℕ∞) :=
    MeasureTheory.hittingAfter_le_of_mem
      (u := fun (k : ℕ) (Y : ℕ → Site B) => Y k) (s := Cᶜ) (n := 0)
      (i := WithTop.untopA (exitTime' B A X)) (ω := X) (Nat.zero_le _) hn
  have hfin : exitTime' B A X ≠ ⊤ := (lt_of_lt_of_le h le_top).ne
  have hcoe : ((WithTop.untopA (exitTime' B A X) : ℕ) : ℕ∞) = exitTime' B A X := by
    rw [WithTop.untopA_eq_untop hfin]
    exact WithTop.coe_untop _ hfin
  rw [hcoe] at hle
  exact (not_lt_of_ge hle) h

/-- A shared path preserves a directed difference supported on one site. -/
theorem step_subset_union_singleton (A C : Set (Site B)) (X : ℕ → Site B)
    (x : Site B) (hAC : A ⊆ C ∪ {x}) :
    ∃ y : Site B,
      A ∪ {exitSite' B A X} ⊆ (C ∪ {exitSite' B C X}) ∪ {y} := by
  by_cases htop : exitTime' B A X = ⊤
  · rw [step_eq_self_of_top B htop]
    exact ⟨x, hAC.trans (Set.union_subset_union_left {x} Set.subset_union_left)⟩
  rcases lt_trichotomy (exitTime' B A X) (exitTime' B C X) with hlt | heq | hgt
  · refine ⟨x, ?_⟩
    rintro p (hp | hp)
    · rcases hAC hp with hpC | hpx
      · exact Or.inl (Or.inl hpC)
      · exact Or.inr hpx
    · have hpC : p ∈ C := (Set.mem_singleton_iff.mp hp) ▸ exitSite_mem_of_lt B hlt
      exact Or.inl (Or.inl hpC)
  · have hsite : exitSite' B A X = exitSite' B C X := by
      change X (WithTop.untopA (exitTime' B A X)) =
        X (WithTop.untopA (exitTime' B C X))
      rw [heq]
    refine ⟨x, ?_⟩
    rintro p (hp | hp)
    · rcases hAC hp with hpC | hpx
      · exact Or.inl (Or.inl hpC)
      · exact Or.inr hpx
    · exact Or.inl (Or.inr (hsite ▸ hp))
  · have hmem : exitSite' B C X ∈ A := exitSite_mem_of_lt B hgt
    have hnot : exitSite' B C X ∉ C :=
      exitSite'_mem_compl B C ((lt_of_lt_of_le hgt le_top).ne)
    have hx : exitSite' B C X = x := by
      rcases hAC hmem with hpC | hpx
      · exact False.elim (hnot hpC)
      · exact Set.mem_singleton_iff.mp hpx
    refine ⟨exitSite' B A X, ?_⟩
    rintro p (hp | hp)
    · rcases hAC hp with hpC | hpx
      · exact Or.inl (Or.inl hpC)
      · exact Or.inl (Or.inr (hx.symm ▸ hpx))
    · exact Or.inr hp

/-- Changing at most one of the consumed coordinates leaves each directed
cluster difference supported on one site; the seed may be arbitrary. -/
theorem clusterFrom_subset_union_singleton (S : Set (Site B)) (ω ω' : TrajSeq B)
    (T j : ℕ) (h : ∀ i, i < T → i ≠ j → ω i = ω' i) :
    ∃ x : Site B, clusterFrom B S ω T ⊆ clusterFrom B S ω' T ∪ {x} := by
  induction T with
  | zero => exact ⟨(B.pt, 0), Set.subset_union_left⟩
  | succ n ih =>
    by_cases hnj : n = j
    · have hprev : clusterFrom B S ω n = clusterFrom B S ω' n :=
        clusterFrom_congr B S ω ω' (fun i hi => h i (by omega) (by omega))
      refine ⟨exitSite' B (clusterFrom B S ω n) (ω n), ?_⟩
      rw [clusterFrom_succ, clusterFrom_succ, hprev]
      exact Set.union_subset_union_left _ Set.subset_union_left
    · obtain ⟨x, hx⟩ := ih (fun i hi hij => h i (by omega) hij)
      rw [clusterFrom_succ, clusterFrom_succ, h n (by omega) hnj]
      exact step_subset_union_singleton B _ _ _ x hx

/-- Each directed difference has cardinality at most one. -/
theorem clusterFrom_sdiff_encard_le_one (S : Set (Site B)) (ω ω' : TrajSeq B)
    (T j : ℕ) (h : ∀ i, i < T → i ≠ j → ω i = ω' i) :
    Set.encard (clusterFrom B S ω T \ clusterFrom B S ω' T) ≤ 1 := by
  obtain ⟨x, hx⟩ := clusterFrom_subset_union_singleton B S ω ω' T j h
  have hsub : clusterFrom B S ω T \ clusterFrom B S ω' T ⊆ {x} := by
    intro p hp
    exact (hx hp.1).resolve_left hp.2
  exact (Set.encard_mono hsub).trans_eq (Set.encard_singleton x)

/-- The positive-height clusters differ at at most two sites after changing
at most one of the first `T` trajectories. Unused coordinates are unrestricted. -/
theorem clusterPlusTraj_symmDiff_encard_le_two (ω ω' : TrajSeq B) (T j : ℕ)
    (h : ∀ i, i < T → i ≠ j → ω i = ω' i) :
    Set.encard (symmDiff (clusterPlusTraj B ω T) (clusterPlusTraj B ω' T)) ≤ 2 := by
  have hforward := clusterFrom_sdiff_encard_le_one B (R B 0) ω ω' T j h
  have hbackward := clusterFrom_sdiff_encard_le_one B (R B 0) ω' ω T j
    (fun i hi hij => (h i hi hij).symm)
  have hsub (a b : TrajSeq B) :
      clusterPlusTraj B a T \ clusterPlusTraj B b T ⊆
        clusterFrom B (R B 0) a T \ clusterFrom B (R B 0) b T := by
    rintro p ⟨hp, hn⟩
    exact ⟨hp.1, fun hb => hn ⟨hb, hp.2⟩⟩
  rw [Set.symmDiff_def]
  calc
    _ ≤ Set.encard (clusterPlusTraj B ω T \ clusterPlusTraj B ω' T) +
        Set.encard (clusterPlusTraj B ω' T \ clusterPlusTraj B ω T) :=
      Set.encard_union_le _ _
    _ ≤ 1 + 1 := add_le_add ((Set.encard_mono (hsub ω ω')).trans hforward)
      ((Set.encard_mono (hsub ω' ω)).trans hbackward)
    _ = 2 := by norm_num

end IdlaCyl.CanonicalExchange
