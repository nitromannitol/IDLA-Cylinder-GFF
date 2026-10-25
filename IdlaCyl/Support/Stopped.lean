module

/-
`Ā_h(t)`, IDLA with particles halted on reaching height `h`
(`tex:1147-1152`).

`Ā_h(0) = R_0`, and `(X̄_{t+1},Ȳ_{t+1})` is the exit location from
`Ā_h(t) ∩ R_{h-1}`.  The key facts — `Ā_h(t) ⊆ R_h`, `eq:monotone_stop`, and
`Ā_h(t) ⊆ A(t)` — are all *pathwise*, from `exitSite'_mem_of_subset`, with no
coupling and no abelian property.
-/
public import IdlaCyl.Support.Admissible
public import IdlaCyl.Support.Exit

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IdlaCyl

variable (B : Base)

/-- `Ā_h(t)`, IDLA with particles halted on reaching height `h` (`tex:1147-1152`). -/
noncomputable def stoppedCluster (B : Base) (h : ℤ) (ω : TrajSeq B) : ℕ → Set (Site B)
  | 0     => R B 0
  | t + 1 => stoppedCluster B h ω t ∪
               {exitSite' B (stoppedCluster B h ω t ∩ R B ((h : ℝ) - 1)) (ω t)}

noncomputable def stoppedSettleSite (B : Base) (h : ℤ) (ω : TrajSeq B) (t : ℕ) : Site B :=
  exitSite' B (stoppedCluster B h ω t ∩ R B ((h : ℝ) - 1)) (ω t)

/-
`stoppedCluster_subset` and `stoppedSettleSite_ver_le` are FALSE without a
starting-site hypothesis (erratum E16): `CylAdmissible` bounds only consecutive
steps, not the starting site `ω j 0`, but the paper's particles start
"uniformly on `{(x,0):x∈V_N}`" (`tex:1149-1150`).  Counterexample: the base walk
is lazy (`Base.P x x = 1/2 > 0`), so the constant trajectory
`ω 0 := fun _ => (B.pt, 10^6)` is `CylAdmissible`; with `h = 1` its immediate
exit from `R B 0` is `(B.pt, 10^6) ∉ R B 1`.  Both statements therefore carry
`h0 : ∀ j, ω j 0 ∈ R B 0`, which holds a.e. under `idlaMeasure`.
-/

/-- "It is ensured by the definition that `Ā_h(t) ⊆ R_h`" (`tex:1151`). -/
theorem stoppedCluster_subset (B : Base) (h : ℤ) (hh : 1 ≤ h) (ω : TrajSeq B)
    (hadm : ∀ j, CylAdmissible B (ω j)) (h0 : ∀ j, ω j 0 ∈ R B 0)
    (hfin : ∀ t, exitTime' B (stoppedCluster B h ω t ∩ R B ((h : ℝ) - 1)) (ω t) ≠ ⊤)
    (t : ℕ) :
    stoppedCluster B h ω t ⊆ R B (h : ℝ) := by
  induction t with
  | zero =>
    intro q hq
    exact R_mono (by exact_mod_cast (by omega : (0 : ℤ) ≤ h)) hq
  | succ n ih =>
    intro q hq
    rw [show stoppedCluster B h ω (n + 1)
        = stoppedCluster B h ω n ∪
          {exitSite' B (stoppedCluster B h ω n ∩ R B ((h : ℝ) - 1)) (ω n)} from rfl] at hq
    rcases hq with hq | rfl
    · exact ih hq
    · set S : Set (Site B) := stoppedCluster B h ω n ∩ R B ((h : ℝ) - 1) with hS
      have hτ : exitTime' B S (ω n) ≠ ⊤ := hfin n
      set k : ℕ := (exitTime' B S (ω n)).untopA with hkdef
      have hmin : ∀ j, j < k → (ω n) j ∈ S := by
        intro j hj
        by_contra hjs
        have hle : exitTime' B S (ω n) ≤ (j : ℕ∞) :=
          MeasureTheory.hittingAfter_le_of_mem
            (u := fun (k : ℕ) (Y : ℕ → Site B) => Y k) (s := Sᶜ) (n := 0)
            (i := j) (ω := ω n) (Nat.zero_le j) hjs
        have : k ≤ j := (WithTop.untopA_le_iff hτ).mpr hle
        omega
      have hsite : exitSite' B S (ω n) = (ω n) k := rfl
      rw [hsite]
      have hbase : R B 0 ⊆ R B (h : ℝ) :=
        R_mono (by exact_mod_cast (by omega : (0 : ℤ) ≤ h))
      have hpath : ∀ j ≤ k, (ω n) j ∈ R B (h : ℝ) := by
        intro j
        induction j with
        | zero => intro _; exact hbase (h0 n)
        | succ i _ =>
          intro hi
          have hik : i < k := by omega
          have hprev := hmin i hik
          have hprevR : (((ω n) i).2 : ℝ) ≤ (h : ℝ) - 1 := hprev.2
          have hprevZ : ((ω n) i).2 ≤ h - 1 := by
            have hcast : (((ω n) i).2 : ℝ) ≤ ((h - 1 : ℤ) : ℝ) := by
              push_cast
              linarith only [hprevR]
            exact_mod_cast hcast
          have hstep := CylAdmissible.ver_step B (hadm n) i
          have hle_h : ((ω n) (i + 1)).2 ≤ h := by
            rcases hstep with h' | h' | h' <;> omega
          show (((ω n) (i + 1)).2 : ℝ) ≤ (h : ℝ)
          exact_mod_cast hle_h
      exact hpath k le_rfl

theorem stoppedSettleSite_ver_le (B : Base) (h : ℤ) (hh : 1 ≤ h) (ω : TrajSeq B)
    (hadm : ∀ j, CylAdmissible B (ω j)) (h0 : ∀ j, ω j 0 ∈ R B 0)
    (hfin : ∀ t, exitTime' B (stoppedCluster B h ω t ∩ R B ((h : ℝ) - 1)) (ω t) ≠ ⊤)
    (t : ℕ) :
    (stoppedSettleSite B h ω t).2 ≤ h := by
  exact Int.cast_le.mp
    (mem_R.mp (stoppedCluster_subset B h hh ω hadm h0 hfin (t + 1) (Or.inr rfl)))

/-- `eq:monotone_stop` (`tex:1156`), pathwise — no coupling. -/
theorem stoppedCluster_mono_height (B : Base) {h₁ h₂ : ℤ} (hh : h₁ ≤ h₂) (ω : TrajSeq B)
    (hfin : ∀ t, exitTime' B (stoppedCluster B h₂ ω t ∩ R B ((h₂ : ℝ) - 1)) (ω t) ≠ ⊤)
    (t : ℕ) : stoppedCluster B h₁ ω t ⊆ stoppedCluster B h₂ ω t := by
  induction t with
  | zero => exact Set.Subset.rfl
  | succ n ih =>
    have hR : R B ((h₁ : ℝ) - 1) ⊆ R B ((h₂ : ℝ) - 1) := R_mono (by
      have h' : h₁ - 1 ≤ h₂ - 1 := by omega
      exact_mod_cast h')
    have hsub : stoppedCluster B h₁ ω n ∩ R B ((h₁ : ℝ) - 1)
        ⊆ stoppedCluster B h₂ ω n ∩ R B ((h₂ : ℝ) - 1) :=
      Set.inter_subset_inter ih hR
    have hmem := exitSite'_mem_of_subset B hsub (hfin n)
    have hS₂ : stoppedCluster B h₂ ω n ∩ R B ((h₂ : ℝ) - 1) ⊆ stoppedCluster B h₂ ω n :=
      Set.inter_subset_left
    have hgoal : exitSite' B (stoppedCluster B h₁ ω n ∩ R B ((h₁ : ℝ) - 1)) (ω n)
        ∈ stoppedCluster B h₂ ω n
            ∪ {exitSite' B (stoppedCluster B h₂ ω n ∩ R B ((h₂ : ℝ) - 1)) (ω n)} := by
      rcases hmem with hmem | hmem
      · exact Or.inl (hS₂ hmem)
      · exact Or.inr hmem
    exact Set.union_subset (ih.trans Set.subset_union_left) (Set.singleton_subset_iff.mpr hgoal)

/-- `Ā_h(t) ⊆ A(t)` (`tex:1153-1155`), pathwise. -/
theorem stoppedCluster_subset_clusterTraj (B : Base) (h : ℤ) (ω : TrajSeq B)
    (hfin : ∀ t, exitTime' B (clusterTraj B ω t) (ω t) ≠ ⊤) (t : ℕ) :
    stoppedCluster B h ω t ⊆ clusterTraj B ω t := by
  induction t with
  | zero => exact Set.Subset.rfl
  | succ n ih =>
    have hsub : stoppedCluster B h ω n ∩ R B ((h : ℝ) - 1) ⊆ clusterTraj B ω n :=
      Set.inter_subset_left.trans ih
    have hmem := exitSite'_mem_of_subset B hsub (hfin n)
    have hclusterTraj_succ : clusterTraj B ω (n + 1)
        = clusterTraj B ω n ∪ {exitSite' B (clusterTraj B ω n) (ω n)} :=
      clusterFrom_succ B (R B 0) ω n
    rw [hclusterTraj_succ]
    exact Set.union_subset (ih.trans Set.subset_union_left) (Set.singleton_subset_iff.mpr hmem)

/-- A particle that halts strictly below `h` is fresh: the identification of the
settle sites used in the pathwise decomposition at `tex:1236-1240`. -/
theorem stoppedSettleSite_notMem_of_lt (B : Base) (h : ℤ) (ω : TrajSeq B) (t : ℕ)
    (hfin : exitTime' B (stoppedCluster B h ω t ∩ R B ((h : ℝ) - 1)) (ω t) ≠ ⊤)
    (hlt : (stoppedSettleSite B h ω t).2 < h) :
    stoppedSettleSite B h ω t ∉ stoppedCluster B h ω t := by
  intro hmemA
  have hnotS : stoppedSettleSite B h ω t
      ∉ stoppedCluster B h ω t ∩ R B ((h : ℝ) - 1) :=
    exitSite'_mem_compl B _ hfin
  have hz : (stoppedSettleSite B h ω t).2 ≤ h - 1 := by omega
  have hR : stoppedSettleSite B h ω t ∈ R B ((h : ℝ) - 1) := mem_R.mpr (by exact_mod_cast hz)
  exact hnotS ⟨hmemA, hR⟩

end IdlaCyl
