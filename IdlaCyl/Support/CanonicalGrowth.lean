/-
The upper part of the canonical cluster grows by one site per walk.

`tex:265`: if every walk so far exits the cluster in finite time, then
`|A_+(t)| = t`, where `A_+(t)` is the part of the cluster strictly above level `0`.
-/
import IdlaCyl.Support.CanonicalIdla
import IdlaCyl.Support.Exit
import IdlaCyl.Support.CanonicalExit

namespace IdlaCyl

/-- One step of the canonical cluster. -/
theorem clusterTraj_plus_ncard_of_succ (B : Base) (ω : TrajSeq B) (t : ℕ) :
    clusterTraj B ω (t + 1) = clusterTraj B ω t ∪ {settleSite B ω t} :=
  clusterFrom_succ B (R B 0) ω t

/-- The flat seed `R B 0` is contained in every cluster. -/
theorem clusterTraj_plus_ncard_of_seed_subset (B : Base) (ω : TrajSeq B) (t : ℕ) :
    R B 0 ⊆ clusterTraj B ω t :=
  clusterFrom_mono B (R B 0) ω (Nat.zero_le t)

/-- A walk that exits the cluster in finite time settles strictly above level `0`, at a
site outside the cluster. -/
theorem clusterTraj_plus_ncard_of_settle (B : Base) (ω : TrajSeq B) (t : ℕ)
    (h : exitTime' B (clusterTraj B ω t) (ω t) ≠ ⊤) :
    settleSite B ω t ∉ clusterTraj B ω t ∧ 1 ≤ (settleSite B ω t).2 := by
  have hnot : settleSite B ω t ∉ clusterTraj B ω t := exitSite'_mem_compl B _ h
  refine ⟨hnot, ?_⟩
  have hR : settleSite B ω t ∉ R B 0 := fun hm =>
    hnot (clusterTraj_plus_ncard_of_seed_subset B ω t hm)
  rw [mem_R, not_le] at hR
  have hpos : (0 : ℤ) < (settleSite B ω t).2 := by exact_mod_cast hR
  omega

/-- The part of the cluster above level `0` is finite. -/
theorem clusterTraj_plus_ncard_of_finite (B : Base) (ω : TrajSeq B) (t : ℕ) :
    (clusterTraj B ω t ∩ {p : Site B | 1 ≤ p.2}).Finite := by
  refine (Finset.finite_toSet ((Finset.range t).image (settleSite B ω))).subset ?_
  intro p hp
  rw [clusterTraj_eq_union] at hp
  rcases hp with ⟨hp | hp, hp1⟩
  · exfalso
    have h0 : (p.2 : ℝ) ≤ 0 := hp
    have h1 : (1 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast hp1
    linarith
  · exact hp

theorem clusterTraj_plus_ncard_of (B : Base) (ω : TrajSeq B) (t : ℕ)
    (h : ∀ j < t, exitTime' B (clusterTraj B ω j) (ω j) ≠ ⊤) :
    (clusterTraj B ω t ∩ {p : Site B | 1 ≤ p.2}).ncard = t := by
  induction t with
  | zero =>
    have hempty : clusterTraj B ω 0 ∩ {p : Site B | 1 ≤ p.2} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
      obtain ⟨hp0, hp1⟩ := hp
      have h0 : (p.2 : ℝ) ≤ 0 := hp0
      have h1 : (1 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast hp1
      linarith
    rw [hempty, Set.ncard_empty]
  | succ n ih =>
    have ih' := ih fun j hj => h j (by omega)
    obtain ⟨hnot, hpos⟩ := clusterTraj_plus_ncard_of_settle B ω n (h n (by omega))
    have hset : clusterTraj B ω (n + 1) ∩ {p : Site B | 1 ≤ p.2}
        = insert (settleSite B ω n) (clusterTraj B ω n ∩ {p : Site B | 1 ≤ p.2}) := by
      rw [clusterTraj_plus_ncard_of_succ]
      ext p
      constructor
      · rintro ⟨hp | hp, hp1⟩
        · exact Or.inr ⟨hp, hp1⟩
        · exact Or.inl hp
      · rintro (rfl | ⟨hp, hp1⟩)
        · exact ⟨Or.inr rfl, hpos⟩
        · exact ⟨Or.inl hp, hp1⟩
    rw [hset, Set.ncard_insert_of_notMem (fun hm => hnot hm.1)
      (clusterTraj_plus_ncard_of_finite B ω n), ih']

/-- `|A_+(t)| = t` almost surely (`tex:265`, `tex:339`): every walk exits the cluster
(`exitTraj_ae_finite`), so the cluster gains one site above level `0` per step. -/
theorem clusterTraj_plus_ncard (B : Base) (t : ℕ) :
    ∀ᵐ ω ∂idlaMeasure B, (clusterTraj B ω t ∩ {p : Site B | 1 ≤ p.2}).ncard = t := by
  have hall : ∀ᵐ ω ∂idlaMeasure B, ∀ j, exitTime' B (clusterTraj B ω j) (ω j) ≠ ⊤ :=
    MeasureTheory.ae_all_iff.mpr fun j => exitTraj_ae_finite B j
  filter_upwards [hall] with ω hω
  exact clusterTraj_plus_ncard_of B ω t fun j _ => hω j

end IdlaCyl
