/-
Lemma `le:mono-init` (`tex:1401-1405`), from Section "Maximal fluctuations bound".

The paper's own words:

  "Let $\mathcal{B}_1 \subseteq \mathcal{B}_2 \subsetneq V_N \times \bbZ$ be two
   proper subsets of the cylinder, and let $\o = (\o_1, \o_2, \ldots)$ be a
   sequence of infinite cylinder walks with prescribed starting sites. For each
   $i \in \{1, 2\}$ and $k \geq 0$, let $\Phi_k(\mathcal{B}_i)$ denote the cluster
   obtained from $\mathcal{B}_i$ after the first $k$ walks have been released and
   settled according to the usual IDLA rule (the $j$-th walk settles at the first
   site of $\o_j$ outside the current cluster). Assume that for each
   $i \in \{1, 2\}$ and each $k \geq 0$, the first exit time of $\o_{k+1}$ from
   $\Phi_k(\mathcal{B}_i)$ is almost surely finite. Then
   \[
     \Phi_k(\mathcal{B}_1) \;\subseteq\; \Phi_k(\mathcal{B}_2)
       \qquad \text{for every } k \geq 0\,.
   \]"
-/

import IdlaCyl.Support.Base
import IdlaCyl.Support.Cylinder
import IdlaCyl.Support.Idla

open MeasureTheory
open IdlaCyl

namespace IdlaCyl.Frozen

-- NEEDS: Lemma `le:mono-init` concerns IDLA on the cylinder run from an
-- *arbitrary* starting subset `𝒜ᵢ`, along a *prescribed* sequence of cylinder
-- walks. The API only runs IDLA from the flat configuration `R 0` with
-- instructions started uniformly on the layer `V_N × {0}` (`cluster`,
-- `stepWalk`, `exitSite`), so it has no notion of
--   * the cluster `Φ_k(𝒜)` obtained from a starting set `𝒜` after `k`
--     prescribed walks have settled (the paper's `Φ_k(𝒜ᵢ)`), nor
--   * the joint law of the walk sequence, which is what makes the paper's
--     "almost surely finite" meaningful.
-- We therefore do not define these; following the instructions we carry the run
-- operator `Φ` and a probability space `(Ω, μ)` for the walk drivers as
-- explicit parameters, and record the IDLA recursion (`hΦ_zero`, `hΦ_succ`,
-- with the settling site the first exit site of the walk, exactly as in the
-- text) and the almost-sure finiteness hypothesis (`haefin`) as hypotheses.
-- The walks are the trajectories `cylPath B (start k) (w ω k)`, with prescribed
-- starting sites `start k`, driven by `w ω k`; by the paper's indexing the walk
-- `ω_{k+1}` is the one released at the step from `Φ_k` to `Φ_{k+1}`.

/-! ### Helper lemmas for `le_mono_init`

The frozen statement uses the legacy `exitTime : ℕ∞` of `Support/Idla.lean`.
We only need two facts about it: it is `⊤` exactly when the walk never leaves
the set, and it is monotone in the set.  Everything else is the pathwise
single-step argument of `exitSite'_mem_of_subset` (`Support/Exit.lean`),
transcribed for the `toNat` settling map. -/

/-- The legacy exit time is `⊤` exactly when the trajectory never leaves `S`. -/
theorem le_mono_init_exitTime_eq_top_iff (B : Base) (S : Set (Site B)) (X : ℕ → Site B) :
    exitTime B S X = ⊤ ↔ ∀ n, X n ∈ S := by
  constructor
  · intro h n
    by_contra hn
    have hmem : ((n : ℕ) : ℕ∞) ∈ {k : ℕ∞ | ∃ m : ℕ, (k : ℕ∞) = m ∧ X m ∉ S} :=
      ⟨n, rfl, hn⟩
    have hle : exitTime B S X ≤ ((n : ℕ) : ℕ∞) := by
      unfold exitTime
      exact sInf_le hmem
    rw [h] at hle
    exact (not_le_of_gt (ENat.coe_lt_top n)) hle
  · intro h
    have hP : {k : ℕ∞ | ∃ m : ℕ, (k : ℕ∞) = m ∧ X m ∉ S} = ∅ := by
      ext k
      constructor
      · rintro ⟨m, rfl, hm⟩
        exact absurd (h m) hm
      · intro hk
        exact absurd hk (Set.notMem_empty k)
    unfold exitTime
    rw [hP, sInf_empty]

/-- The legacy exit time is monotone in the set: a larger set is exited no earlier. -/
theorem le_mono_init_exitTime_mono (B : Base) {S S' : Set (Site B)} (hss : S ⊆ S')
    (X : ℕ → Site B) : exitTime B S X ≤ exitTime B S' X := by
  unfold exitTime
  apply sInf_le_sInf
  intro k hk
  obtain ⟨m, rfl, hm⟩ := hk
  exact ⟨m, rfl, fun hSm => hm (hss hSm)⟩

/-- On the finite branch the settling site really is an exit from `S`. -/
theorem le_mono_init_toNat_mem (B : Base) (S : Set (Site B)) (X : ℕ → Site B)
    (hfin : exitTime B S X ≠ ⊤) : X ((exitTime B S X).toNat) ∉ S := by
  have hP : ({k : ℕ∞ | ∃ m : ℕ, (k : ℕ∞) = m ∧ X m ∉ S}).Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have : exitTime B S X = ⊤ := by
      unfold exitTime
      rw [hne, sInf_empty]
    exact hfin this
  have hmem : sInf ({k : ℕ∞ | ∃ m : ℕ, (k : ℕ∞) = m ∧ X m ∉ S}) ∈
      {k : ℕ∞ | ∃ m : ℕ, (k : ℕ∞) = m ∧ X m ∉ S} := csInf_mem hP
  obtain ⟨m, hm_eq, hmS⟩ := hmem
  have htoNat : (exitTime B S X).toNat = m := by
    have hEq : exitTime B S X = ((m : ℕ) : ℕ∞) := by
      unfold exitTime
      exact hm_eq
    rw [hEq, ENat.toNat_coe]
  rw [htoNat]
  exact hmS

/-- **Single step of monotonicity.**  For `S ⊆ S'`, the site settled from `S`
lies in `S'` or coincides with the site settled from `S'`.  Pathwise, with no
coupling and no a.s. hypothesis. -/
theorem le_mono_init_settle_mem (B : Base) {S S' : Set (Site B)} (hss : S ⊆ S')
    (X : ℕ → Site B) :
    X ((exitTime B S X).toNat) ∈ S' ∪ {X ((exitTime B S' X).toNat)} := by
  by_cases htop : exitTime B S X = ⊤
  · have hS_all : ∀ n, X n ∈ S := (le_mono_init_exitTime_eq_top_iff B S X).mp htop
    have htop' : exitTime B S' X = ⊤ :=
      (le_mono_init_exitTime_eq_top_iff B S' X).mpr (fun n => hss (hS_all n))
    have h1 : (exitTime B S X).toNat = 0 := by rw [htop]; rfl
    have h2 : (exitTime B S' X).toNat = 0 := by rw [htop']; rfl
    rw [h1, h2]
    exact Or.inl (hss (hS_all 0))
  · have hm : X ((exitTime B S X).toNat) ∉ S := le_mono_init_toNat_mem B S X htop
    by_cases hmem : X ((exitTime B S X).toNat) ∈ S'
    · exact Or.inl hmem
    · refine Or.inr ?_
      have ht' : exitTime B S' X = exitTime B S X := by
        apply le_antisymm
        · have hle : exitTime B S' X ≤ ((exitTime B S X).toNat : ℕ∞) := by
            unfold exitTime
            exact sInf_le ⟨(exitTime B S X).toNat, rfl, hmem⟩
          rwa [ENat.coe_toNat htop] at hle
        · exact le_mono_init_exitTime_mono B hss X
      rw [ht']
      exact Set.mem_singleton _

-- FROZEN-STATEMENT-BEGIN
theorem le_mono_init
    (B : Base)
    (𝒜₁ 𝒜₂ : Set (Site B))
    (hsub : 𝒜₁ ⊆ 𝒜₂)
    (hproper₁ : 𝒜₁ ≠ (Set.univ : Set (Site B)))
    (hproper₂ : 𝒜₂ ≠ (Set.univ : Set (Site B)))
    (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (start : ℕ → Site B)
    (w : Ω → ℕ → WalkDriver)
    (Φ : Ω → Set (Site B) → ℕ → Set (Site B))
    (hΦ_zero : ∀ ω S, Φ ω S 0 = S)
    (hΦ_succ : ∀ ω S k,
      Φ ω S (k + 1) =
        Φ ω S k ∪
          {cylPath B (start k) (w ω k)
            (exitTime B (Φ ω S k) (cylPath B (start k) (w ω k))).toNat})
    (haefin : ∀ S ∈ ({𝒜₁, 𝒜₂} : Set (Set (Site B))), ∀ k,
      ∀ᵐ ω ∂μ,
        exitTime B (Φ ω S k) (cylPath B (start k) (w ω k)) ≠ ⊤)
    : ∀ᵐ ω ∂μ, ∀ k, Φ ω 𝒜₁ k ⊆ Φ ω 𝒜₂ k
-- FROZEN-STATEMENT-END
  := by
  -- The printed properness premises are not needed by the induction.
  have _ := hproper₁
  have _ := hproper₂
  have hfin : ∀ᵐ ω ∂μ,
      ∀ k, exitTime B (Φ ω 𝒜₁ k) (cylPath B (start k) (w ω k)) ≠ ⊤ :=
    ae_all_iff.2 (fun k => haefin 𝒜₁ (by simp) k)
  filter_upwards [hfin] with ω _hω
  intro k
  induction k with
  | zero =>
      rw [hΦ_zero, hΦ_zero]
      exact hsub
  | succ k ih =>
      rw [hΦ_succ ω 𝒜₁ k, hΦ_succ ω 𝒜₂ k]
      intro p hp
      rcases hp with hp | hp
      · exact Or.inl (ih hp)
      · rw [Set.mem_singleton_iff] at hp
        subst hp
        exact le_mono_init_settle_mem B (S := Φ ω 𝒜₁ k) (S' := Φ ω 𝒜₂ k) ih
          (cylPath B (start k) (w ω k))

end IdlaCyl.Frozen
