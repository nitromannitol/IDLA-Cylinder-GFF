/-
The harmonic martingale statistic of `le:martingale` (`tex:687-707`).

  `M(t) := (1/N) ⟪D_t, ψ⟫ = (1/N) ∑_{(x,y) ∈ A_+(t)} ψ(x,y)`.

The definition below is the `Finset.range` sum over the settling sites, *not*
the `finsum` pairing: the `finsum` would silently read `0` if
`discrepancyTraj_support_finite` failed, and `M ≡ 0` is a genuine martingale.
`harmonicMartingale_eq_pairing` proves the two expressions agree almost surely,
on the event where every walk exits (`exitTraj_ae_finite`), so the settling
sites are distinct and all lie above level `0`.

This file defines the statistic and proves the identification.  The martingale
property itself (`le:martingale`) is proved later; it consumes the optional-stopping core
`condExp_settleSite_eq_zero` and carries integrability as an explicit binder.
-/
import IdlaCyl.Support.Discrepancy

namespace IdlaCyl

open MeasureTheory
open scoped BigOperators

variable (B : Base)

/-- `M(t) = (1/N) ⟪D_t, ψ⟫ = (1/N) ∑_{A_+(t)} ψ` (`tex:691-693`), written as a
`Finset.range` sum over the settling sites so that it has no junk branch. -/
noncomputable def harmonicMartingale (ψ : Site B → ℝ) (t : ℕ) (ω : TrajSeq B) : ℝ :=
  (1 / (B.card : ℝ)) * ∑ k ∈ Finset.range t, ψ (settleSite B ω k)

/-- On the almost-sure event that every walk exits, the settling sites up to
time `t` are distinct: the `i`-th one lies in `A(i+1)` and hence in `A(j)` for
`j > i`, while the `j`-th one is fresh for `A(j)`. -/
theorem range_settleSite_injective (ω : TrajSeq B) (t : ℕ)
    (h : ∀ j, exitTime' B (clusterTraj B ω j) (ω j) ≠ ⊤) :
    ∀ i ∈ Finset.range t, ∀ j ∈ Finset.range t,
      settleSite B ω i = settleSite B ω j → i = j := by
  intro i _ j _ hij
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hmem_i : settleSite B ω i ∈ clusterTraj B ω j := by
      have hmem_succ : settleSite B ω i ∈ clusterTraj B ω (i + 1) := by
        rw [clusterTraj_eq_union]
        exact Or.inr (Finset.mem_image.mpr
          ⟨i, Finset.mem_range.mpr (Nat.lt_succ_self i), rfl⟩)
      exact clusterFrom_mono B (R B 0) ω (by omega) hmem_succ
    have hnot_j : settleSite B ω j ∉ clusterTraj B ω j :=
      (clusterTraj_plus_ncard_of_settle B ω j (h j)).1
    exact absurd (hij ▸ hmem_i) hnot_j
  · exact heq
  · have hmem_j : settleSite B ω j ∈ clusterTraj B ω i := by
      have hmem_succ : settleSite B ω j ∈ clusterTraj B ω (j + 1) := by
        rw [clusterTraj_eq_union]
        exact Or.inr (Finset.mem_image.mpr
          ⟨j, Finset.mem_range.mpr (Nat.lt_succ_self j), rfl⟩)
      exact clusterFrom_mono B (R B 0) ω (by omega) hmem_succ
    have hnot_i : settleSite B ω i ∉ clusterTraj B ω i :=
      (clusterTraj_plus_ncard_of_settle B ω i (h i)).1
    exact absurd (hij.symm ▸ hmem_j) hnot_i

/-- On the same event, `A_+(t)` is exactly the set of settling sites up to time
`t`: each is fresh and above level `0`, so no filtering is needed. -/
theorem clusterPlusFinset_eq_image (ω : TrajSeq B) (t : ℕ)
    (h : ∀ j, exitTime' B (clusterTraj B ω j) (ω j) ≠ ⊤) :
    clusterPlusFinset B ω t = (Finset.range t).image (settleSite B ω) := by
  rw [clusterPlusFinset]
  refine Finset.filter_true_of_mem fun p hp => ?_
  rw [Finset.mem_image] at hp
  obtain ⟨j, _, rfl⟩ := hp
  exact (clusterTraj_plus_ncard_of_settle B ω j (h j)).2

/-- **The increment identity** (`tex:693-697`): `M(t+1) - M(t)` is the
normalised value of `ψ` at the `t`-th settling site. -/
theorem harmonicMartingale_succ (ψ : Site B → ℝ) (t : ℕ) (ω : TrajSeq B) :
    harmonicMartingale B ψ (t + 1) ω - harmonicMartingale B ψ t ω
      = (1 / (B.card : ℝ)) * ψ (settleSite B ω t) := by
  unfold harmonicMartingale
  rw [Finset.sum_range_succ]
  ring

/-- **`tex:691-693`.**  Almost surely, `M(t) = (1/N) ⟪D_t, ψ⟫` for a
zero-horizontal-average `ψ`.  The null set excluded is the one where some walk
never exits and the `Finset.range` sum would repeat a settling site. -/
theorem harmonicMartingale_eq_pairing (ψ : Site B → ℝ) (hzero : ZeroHorizontalAverage B ψ)
    (t : ℕ) :
    ∀ᵐ ω ∂idlaMeasure B,
      harmonicMartingale B ψ t ω = (1 / (B.card : ℝ)) * pairingTraj B ω t ψ := by
  have hall : ∀ᵐ ω ∂idlaMeasure B,
      ∀ j, exitTime' B (clusterTraj B ω j) (ω j) ≠ ⊤ :=
    MeasureTheory.ae_all_iff.mpr fun j => exitTraj_ae_finite B j
  filter_upwards [hall] with ω hω
  have hinj := range_settleSite_injective B ω t hω
  rw [harmonicMartingale, pairingTraj_eq_sum_clusterPlus B ω t ψ hzero,
    clusterPlusFinset_eq_image B ω t hω, Finset.sum_image hinj]

end IdlaCyl
