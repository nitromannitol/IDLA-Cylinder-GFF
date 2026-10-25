module

/-
Entrance coupons force a filled layer in ordinary canonical growth.
Source: paper/idla-cylinder-gff.tex, tex:246-265,595-610,1440-1453.
Occupation above the filled rectangle is arbitrary; no walk
is stopped or deleted in the canonical process used here.
-/
public import IdlaCyl.Support.Reduction.Coupon

@[expose] public section

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Before its first hit of j, a nearest-neighbour path started below j is below j. -/
theorem before_first_entrance (B : Base) (j : ℤ) (X : ℕ → Site B)
    (ha : CylAdmissible B X) (h0 : (X 0).2 ≤ j) (k : ℕ)
    (hk : hitLevel B j X = (k : ℕ∞)) (n : ℕ) (hn : n < k) :
    (X n).2 ≤ j - 1 := by
  by_contra h
  have hnj : j ≤ (X n).2 := by omega
  obtain ⟨i, hin, hij⟩ := ha.exists_eq_level B h0 hnj
  exact ((hitLevel_eq_coe_iff B j X k).mp hk).2 i (by omega) hij

/-- The first-entrance coupon is occupied after this ordinary, unstopped release.
If empty, it is precisely the walk's first exit; if occupied, it was already in S. -/
theorem entrance_mem_after_release (B : Base) (S : Set (Site B)) (j : ℤ)
    (hS : R B ((j : ℝ) - 1) ⊆ S) (X : ℕ → Site B)
    (ha : CylAdmissible B X) (h0 : (X 0).2 ≤ j)
    (hf : hitLevel B j X ≠ ⊤) :
    firstHitSite B j X ∈ S ∪ {exitSite' B S X} := by
  by_cases hmem : firstHitSite B j X ∈ S
  · exact Or.inl hmem
  · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hf
    have hhit : hitLevel B j X = (k : ℕ∞) := hk.symm
    have hsite := firstHitSite_eq_of_hitLevel_eq B j X k hhit
    have hbefore : ∀ n < k, X n ∈ S := by
      intro n hn
      apply hS
      have hv := before_first_entrance B j X ha h0 k hhit n hn
      change ((X n).2 : ℝ) ≤ (j : ℝ) - 1
      exact_mod_cast hv
    have hexit : exitTime' B S X = (k : ℕ∞) :=
      (exitTime'_eq_coe_iff B S X k).mpr ⟨by rwa [← hsite], hbefore⟩
    apply Or.inr
    show firstHitSite B j X = exitSite' B S X
    rw [hsite]
    change X k = X (WithTop.untopA (exitTime' B S X))
    rw [hexit, untopA_natCast]

/-- Finite growth always retains the whole initial seed. -/
theorem seed_subset_growth (B : Base) (F : ResumeFinite B) (ω : TrajSeq B) (n : ℕ) :
    resumeSeed B F ⊆ resumeSeed B (resumeGrow B F ω n) := by
  rw [resumeSeed_grow]
  exact clusterFrom_mono B (resumeSeed B F) ω (Nat.zero_le n)

/-- A covered coupon remains present at the end of the batch. -/
theorem entrance_mem_after_batch (B : Base) (F : ResumeFinite B) (h j : ℤ)
    (hh : h ≤ j) (hF : R B ((j : ℝ) - 1) ⊆ resumeSeed B F)
    (ω : TrajSeq B) (hω : ∀ i, CylAdmissible B (ω i) ∧ (ω i 0).2 = h ∧
      ∀ z : ℤ, ∃ n, (ω i n).2 = z) (M i : ℕ) (hi : i < M) :
    firstHitSite B j (ω i) ∈ resumeSeed B (resumeGrow B F ω M) := by
  have hf : hitLevel B j (ω i) ≠ ⊤ := by
    intro htop
    obtain ⟨n, hn⟩ := (hω i).2.2 j
    exact (hitLevel_eq_top_iff B j (ω i)).mp htop n hn
  have hcoupon := entrance_mem_after_release B (resumeSeed B (resumeGrow B F ω i)) j
    (hF.trans (seed_subset_growth B F ω i)) (ω i) (hω i).1
    (by rw [(hω i).2.1]; exact hh) hf
  have hnext : firstHitSite B j (ω i) ∈ resumeSeed B (resumeGrow B F ω (i + 1)) := by
    rw [resumeSeed_grow, clusterFrom_succ, ← resumeSeed_grow]
    exact hcoupon
  rw [resumeSeed_grow] at hnext ⊢
  exact clusterFrom_mono B _ ω (Nat.succ_le_of_lt hi) hnext

/-- All coupons present imply the next whole rectangle is filled, for valid paths. -/
theorem coupons_force_filled (B : Base) (F : ResumeFinite B) (h j : ℤ)
    (hh : h ≤ j) (hF : R B ((j : ℝ) - 1) ⊆ resumeSeed B F)
    (ω : TrajSeq B) (hω : ∀ i, CylAdmissible B (ω i) ∧ (ω i 0).2 = h ∧
      ∀ z : ℤ, ∃ n, (ω i n).2 = z) (M : ℕ)
    (hc : ω ∉ missingCoupons B j M) :
    resumeGrow B F ω M ∈ filled B j := by
  intro z hz
  have hzj : z.2 ≤ j := by exact_mod_cast (mem_R.mp hz)
  by_cases hlow : z.2 ≤ j - 1
  · exact seed_subset_growth B F ω M (hF (mem_R.mpr (by exact_mod_cast hlow)))
  · have heq : z.2 = j := by omega
    have hex : ∃ i < M, firstHitSite B j (ω i) = (z.1, j) := by
      by_contra hno
      apply hc
      refine ⟨z.1, fun i hi he => hno ⟨i, hi, he⟩⟩
    obtain ⟨i, hi, he⟩ := hex
    have hm := entrance_mem_after_batch B F h j hh hF ω hω M i hi
    rwa [he, ← heq, Prod.eta] at hm

/-- Ordinary growth's failure to fill a layer is bounded by the coupon event. -/
theorem canonical_one_layer_coupon (B : Base) (F : ResumeFinite B)
    (h j : ℤ) (hh : h ≤ j) (hF : R B ((j : ℝ) - 1) ⊆ resumeSeed B F) (M : ℕ) :
    layerGrowthLaw B F h M (filled B j)ᶜ ≤
      layerDrivingLaw B h (missingCoupons B j M) := by
  rw [layerGrowthLaw, Measure.map_apply (measurable_resumeGrow B F M)
    (Set.to_countable _).measurableSet]
  apply measure_mono_ae
  filter_upwards [layerDriving_ae_good B h] with ω hω
  intro hbad
  by_contra hc
  exact hbad (coupons_force_filled B F h j hh hF ω hω M hc)

/-- One-layer polynomial bound for the actual canonical process, with any extra seed sites. -/
theorem canonical_one_layer_fill (B : Base) (F : ResumeFinite B)
    (h j : ℤ) (hh : h ≤ j) (hF : R B ((j : ℝ) - 1) ⊆ resumeSeed B F)
    (M : ℕ) (q : ℝ)
    (hM : (q + 1) * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (M : ℝ)) :
    layerGrowthLaw B F h M (filled B j)ᶜ ≤
      ENNReal.ofReal ((B.card : ℝ) ^ (-q)) :=
  (canonical_one_layer_coupon B F h j hh hF M).trans (missing_coupons_poly B h j M q hM)

end IdlaCyl.Reduction
