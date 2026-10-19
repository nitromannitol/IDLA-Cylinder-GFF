/-
Height support of the actual layered exploration; success gives the exact raw rectangle.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396,1440-1453.
Extra seed sites are allowed in the generic step; the initial
flat experiment has none above its current stopping layer.
-/
import IdlaCyl.Support.Reduction.LayeredFilling
import IdlaCyl.Support.Reduction.PauseAccounting

namespace IdlaCyl.Reduction

open MeasureTheory

/-- A coupon update preserves an upper height bound containing both the old seed and the coupon. -/
theorem freezeCoupon_seed_subset (B : Base) (s : ResumeState B) (z : Site B) (a : ℝ)
    (hs : resumeSeed B s.1 ⊆ R B a) (hz : z ∈ R B a) :
    resumeSeed B (freezeCoupon B s z).1 ⊆ R B a := by
  unfold freezeCoupon
  split_ifs
  · exact hs
  · rw [resumeSeed_insert]
    exact Set.union_subset hs (Set.singleton_subset_iff.mpr hz)

/-- Every coordinate of a batch has an entrance site at the actual stopping height almost surely. -/
theorem layerDriving_ae_entrance_heights (B : Base) (h j : ℤ) :
    ∀ᵐ ω ∂layerDrivingLaw B h, ∀ i, (firstHitSite B j (ω i)).2 = j := by
  filter_upwards [layerDriving_ae_good B h] with ω hω
  intro i
  apply firstHitSite_ver B j (ω i)
  intro htop
  obtain ⟨n, hn⟩ := (hω i).2.2 j
  exact (hitLevel_eq_top_iff B j (ω i)).mp htop n hn

/-- A finite frozen batch never rises above its coupons' layer. -/
theorem freezeGrow_seed_subset (B : Base) (j : ℤ) (s : ResumeState B)
    (hs : resumeSeed B s.1 ⊆ R B (j : ℝ)) (ω : TrajSeq B) (M : ℕ)
    (hω : ∀ i < M, (firstHitSite B j (ω i)).2 = j) :
    resumeSeed B (freezeGrow B j s ω M).1 ⊆ R B (j : ℝ) := by
  induction M with
  | zero => exact hs
  | succ M ih =>
      apply freezeCoupon_seed_subset B _ _ _ (ih (fun i hi => hω i (by omega)))
      exact mem_R.mpr (by rw [hω M (by omega)])

/-- The actual batch kernel has no occupied sites above the stopping layer. -/
theorem freezeBatch_ae_seed_subset (B : Base) (j : ℤ) (M : ℕ) (s : ResumeState B)
    (hs : resumeSeed B s.1 ⊆ R B (j : ℝ)) :
    ∀ᵐ t ∂freezeBatch B j M s, resumeSeed B t.1 ⊆ R B (j : ℝ) := by
  rw [← freezeBatch_law]
  apply (ae_map_iff (measurable_freezeGrow B j s M).aemeasurable
    (Set.to_countable _).measurableSet).mpr
  filter_upwards [layerDriving_ae_entrance_heights B 0 j] with ω hω
  exact freezeGrow_seed_subset B j s hs ω M (fun i _ => hω i)

/-- Even after an early failed fill, no occupied site exceeds the last possible layer. -/
theorem layeredPause_ae_seed_subset (B : Base) (M n j : ℕ) (s : ResumeState B)
    (hs : resumeSeed B s.1 ⊆ R B (j : ℝ)) (r : ℕ) :
    ∀ᵐ t ∂layeredPause B M n j s r,
      resumeSeed B t.1.1 ⊆ R B ((j + n : ℕ) : ℝ) := by
  induction n generalizing j s r with
  | zero =>
      exact (ae_dirac_iff (Set.to_countable _).measurableSet).mpr hs
  | succ n ih =>
      unfold layeredPause
      split_ifs
      · apply ae_bind_of_ae_ae _ _ (measurable_of_countable _) _
          (Set.to_countable _).measurableSet
        have hstep : resumeSeed B s.1 ⊆ R B ((j + 1 : ℕ) : ℝ) :=
          hs.trans (R_mono (by exact_mod_cast Nat.le_succ j))
        filter_upwards [freezeBatch_ae_seed_subset B (j + 1 : ℕ) M s hstep] with t ht
        have h := ih (j + 1) t ht (r - M)
        rwa [show j + 1 + n = j + (n + 1) by omega] at h
      · apply (ae_dirac_iff (Set.to_countable _).measurableSet).mpr
        exact hs.trans (R_mono (by exact_mod_cast (Nat.le_add_right j (n + 1))))

/-- The initial experiment's seed is always below its requested final raw layer. -/
theorem layeredPause_flat_seed_subset (B : Base) (M ℓ ρ : ℕ) :
    ∀ᵐ t ∂layeredPause B M ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ),
      resumeSeed B t.1.1 ⊆ R B (ℓ : ℝ) := by
  have hs : resumeSeed B (resumeEmpty B) ⊆ R B ((0 : ℕ) : ℝ) := by
    rw [resumeSeed_empty, Nat.cast_zero]
  simpa only [Nat.zero_add] using
    layeredPause_ae_seed_subset B M ℓ 0 (resumeEmpty B, []) hs (M * ℓ + ρ)

/-- On successful filling the ACTUAL seed is exactly R_ℓ and exactly ρ starts remain hidden. -/
theorem layeredPause_flat_rectangle (B : Base) (M ℓ ρ : ℕ) (q : ℝ)
    (hM : (q + 1) * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (M : ℝ)) :
    layeredPause B M ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ)
        {t | resumeSeed B t.1.1 = R B (ℓ : ℝ) ∧ t.2 = ρ}ᶜ ≤
      ENNReal.ofReal ((ℓ : ℝ) * (B.card : ℝ) ^ (-q)) := by
  apply (measure_mono_ae (show {t : ResumeState B × ℕ |
      resumeSeed B t.1.1 = R B (ℓ : ℝ) ∧ t.2 = ρ}ᶜ ≤ᵐ[
        layeredPause B M ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ)]
      {t | R B (ℓ : ℝ) ⊆ resumeSeed B t.1.1 ∧ t.2 = ρ}ᶜ from ?_)).trans
  · exact layeredPause_flat_fill B M ℓ ρ q hM
  · filter_upwards [layeredPause_flat_seed_subset B M ℓ ρ] with t ht
    intro hbad hgood
    exact hbad ⟨Set.Subset.antisymm ht hgood.1, hgood.2⟩

end IdlaCyl.Reduction
