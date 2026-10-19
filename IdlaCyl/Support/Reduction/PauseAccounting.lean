/-
Exact mass accounting for the literal frozen exploration, including duplicate copies.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396,1440-1453.
Counts are finite cardinalities of actual occupied extensions
and list lengths; an infinite set's ncard is never used.
-/
import IdlaCyl.Support.Reduction.FreezeBatchLaw

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Each coupon adds exactly one particle: settled or mobile, with no deletion. -/
theorem freezeCoupon_mass (B : Base) (s : ResumeState B) (z : Site B) :
    (freezeCoupon B s z).1.val.card + (freezeCoupon B s z).2.length =
      s.1.val.card + s.2.length + 1 := by
  unfold freezeCoupon
  split_ifs with hz
  · simp only [List.length_append, List.length_singleton]
    omega
  · have hz0 : z ∉ R B 0 := fun h => hz (Or.inl h)
    have hzF : z ∉ s.1.val := fun h => hz (Or.inr h)
    simp only [resumeInsert, dif_neg hz0, Finset.card_insert_of_notMem hzF]
    omega

/-- Exactly M particles have been added at the end of a batch, on every input path. -/
theorem freezeGrow_mass (B : Base) (j : ℤ) (s : ResumeState B) (ω : TrajSeq B) (M : ℕ) :
    (freezeGrow B j s ω M).1.val.card + (freezeGrow B j s ω M).2.length =
      s.1.val.card + s.2.length + M := by
  induction M with
  | zero => rfl
  | succ M ih =>
      have h := freezeCoupon_mass B (freezeGrow B j s ω M) (firstHitSite B j (ω M))
      change (freezeCoupon B _ _).1.val.card + (freezeCoupon B _ _).2.length = _
      omega

/-- Exact mass conservation for the actual fresh batch kernel. -/
theorem freezeBatch_mass (B : Base) (j : ℤ) (M : ℕ) (s : ResumeState B) :
    ∀ᵐ t ∂freezeBatch B j M s,
      t.1.val.card + t.2.length = s.1.val.card + s.2.length + M := by
  rw [← freezeBatch_law]
  apply (ae_map_iff (measurable_freezeGrow B j s M).aemeasurable
    (Set.to_countable _).measurableSet).mpr
  exact Filter.Eventually.of_forall (freezeGrow_mass B j s · M)

/-- Freshly frozen mobile particles are all at already occupied sites. -/
theorem freezeGrow_queue_occupied (B : Base) (j : ℤ) (s : ResumeState B)
    (hs : ∀ z ∈ s.2, z ∈ resumeSeed B s.1) (ω : TrajSeq B) (M : ℕ) :
    ∀ z ∈ (freezeGrow B j s ω M).2, z ∈ resumeSeed B (freezeGrow B j s ω M).1 := by
  induction M with
  | zero => exact hs
  | succ M ih => exact freezeCoupon_queue_occupied B _ ih _

/-- Push an almost-sure statement through a measurable fresh conditional kernel. -/
theorem ae_bind_of_ae_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (κ : α → Measure β) (hκ : Measurable κ) (p : β → Prop)
    (hp : MeasurableSet {b | p b}) (ha : ∀ᵐ a ∂μ, ∀ᵐ b ∂κ a, p b) :
    ∀ᵐ b ∂μ.bind κ, p b := by
  rw [ae_iff]
  change (μ.bind κ) {b | p b}ᶜ = 0
  rw [Measure.bind_apply hp.compl hκ.aemeasurable]
  have hzero : (fun a => κ a {b | ¬ p b}) =ᵐ[μ] (fun _ => 0) :=
    ha.mono (fun _ h => ae_iff.mp h)
  change (∫⁻ a, κ a {b | ¬ p b} ∂μ) = 0
  rw [lintegral_congr_ae hzero, lintegral_zero]

/-- The paused mass plus the still-hidden starts equals the original deterministic total. -/
theorem layeredPause_mass (B : Base) (M n j : ℕ) (s : ResumeState B)
    (r : ℕ) (hr : M * n ≤ r) :
    ∀ᵐ t ∂layeredPause B M n j s r,
      t.1.1.val.card + t.1.2.length + t.2 = s.1.val.card + s.2.length + r := by
  induction n generalizing j s r with
  | zero =>
      exact (ae_dirac_iff (Set.to_countable _).measurableSet).mpr rfl
  | succ n ih =>
      have hbudget : M * n ≤ r - M := by rw [Nat.mul_succ] at hr; omega
      have hM : M ≤ r := by rw [Nat.mul_succ] at hr; omega
      unfold layeredPause
      split_ifs
      · apply ae_bind_of_ae_ae _ _ (measurable_of_countable _) _
          (Set.to_countable _).measurableSet
        filter_upwards [freezeBatch_mass B (j + 1 : ℕ) M s] with t ht
        filter_upwards [ih (j + 1) t (r - M) hbudget] with u hu
        omega
      · exact (ae_dirac_iff (Set.to_countable _).measurableSet).mpr rfl

/-- The mass ledger for the actual initial phase includes all unreleased particles. -/
theorem layeredPause_flat_mass (B : Base) (M ℓ ρ : ℕ) :
    ∀ᵐ t ∂layeredPause B M ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ),
      t.1.1.val.card + t.1.2.length + t.2 = M * ℓ + ρ := by
  simpa only [resumeEmpty, Finset.card_empty, List.length_nil, Nat.zero_add] using
    layeredPause_mass B M ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ) (by omega)

end IdlaCyl.Reduction
