module

/-
Per-layer settled/mobile particle ledger for the literal freezing algorithm.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396,1440-1453.
Every duplicate remains a separate list entry. Finite counts
refer to actual occupied extensions and actual mobile-particle lists.
-/
public import IdlaCyl.Support.Reduction.PauseAccounting

@[expose] public section

attribute [local instance] Classical.propDecidable

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Actual occupied sites of a canonical finite extension on one integer layer. -/
noncomputable def occupiedOnLayer (B : Base) (F : ResumeFinite B) (k : ℤ) : ℕ :=
  (F.val.filter (fun z => z.2 = k)).card

/-- Mobile particles on a layer, counting every duplicate separately. -/
noncomputable def mobileOnLayer (B : Base) (L : List (Site B)) (k : ℤ) : ℕ :=
  (L.filter (fun z => z.2 = k)).length

/-- The layer ledger changes by one exactly at the new coupon's height. -/
theorem freezeCoupon_layer_mass (B : Base) (s : ResumeState B) (z : Site B) (k : ℤ) :
    occupiedOnLayer B (freezeCoupon B s z).1 k +
        mobileOnLayer B (freezeCoupon B s z).2 k =
      occupiedOnLayer B s.1 k + mobileOnLayer B s.2 k + if z.2 = k then 1 else 0 := by
  by_cases hz : z ∈ resumeSeed B s.1
  · simp only [freezeCoupon, if_pos hz, occupiedOnLayer, mobileOnLayer,
      List.filter_append, List.filter_singleton, List.length_append]
    by_cases hzk : z.2 = k
    · simp [hzk, Nat.add_assoc]
    · simp [hzk]
  · have hz0 : z ∉ R B 0 := fun h => hz (Or.inl h)
    have hzF : z ∉ s.1.val := fun h => hz (Or.inr h)
    have hzfilter : z ∉ s.1.val.filter (fun w => w.2 = k) :=
      fun h => hzF (Finset.mem_filter.mp h).1
    simp only [freezeCoupon, if_neg hz, resumeInsert, dif_neg hz0,
      occupiedOnLayer, mobileOnLayer, Finset.filter_insert]
    by_cases hzk : z.2 = k
    · simp only [if_pos hzk, Finset.card_insert_of_notMem hzfilter]
      omega
    · simp only [if_neg hzk]
      omega

/-- A batch of M coupons at j increases only layer j's settled/mobile ledger by M. -/
theorem freezeGrow_layer_mass (B : Base) (j : ℤ) (s : ResumeState B)
    (ω : TrajSeq B) (M : ℕ) (hω : ∀ i < M, (firstHitSite B j (ω i)).2 = j) (k : ℤ) :
    occupiedOnLayer B (freezeGrow B j s ω M).1 k +
        mobileOnLayer B (freezeGrow B j s ω M).2 k =
      occupiedOnLayer B s.1 k + mobileOnLayer B s.2 k + if j = k then M else 0 := by
  induction M with
  | zero => simp only [freezeGrow, ite_self, Nat.add_zero]
  | succ M ih =>
      have hi := ih (fun i hi => hω i (by omega))
      have hstep := freezeCoupon_layer_mass B (freezeGrow B j s ω M) (firstHitSite B j (ω M)) k
      rw [hω M (by omega)] at hstep
      change occupiedOnLayer B (freezeCoupon B _ _).1 k +
        mobileOnLayer B (freezeCoupon B _ _).2 k = _
      by_cases hjk : j = k
      · rw [if_pos hjk] at hi hstep ⊢
        omega
      · rw [if_neg hjk] at hi hstep ⊢
        omega

/-- The actual batch kernel has the same layerwise mass ledger almost surely. -/
theorem freezeBatch_layer_mass (B : Base) (j : ℤ) (M : ℕ) (s : ResumeState B) (k : ℤ) :
    ∀ᵐ t ∂freezeBatch B j M s,
      occupiedOnLayer B t.1 k + mobileOnLayer B t.2 k =
        occupiedOnLayer B s.1 k + mobileOnLayer B s.2 k + if j = k then M else 0 := by
  rw [← freezeBatch_law]
  apply (ae_map_iff (measurable_freezeGrow B j s M).aemeasurable
    (Set.to_countable _).measurableSet).mpr
  filter_upwards [layerDriving_ae_good B 0] with ω hω
  have hheights (i : ℕ) : (firstHitSite B j (ω i)).2 = j := by
    apply firstHitSite_ver B j (ω i)
    intro htop
    obtain ⟨n, hn⟩ := (hω i).2.2 j
    exact (hitLevel_eq_top_iff B j (ω i)).mp htop n hn
  exact freezeGrow_layer_mass B j s ω M (fun i _ => hheights i) k

/-- If no scheduled starts remain hidden, every scheduled layer received its M particles.
An abort with the same remaining count can occur only for M=0, when the ledger is unchanged. -/
theorem layeredPause_layer_mass (B : Base) (M n j : ℕ) (s : ResumeState B)
    (ρ : ℕ) (k : ℤ) :
    ∀ᵐ t ∂layeredPause B M n j s (M * n + ρ), t.2 = ρ →
      occupiedOnLayer B t.1.1 k + mobileOnLayer B t.1.2 k =
        occupiedOnLayer B s.1 k + mobileOnLayer B s.2 k +
          if (j : ℤ) < k ∧ k ≤ (j + n : ℕ) then M else 0 := by
  induction n generalizing j s with
  | zero =>
      apply (ae_dirac_iff (Set.to_countable _).measurableSet).mpr
      intro _
      have hfalse : ¬ ((j : ℤ) < k ∧ k ≤ (j + 0 : ℕ)) := by omega
      rw [if_neg hfalse, Nat.add_zero]
  | succ n ih =>
      have hremain : M * (n + 1) + ρ - M = M * n + ρ := by rw [Nat.mul_succ]; omega
      by_cases hF : R B (j : ℝ) ⊆ resumeSeed B s.1
      · rw [layeredPause, if_pos hF, hremain]
        apply ae_bind_of_ae_ae _ _ (measurable_of_countable _) _
          (Set.to_countable _).measurableSet
        filter_upwards [freezeBatch_layer_mass B (j + 1 : ℕ) M s k] with t ht
        filter_upwards [ih (j + 1) t] with u hu
        intro hur
        have hi := hu hur
        have hsum : (if ((j + 1 : ℕ) : ℤ) = k then M else 0) +
            (if ((j + 1 : ℕ) : ℤ) < k ∧ k ≤ (j + 1 + n : ℕ) then M else 0) =
            (if (j : ℤ) < k ∧ k ≤ (j + (n + 1) : ℕ) then M else 0) := by
          split_ifs <;> omega
        simp only [Nat.cast_add, Nat.cast_one] at ht hi hsum ⊢
        omega
      · rw [layeredPause, if_neg hF]
        apply (ae_dirac_iff (Set.to_countable _).measurableSet).mpr
        intro hr
        have hMle : M ≤ M * (n + 1) := Nat.le_mul_of_pos_right M (by omega)
        have hM : M = 0 := by omega
        subst M
        simp only [ite_self, Nat.add_zero]

/-- The flat experiment's successful remaining-count branch has exactly M particles per layer. -/
theorem layeredPause_flat_layer_mass (B : Base) (M ℓ ρ : ℕ) (k : ℤ) :
    ∀ᵐ t ∂layeredPause B M ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ), t.2 = ρ →
      occupiedOnLayer B t.1.1 k + mobileOnLayer B t.1.2 k =
        if 1 ≤ k ∧ k ≤ (ℓ : ℤ) then M else 0 := by
  have h := layeredPause_layer_mass B M ℓ 0 (resumeEmpty B, []) ρ k
  have hiff : ((0 : ℤ) < k ∧ k ≤ (ℓ : ℤ)) ↔ 1 ≤ k ∧ k ≤ (ℓ : ℤ) := by omega
  simpa only [occupiedOnLayer, mobileOnLayer, resumeEmpty, Finset.filter_empty,
    Finset.card_empty, List.filter_nil, List.length_nil, Nat.zero_add, Nat.cast_zero, hiff] using h

end IdlaCyl.Reduction
