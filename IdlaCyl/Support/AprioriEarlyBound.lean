module

/-
Canonical early outer bound for `pr:apriori`(a), `tex:559-567`.
The analytic argument is at `tex:623-629`. The layer-union API introduces a
geometric prefactor, absorbed using the paper's strict inequality β > e² C.
This is ordinary support work, with no frozen-statement closure claim.
-/
public import IdlaCyl.Support.AprioriFinal
public import IdlaCyl.Support.AprioriEarly
public import IdlaCyl.Support.Recurrence.Discharge

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IdlaCyl

open scoped ENNReal BigOperators

private theorem early_exponent_le (L s r β m : ℝ) (hs : s ≤ 0)
    (hm : β * L ≤ m) (hbudget : -r ≤ β * (-1 - s) * L) :
    L + m * s - r ≤ L * (-(β - 1)) := by
  have hnonneg : 0 ≤ β * (-1 - s) * L + r := by
    calc
      0 = -r + r := by ring
      _ ≤ β * (-1 - s) * L + r := by
        simpa only [add_comm] using add_le_add_right hbudget r
  calc
    L + m * s - r ≤ L + (β * L) * s - r :=
      sub_le_sub_right (add_le_add (le_refl L) (mul_le_mul_of_nonpos_right hm hs)) r
    _ = L * (-(β - 1)) - (β * (-1 - s) * L + r) := by ring
    _ ≤ L * (-(β - 1)) := sub_le_self _ hnonneg

/-- The strict geometric decay absorbs the prefactor uniformly in the integer
size, with a threshold depending only on `q` and `β`. -/
theorem geometric_log_height_bound
    (q β : ℝ) (hq0 : 0 < q) (hq1 : q < Real.exp (-1))
    (hβ : 0 < β) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (N : ℝ) * q ^ (Nat.floor (β * Real.log (N : ℝ)) + 1)
          * (1 - q)⁻¹
        ≤ (N : ℝ) ^ (-(β - 1)) := by
  have hlogq : Real.log q < -1 := (Real.log_lt_iff_lt_exp hq0).mpr hq1
  have hq_lt_one : q < 1 :=
    hq1.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  have hden : 0 < 1 - q := sub_pos.mpr hq_lt_one
  have hδ : 0 < -1 - Real.log q := sub_pos.mpr hlogq
  have hβδ : 0 < β * (-1 - Real.log q) := mul_pos hβ hδ
  set K : ℝ := -Real.log (1 - q) / (β * (-1 - Real.log q)) with hK
  clear_value K
  refine ⟨max 2 ⌈Real.exp K⌉₊, le_max_left _ _, ?_⟩
  intro N hN
  have hNtwo : 2 ≤ N := (le_max_left _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hNtwo)
  have hexp : Real.exp K ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans hN))
  have hlogN : K ≤ Real.log (N : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos K) hexp
    rwa [Real.log_exp] at h
  have hbudget : -Real.log (1 - q) ≤ β * (-1 - Real.log q) * Real.log (N : ℝ) := by
    rw [hK] at hlogN
    simpa only [mul_comm] using (div_le_iff₀ hβδ).mp hlogN
  have hfloor : β * Real.log (N : ℝ) ≤
      ((Nat.floor (β * Real.log (N : ℝ)) + 1 : ℕ) : ℝ) := by
    exact (Nat.lt_floor_add_one (β * Real.log (N : ℝ))).le.trans_eq (by push_cast; rfl)
  have hpow : q ^ (Nat.floor (β * Real.log (N : ℝ)) + 1) =
      Real.exp (((Nat.floor (β * Real.log (N : ℝ)) + 1 : ℕ) : ℝ) * Real.log q) := by
    conv_lhs => rw [← Real.exp_log hq0]
    rw [Real.exp_nat_mul]
  have hinv : (1 - q)⁻¹ = Real.exp (-Real.log (1 - q)) := by
    rw [Real.exp_neg, Real.exp_log hden]
  rw [hpow, hinv, ← Real.exp_log hNpos, ← Real.exp_add, ← Real.exp_add,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  apply Real.exp_le_exp.mpr
  simpa only [sub_eq_add_neg] using
    early_exponent_le (Real.log (N : ℝ)) (Real.log q) (Real.log (1 - q)) β _
    (hlogq.le.trans (by norm_num)) hfloor hbudget

private theorem early_scaled_time_le (γ C N T L β : ℝ) (hγ : 0 ≤ γ)
    (hN : 0 < N) (hγC : γ * C = β) (hT : T ≤ C * N * L) :
    γ * T / N ≤ β * L := by
  calc
    γ * T / N ≤ γ * (C * N * L) / N :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hT hγ) hN.le
    _ = (γ * C) * L * (N / N) := by ring
    _ = β * L := by rw [hγC, div_self (ne_of_gt hN), mul_one]

/-- The early binomial tail is bounded uniformly over all natural times below
`C N log N`. There is no assumed tail estimate or probability input. -/
theorem apriori_tail_le (C : ℝ) (hC : 0 < C)
    (β : ℝ) (hβ : max 1 (Real.exp 2 * C) < β) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ T : ℕ,
      (T : ℝ) ≤ C * (N : ℝ) * Real.log (N : ℝ) →
        ∑' m : ℤ, (if β * Real.log (N : ℝ) < m then
            ENNReal.ofReal ((1 / (N : ℝ)) ^ (m - 1).toNat
              * (Nat.choose T ((m - 1).toNat + 1) : ℝ)) else 0)
          ≤ ENNReal.ofReal ((N : ℝ) ^ (-(β - 1))) := by
  have hβpos : 0 < β :=
    zero_lt_one.trans ((le_max_left _ _).trans_lt hβ)
  set γ : ℝ := β / C with hγdef
  clear_value γ
  have hγ : Real.exp 2 < γ := by
    rw [hγdef]
    exact (lt_div_iff₀ hC).mpr ((le_max_right _ _).trans_lt hβ)
  have hγpos : 0 < γ := (Real.exp_pos 2).trans hγ
  have hγC : γ * C = β := by rw [hγdef, div_mul_cancel₀ _ (ne_of_gt hC)]
  set q : ℝ := Real.exp 1 / γ with hqdef
  clear_value q
  have hq0 : 0 < q := by rw [hqdef]; exact div_pos (Real.exp_pos 1) hγpos
  have hq1 : q < Real.exp (-1) := by
    rw [hqdef, div_lt_iff₀ hγpos]
    calc
      Real.exp 1 = Real.exp (-1) * Real.exp 2 := by
        rw [← Real.exp_add]; norm_num
      _ < Real.exp (-1) * γ := mul_lt_mul_of_pos_left hγ (Real.exp_pos (-1))
  have hq_lt_one : q < 1 :=
    hq1.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  have hden : 0 < 1 - q := sub_pos.mpr hq_lt_one
  obtain ⟨N₀, hN₀two, hscalar⟩ := geometric_log_height_bound q β hq0 hq1 hβpos
  refine ⟨N₀, ?_⟩
  intro N hN T hT
  have hNtwo : 2 ≤ N := hN₀two.trans hN
  have hNnat : 0 < N := lt_of_lt_of_le (by decide : 0 < 2) hNtwo
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hNtwo))
  have hh : 0 ≤ β * Real.log (N : ℝ) := mul_nonneg hβpos.le hlogN
  have htime : γ * (T : ℝ) / (N : ℝ) ≤ β * Real.log (N : ℝ) :=
    early_scaled_time_le γ C (N : ℝ) (T : ℝ) (Real.log (N : ℝ)) β
      hγpos.le hNpos hγC hT
  have hterms :
      (∑' m : ℤ, (if β * Real.log (N : ℝ) < m then
          ENNReal.ofReal ((1 / (N : ℝ)) ^ (m - 1).toNat
            * (Nat.choose T ((m - 1).toNat + 1) : ℝ)) else 0))
        ≤ ∑' m : ℤ, (if β * Real.log (N : ℝ) < m then
            ENNReal.ofReal (N : ℝ) * (ENNReal.ofReal q) ^ m.toNat else 0) := by
    refine ENNReal.tsum_le_tsum fun m => ?_
    by_cases hm : β * Real.log (N : ℝ) < (m : ℝ)
    · rw [if_pos hm, if_pos hm]
      have hmpos : (0 : ℤ) < m := by exact_mod_cast (hh.trans_lt hm)
      have hmcast : (m.toNat : ℝ) = (m : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hmpos.le
      have hjeq : (m - 1).toNat + 1 = m.toNat := by omega
      have hjcast : (((m - 1).toNat + 1 : ℕ) : ℝ) = (m : ℝ) := by
        rw [hjeq]; exact hmcast
      have hbig : γ * (T : ℝ) / (N : ℝ) ≤
          (((m - 1).toNat + 1 : ℕ) : ℝ) := by
        rw [hjcast]; exact htime.trans hm.le
      have hbound := binom_term_le N T ((m - 1).toNat + 1) hNnat γ hγ
        (by omega) hbig
      rw [show ((m - 1).toNat + 1) - 1 = (m - 1).toNat from by omega,
        hjeq, ← hqdef] at hbound
      rw [hjeq, ← ENNReal.ofReal_pow hq0.le,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg N)]
      exact ENNReal.ofReal_le_ofReal hbound
    · rw [if_neg hm, if_neg hm]
  have hgeom := tsum_geom_tail (β * Real.log (N : ℝ)) hh
    (ENNReal.ofReal (N : ℝ)) (ENNReal.ofReal q)
    (ne_of_gt (ENNReal.ofReal_pos.mpr hq0))
  have hconvert : ENNReal.ofReal (N : ℝ) *
        (ENNReal.ofReal q) ^ (Nat.floor (β * Real.log (N : ℝ)) + 1) *
        (1 - ENNReal.ofReal q)⁻¹ =
      ENNReal.ofReal ((N : ℝ) * q ^ (Nat.floor (β * Real.log (N : ℝ)) + 1) *
        (1 - q)⁻¹) := by
    rw [← ENNReal.ofReal_pow hq0.le, ← ENNReal.ofReal_mul (Nat.cast_nonneg N),
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hq0.le,
      ← ENNReal.ofReal_inv_of_pos hden, ← ENNReal.ofReal_mul (by positivity)]
  exact hterms.trans (hgeom.trans (hconvert.le.trans
    (ENNReal.ofReal_le_ofReal (hscalar N hN))))

/-- Canonical `pr:apriori`(a), with the recurrence producer and the analytic
binomial-tail proof supplied internally. The threshold precedes every carrier
and every natural time. -/
theorem pr_apriori_part_a (C : ℝ) (hC : 0 < C)
    (β : ℝ) (hβ : max 1 (Real.exp 2 * C) < β) :
    ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card → ∀ T : ℕ,
      (T : ℝ) ≤ C * (B.card : ℝ) * Real.log (B.card : ℝ) →
        idlaMeasure B {ω : TrajSeq B |
            ¬ (clusterTraj B ω T ⊆ R B (β * Real.log (B.card : ℝ)))}
          ≤ ENNReal.ofReal ((B.card : ℝ) ^ (-(β - 1))) :=
  apriori_early_of_tail External.lazyRwRecurrent_holds C hC β hβ
    (apriori_tail_le C hC β hβ)

end IdlaCyl
