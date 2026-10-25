module

/-
The closed form of `pr:apriori`, part (b) (`paper/idla-cylinder-gff.tex:559-567`,
proof at `tex:585-650`), on the canonical `TrajSeq`/`idlaMeasure` carrier.

`IdlaCyl.idlaMeasure_not_subset_le_tsum_binom` (`Support/CanonicalApriori.lean`)
bounds `ℙ(A(T) ⊄ R_h)` by the binomial tail `∑_{m > h} N^{-(m-1)} C(T,m)`.  This
file evaluates that tail: with `N = B.card`, `h = β T / N` and the paper's
`K₀ = 2 / (β (log β - 2))`, for `β > e²` and `T ≥ K₀ N log N`,

  `∑_{m > h} N^{-(m-1)} C(T,m) ≤ e^{-h}`,

so `ℙ(A(T) ⊄ R_{βT/N}) ≤ e^{-βT/N}` for `N` large, which is `tex:567` (b).

The route is the paper's (`tex:585-619`, `eq:mu-recurrence` + `LBG_up`):

* `Nat.choose_le_pow_div` and Stirling (`Stirling.le_factorial_stirling`) give,
  per term and for `j ≥ βT/N`, `N^{-(j-1)} C(T,j) ≤ N (e/β)^j`;
* the tail is geometric, `∑_{j > h} N (e/β)^j ≤ N (e/β)^{⌊h⌋+1} / (1 - e/β)`;
* `N (e/β)^{⌊h⌋+1} ≤ exp(log N - h (log β - 1))`, so `T ≥ K₀ N log N` makes the
  whole bound at most `e^{-h}`.

Everything is on the canonical carrier; no `Driver` / `driverLaw` / `cluster`.
-/

public import IdlaCyl.Support.CanonicalApriori

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
open MeasureTheory Filter
open scoped ENNReal BigOperators
namespace IdlaCyl

theorem pow_div_exp_le_factorial (j : ℕ) :
    ((j : ℝ) / Real.exp 1) ^ j ≤ (j.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj; simp
  have h1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h2 : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * j) := by
    rw [Real.one_le_sqrt]; have hp := Real.pi_gt_three; nlinarith
  have h := Stirling.le_factorial_stirling j
  have hp : (0 : ℝ) ≤ ((j : ℝ) / Real.exp 1) ^ j := by positivity
  exact le_trans (le_mul_of_one_le_left hp h2) h

theorem inv_factorial_le (j : ℕ) (hj : 1 ≤ j) :
    (1 : ℝ) / (j.factorial : ℝ) ≤ (Real.exp 1 / (j : ℝ)) ^ j := by
  have hfact := pow_div_exp_le_factorial j
  have h1 : (0 : ℝ) < ((j : ℝ) / Real.exp 1) ^ j := by
    have : (0:ℝ) < j := by exact_mod_cast hj
    positivity
  have h2 : (0 : ℝ) < (j.factorial : ℝ) := by positivity
  have hinv : (Real.exp 1 / (j : ℝ)) ^ j = (((j : ℝ) / Real.exp 1) ^ j)⁻¹ := by
    rw [← inv_pow]; congr 1; rw [inv_div]
  rw [one_div, hinv]
  exact (inv_le_inv₀ h2 h1).mpr hfact

theorem binom_term_le (N T j : ℕ) (hN : 0 < N) (β : ℝ) (hβ : Real.exp 2 < β)
    (hj : 1 ≤ j) (hbig : β * (T : ℝ) / (N : ℝ) ≤ (j : ℝ)) :
    (1 / (N : ℝ)) ^ (j - 1) * (Nat.choose T j : ℝ) ≤
      (N : ℝ) * (Real.exp 1 / β) ^ j := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hβpos : 0 < β := by have := Real.exp_pos (2:ℝ); nlinarith
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hsplit : (1 / (N : ℝ)) ^ (j - 1) = (N : ℝ) * (1 / (N : ℝ)) ^ j := by
    have hje : j = (j - 1) + 1 := by omega
    conv_rhs => rw [hje, pow_succ]
    field_simp
  rw [hsplit, mul_assoc]
  gcongr 1
  calc (1 / (N : ℝ)) ^ j * (Nat.choose T j : ℝ)
      ≤ (1 / (N : ℝ)) ^ j * ((T : ℝ) ^ j / (j.factorial : ℝ)) := by
        gcongr
        exact Nat.choose_le_pow_div (α := ℝ) j T
    _ = ((T : ℝ) / (N : ℝ)) ^ j / (j.factorial : ℝ) := by rw [div_pow]; ring
    _ = ((T : ℝ) / (N : ℝ)) ^ j * (1 / (j.factorial : ℝ)) := by rw [div_eq_mul_one_div]
    _ ≤ ((T : ℝ) / (N : ℝ)) ^ j * (Real.exp 1 / (j : ℝ)) ^ j := by
        gcongr
        exact inv_factorial_le j hj
    _ = (Real.exp 1 * ((T : ℝ) / (N : ℝ)) / (j : ℝ)) ^ j := by rw [div_pow, mul_div_assoc]; ring
    _ ≤ (Real.exp 1 / β) ^ j := by
        apply pow_le_pow_left₀
        · positivity
        · rw [div_le_div_iff₀ hjpos hβpos]
          have hb : β * ((T : ℝ) / (N : ℝ)) ≤ (j : ℝ) := by
            rwa [mul_div_assoc] at hbig
          nlinarith [Real.exp_pos (1:ℝ), hb]

theorem tsum_geom_tail (h : ℝ) (hh : 0 ≤ h) (C A : ℝ≥0∞) (hA : A ≠ 0) :
    (∑' m : ℤ, (if h < (m : ℝ) then C * A ^ m.toNat else 0))
      ≤ C * A ^ (Nat.floor h + 1) * (1 - A)⁻¹ := by
  set c : ℕ := Nat.floor h + 1 with hc
  have hclt : h < (c : ℝ) := by
    have := Nat.lt_floor_add_one h
    rw [hc]; push_cast; linarith
  have hreindex :
      (∑' m : ℤ, (if h < (m : ℝ) then C * A ^ m.toNat else 0))
        = ∑' j : ℕ, C * A ^ c * A ^ j := by
    refine tsum_eq_tsum_of_ne_zero_bij
      (fun x : ↑(Function.support (fun j : ℕ => C * A ^ c * A ^ j)) =>
        (x.val : ℤ) + (c : ℤ)) ?_ ?_ ?_
    · intro x y hxy
      have hxy' : (x.val : ℤ) = (y.val : ℤ) := add_right_cancel hxy
      exact Subtype.ext (by exact_mod_cast hxy')
    · intro m hm
      rw [Function.mem_support] at hm
      have hmh : h < (m : ℝ) := by
        by_contra hlt
        rw [if_neg hlt] at hm
        exact hm rfl
      have hm0 : 0 ≤ m := by
        have : (0 : ℝ) ≤ (m : ℝ) := le_trans hh (le_of_lt hmh)
        exact_mod_cast this
      rw [if_pos hmh] at hm
      have hCm : C ≠ 0 := by
        intro hC; exact hm (by rw [hC, zero_mul])
      have hmh' : (m.toNat : ℝ) = (m : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hm0
      have hcm : c ≤ m.toNat := by
        have hfloor : Nat.floor h < m.toNat := by
          rw [Nat.floor_lt hh]; rw [hmh']; exact hmh
        omega
      have hj : (fun j : ℕ => C * A ^ c * A ^ j) (m.toNat - c) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hCm (pow_ne_zero _ hA)) (pow_ne_zero _ hA)
      refine ⟨⟨m.toNat - c, hj⟩, ?_⟩
      show ((m.toNat - c : ℕ) : ℤ) + (c : ℤ) = m
      have hmto : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm0
      omega
    · intro x
      have hx : h < (((x.val : ℤ) + (c : ℤ) : ℤ) : ℝ) := by
        push_cast
        have : (0 : ℝ) ≤ (x.val : ℝ) := Nat.cast_nonneg x.val
        linarith
      rw [if_pos hx]
      have htoNat : ((x.val : ℤ) + (c : ℤ)).toNat = x.val + c := by
        rw [← Nat.cast_add, Int.toNat_natCast]
      rw [htoNat, pow_add]
      ring
  rw [hreindex,
    show (∑' j : ℕ, C * A ^ c * A ^ j) = (C * A ^ c) * ∑' j : ℕ, A ^ j from
      ENNReal.tsum_mul_left,
    ENNReal.tsum_geometric]

theorem apriori_tsum_le (B : Base) (T : ℕ) (β : ℝ) (hβ : Real.exp 2 < β)
    (h : ℝ) (hh : 0 ≤ h) (hlink : h = β * (T : ℝ) / (B.card : ℝ)) :
    (∑' m : ℤ, (if h < (m : ℝ) then
        ENNReal.ofReal ((1 / (B.card : ℝ)) ^ ((m - 1).toNat) *
          (Nat.choose T ((m - 1).toNat + 1) : ℝ))
      else 0))
      ≤ ∑' m : ℤ, (if h < (m : ℝ) then
          ENNReal.ofReal (B.card : ℝ) * (ENNReal.ofReal (Real.exp 1 / β)) ^ m.toNat
        else 0) := by
  have hβpos : 0 < β := by have := Real.exp_pos (2:ℝ); nlinarith
  have heβ : 0 < Real.exp 1 / β := div_pos (Real.exp_pos 1) hβpos
  refine ENNReal.tsum_le_tsum fun m => ?_
  by_cases hm : h < (m : ℝ)
  · rw [if_pos hm, if_pos hm]
    have hN : 0 < B.card := lt_of_lt_of_le (by norm_num) B.nontrivial
    have hmpos : (0 : ℤ) < m := by
      have : (0 : ℝ) < (m : ℝ) := lt_of_le_of_lt hh hm
      exact_mod_cast this
    have hmcast : (m.toNat : ℝ) = (m : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (le_of_lt hmpos)
    have hjeq : (m - 1).toNat + 1 = m.toNat := by omega
    have hjcast : (((m - 1).toNat + 1 : ℕ) : ℝ) = (m : ℝ) := by
      rw [hjeq]; exact hmcast
    have hbig : β * (T : ℝ) / (B.card : ℝ) ≤ (((m - 1).toNat + 1 : ℕ) : ℝ) := by
      rw [← hlink, hjcast]; exact le_of_lt hm
    have hbound := binom_term_le B.card T ((m - 1).toNat + 1) hN β hβ (by omega) hbig
    rw [show ((m - 1).toNat + 1) - 1 = (m - 1).toNat from by omega] at hbound
    have hrhs : ENNReal.ofReal (B.card : ℝ) *
          (ENNReal.ofReal (Real.exp 1 / β)) ^ m.toNat
        = ENNReal.ofReal ((B.card : ℝ) * (Real.exp 1 / β) ^ m.toNat) := by
      rw [← ENNReal.ofReal_pow heβ.le, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    rw [hrhs]
    apply ENNReal.ofReal_le_ofReal
    exact hbound.trans_eq (by rw [hjeq])
  · rw [if_neg hm, if_neg hm]

theorem apriori_tsum_le_exp (B : Base) (hrec : External.LazyRwRecurrent) (T : ℕ) (β : ℝ)
    (hβ : Real.exp 2 < β) (h : ℝ) (hh : 0 ≤ h)
    (hlink : h = β * (T : ℝ) / (B.card : ℝ)) :
    idlaMeasure B {ω : TrajSeq B | ¬ (clusterTraj B ω T ⊆ R B h)}
      ≤ ENNReal.ofReal ((B.card : ℝ) * (Real.exp 1 / β) ^ (Nat.floor h + 1) *
          (1 - Real.exp 1 / β)⁻¹) := by
  have hβpos : 0 < β := by have := Real.exp_pos (2:ℝ); nlinarith
  have ha0 : 0 < Real.exp 1 / β := div_pos (Real.exp_pos 1) hβpos
  have h1a : 0 < 1 - Real.exp 1 / β := by
    have he1 : Real.exp 1 < β := by
      exact lt_trans (Real.exp_lt_exp.mpr (by norm_num)) hβ
    have : Real.exp 1 / β < 1 := (div_lt_one hβpos).mpr he1
    linarith
  have hA : ENNReal.ofReal (Real.exp 1 / β) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr ha0)
  refine (idlaMeasure_not_subset_le_tsum_binom B hrec T h hh).trans ?_
  refine (apriori_tsum_le B T β hβ h hh hlink).trans ?_
  refine (tsum_geom_tail h hh (ENNReal.ofReal (B.card : ℝ))
    (ENNReal.ofReal (Real.exp 1 / β)) hA).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_pow ha0.le, ← ENNReal.ofReal_mul (Nat.cast_nonneg (B.card)),
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (le_of_lt ha0),
    ← ENNReal.ofReal_inv_of_pos h1a, ← ENNReal.ofReal_mul (by positivity)]

theorem arith_bound (β : ℝ) (hβ : Real.exp 2 < β) (N : ℕ) (hN : 1 ≤ N)
    (h : ℝ)
    (hlog : -Real.log (1 - Real.exp 1 / β) ≤ Real.log (N : ℝ))
    (hK : 2 * Real.log (N : ℝ) ≤ h * (Real.log β - 2)) :
    (N : ℝ) * (Real.exp 1 / β) ^ (Nat.floor h + 1) * (1 - Real.exp 1 / β)⁻¹
      ≤ Real.exp (-h) := by
  have hβpos : 0 < β := lt_trans (Real.exp_pos 2) hβ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have he1 : Real.exp 1 < β := lt_trans (Real.exp_lt_exp.mpr (by norm_num)) hβ
  have ha0 : 0 < Real.exp 1 / β := div_pos (Real.exp_pos 1) hβpos
  have h1a : 0 < 1 - Real.exp 1 / β := by
    have : Real.exp 1 / β < 1 := (div_lt_one hβpos).mpr he1
    linarith
  have hlogβ : 2 < Real.log β := (Real.lt_log_iff_exp_lt hβpos).mpr hβ
  have hmlog : (1 - Real.log β) ≤ 0 := by linarith
  have hmfloor : h < (Nat.floor h : ℝ) + 1 := Nat.lt_floor_add_one h
  have hmge : h ≤ (Nat.floor h : ℝ) + 1 := le_of_lt hmfloor
  set m : ℕ := Nat.floor h + 1 with hmdef
  have ham : (Real.exp 1 / β) ^ m = Real.exp ((m : ℝ) * (1 - Real.log β)) := by
    have hl : Real.log (Real.exp 1 / β) = 1 - Real.log β := by
      rw [Real.log_div (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hβpos), Real.log_exp]
    have h2 : (Real.exp 1 / β) ^ m = (Real.exp (Real.log (Real.exp 1 / β))) ^ m := by
      rw [Real.exp_log ha0]
    rw [h2, ← Real.exp_nat_mul, hl]
  have hNexp : (N : ℝ) = Real.exp (Real.log (N : ℝ)) := (Real.exp_log hNpos).symm
  have hinv : (1 - Real.exp 1 / β)⁻¹ = Real.exp (-Real.log (1 - Real.exp 1 / β)) := by
    rw [Real.exp_neg, Real.exp_log h1a]
  rw [ham, hNexp, hinv, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hmle : (m : ℝ) * (1 - Real.log β) ≤ h * (1 - Real.log β) := by
    have hmv : (m : ℝ) = (Nat.floor h : ℝ) + 1 := by rw [hmdef]; push_cast; ring
    rw [hmv]
    exact mul_le_mul_of_nonpos_right hmge hmlog
  have h1 : Real.log (N : ℝ) - Real.log (1 - Real.exp 1 / β) ≤ h * (Real.log β - 2) := by
    linarith
  linarith

theorem pr_apriori_part_b (β : ℝ) (hβ : Real.exp 2 < β) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card → ∀ T : ℕ,
      K₀ * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (T : ℝ) →
        idlaMeasure B {ω : TrajSeq B |
            ¬ (clusterTraj B ω T ⊆ R B (β * (T : ℝ) / (B.card : ℝ)))}
          ≤ ENNReal.ofReal (Real.exp (-(β * (T : ℝ) / (B.card : ℝ)))) := by
  have hβpos : 0 < β := lt_trans (Real.exp_pos 2) hβ
  have he1 : Real.exp 1 < β := lt_trans (Real.exp_lt_exp.mpr (by norm_num)) hβ
  have ha0 : 0 < Real.exp 1 / β := div_pos (Real.exp_pos 1) hβpos
  have h1a : 0 < 1 - Real.exp 1 / β := by
    have : Real.exp 1 / β < 1 := (div_lt_one hβpos).mpr he1
    linarith
  have hlogβ : 2 < Real.log β := (Real.lt_log_iff_exp_lt hβpos).mpr hβ
  refine ⟨2 / (β * (Real.log β - 2)), by positivity, ⌈(1 - Real.exp 1 / β)⁻¹⌉₊ + 2, ?_⟩
  intro B hNB T hT
  have hcard : 1 ≤ B.card := le_trans (by omega) hNB
  have hNpos : (0 : ℝ) < B.card := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hcard)
  have hlogN : -Real.log (1 - Real.exp 1 / β) ≤ Real.log (B.card : ℝ) := by
    have hge : (1 - Real.exp 1 / β)⁻¹ ≤ (B.card : ℝ) := by
      have h1 : ((⌈(1 - Real.exp 1 / β)⁻¹⌉₊ : ℝ)) ≤ (B.card : ℝ) := by
        exact_mod_cast (le_trans (Nat.le_add_right _ 2) hNB)
      have h2 : (1 - Real.exp 1 / β)⁻¹ ≤ (⌈(1 - Real.exp 1 / β)⁻¹⌉₊ : ℝ) := Nat.le_ceil _
      linarith
    have h3 : Real.log ((1 - Real.exp 1 / β)⁻¹) ≤ Real.log (B.card : ℝ) :=
      Real.log_le_log (by positivity) hge
    rwa [Real.log_inv] at h3
  have hK : 2 * Real.log (B.card : ℝ) ≤ (β * (T : ℝ) / (B.card : ℝ)) * (Real.log β - 2) := by
    have hpos : 0 < Real.log β - 2 := by linarith
    have hden : 0 < β * (Real.log β - 2) := mul_pos hβpos hpos
    have key : (2 / (β * (Real.log β - 2))) * (B.card : ℝ) * Real.log (B.card : ℝ)
        * ((β * (Real.log β - 2)) / (B.card : ℝ)) = 2 * Real.log (B.card : ℝ) := by
      field_simp
    have hmul := mul_le_mul_of_nonneg_right hT (le_of_lt (div_pos hden hNpos))
    calc 2 * Real.log (B.card : ℝ)
        = (2 / (β * (Real.log β - 2))) * (B.card : ℝ) * Real.log (B.card : ℝ)
            * ((β * (Real.log β - 2)) / (B.card : ℝ)) := key.symm
      _ ≤ (T : ℝ) * ((β * (Real.log β - 2)) / (B.card : ℝ)) := hmul
      _ = (β * (T : ℝ) / (B.card : ℝ)) * (Real.log β - 2) := by ring
  have hlink : β * (T : ℝ) / (B.card : ℝ) = β * (T : ℝ) / (B.card : ℝ) := rfl
  have hmain := apriori_tsum_le_exp B External.lazyRwRecurrent_holds T β hβ
    (β * (T : ℝ) / (B.card : ℝ)) (by positivity) hlink
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  exact arith_bound β hβ B.card hcard (β * (T : ℝ) / (B.card : ℝ)) hlogN hK

end IdlaCyl
