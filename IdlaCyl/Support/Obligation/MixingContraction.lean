/-
The mixing-time defining set is nonempty, given a positive power of the kernel.

`paper/idla-cylinder-gff.tex:269` (the mixing time): "the smallest integer
`t ≥ 0` with `max_x ‖P_N^t(x,·) - π_N‖_TV ≤ 1/4`".  This file proves, by a
Doeblin contraction, that the set of such `t` is nonempty whenever some power
`P_N^m` has all entries bounded below by a positive constant.  That positivity
is taken as a hypothesis here; it is the separate obligation about powers of
the lazy kernel.
-/
import IdlaCyl.Support.Spectral

namespace IdlaCyl.Obligation

open IdlaCyl

/-- Entries of `P_N^n` are nonnegative. -/
theorem mixingTime_spec_of_pos_nonneg (B : Base) (n : ℕ) (x y : B.V) :
    0 ≤ basePow B n x y := by
  induction n generalizing y with
  | zero => simp only [basePow]; split_ifs <;> norm_num
  | succ n ih =>
    simp only [basePow]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (ih z) (B.P_nonneg z y)

/-- Rows of `P_N^n` sum to one. -/
theorem mixingTime_spec_of_pos_row_sum (B : Base) (n : ℕ) (x : B.V) :
    ∑ y, basePow B n x y = 1 := by
  induction n with
  | zero => simp [basePow]
  | succ n ih =>
    simp only [basePow]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, B.P_row_sum, mul_one]
    exact ih

/-- Columns of `P_N^n` sum to one, by symmetry of `P_N`. -/
theorem mixingTime_spec_of_pos_col_sum (B : Base) (n : ℕ) (y : B.V) :
    ∑ x, basePow B n x y = 1 := by
  induction n generalizing y with
  | zero => simp [basePow]
  | succ n ih =>
    simp only [basePow]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ih, one_mul]
    calc ∑ z, B.P z y = ∑ z, B.P y z := Finset.sum_congr rfl fun z _ => B.P_symm z y
      _ = 1 := B.P_row_sum y

/-- The semigroup property `P^(n+k) = P^n P^k`. -/
theorem mixingTime_spec_of_pos_add (B : Base) (n k : ℕ) (x y : B.V) :
    basePow B (n + k) x y = ∑ z, basePow B n x z * basePow B k z y := by
  induction k generalizing y with
  | zero => simp [basePow]
  | succ k ih =>
    show basePow B ((n + k) + 1) x y = _
    simp only [basePow]
    simp_rw [ih, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]

/-- A constant sum over the vertices is `N` times the constant. -/
theorem mixingTime_spec_of_pos_sum_const (B : Base) (c : ℝ) :
    ∑ _y : B.V, c = (B.card : ℝ) * c := by
  simp [Base.card]

/-- `N ≠ 0`. -/
theorem mixingTime_spec_of_pos_card_ne (B : Base) : (B.card : ℝ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr (by simp [Base.card])

/-- One Doeblin contraction step. -/
theorem mixingTime_spec_of_pos_contract (B : Base) (m : ℕ) (δ : ℝ)
    (hδ : ∀ x y : B.V, δ ≤ basePow B m x y) (n : ℕ) (x : B.V) :
    ∑ y, |basePow B (n + m) x y - 1 / (B.card : ℝ)|
      ≤ (1 - (B.card : ℝ) * δ) * ∑ y, |basePow B n x y - 1 / (B.card : ℝ)| := by
  have hN := mixingTime_spec_of_pos_card_ne B
  set ν : B.V → ℝ := fun z => basePow B n x z - 1 / (B.card : ℝ) with hν
  have hsum : ∑ z, ν z = 0 := by
    simp only [hν, Finset.sum_sub_distrib, mixingTime_spec_of_pos_row_sum,
      mixingTime_spec_of_pos_sum_const]
    field_simp
    simp
  have key : ∀ y, basePow B (n + m) x y - 1 / (B.card : ℝ)
      = ∑ z, ν z * (basePow B m z y - δ) := by
    intro y
    have h1 : basePow B (n + m) x y - 1 / (B.card : ℝ)
        = ∑ z, ν z * basePow B m z y := by
      rw [mixingTime_spec_of_pos_add]
      simp only [hν, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
        mixingTime_spec_of_pos_col_sum, mul_one]
    have h2 : ∑ z, ν z * (basePow B m z y - δ) = ∑ z, ν z * basePow B m z y := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, zero_mul, sub_zero]
    rw [h1, h2]
  calc ∑ y, |basePow B (n + m) x y - 1 / (B.card : ℝ)|
      = ∑ y, |∑ z, ν z * (basePow B m z y - δ)| := by simp_rw [key]
    _ ≤ ∑ y, ∑ z, |ν z| * (basePow B m z y - δ) := by
        refine Finset.sum_le_sum fun y _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine le_of_eq (Finset.sum_congr rfl fun z _ => ?_)
        rw [abs_mul, abs_of_nonneg (sub_nonneg.2 (hδ z y))]
    _ = ∑ z, |ν z| * ∑ y, (basePow B m z y - δ) := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
    _ = (1 - (B.card : ℝ) * δ) * ∑ y, |basePow B n x y - 1 / (B.card : ℝ)| := by
        simp only [Finset.sum_sub_distrib, mixingTime_spec_of_pos_row_sum,
          mixingTime_spec_of_pos_sum_const]
        simp only [hν]
        rw [← Finset.sum_mul]
        ring

/-- The contraction factor `1 - N δ` lies in `[0, 1)`. -/
theorem mixingTime_spec_of_pos_factor (B : Base) (m : ℕ) (δ : ℝ) (hpos : 0 < δ)
    (hδ : ∀ x y : B.V, δ ≤ basePow B m x y) :
    0 ≤ 1 - (B.card : ℝ) * δ ∧ 1 - (B.card : ℝ) * δ < 1 := by
  obtain ⟨x0⟩ := (inferInstance : Nonempty B.V)
  constructor
  · have h : ∑ _y : B.V, δ ≤ ∑ y, basePow B m x0 y :=
      Finset.sum_le_sum fun y _ => hδ x0 y
    rw [mixingTime_spec_of_pos_sum_const, mixingTime_spec_of_pos_row_sum] at h
    linarith
  · have hN : (0 : ℝ) < B.card := by
      have : 2 ≤ B.card := B.nontrivial
      exact_mod_cast lt_of_lt_of_le (by norm_num) this
    have := mul_pos hN hpos
    linarith

/-- Iterating the contraction `k` times, starting from total mass `2`. -/
theorem mixingTime_spec_of_pos_iterate (B : Base) (m : ℕ) (δ : ℝ)
    (hδ : ∀ x y : B.V, δ ≤ basePow B m x y) (hq : 0 ≤ 1 - (B.card : ℝ) * δ)
    (k : ℕ) (x : B.V) :
    ∑ y, |basePow B (k * m) x y - 1 / (B.card : ℝ)|
      ≤ (1 - (B.card : ℝ) * δ) ^ k * 2 := by
  have hN := mixingTime_spec_of_pos_card_ne B
  induction k with
  | zero =>
    simp only [Nat.zero_mul, pow_zero, one_mul]
    calc ∑ y, |basePow B 0 x y - 1 / (B.card : ℝ)|
        ≤ ∑ y, (basePow B 0 x y + 1 / (B.card : ℝ)) := by
          refine Finset.sum_le_sum fun y _ => ?_
          have h0 := mixingTime_spec_of_pos_nonneg B 0 x y
          have h1 : (0 : ℝ) ≤ 1 / (B.card : ℝ) := by positivity
          exact abs_le.mpr ⟨by linarith, by linarith⟩
      _ = 2 := by
          rw [Finset.sum_add_distrib, mixingTime_spec_of_pos_row_sum,
            mixingTime_spec_of_pos_sum_const]
          field_simp
          norm_num
  | succ k ih =>
    rw [Nat.succ_mul]
    calc ∑ y, |basePow B (k * m + m) x y - 1 / (B.card : ℝ)|
        ≤ (1 - (B.card : ℝ) * δ) * ∑ y, |basePow B (k * m) x y - 1 / (B.card : ℝ)| :=
          mixingTime_spec_of_pos_contract B m δ hδ (k * m) x
      _ ≤ (1 - (B.card : ℝ) * δ) * ((1 - (B.card : ℝ) * δ) ^ k * 2) :=
          mul_le_mul_of_nonneg_left ih hq
      _ = (1 - (B.card : ℝ) * δ) ^ (k + 1) * 2 := by ring

/-- The mixing-time defining set is nonempty once some power of `P_N` is
entrywise bounded below by a positive constant (`tex:269`). -/
theorem mixingTime_spec_of_pos (B : Base)
    (h : ∃ m : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ x y : B.V, δ ≤ basePow B m x y) :
    {t : ℕ | ∀ x : B.V, tvToUniform B t x ≤ 1 / 4}.Nonempty := by
  obtain ⟨m, δ, hpos, hδ⟩ := h
  obtain ⟨hq0, hq1⟩ := mixingTime_spec_of_pos_factor B m δ hpos hδ
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 4) hq1
  refine ⟨k * m, fun x => ?_⟩
  have h1 := mixingTime_spec_of_pos_iterate B m δ hδ hq0 k x
  unfold tvToUniform
  linarith

end IdlaCyl.Obligation
