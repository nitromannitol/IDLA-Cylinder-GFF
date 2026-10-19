import IdlaCyl.Support.Spectral
import IdlaCyl.Support.Obligation.MixingContraction
import IdlaCyl.Support.Obligation.BasePowPos

/-!
# Spectral comparisons for the quantitative reduction

Three comparisons between the spectral gap of the base kernel and its mixing
time, with the mixing time taken at threshold `1/4`. The objects are those of
`Support/Spectral.lean`: the mixing time (`paper/idla-cylinder-gff.tex:269`),
the spectral data (`tex:301-311`) and `q_k` (`tex:717-721`).

* `relaxTime_le_two_mixingTime`: `τ_rel ≤ 2 τ_mix`. At time `τ_mix` the total
  variation bound and the zero mean of the second eigenfunction give
  `λ_2^t ≤ 1/2`, and Bernoulli's inequality turns that into `t (1 - λ_2) ≥ 1/2`.
* `inv_sqrt_relaxTime_le_qk_two`: `1/√τ_rel ≤ q_2`, where `cosh q_2 = 2 - λ_2`.
* `sqrt_relaxTime_le`: `√τ_rel ≤ √2 · √τ_mix`, the consequence of the first.

The defining set of the mixing time is nonempty for every base
(`mixingTime_set_nonempty`), which is what makes `sInf` return a genuine mixing
time rather than the junk value `0`.
-/

namespace IdlaCyl.Reduction

open IdlaCyl

variable {B : Base}

/-- At time `0` the total variation distance to the uniform law exceeds `1/4`
at every vertex, once the base has two vertices. -/
theorem tvToUniform_zero_gt (hN : 2 ≤ B.card) (x : B.V) : 1 / 4 < tvToUniform B 0 x := by
  have h1 : 1 < Fintype.card B.V := lt_of_lt_of_le (by norm_num) hN
  have hpos : (0 : ℝ) < B.card := by exact_mod_cast (by omega : 0 < B.card)
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card h1 x
  have hc0 : 0 ≤ 1 / (B.card : ℝ) := by positivity
  have hc1 : 1 / (B.card : ℝ) ≤ 1 := by
    rw [div_le_one hpos]
    exact_mod_cast (by omega : 1 ≤ B.card)
  have hsub : ∑ z ∈ ({x, y} : Finset B.V), |basePow B 0 x z - 1 / (B.card : ℝ)|
      ≤ ∑ z : B.V, |basePow B 0 x z - 1 / (B.card : ℝ)| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => abs_nonneg _
  rw [Finset.sum_pair hy.symm] at hsub
  have hxx : basePow B 0 x x = 1 := by simp [basePow]
  have hxy : basePow B 0 x y = 0 := by simp [basePow, hy.symm]
  rw [hxx, hxy, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - 1 / (B.card : ℝ)), zero_sub,
    abs_neg, abs_of_nonneg hc0] at hsub
  unfold tvToUniform
  linarith

/-- Iterating the eigen relation: `∑_y P^t(x,y) f_k(y) = λ_k^t f_k(x)` for `1 ≤ k ≤ N`. -/
theorem sum_basePow_mul_eigen (S : SpectralData B) {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ B.card)
    (t : ℕ) (x : B.V) :
    ∑ y : B.V, basePow B t x y * S.f k y = S.lam k ^ t * S.f k x := by
  induction t generalizing x with
  | zero => simp [basePow]
  | succ t ih =>
    simp only [basePow]
    calc ∑ y : B.V, (∑ z : B.V, basePow B t x z * B.P z y) * S.f k y
        = ∑ z : B.V, basePow B t x z * ∑ y : B.V, B.P z y * S.f k y := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => by ring
      _ = ∑ z : B.V, basePow B t x z * (S.lam k * S.f k z) :=
          Finset.sum_congr rfl fun z _ => by rw [S.eigen k hk1 hkN z]
      _ = S.lam k * ∑ z : B.V, basePow B t x z * S.f k z := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun z _ => by ring
      _ = S.lam k * (S.lam k ^ t * S.f k x) := by rw [ih x]
      _ = S.lam k ^ (t + 1) * S.f k x := by ring

/-- The second eigenfunction has mean zero, by orthogonality to `f_1 ≡ 1`. -/
theorem sum_eigen_two_eq_zero (S : SpectralData B) (hN : 2 ≤ B.card) :
    ∑ x : B.V, S.f 2 x = 0 := by
  have hd := S.orthonormal 1 2 le_rfl (by omega) (by norm_num) hN
  have hne : (1 : ℕ) ≠ 2 := by norm_num
  have hpos : (0 : ℝ) < B.card := by exact_mod_cast (by omega : 0 < B.card)
  simp only [S.f_one, one_mul, if_neg hne] at hd
  rcases mul_eq_zero.mp hd with h0 | h0
  · exact absurd h0 (one_div_pos.mpr hpos).ne'
  · exact h0

/-- A vertex where `|f_2|` is maximal, and `|f_2|` is positive there. -/
theorem exists_max_abs_two (S : SpectralData B) (hN : 2 ≤ B.card) :
    ∃ x0 : B.V, (∀ y : B.V, |S.f 2 y| ≤ |S.f 2 x0|) ∧ 0 < |S.f 2 x0| := by
  haveI : Nonempty B.V := ⟨B.pt⟩
  obtain ⟨x0, -, hx0⟩ :=
    Finset.exists_max_image Finset.univ (fun y => |S.f 2 y|) Finset.univ_nonempty
  refine ⟨x0, fun y => hx0 y (Finset.mem_univ y), ?_⟩
  rcases (abs_nonneg (S.f 2 x0)).lt_or_eq with h | h
  · exact h
  · exfalso
    have hz : ∀ y : B.V, S.f 2 y = 0 := fun y => by
      have hy : |S.f 2 y| ≤ |S.f 2 x0| := hx0 y (Finset.mem_univ y)
      rw [← h] at hy
      exact abs_nonpos_iff.mp hy
    have hd := S.orthonormal 2 2 (by norm_num) hN (by norm_num) hN
    simp [hz] at hd

/-- The total variation bound at a maximal vertex of `f_2`:
`λ_2^t ≤ 2 · ‖P^t(x,·) - π‖_TV` for every `t`. -/
theorem lam_two_pow_le_two_tv (S : SpectralData B) (hN : 2 ≤ B.card) (t : ℕ) (x : B.V)
    (hx : ∀ y : B.V, |S.f 2 y| ≤ |S.f 2 x|) (hM : 0 < |S.f 2 x|) :
    S.lam 2 ^ t ≤ 2 * tvToUniform B t x := by
  have hlam : 0 ≤ S.lam 2 := S.lam_nonneg 2 (by norm_num) hN
  have h1 := sum_basePow_mul_eigen S (k := 2) (by norm_num) hN t x
  have h2 : ∑ y : B.V, (1 / (B.card : ℝ)) * S.f 2 y = 0 := by
    rw [← Finset.mul_sum, sum_eigen_two_eq_zero S hN, mul_zero]
  have hid : S.lam 2 ^ t * S.f 2 x
      = ∑ y : B.V, (basePow B t x y - 1 / (B.card : ℝ)) * S.f 2 y := by
    simp only [sub_mul]
    rw [Finset.sum_sub_distrib, h2, sub_zero, h1]
  have htv : ∑ y : B.V, |basePow B t x y - 1 / (B.card : ℝ)| = 2 * tvToUniform B t x := by
    unfold tvToUniform
    ring
  have hbound : |∑ y : B.V, (basePow B t x y - 1 / (B.card : ℝ)) * S.f 2 y|
      ≤ ∑ y : B.V, |basePow B t x y - 1 / (B.card : ℝ)| * |S.f 2 x| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hx y) (abs_nonneg _)
  have key : S.lam 2 ^ t * |S.f 2 x| ≤ 2 * tvToUniform B t x * |S.f 2 x| := by
    calc S.lam 2 ^ t * |S.f 2 x| = |S.lam 2 ^ t * S.f 2 x| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg hlam t)]
      _ = |∑ y : B.V, (basePow B t x y - 1 / (B.card : ℝ)) * S.f 2 y| := by rw [hid]
      _ ≤ ∑ y : B.V, |basePow B t x y - 1 / (B.card : ℝ)| * |S.f 2 x| := hbound
      _ = 2 * tvToUniform B t x * |S.f 2 x| := by rw [← Finset.sum_mul, htv]
  exact le_of_mul_le_mul_right key hM

/-- The defining set of the mixing time is nonempty (`tex:269`), by the proved
route `Obligation.mixingTime_spec_of_pos` from a positive power of the kernel. -/
theorem mixingTime_set_nonempty (B : Base) :
    {t : ℕ | ∀ x : B.V, tvToUniform B t x ≤ 1 / 4}.Nonempty :=
  Obligation.mixingTime_spec_of_pos B (Obligation.basePow_pos_uniform B)

/-- With two vertices, `mixingTime B ≥ 1`: at time `0` the distance to uniform
exceeds `1/4`. -/
theorem one_le_mixingTime (hN : 2 ≤ B.card) : 1 ≤ mixingTime B := by
  have hmem : ∀ x : B.V, tvToUniform B (mixingTime B) x ≤ 1 / 4 :=
    Nat.sInf_mem (mixingTime_set_nonempty B)
  rcases Nat.eq_zero_or_pos (mixingTime B) with h0 | h0
  · have h := hmem B.pt
    rw [h0] at h
    linarith [tvToUniform_zero_gt hN B.pt]
  · exact h0

/-- `τ_rel ≤ 2 τ_mix`. -/
theorem relaxTime_le_two_mixingTime (S : SpectralData B) (hN : 2 ≤ B.card) :
    S.relaxTime ≤ 2 * mixingTime B := by
  obtain ⟨x0, hx0, hM⟩ := exists_max_abs_two S hN
  have hmem : ∀ x : B.V, tvToUniform B (mixingTime B) x ≤ 1 / 4 :=
    Nat.sInf_mem (mixingTime_set_nonempty B)
  have hlam : 0 ≤ S.lam 2 := S.lam_nonneg 2 (by norm_num) hN
  have hpow := lam_two_pow_le_two_tv S hN (mixingTime B) x0 hx0 hM
  have hhalf : S.lam 2 ^ mixingTime B ≤ 1 / 2 := by linarith [hmem x0]
  have hbern : 1 + (mixingTime B : ℝ) * (S.lam 2 - 1) ≤ S.lam 2 ^ mixingTime B := by
    have h := one_add_mul_le_pow (a := S.lam 2 - 1) (by linarith) (mixingTime B)
    rwa [show (1 : ℝ) + (S.lam 2 - 1) = S.lam 2 by ring] at h
  have hgap : 1 / 2 ≤ (mixingTime B : ℝ) * S.gap := by
    have h := le_trans hbern hhalf
    unfold SpectralData.gap
    linarith [mul_sub (mixingTime B : ℝ) 1 (S.lam 2), mul_one (mixingTime B : ℝ)]
  have hg : 0 < S.gap := by
    unfold SpectralData.gap
    linarith [S.lam_two_lt hN]
  unfold SpectralData.relaxTime
  rw [div_le_iff₀ hg]
  linarith [show 2 * (mixingTime B : ℝ) * S.gap = 2 * ((mixingTime B : ℝ) * S.gap) by ring]

/-- For `0 ≤ x ≤ 1`, `cosh x ≤ 1 + x²`. -/
theorem cosh_le_one_add_sq {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.cosh x ≤ 1 + x ^ 2 := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith
  have hy0 : 0 ≤ x ^ 2 / 2 := by positivity
  calc Real.cosh x ≤ Real.exp (x ^ 2 / 2) := Real.cosh_le_exp_half_sq x
    _ ≤ 1 / (1 - x ^ 2 / 2) := Real.exp_bound_div_one_sub_of_interval hy0 (by linarith)
    _ ≤ 1 + x ^ 2 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx2)]

/-- `1/√τ_rel ≤ q_2`, i.e. `√(1 - λ_2) ≤ arcosh(2 - λ_2)`. -/
theorem inv_sqrt_relaxTime_le_qk_two (S : SpectralData B) (hN : 2 ≤ B.card) :
    1 / Real.sqrt S.relaxTime ≤ S.qk 2 := by
  have hlam : 0 ≤ S.lam 2 := S.lam_nonneg 2 (by norm_num) hN
  have hg : 0 < S.gap := by
    unfold SpectralData.gap
    linarith [S.lam_two_lt hN]
  have hg1 : S.gap ≤ 1 := by
    unfold SpectralData.gap
    linarith
  have hsq : 1 / Real.sqrt S.relaxTime = Real.sqrt S.gap := by
    simp only [SpectralData.relaxTime, one_div, Real.sqrt_inv, inv_inv]
  rw [hsq]
  have hx0 : 0 ≤ Real.sqrt S.gap := Real.sqrt_nonneg _
  have hx1 : Real.sqrt S.gap ≤ 1 := by
    have h := Real.sqrt_le_sqrt hg1
    rwa [Real.sqrt_one] at h
  have hcos : Real.cosh (Real.sqrt S.gap) ≤ Real.cosh (S.qk 2) := by
    have h := cosh_le_one_add_sq hx0 hx1
    rw [Real.sq_sqrt hg.le] at h
    rw [S.cosh_qk (k := 2) (by norm_num) hN]
    have hdef : S.gap = 1 - S.lam 2 := rfl
    linarith
  have habs := Real.cosh_le_cosh.mp hcos
  rwa [abs_of_nonneg hx0, abs_of_nonneg (S.qk_pos le_rfl hN).le] at habs

/-- `√τ_rel ≤ √2 · √τ_mix`, from `τ_rel ≤ 2 τ_mix`. -/
theorem sqrt_relaxTime_le (S : SpectralData B) (hN : 2 ≤ B.card) :
    Real.sqrt S.relaxTime ≤ Real.sqrt 2 * Real.sqrt (mixingTime B) := by
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact Real.sqrt_le_sqrt (relaxTime_le_two_mixingTime S hN)

end IdlaCyl.Reduction
