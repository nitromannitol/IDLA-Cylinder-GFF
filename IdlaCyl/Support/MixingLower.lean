/-
The relaxation lower bound for the mixing time of the base kernel.

`paper/idla-cylinder-gff.tex:269` defines the total variation mixing time
`τ_mix` at threshold `1/4`, and `paper/idla-cylinder-gff.tex:301-311` gives the
spectrum `1 = λ_1 > λ_2 ≥ ⋯ ≥ λ_N ≥ 0` of `P_N` with orthonormal eigenvectors
`f_1 ≡ 1, f_2, …, f_N` for `⟨f,g⟩ = (1/N) ∑_x f(x) g(x)`.

The argument: `P_N^t f_2 = λ_2^t f_2`, and `f_2` has zero mean, so the
eigenvalue equation at a maximiser `x₀` of `|f_2|` can be written with the
centred kernel `P_N^t(x₀,·) - 1/N`, whose `ℓ¹` norm is `2 ‖P_N^t(x₀,·) - π_N‖_TV`.
-/
import IdlaCyl.Support.Obligations

namespace IdlaCyl

open scoped BigOperators

/-- The `t`-step kernel applied to an eigenvector: `∑_y P_N^t(x,y) f_k(y) = λ_k^t f_k(x)`
for every `1 ≤ k ≤ N`. -/
theorem lam_two_pow_basePow_eigen (B : Base) (S : SpectralData B) {k : ℕ}
    (hk : 1 ≤ k) (hkN : k ≤ B.card) (t : ℕ) (x : B.V) :
    ∑ y : B.V, basePow B t x y * S.f k y = S.lam k ^ t * S.f k x := by
  induction t generalizing x with
  | zero => simp [basePow]
  | succ t ih =>
    calc ∑ y : B.V, basePow B (t + 1) x y * S.f k y
        = ∑ y : B.V, ∑ z : B.V, basePow B t x z * B.P z y * S.f k y := by
          simp only [basePow, Finset.sum_mul]
      _ = ∑ z : B.V, basePow B t x z * ∑ y : B.V, B.P z y * S.f k y := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          ring
      _ = ∑ z : B.V, basePow B t x z * (S.lam k * S.f k z) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [S.eigen k hk hkN z]
      _ = S.lam k * ∑ z : B.V, basePow B t x z * S.f k z := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          ring
      _ = S.lam k * (S.lam k ^ t * S.f k x) := by rw [ih x]
      _ = S.lam k ^ (t + 1) * S.f k x := by ring

/-- The second eigenvector has zero mean: `∑_x f_2(x) = 0`, by orthogonality to `f_1 ≡ 1`. -/
theorem lam_two_pow_sum_f_two (B : Base) (S : SpectralData B) :
    ∑ x : B.V, S.f 2 x = 0 := by
  have h2 : 2 ≤ B.card := B.nontrivial
  have hN0 : (B.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h := S.orthonormal 1 2 le_rfl (by omega) (by norm_num) (by omega)
  simp only [S.f_one, one_mul] at h
  rw [if_neg (show ¬ (1 : ℕ) = 2 by norm_num)] at h
  exact (mul_eq_zero.mp h).resolve_left (one_div_ne_zero hN0)

/-- The total variation distance written as an `ℓ¹` norm of the centred kernel:
`∑_y |P_N^t(x,y) - 1/N| = 2 ‖P_N^t(x,·) - π_N‖_TV`. -/
theorem lam_two_pow_sum_abs_eq (B : Base) (t : ℕ) (x : B.V) :
    ∑ y : B.V, |basePow B t x y - 1 / (B.card : ℝ)| = 2 * tvToUniform B t x := by
  unfold tvToUniform
  ring

/-- The relaxation lower bound on the mixing time, in exponential form:
`λ_2^t ≤ 2 max_x ‖P_N^t(x,·) - π_N‖_TV` for every `t`. -/
theorem lam_two_pow_le_two_mul_tv (B : Base) (S : SpectralData B) (t : ℕ) :
    S.lam 2 ^ t ≤ 2 * ⨆ x : B.V, tvToUniform B t x := by
  have h2 : 2 ≤ B.card := B.nontrivial
  obtain ⟨x₀, -, hx₀⟩ :=
    Finset.exists_max_image Finset.univ (fun x => |S.f 2 x|) Finset.univ_nonempty
  have hmax : ∀ y : B.V, |S.f 2 y| ≤ |S.f 2 x₀| := fun y => hx₀ y (Finset.mem_univ y)
  have hpos : 0 < |S.f 2 x₀| := by
    by_contra hcon
    have h0 : |S.f 2 x₀| = 0 := le_antisymm (not_lt.mp hcon) (abs_nonneg _)
    have hz : ∀ y : B.V, S.f 2 y = 0 := fun y =>
      abs_eq_zero.mp (le_antisymm ((hmax y).trans h0.le) (abs_nonneg _))
    have h := S.orthonormal 2 2 (by norm_num) (by omega) (by norm_num) (by omega)
    simp [hz] at h
  have hkey : S.lam 2 ^ t * S.f 2 x₀
      = ∑ y : B.V, (basePow B t x₀ y - 1 / (B.card : ℝ)) * S.f 2 y := by
    have hzero : ∑ y : B.V, (1 / (B.card : ℝ)) * S.f 2 y = 0 := by
      rw [← Finset.mul_sum, lam_two_pow_sum_f_two B S, mul_zero]
    have h := lam_two_pow_basePow_eigen B S (k := 2) (by norm_num) (by omega) t x₀
    simp only [sub_mul, Finset.sum_sub_distrib, hzero, sub_zero]
    exact h.symm
  have habs : |S.lam 2 ^ t| * |S.f 2 x₀|
      ≤ (∑ y : B.V, |basePow B t x₀ y - 1 / (B.card : ℝ)|) * |S.f 2 x₀| := by
    calc |S.lam 2 ^ t| * |S.f 2 x₀| = |S.lam 2 ^ t * S.f 2 x₀| := (abs_mul _ _).symm
      _ = |∑ y : B.V, (basePow B t x₀ y - 1 / (B.card : ℝ)) * S.f 2 y| := by rw [hkey]
      _ ≤ ∑ y : B.V, |(basePow B t x₀ y - 1 / (B.card : ℝ)) * S.f 2 y| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y : B.V, |basePow B t x₀ y - 1 / (B.card : ℝ)| * |S.f 2 y| := by
          simp only [abs_mul]
      _ ≤ ∑ y : B.V, |basePow B t x₀ y - 1 / (B.card : ℝ)| * |S.f 2 x₀| :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hmax y) (abs_nonneg _)
      _ = (∑ y : B.V, |basePow B t x₀ y - 1 / (B.card : ℝ)|) * |S.f 2 x₀| := by
          rw [Finset.sum_mul]
  have hcen : |S.lam 2 ^ t| ≤ ∑ y : B.V, |basePow B t x₀ y - 1 / (B.card : ℝ)| :=
    le_of_mul_le_mul_right habs hpos
  have htv : tvToUniform B t x₀ ≤ ⨆ x : B.V, tvToUniform B t x :=
    le_ciSup (Set.finite_range _).bddAbove x₀
  calc S.lam 2 ^ t ≤ |S.lam 2 ^ t| := le_abs_self _
    _ ≤ ∑ y : B.V, |basePow B t x₀ y - 1 / (B.card : ℝ)| := hcen
    _ = 2 * tvToUniform B t x₀ := lam_two_pow_sum_abs_eq B t x₀
    _ ≤ 2 * ⨆ x : B.V, tvToUniform B t x := mul_le_mul_of_nonneg_left htv (by norm_num)

/-- The relaxation lower bound at the mixing time, in exponential form: `λ_2^{τ_mix} ≤ 1/2`.
This is the exponential form of the standard bound `τ_mix ≥ (τ_rel - 1) log 2`, with
`τ_rel = 1/(1 - λ_2)`. Every `tvToUniform` is at most `1/4` at `τ_mix`, because
`mixingTime_spec` makes the defining set nonempty, so `sInf` is attained. -/
theorem lam_two_pow_mixingTime_le (B : Base) (S : SpectralData B) :
    S.lam 2 ^ mixingTime B ≤ 1 / 2 := by
  have hmem : ∀ x : B.V, tvToUniform B (mixingTime B) x ≤ 1 / 4 := by
    unfold mixingTime
    exact Nat.sInf_mem (mixingTime_spec B)
  have hsup : (⨆ x : B.V, tvToUniform B (mixingTime B) x) ≤ 1 / 4 := ciSup_le hmem
  calc S.lam 2 ^ mixingTime B ≤ 2 * ⨆ x : B.V, tvToUniform B (mixingTime B) x :=
        lam_two_pow_le_two_mul_tv B S (mixingTime B)
    _ ≤ 2 * (1 / 4) := mul_le_mul_of_nonneg_left hsup (by norm_num)
    _ = 1 / 2 := by norm_num

/-- Nonvacuity: the mixing-time bound holds for every base and every spectral data. -/
example : ∀ (B : Base) (S : SpectralData B), S.lam 2 ^ mixingTime B ≤ 1 / 2 :=
  fun B S => lam_two_pow_mixingTime_le B S

end IdlaCyl
