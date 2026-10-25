module

/-
Finite Parseval/orthogonality for the spectral layer, on the canonical
cylinder.

`tex:305-308` (`eq:product`) gives the orthonormality of the eigenbasis in the
normalised inner product; `tex:941-948` (`eqn:psi squared`) turns it into the exact
layerwise `ℓ²` norm of the harmonic extension.  This file lands both, over a
`Finset` of modes so that `psiExt`'s range `Icc 2 K` is handled directly.

All sums are finite; there is no completeness or spanning hypothesis, which is
correct because only the finitely many modes `2, …, K` are used.
-/
public import IdlaCyl.Support.HarmonicExtension

@[expose] public section

namespace IdlaCyl

open scoped BigOperators

variable (B : Base) {ι : Type*} [DecidableEq ι]

/-- Orthonormality for the normalised counting-measure inner product
(`eq:product`, `tex:305-308`), in the unnormalised form `∑_x f_i(x) f_j(x) =
N δ_{ij}`. -/
def CountingOrthonormal (f : ι → B.V → ℝ) : Prop :=
  ∀ i j, (∑ x : B.V, f i x * f j x) = if i = j then (B.card : ℝ) else 0

/-- The restriction of `CountingOrthonormal` to a finite set of modes. -/
def CountingOrthonormalOn (s : Finset ι) (f : ι → B.V → ℝ) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, (∑ x : B.V, f i x * f j x) = if i = j then (B.card : ℝ) else 0

/-- The mode sum `∑_{i ∈ s} c_i f_i(x)`. -/
noncomputable def modeSumOn (s : Finset ι) (f : ι → B.V → ℝ) (c : ι → ℝ) (x : B.V) : ℝ :=
  ∑ i ∈ s, c i * f i x

/-- **Parseval for a finite orthogonal family.**  Exact, with the factor `N`. -/
theorem modeSumOn_norm (s : Finset ι) (f : ι → B.V → ℝ)
    (hf : CountingOrthonormalOn B s f) (c : ι → ℝ) :
    (∑ x : B.V, modeSumOn B s f c x ^ 2) = (B.card : ℝ) * ∑ i ∈ s, c i ^ 2 := by
  classical
  let N : ℝ := B.card
  have collapse (i : ι) (hi : i ∈ s) :
      (∑ j ∈ s, c i * c j * (if i = j then N else 0)) = c i ^ 2 * N := by
    rw [Finset.sum_eq_single_of_mem i hi]
    · rw [if_pos rfl]
      ring
    · intro j _ hji
      rw [if_neg (Ne.symm hji)]
      ring
  calc
    (∑ x : B.V, modeSumOn B s f c x ^ 2)
        = ∑ x : B.V, ∑ i ∈ s, ∑ j ∈ s, c i * c j * (f i x * f j x) := by
          apply Finset.sum_congr rfl
          intro x _
          unfold modeSumOn
          rw [pow_two, Finset.sum_mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ i ∈ s, ∑ x : B.V, ∑ j ∈ s, c i * c j * (f i x * f j x) := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ s, ∑ j ∈ s, ∑ x : B.V, c i * c j * (f i x * f j x) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
    _ = ∑ i ∈ s, ∑ j ∈ s, c i * c j * (∑ x : B.V, f i x * f j x) := by
          simp only [Finset.mul_sum]
    _ = ∑ i ∈ s, ∑ j ∈ s, c i * c j * (if i = j then N else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          rw [hf i hi j hj]
    _ = ∑ i ∈ s, c i ^ 2 * N := by
          apply Finset.sum_congr rfl
          intro i hi
          exact collapse i hi
    _ = (B.card : ℝ) * ∑ i ∈ s, c i ^ 2 := by
          rw [← Finset.sum_mul]
          dsimp [N]
          ring

theorem exp_sq (t : ℝ) : Real.exp t ^ 2 = Real.exp (2 * t) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- **`eqn:psi squared`** (`tex:941-948`): the exact layerwise norm of the mode
sum, with `N` and the rates `q_i`. -/
theorem harmonic_layer_norm (s : Finset ι) (f : ι → B.V → ℝ)
    (hf : CountingOrthonormalOn B s f) (c q : ι → ℝ) (h : ℝ) (y : ℤ) :
    (∑ x : B.V, (∑ i ∈ s, c i * exponentialMode B (f i) (q i) h (x, y)) ^ 2) =
      (B.card : ℝ) * ∑ i ∈ s, c i ^ 2 * Real.exp (2 * q i * ((y : ℝ) - h)) := by
  let b : ι → ℝ := fun i => c i * Real.exp (q i * ((y : ℝ) - h))
  have hfun (x : B.V) :
      (∑ i ∈ s, c i * exponentialMode B (f i) (q i) h (x, y)) = modeSumOn B s f b x := by
    unfold modeSumOn
    apply Finset.sum_congr rfl
    intro i _
    dsimp [exponentialMode, b]
    ring
  simp_rw [hfun]
  rw [modeSumOn_norm B s f hf b]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  dsimp [b]
  rw [mul_pow, exp_sq]
  congr 2
  ring

/-- The eigenbasis of `SpectralData` is orthonormal on the paper's index range
`1 ≤ k ≤ N` (`tex:305-308`). -/
theorem SpectralData.countingOrthonormalOn (S : SpectralData B) :
    CountingOrthonormalOn B (Finset.Icc 1 B.card) (fun k => S.f k) := by
  intro i hi j hj
  rw [Finset.mem_Icc] at hi hj
  have hN : (B.card : ℝ) ≠ 0 := by
    have hpos : 0 < B.card := lt_of_lt_of_le (by norm_num) B.nontrivial
    exact_mod_cast hpos.ne'
  have hmul : (∑ x : B.V, S.f i x * S.f j x)
      = (B.card : ℝ) * (if i = j then 1 else 0) := by
    have h := S.orthonormal i j hi.1 hi.2 hj.1 hj.2
    rw [one_div] at h
    calc (∑ x : B.V, S.f i x * S.f j x)
        = (B.card : ℝ) * ((B.card : ℝ)⁻¹ * ∑ x : B.V, S.f i x * S.f j x) := by
          rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul]
      _ = (B.card : ℝ) * (if i = j then 1 else 0) := by rw [h]
  rw [hmul]
  by_cases hij : i = j <;> simp [hij]

/-- **`eqn:psi squared` for `psiExt`** (`tex:941-948`), on the mode range
`2, …, K` used in `th:GFF` (`K ≤ N`). -/
theorem psiExt_layer_sq (S : SpectralData B) (h : ℤ) (K : ℕ) (α : ℕ → ℝ) (hK : K ≤ B.card)
    (y : ℤ) :
    (∑ x : B.V,
        (∑ k ∈ Finset.Icc 2 K, α k * exponentialMode B (S.f k) (S.qk k) (h : ℝ) (x, y)) ^ 2) =
      (B.card : ℝ) *
        ∑ k ∈ Finset.Icc 2 K, α k ^ 2 *
          Real.exp (2 * S.qk k * ((y : ℝ) - (h : ℝ))) := by
  apply harmonic_layer_norm B (Finset.Icc 2 K) (fun k => S.f k) _ α (fun k => S.qk k) (h : ℝ) y
  intro i hi j hj
  rw [Finset.mem_Icc] at hi hj
  refine SpectralData.countingOrthonormalOn B S i ?_ j ?_
  · rw [Finset.mem_Icc]
    exact ⟨by omega, le_trans hi.2 hK⟩
  · rw [Finset.mem_Icc]
    exact ⟨by omega, le_trans hj.2 hK⟩

/-- Bessel's inequality at a site for a finite orthogonal family, with no
complete-basis hypothesis. -/
theorem row_besselOn (s : Finset ι) (f : ι → B.V → ℝ)
    (hf : CountingOrthonormalOn B s f) (x₀ : B.V) :
    (∑ i ∈ s, f i x₀ ^ 2) ≤ (B.card : ℝ) := by
  classical
  let N : ℝ := B.card
  let S : ℝ := ∑ i ∈ s, f i x₀ ^ 2
  let g : B.V → ℝ := modeSumOn B s f (fun i => f i x₀)
  have hN : 0 < N := by
    dsimp [N]
    have hpos : 0 < B.card := lt_of_lt_of_le (by norm_num) B.nontrivial
    exact_mod_cast hpos
  have hg : (∑ x : B.V, g x ^ 2) = N * S := modeSumOn_norm B s f hf (fun i => f i x₀)
  have hg₀ : g x₀ = S := by
    simp only [g, modeSumOn, S, pow_two]
  have hd₁ (x : B.V) : (if x = x₀ then N else 0) ^ 2 =
      if x = x₀ then N ^ 2 else 0 := by
    split_ifs <;> simp
  have hd₂ (x : B.V) : 2 * (if x = x₀ then N else 0) * g x =
      if x = x₀ then 2 * N * g x₀ else 0 := by
    by_cases hx : x = x₀
    · subst hx
      simp
    · simp [hx]
  have hres : 0 ≤ N ^ 2 - 2 * N * S + N * S := by
    have hn : 0 ≤ ∑ x : B.V, ((if x = x₀ then N else 0) - g x) ^ 2 :=
      Finset.sum_nonneg (fun x _ => sq_nonneg _)
    simp_rw [sub_sq] at hn
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hn
    simp_rw [hd₁, hd₂] at hn
    simpa [hg, hg₀] using hn
  change S ≤ N
  by_contra h
  have hprod : 0 < N * (S - N) := mul_pos hN (sub_pos.mpr (lt_of_not_ge h))
  nlinarith

/-- The pointwise bound that makes the largest martingale increment small
(`thm:martingale-CLT` (b), `tex:888`). -/
theorem modeSumOn_pointwise_sq (s : Finset ι) (f : ι → B.V → ℝ)
    (hf : CountingOrthonormalOn B s f) (c : ι → ℝ) (x : B.V) :
    modeSumOn B s f c x ^ 2 ≤ (B.card : ℝ) * ∑ i ∈ s, c i ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s c (fun i => f i x)
  have hc : 0 ≤ ∑ i ∈ s, c i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hb := mul_le_mul_of_nonneg_left (row_besselOn B s f hf x) hc
  unfold modeSumOn
  exact hcs.trans (by simpa [mul_comm] using hb)

end IdlaCyl
