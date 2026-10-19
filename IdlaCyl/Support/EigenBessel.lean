/-
Bessel's inequality for the eigenbasis at one vertex.

`paper/idla-cylinder-gff.tex:1096`:

  "Since `(f_j^N)_{j=1}^N` is an orthonormal basis of `ℝ^{V_N}` in the normalized
   inner product, Parseval's identity gives `∑_{j=1}^N (f_j^N(x))^2 = N` for
   every `x ∈ V_N`, hence `∑_{j=2}^K (f_j^N(x))^2 ≤ N`."

The paper uses Parseval's identity, which is an equality for a full basis.
Only the inequality is needed, and it follows from orthonormality of the
modes `1 ≤ k ≤ N` alone, by expanding the squared distance from the indicator
of `x` to its projection onto the span of the modes `2 ≤ k ≤ K`.
-/
import IdlaCyl.Support.Spectral

namespace IdlaCyl

open Finset

/-- For a diagonalisation of the base kernel with orthonormal eigenvectors, the
squared values of the modes `2 ≤ k ≤ K` at any vertex sum to at most the number
of vertices `N`. -/
theorem sum_sq_eigen_le_card (B : Base) (S : SpectralData B) (K : ℕ) (hK : K ≤ B.card)
    (x : B.V) :
    ∑ k ∈ Finset.Icc 2 K, (S.f k x) ^ 2 ≤ (B.card : ℝ) := by
  set n : ℝ := (B.card : ℝ) with hn_def
  have hn2 : (2 : ℝ) ≤ n := by
    have h2 : 2 ≤ B.card := B.nontrivial
    rw [hn_def]
    exact_mod_cast h2
  have hnpos : 0 < n := by linarith
  have hne : n ≠ 0 := ne_of_gt hnpos
  set I : Finset ℕ := Finset.Icc 2 K with hI
  have hidx : ∀ k ∈ I, 1 ≤ k ∧ k ≤ B.card := by
    intro k hk
    rw [hI, Finset.mem_Icc] at hk
    obtain ⟨hk1, hk2⟩ := hk
    exact ⟨by omega, by omega⟩
  -- orthogonality in the unnormalised form
  have horth : ∀ j ∈ I, ∀ k ∈ I,
      ∑ y : B.V, S.f j y * S.f k y = n * (if j = k then 1 else 0) := by
    intro j hj k hk
    have h1 := S.orthonormal j k (hidx j hj).1 (hidx j hj).2 (hidx k hk).1 (hidx k hk).2
    rw [← hn_def] at h1
    have h2 : n * ((1 / n) * ∑ y : B.V, S.f j y * S.f k y)
        = n * (if j = k then 1 else 0) := by
      rw [h1]
    rw [← mul_assoc, mul_one_div_cancel hne, one_mul] at h2
    exact h2
  -- the projection `h = ∑_k c_k f_k` with coefficients `c_k = f_k(x) / N`
  set c : ℕ → ℝ := fun k => S.f k x / n with hc
  set h : B.V → ℝ := fun y => ∑ k ∈ I, c k * S.f k y with hh
  have hsumsq : ∑ y : B.V, (h y) ^ 2 = n * ∑ k ∈ I, c k ^ 2 := by
    have expand : ∀ y : B.V,
        (h y) ^ 2 = ∑ j ∈ I, ∑ k ∈ I, (c j * c k) * (S.f j y * S.f k y) := by
      intro y
      simp only [hh, sq, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hterm : ∀ j ∈ I, ∀ k ∈ I,
        ∑ y : B.V, (c j * c k) * (S.f j y * S.f k y)
          = (c j * c k) * (n * (if j = k then 1 else 0)) := by
      intro j hj k hk
      rw [← Finset.mul_sum, horth j hj k hk]
    have hdiag : ∀ j ∈ I, ∑ k ∈ I, (c j * c k) * (n * (if j = k then 1 else 0))
        = n * c j ^ 2 := by
      intro j hj
      rw [Finset.sum_eq_single_of_mem j hj
        (fun k _ hkj => by simp [Ne.symm hkj])]
      rw [if_pos rfl]
      ring
    simp only [expand]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun k hk => hterm j hj k hk), hdiag j hj]
  -- the projection evaluated at `x`, and its squared norm, in terms of `T`
  set T : ℝ := ∑ k ∈ I, S.f k x ^ 2 with hT_def
  have hxT : h x = (1 / n) * T := by
    simp only [hh, hc, hT_def]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hnormT : n * ∑ k ∈ I, c k ^ 2 = (1 / n) * T := by
    rw [Finset.mul_sum, hT_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [hc]
    field_simp
  -- expansion of `‖1_x - h‖²`
  have hv2 : ∑ y : B.V, (if y = x then (1 : ℝ) else 0) ^ 2 = 1 := by
    simp [ite_pow]
  have hcross : ∑ y : B.V, (if y = x then (1 : ℝ) else 0) * h y = h x := by
    simp [ite_mul]
  have hexp : ∑ y : B.V, ((if y = x then (1 : ℝ) else 0) - h y) ^ 2
      = 1 - 2 * h x + ∑ y : B.V, (h y) ^ 2 := by
    have hpt : ∀ y : B.V, ((if y = x then (1 : ℝ) else 0) - h y) ^ 2
        = (if y = x then (1 : ℝ) else 0) ^ 2
          - 2 * ((if y = x then (1 : ℝ) else 0) * h y) + (h y) ^ 2 :=
      fun y => by ring
    simp only [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hv2, hcross]
  have hnonneg : 0 ≤ ∑ y : B.V, ((if y = x then (1 : ℝ) else 0) - h y) ^ 2 :=
    Finset.sum_nonneg (fun y _ => sq_nonneg _)
  have hfin : (1 / n) * T ≤ 1 := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hfin hnpos.le
  rwa [← mul_assoc, mul_one_div_cancel hne, one_mul, mul_one] at hscaled

end IdlaCyl
