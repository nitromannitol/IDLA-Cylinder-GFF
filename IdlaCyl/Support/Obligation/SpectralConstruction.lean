module

/-
The spectral decomposition of the base kernel, conditional on three
quadratic-form facts about `P_N`.

`paper/idla-cylinder-gff.tex:301-311`: `P_N` has real eigenvalues
`1 = λ_1 > λ_2 ≥ ⋯ ≥ λ_N ≥ 0`, with eigenvectors `f_1 ≡ 1, …, f_N` forming an
orthonormal basis for `⟨f,g⟩ = (1/N) ∑_x f(x) g(x)`.

`P_N` is symmetric and fixes the constants, so it preserves the orthogonal
complement `W` of the constants in `ℝ^{V_N} = EuclideanSpace ℝ V_N`.  The
spectral theorem on `W` gives `N - 1` orthonormal eigenvectors `e_i` with
decreasing eigenvalues `ev i`; the paper's data is `λ_1 = 1`, `f_1 ≡ 1`, and
`λ_{i+2} = ev i`, `f_{i+2} = √N e_i`.  Each `ev i` is a Rayleigh quotient,
so `0 ≤ ev i ≤ 1` follows from the quadratic-form inputs `hnn`, `hle`, and
`ev i < 1` from `hfix` (a unit eigenvector for `1` is constant, hence zero on
`W`).
-/
public import IdlaCyl.Support.Spectral

@[expose] public section

namespace IdlaCyl.Obligation

open IdlaCyl

/-- `P_N` as a linear map of `ℝ^{V_N}` with its Euclidean structure. -/
noncomputable def specOp (B : Base) : EuclideanSpace ℝ B.V →ₗ[ℝ] EuclideanSpace ℝ B.V :=
  Matrix.toEuclideanLin (Matrix.of fun x x' => B.P x x')

theorem spectralData_exists_of_op_apply (B : Base) (u : EuclideanSpace ℝ B.V) (x : B.V) :
    WithLp.ofLp (specOp B u) x = ∑ x', B.P x x' * WithLp.ofLp u x' := by
  simp [specOp, Matrix.mulVec, dotProduct]

theorem spectralData_exists_of_inner_eq (B : Base) (u w : EuclideanSpace ℝ B.V) :
    inner ℝ u w = ∑ x, WithLp.ofLp u x * WithLp.ofLp w x := by
  simp [PiLp.inner_apply, mul_comm]

theorem spectralData_exists_of_op_symm (B : Base) : (specOp B).IsSymmetric := by
  unfold specOp
  refine Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.IsHermitian.ext fun i j => ?_)
  simp [B.P_symm]

/-- The constant function `1` in `ℝ^{V_N}`. -/
noncomputable def specOne (B : Base) : EuclideanSpace ℝ B.V :=
  WithLp.toLp 2 (fun _ => (1 : ℝ))

/-- The orthogonal complement of the constants. -/
noncomputable def specW (B : Base) : Submodule ℝ (EuclideanSpace ℝ B.V) :=
  (ℝ ∙ specOne B)ᗮ

theorem spectralData_exists_of_one_ne_zero (B : Base) : specOne B ≠ 0 := by
  intro h
  have := congrArg (fun u : EuclideanSpace ℝ B.V => WithLp.ofLp u B.pt) h
  simp [specOne] at this

theorem spectralData_exists_of_mem_W (B : Base) (v : EuclideanSpace ℝ B.V) :
    v ∈ specW B ↔ ∑ x, WithLp.ofLp v x = 0 := by
  unfold specW
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right,
    spectralData_exists_of_inner_eq]
  simp [specOne]

theorem spectralData_exists_of_op_one (B : Base) : specOp B (specOne B) = specOne B := by
  ext x
  rw [spectralData_exists_of_op_apply]
  simp [specOne, B.P_row_sum]

theorem spectralData_exists_of_op_mem_W (B : Base) :
    ∀ v ∈ specW B, specOp B v ∈ specW B := by
  intro v hv
  unfold specW at hv ⊢
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hv ⊢
  rw [← spectralData_exists_of_op_symm B (specOne B) v, spectralData_exists_of_op_one]
  exact hv

theorem spectralData_exists_of_finrank (B : Base) :
    Module.finrank ℝ (specW B) = B.card - 1 := by
  have h2 : 2 ≤ B.card := B.nontrivial
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ B.V) = B.card - 1 + 1) :=
    ⟨by rw [finrank_euclideanSpace]; show B.card = B.card - 1 + 1; omega⟩
  exact Submodule.finrank_orthogonal_span_singleton (spectralData_exists_of_one_ne_zero B)

/-- `P_N` restricted to the orthogonal complement of the constants. -/
noncomputable def specRes (B : Base) : specW B →ₗ[ℝ] specW B :=
  (specOp B).restrict (spectralData_exists_of_op_mem_W B)

theorem spectralData_exists_of_res_symm (B : Base) : (specRes B).IsSymmetric :=
  (spectralData_exists_of_op_symm B).restrict_invariant (spectralData_exists_of_op_mem_W B)

/-- The eigenvalues of `P_N` on the complement of the constants, in decreasing order. -/
noncomputable def specEv (B : Base) : Fin (B.card - 1) → ℝ :=
  (spectralData_exists_of_res_symm B).eigenvalues (spectralData_exists_of_finrank B)

/-- The corresponding orthonormal eigenvectors, as vectors of `ℝ^{V_N}`. -/
noncomputable def specVec (B : Base) (i : Fin (B.card - 1)) : EuclideanSpace ℝ B.V :=
  (((spectralData_exists_of_res_symm B).eigenvectorBasis
    (spectralData_exists_of_finrank B) i : specW B) : EuclideanSpace ℝ B.V)

theorem spectralData_exists_of_ev_antitone (B : Base) : Antitone (specEv B) :=
  (spectralData_exists_of_res_symm B).eigenvalues_antitone (spectralData_exists_of_finrank B)

theorem spectralData_exists_of_vec_mem (B : Base) (i : Fin (B.card - 1)) :
    specVec B i ∈ specW B :=
  ((spectralData_exists_of_res_symm B).eigenvectorBasis (spectralData_exists_of_finrank B) i).2

theorem spectralData_exists_of_vec_eigen (B : Base) (i : Fin (B.card - 1)) :
    specOp B (specVec B i) = specEv B i • specVec B i := by
  have h := (spectralData_exists_of_res_symm B).apply_eigenvectorBasis
    (spectralData_exists_of_finrank B) i
  have h' := congrArg (fun w : specW B => (w : EuclideanSpace ℝ B.V)) h
  simpa [specVec, specEv, specRes, LinearMap.restrict_apply] using h'

theorem spectralData_exists_of_vec_inner (B : Base) (i j : Fin (B.card - 1)) :
    inner ℝ (specVec B i) (specVec B j) = if i = j then (1 : ℝ) else 0 := by
  have h := orthonormal_iff_ite.mp
    ((spectralData_exists_of_res_symm B).eigenvectorBasis
      (spectralData_exists_of_finrank B)).orthonormal i j
  simpa [specVec, Submodule.coe_inner] using h


theorem spectralData_exists_of_vec_sum_zero (B : Base) (i : Fin (B.card - 1)) :
    ∑ x, WithLp.ofLp (specVec B i) x = 0 :=
  (spectralData_exists_of_mem_W B _).mp (spectralData_exists_of_vec_mem B i)

theorem spectralData_exists_of_vec_eigen_apply (B : Base) (i : Fin (B.card - 1)) (x : B.V) :
    ∑ x', B.P x x' * WithLp.ofLp (specVec B i) x' = specEv B i * WithLp.ofLp (specVec B i) x := by
  rw [← spectralData_exists_of_op_apply, spectralData_exists_of_vec_eigen]
  simp

theorem spectralData_exists_of_vec_orth (B : Base) (i j : Fin (B.card - 1)) :
    ∑ x, WithLp.ofLp (specVec B i) x * WithLp.ofLp (specVec B j) x
      = if i = j then (1 : ℝ) else 0 := by
  rw [← spectralData_exists_of_inner_eq]
  exact spectralData_exists_of_vec_inner B i j

theorem spectralData_exists_of_ev_eq_quad (B : Base) (i : Fin (B.card - 1)) :
    specEv B i = ∑ x, ∑ x', WithLp.ofLp (specVec B i) x * B.P x x' *
      WithLp.ofLp (specVec B i) x' := by
  have h1 : ∀ x, ∑ x', WithLp.ofLp (specVec B i) x * B.P x x' * WithLp.ofLp (specVec B i) x'
      = specEv B i * (WithLp.ofLp (specVec B i) x * WithLp.ofLp (specVec B i) x) := by
    intro x
    calc ∑ x', WithLp.ofLp (specVec B i) x * B.P x x' * WithLp.ofLp (specVec B i) x'
        = WithLp.ofLp (specVec B i) x * ∑ x', B.P x x' * WithLp.ofLp (specVec B i) x' := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x' _ => by ring
      _ = _ := by rw [spectralData_exists_of_vec_eigen_apply]; ring
  rw [Finset.sum_congr rfl fun x _ => h1 x, ← Finset.mul_sum,
    spectralData_exists_of_vec_orth B i i]
  simp

theorem spectralData_exists_of_ev_nonneg (B : Base)
    (hnn : ∀ v : B.V → ℝ, 0 ≤ ∑ x, ∑ x', v x * B.P x x' * v x') (i : Fin (B.card - 1)) :
    0 ≤ specEv B i := by
  rw [spectralData_exists_of_ev_eq_quad]
  exact hnn _

theorem spectralData_exists_of_ev_le_one (B : Base)
    (hle : ∀ v : B.V → ℝ, ∑ x, ∑ x', v x * B.P x x' * v x' ≤ ∑ x, v x ^ 2)
    (i : Fin (B.card - 1)) : specEv B i ≤ 1 := by
  rw [spectralData_exists_of_ev_eq_quad]
  refine (hle _).trans (le_of_eq ?_)
  simpa [sq] using spectralData_exists_of_vec_orth B i i

theorem spectralData_exists_of_ev_ne_one (B : Base)
    (hfix : ∀ v : B.V → ℝ, (∀ x, ∑ x', B.P x x' * v x' = v x) → ∀ x y, v x = v y)
    (i : Fin (B.card - 1)) : specEv B i ≠ 1 := by
  intro h1
  have hfixed : ∀ x, ∑ x', B.P x x' * WithLp.ofLp (specVec B i) x'
      = WithLp.ofLp (specVec B i) x := by
    intro x
    rw [spectralData_exists_of_vec_eigen_apply, h1, one_mul]
  have hconst := hfix _ hfixed
  have h2 : 2 ≤ B.card := B.nontrivial
  have hN : (B.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsum := spectralData_exists_of_vec_sum_zero B i
  rw [Finset.sum_congr rfl fun x _ => hconst x B.pt, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have hzero : WithLp.ofLp (specVec B i) B.pt = 0 := by
    rcases mul_eq_zero.mp hsum with h | h
    · exact absurd h hN
    · exact h
  have horth := spectralData_exists_of_vec_orth B i i
  rw [Finset.sum_congr rfl fun x _ => by rw [hconst x B.pt, hzero, zero_mul]] at horth
  simp at horth

theorem spectralData_exists_of_ev_lt_one (B : Base)
    (hle : ∀ v : B.V → ℝ, ∑ x, ∑ x', v x * B.P x x' * v x' ≤ ∑ x, v x ^ 2)
    (hfix : ∀ v : B.V → ℝ, (∀ x, ∑ x', B.P x x' * v x' = v x) → ∀ x y, v x = v y)
    (i : Fin (B.card - 1)) : specEv B i < 1 :=
  lt_of_le_of_ne (spectralData_exists_of_ev_le_one B hle i)
    (spectralData_exists_of_ev_ne_one B hfix i)


/-! ### Re-indexing to the paper's `1 ≤ k ≤ N` -/

/-- The eigenvalues in the paper's indexing: `λ_1 = 1`, `λ_{i+2} = ev i`. -/
noncomputable def specLam (B : Base) (ev : Fin (B.card - 1) → ℝ) (k : ℕ) : ℝ :=
  if k = 1 then 1 else if h : 2 ≤ k ∧ k ≤ B.card then ev ⟨k - 2, by omega⟩ else 0

/-- The eigenvectors in the paper's indexing and normalisation: `f_1 ≡ 1`,
`f_{i+2} = √N e_i`. -/
noncomputable def specF (B : Base) (e : Fin (B.card - 1) → EuclideanSpace ℝ B.V) (k : ℕ)
    (x : B.V) : ℝ :=
  if k = 1 then 1
  else if h : 2 ≤ k ∧ k ≤ B.card then
    Real.sqrt B.card * WithLp.ofLp (e ⟨k - 2, by omega⟩) x
  else 0

theorem spectralData_exists_of_exists_idx (B : Base) {k : ℕ} (hk2 : 2 ≤ k) (hk : k ≤ B.card) :
    ∃ i : Fin (B.card - 1), k = i.val + 2 :=
  ⟨⟨k - 2, by omega⟩, by simp only; omega⟩

theorem spectralData_exists_of_lam_idx (B : Base) (ev : Fin (B.card - 1) → ℝ)
    (i : Fin (B.card - 1)) : specLam B ev (i.val + 2) = ev i := by
  have h : 2 ≤ i.val + 2 ∧ i.val + 2 ≤ B.card := by have := i.2; omega
  unfold specLam
  rw [if_neg (by omega), dif_pos h]
  simp

theorem spectralData_exists_of_F_idx (B : Base) (e : Fin (B.card - 1) → EuclideanSpace ℝ B.V)
    (i : Fin (B.card - 1)) (x : B.V) :
    specF B e (i.val + 2) x = Real.sqrt B.card * WithLp.ofLp (e i) x := by
  have h : 2 ≤ i.val + 2 ∧ i.val + 2 ≤ B.card := by have := i.2; omega
  unfold specF
  rw [if_neg (by omega), dif_pos h]
  simp

theorem spectralData_exists_of_card_pos (B : Base) : (0 : ℝ) < B.card := by
  have h2 : 2 ≤ B.card := B.nontrivial
  exact_mod_cast (by omega : 0 < B.card)

theorem spectralData_exists_of_orth_one_one (B : Base)
    (e : Fin (B.card - 1) → EuclideanSpace ℝ B.V) :
    (1 / (B.card : ℝ)) * ∑ x : B.V, specF B e 1 x * specF B e 1 x = 1 := by
  have hN := (spectralData_exists_of_card_pos B).ne'
  simp [specF]
  field_simp
  rfl

theorem spectralData_exists_of_orth_one_idx (B : Base)
    (e : Fin (B.card - 1) → EuclideanSpace ℝ B.V)
    (hsum : ∀ i, ∑ x, WithLp.ofLp (e i) x = 0) (i : Fin (B.card - 1)) :
    (1 / (B.card : ℝ)) * ∑ x : B.V, specF B e 1 x * specF B e (i.val + 2) x = 0 := by
  simp only [spectralData_exists_of_F_idx]
  simp [specF, ← Finset.mul_sum, hsum]

theorem spectralData_exists_of_orth_idx_idx (B : Base)
    (e : Fin (B.card - 1) → EuclideanSpace ℝ B.V)
    (horth : ∀ i j, ∑ x, WithLp.ofLp (e i) x * WithLp.ofLp (e j) x = if i = j then 1 else 0)
    (i j : Fin (B.card - 1)) :
    (1 / (B.card : ℝ)) * ∑ x : B.V, specF B e (i.val + 2) x * specF B e (j.val + 2) x
      = if i.val + 2 = j.val + 2 then 1 else 0 := by
  have hN := (spectralData_exists_of_card_pos B).ne'
  have hs : ∀ x, specF B e (i.val + 2) x * specF B e (j.val + 2) x
      = (B.card : ℝ) * (WithLp.ofLp (e i) x * WithLp.ofLp (e j) x) := by
    intro x
    rw [spectralData_exists_of_F_idx, spectralData_exists_of_F_idx]
    calc Real.sqrt B.card * WithLp.ofLp (e i) x * (Real.sqrt B.card * WithLp.ofLp (e j) x)
        = (Real.sqrt B.card * Real.sqrt B.card) *
          (WithLp.ofLp (e i) x * WithLp.ofLp (e j) x) := by ring
      _ = _ := by rw [Real.mul_self_sqrt (spectralData_exists_of_card_pos B).le]
  rw [Finset.sum_congr rfl fun x _ => hs x, ← Finset.mul_sum, horth i j, ← mul_assoc,
    one_div, inv_mul_cancel₀ hN, one_mul]
  have : (i.val + 2 = j.val + 2) ↔ i = j := by
    constructor
    · intro h; ext; omega
    · intro h; rw [h]
  simp only [this]


/-! ### Assembly -/

/-- Any orthonormal family `e` of mean-zero eigenvectors, with non-increasing
eigenvalues in `[0, 1)`, yields `SpectralData` in the paper's indexing. -/
theorem spectralData_exists_of_assemble (B : Base) (ev : Fin (B.card - 1) → ℝ)
    (e : Fin (B.card - 1) → EuclideanSpace ℝ B.V)
    (hsum : ∀ i, ∑ x, WithLp.ofLp (e i) x = 0)
    (heig : ∀ i x, ∑ x', B.P x x' * WithLp.ofLp (e i) x' = ev i * WithLp.ofLp (e i) x)
    (horth : ∀ i j, ∑ x, WithLp.ofLp (e i) x * WithLp.ofLp (e j) x = if i = j then 1 else 0)
    (hnn : ∀ i, 0 ≤ ev i) (hanti : Antitone ev) (hlt : ∀ i, ev i < 1) :
    Nonempty (SpectralData B) := by
  -- fields in order: eigen, orthonormal, lam_one, f_one, antitone, lam_two_lt, lam_nonneg
  refine ⟨⟨specLam B ev, specF B e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro k hk1 hkN x
    by_cases hk : k = 1
    · subst hk
      simp [specLam, specF, B.P_row_sum]
    · obtain ⟨i, rfl⟩ := spectralData_exists_of_exists_idx B (by omega) hkN
      simp only [spectralData_exists_of_F_idx, spectralData_exists_of_lam_idx]
      calc ∑ x', B.P x x' * (Real.sqrt B.card * WithLp.ofLp (e i) x')
          = Real.sqrt B.card * ∑ x', B.P x x' * WithLp.ofLp (e i) x' := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun x' _ => by ring
        _ = _ := by rw [heig]; ring
  · intro j k hj1 hjN hk1 hkN
    by_cases hj : j = 1 <;> by_cases hk : k = 1
    · subst hj; subst hk
      simpa using spectralData_exists_of_orth_one_one B e
    · subst hj
      obtain ⟨i, rfl⟩ := spectralData_exists_of_exists_idx B (by omega) hkN
      rw [spectralData_exists_of_orth_one_idx B e hsum i, if_neg (by omega)]
    · subst hk
      obtain ⟨i, rfl⟩ := spectralData_exists_of_exists_idx B (by omega) hjN
      have := spectralData_exists_of_orth_one_idx B e hsum i
      rw [if_neg (by omega)]
      simpa [mul_comm] using this
    · obtain ⟨i, rfl⟩ := spectralData_exists_of_exists_idx B (by omega) hjN
      obtain ⟨l, rfl⟩ := spectralData_exists_of_exists_idx B (by omega) hkN
      exact spectralData_exists_of_orth_idx_idx B e horth i l
  · simp [specLam]
  · intro x
    simp [specF]
  · intro j k hj1 hjk hkN
    by_cases hj : j = 1
    · subst hj
      by_cases hk : k = 1
      · subst hk; exact le_rfl
      · obtain ⟨i, rfl⟩ := spectralData_exists_of_exists_idx B (by omega) hkN
        rw [spectralData_exists_of_lam_idx]
        simp [specLam, (hlt i).le]
    · obtain ⟨a, rfl⟩ := spectralData_exists_of_exists_idx B (by omega) (hjk.trans hkN)
      obtain ⟨b, rfl⟩ := spectralData_exists_of_exists_idx B (by omega) hkN
      rw [spectralData_exists_of_lam_idx, spectralData_exists_of_lam_idx]
      exact hanti (show a.val ≤ b.val by omega)
  · intro h2
    have h := spectralData_exists_of_lam_idx B ev ⟨0, by omega⟩
    simp only [zero_add] at h
    rw [h]
    exact hlt _
  · intro k hk1 hkN
    by_cases hk : k = 1
    · subst hk; simp [specLam]
    · obtain ⟨i, rfl⟩ := spectralData_exists_of_exists_idx B (by omega) hkN
      rw [spectralData_exists_of_lam_idx]
      exact hnn i

/-- `IdlaCyl.spectralData_exists`, from the three quadratic-form inputs. -/
theorem spectralData_exists_of (B : Base)
    (hnn : ∀ v : B.V → ℝ, 0 ≤ ∑ x, ∑ x', v x * B.P x x' * v x')
    (hle : ∀ v : B.V → ℝ, ∑ x, ∑ x', v x * B.P x x' * v x' ≤ ∑ x, v x ^ 2)
    (hfix : ∀ v : B.V → ℝ, (∀ x, ∑ x', B.P x x' * v x' = v x) → ∀ x y, v x = v y) :
    Nonempty (SpectralData B) :=
  spectralData_exists_of_assemble B (specEv B) (specVec B)
    (spectralData_exists_of_vec_sum_zero B)
    (spectralData_exists_of_vec_eigen_apply B)
    (spectralData_exists_of_vec_orth B)
    (spectralData_exists_of_ev_nonneg B hnn)
    (spectralData_exists_of_ev_antitone B)
    (spectralData_exists_of_ev_lt_one B hle hfix)

end IdlaCyl.Obligation
