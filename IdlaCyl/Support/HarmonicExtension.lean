module

/-
The harmonic extension `ψ` of `pr:hextension` (`tex:715-746`).

Given `SpectralData B` (the eigenbasis `f_k` with eigenvalues `λ_k`,
`tex:301-311`) and a coefficient sequence `α`, the extension with reference
height `h` is

  `ψ(x,y) = ∑_{k=2}^N α_k f_k(x) e^{q_k (y - h)}`,
  `q_k = arcosh (2 - λ_k)` (`def:qk`).

This file lands the canonical `psiExt` together with the three clauses of
`pr:hextension`: discrete harmonicity, the boundary identity on `y = h`, and the
exponential decay below `h`.  Harmonicity is an immediate application of
`finiteMode_harmonic` from `Support/Harmonic.lean`; the decay uses `q_2 = min_k
q_k` because `λ` is non-increasing.
-/
public import IdlaCyl.Support.Harmonic
public import IdlaCyl.Support.Spectral

@[expose] public section

namespace IdlaCyl

open scoped BigOperators

variable (B : Base)

/-- The harmonic extension (`eq:truepsi`, `tex:738-746`): the finite combination
of the modes `f_k e^{q_k(y-h)}`, `k = 2, …, N`. -/
noncomputable def psiExt (S : SpectralData B) (h : ℤ) (α : ℕ → ℝ) : Site B → ℝ :=
  fun p => ∑ k ∈ Finset.Icc 2 B.card,
    α k * exponentialMode B (S.f k) (S.qk k) (h : ℝ) p

/-- **`pr:hextension`, harmonicity clause** (`tex:716-723`). -/
theorem psiExt_discreteHarmonic (S : SpectralData B) (h : ℤ) (α : ℕ → ℝ) :
    DiscreteHarmonic B (psiExt B S h α) := by
  apply finiteMode_harmonic (s := Finset.Icc 2 B.card) (f := S.f) (lam := S.lam)
    (q := S.qk) (c := α) (h := (h : ℝ))
  · intro k hk x
    rw [Finset.mem_Icc] at hk
    exact S.eigen k (by omega) hk.2 x
  · intro k hk
    rw [Finset.mem_Icc] at hk
    exact S.cosh_qk (by omega) hk.2

/-- **`pr:hextension`, boundary clause** (`tex:722-723`): on the line `y = h`,
`ψ(x,h) = ∑_{k=2}^N α_k f_k(x)`. -/
theorem psiExt_boundary (S : SpectralData B) (h : ℤ) (α : ℕ → ℝ) (x : B.V) :
    psiExt B S h α (x, h) = ∑ k ∈ Finset.Icc 2 B.card, α k * S.f k x := by
  simp [psiExt]

/-- **`pr:hextension`, decay clause** (`tex:689`, `tex:700`).  Since `λ` is
non-increasing, `q_2` is the smallest rate, and the mode sum decays at least as
fast as `e^{q_2(y-h)}` below `h`. -/
theorem psiExt_expDecay (S : SpectralData B) (h : ℤ) (α : ℕ → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ p : Site B, p.2 ≤ h →
      |psiExt B S h α p| ≤ C * Real.exp (c * ((p.2 : ℝ) - (h : ℝ))) := by
  refine ⟨(∑ k ∈ Finset.Icc 2 B.card, |α k| * (∑ x : B.V, |S.f k x|)) + 1,
    by positivity, S.qk 2, S.qk_pos le_rfl B.nontrivial, ?_⟩
  intro p hp
  set c : ℝ := S.qk 2 with hc
  have hcpos : 0 < c := by rw [hc]; exact S.qk_pos le_rfl B.nontrivial
  have hqc : ∀ k ∈ Finset.Icc 2 B.card, c ≤ S.qk k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [hc]
    have hx1 : 0 < 2 - S.lam 2 := by
      have := S.lam_two_lt B.nontrivial
      linarith
    have hx2 : 0 < 2 - S.lam k := by
      have hle1 : S.lam k ≤ 1 := by
        calc S.lam k ≤ S.lam 1 := S.antitone 1 k le_rfl (by omega) hk.2
          _ = 1 := S.lam_one
      linarith
    exact (Real.arcosh_le_arcosh hx1 hx2).mpr (by
      have := S.antitone 2 k (by norm_num) hk.1 hk.2
      linarith)
  have hy : (p.2 : ℝ) - (h : ℝ) ≤ 0 := by
    have : (p.2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hp
    linarith
  calc
    |psiExt B S h α p|
        ≤ ∑ k ∈ Finset.Icc 2 B.card,
            |α k| * |S.f k p.1| * Real.exp (c * ((p.2 : ℝ) - (h : ℝ))) := by
          rw [psiExt]
          refine (Finset.abs_sum_le_sum_abs
            (fun k => α k * exponentialMode B (S.f k) (S.qk k) (h : ℝ) p)
            (Finset.Icc 2 B.card)).trans ?_
          apply Finset.sum_le_sum
          intro k hk
          rw [abs_mul]
          unfold exponentialMode
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          have hexp : Real.exp ((S.qk k) * ((p.2 : ℝ) - (h : ℝ)))
              ≤ Real.exp (c * ((p.2 : ℝ) - (h : ℝ))) :=
            Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (hqc k hk) hy)
          have := mul_le_mul_of_nonneg_left hexp
            (mul_nonneg (abs_nonneg (α k)) (abs_nonneg (S.f k p.1)))
          simpa only [mul_assoc] using this
    _ = Real.exp (c * ((p.2 : ℝ) - (h : ℝ))) *
          ∑ k ∈ Finset.Icc 2 B.card, |α k| * |S.f k p.1| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ ≤ Real.exp (c * ((p.2 : ℝ) - (h : ℝ))) *
          ((∑ k ∈ Finset.Icc 2 B.card, |α k| * (∑ x : B.V, |S.f k x|)) + 1) := by
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          have h1 : (∑ k ∈ Finset.Icc 2 B.card, |α k| * |S.f k p.1|)
              ≤ ∑ k ∈ Finset.Icc 2 B.card, |α k| * (∑ x : B.V, |S.f k x|) :=
            Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
              (Finset.single_le_sum (fun x _ => abs_nonneg (S.f k x))
                (Finset.mem_univ p.1)) (abs_nonneg (α k))
          linarith
    _ = ((∑ k ∈ Finset.Icc 2 B.card, |α k| * (∑ x : B.V, |S.f k x|)) + 1) *
          Real.exp (c * ((p.2 : ℝ) - (h : ℝ))) := by ring

end IdlaCyl
