/-
The full canonical `clm:Q-W` good-event bound (`paper/idla-cylinder-gff.tex:1004-1035`).

`Support/ClmQWBound.lean` gives the deterministic slab reduction
`|Q_N − W_N| ≤ (1/(N a_N)) ∑_{slab} |ψ|²`; `Support/PsiSlab.lean` evaluates the
slab mass of `psiExt` as `(2Δ+1) N ∑_k α_k(T/(N a_N))² e^{2 q_k Δ}`.  This file
multiplies them out into the paper's display at `tex:1031-1034`,

  `|Q_N − W_N| 1_E ≤ (2Δ_N+1)/a_N ∑_{k=2}^K α_k(T/(N a_N))² e^{2 q_k^N Δ_N/a_N}`,

and records the `O(Δ_N/a_N)` form the lemma is used for (`tex:1035-1037`).

## Rate and normalisation conventions

As documented in `Support/ClmQWAnalytic.lean` and `Support/PsiSlab.lean`, the
Lean `SpectralData.qk k` is the *un-rescaled* root `q_k` with
`cosh(q_k) = 2 − λ_k^N`; the paper's rate at `def:qkN` is `q_k^N = a_N q_k`, so
the paper's exponent `2 q_k^N Δ_N/a_N` is `2 · S.qk k · Δ`.  The factor `1/(N a_N)`
of `Q_N` and the factor `N` in the slab mass of `ψ` combine to `1/a_N` — the
paper's prefactor.  A coefficient `(2Δ+1)/(N a_N)` would carry one spurious `1/N`
(and would be false, since the slab mass is genuinely `N(2Δ+1)∑`).

Everything is on the canonical carrier; no `Driver`/`driverLaw`/`cluster`.
-/
import IdlaCyl.Support.PsiSlab
import IdlaCyl.Support.ClmQWAnalytic

namespace IdlaCyl

open MeasureTheory
open scoped BigOperators

variable (B : Base)

/-- **`clm:Q-W`, assembled** (`tex:1016-1034`).  On the good event, the difference
of the two quadratic masses, with `ψ = psiExt` built from the paper's coefficients
`α_k(T/(N a_N))`, is at most the paper's display
`(2Δ+1)/a_N ∑_{k=2}^K α_k(T/(N a_N))² e^{2 q_k Δ}`, where `q_k` is the un-rescaled
root (`S.qk k`), i.e. `e^{2 q_k^N Δ/a_N}` in the paper's rescaled notation. -/
theorem clm_q_w_final (a : ℕ → ℝ) (ha : 0 ≤ a B.card)
    (S : SpectralData B) (h : ℤ) (K : ℕ) (α : ℕ → ℝ → ℝ) (hK : K ≤ B.card)
    (T : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hcenter : (T : ℝ) / (B.card : ℝ) = (h : ℝ))
    (ω : TrajSeq B) (hω : ω ∈ goodEvent B T Δ) :
    |QN B a T (psiExt B S h (psiCoeff K α (a B.card) h)) ω
      - WN B a T (psiExt B S h (psiCoeff K α (a B.card) h)) ω|
      ≤ (2 * Δ + 1) / a B.card *
        ∑ k ∈ Finset.Icc 2 K,
          (α k ((h : ℝ) / (a B.card))) ^ 2 * Real.exp (2 * S.qk k * Δ) := by
  have hN : (0 : ℝ) < (B.card : ℝ) := by
    have h2 : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
    linarith
  have hnonneg : 0 ≤ 1 / ((B.card : ℝ) * a B.card) :=
    div_nonneg zero_le_one (mul_nonneg (le_of_lt hN) ha)
  have h1 := clm_q_w_analytic B a T Δ hΔ ha
    (psiExt B S h (psiCoeff K α (a B.card) h)) ω hω
  have h2 := slabFinset_psiExt_le B S h K α hK (a B.card) T Δ hΔ hcenter
  have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.Icc 2 K,
      (α k ((h : ℝ) / (a B.card))) ^ 2 * Real.exp (2 * S.qk k * Δ) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _))
  calc
    |QN B a T (psiExt B S h (psiCoeff K α (a B.card) h)) ω
        - WN B a T (psiExt B S h (psiCoeff K α (a B.card) h)) ω|
        ≤ 1 / ((B.card : ℝ) * a B.card) *
            ∑ p ∈ slabFinset B T Δ, psiExt B S h (psiCoeff K α (a B.card) h) p ^ 2 := h1
    _ ≤ 1 / ((B.card : ℝ) * a B.card) *
          ((2 * Δ + 1) * (B.card : ℝ) *
            ∑ k ∈ Finset.Icc 2 K,
              (α k ((h : ℝ) / (a B.card))) ^ 2 * Real.exp (2 * S.qk k * Δ)) :=
          mul_le_mul_of_nonneg_left h2 hnonneg
    _ = (2 * Δ + 1) / a B.card *
          ∑ k ∈ Finset.Icc 2 K,
            (α k ((h : ℝ) / (a B.card))) ^ 2 * Real.exp (2 * S.qk k * Δ) := by
          rcases eq_or_ne (a B.card) 0 with ha0 | ha0
          · simp [ha0]
          · field_simp [hN.ne', ha0]

/-- **The `O(Δ/a_N)` form of `clm:Q-W`** (`tex:1035-1037`).  If `Δ ≥ 1/2` and the
spectral sum is bounded by `C`, then `|Q_N − W_N| ≤ 4 C Δ/a_N` on the good event.
The paper applies this with `Δ = Δ_N`, whose boundedness of the spectral sum is
the continuity of `α_k` at `y₀` together with `q_k^N → γ_k` bounded and
`Δ_N/a_N → 0`. -/
theorem clm_q_w_final_le (a : ℕ → ℝ) (ha : 0 ≤ a B.card)
    (S : SpectralData B) (h : ℤ) (K : ℕ) (α : ℕ → ℝ → ℝ) (hK : K ≤ B.card)
    (T : ℕ) (Δ : ℝ) (hΔ : 1 / 2 ≤ Δ)
    (hcenter : (T : ℝ) / (B.card : ℝ) = (h : ℝ))
    (C : ℝ) (hC : 0 ≤ C)
    (hsum : ∑ k ∈ Finset.Icc 2 K,
        (α k ((h : ℝ) / (a B.card))) ^ 2 * Real.exp (2 * S.qk k * Δ) ≤ C)
    (ω : TrajSeq B) (hω : ω ∈ goodEvent B T Δ) :
    |QN B a T (psiExt B S h (psiCoeff K α (a B.card) h)) ω
      - WN B a T (psiExt B S h (psiCoeff K α (a B.card) h)) ω|
      ≤ 4 * C * (Δ / a B.card) := by
  have h0 : 0 ≤ Δ := le_trans (by norm_num) hΔ
  have hmain := clm_q_w_final B a ha S h K α hK T Δ h0 hcenter ω hω
  have hgap : 2 * Δ + 1 ≤ 4 * Δ := by linarith
  calc
    |QN B a T (psiExt B S h (psiCoeff K α (a B.card) h)) ω
        - WN B a T (psiExt B S h (psiCoeff K α (a B.card) h)) ω|
        ≤ (2 * Δ + 1) / a B.card *
            ∑ k ∈ Finset.Icc 2 K,
              (α k ((h : ℝ) / (a B.card))) ^ 2 * Real.exp (2 * S.qk k * Δ) := hmain
    _ ≤ (2 * Δ + 1) / a B.card * C :=
          mul_le_mul_of_nonneg_left hsum (div_nonneg (by linarith) ha)
    _ ≤ 4 * Δ / a B.card * C :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hgap ha) hC
    _ = 4 * C * (Δ / a B.card) := by ring

/-- **`clm:Q-W` at the paper's time** `T = N⌊y₀ a_N⌋` (`tex:1028`), where
`h = T/N = ⌊y₀ a_N⌋` is an integer and the coefficient is `α_k(⌊y₀ a_N⌋/a_N)`. -/
theorem clm_q_w_final_paperT (a : ℕ → ℝ) (ha : 0 ≤ a B.card)
    (S : SpectralData B) (K : ℕ) (α : ℕ → ℝ → ℝ) (hK : K ≤ B.card)
    (y₀ : ℝ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (ω : TrajSeq B) (hω : ω ∈ goodEvent B (B.card * ⌊y₀ * a B.card⌋₊) Δ) :
    |QN B a (B.card * ⌊y₀ * a B.card⌋₊)
        (psiExt B S (⌊y₀ * a B.card⌋₊)
          (psiCoeff K α (a B.card) (⌊y₀ * a B.card⌋₊))) ω
      - WN B a (B.card * ⌊y₀ * a B.card⌋₊)
        (psiExt B S (⌊y₀ * a B.card⌋₊)
          (psiCoeff K α (a B.card) (⌊y₀ * a B.card⌋₊))) ω|
      ≤ (2 * Δ + 1) / a B.card *
        ∑ k ∈ Finset.Icc 2 K,
          (α k ((⌊y₀ * a B.card⌋₊ : ℝ) / (a B.card))) ^ 2 *
            Real.exp (2 * S.qk k * Δ) := by
  have hN : (0 : ℝ) < (B.card : ℝ) := by
    have h2 : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
    linarith
  have hcenter : ((B.card * ⌊y₀ * a B.card⌋₊ : ℕ) : ℝ) / (B.card : ℝ)
      = ((⌊y₀ * a B.card⌋₊ : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    field_simp [hN.ne']
  exact clm_q_w_final B a ha S (⌊y₀ * a B.card⌋₊) K α hK
    (B.card * ⌊y₀ * a B.card⌋₊) Δ hΔ hcenter ω hω

end IdlaCyl
