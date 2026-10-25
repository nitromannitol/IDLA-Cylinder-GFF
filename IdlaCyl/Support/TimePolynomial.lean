module

public import IdlaCyl.Definitions.RectangularMass

@[expose] public section

/-
Polynomial growth of the GFF time `T = N ⌊y₀ a_N⌋` (`paper/idla-cylinder-gff.tex:875`).

The paper's proof of `Theorem th:GFF` (`tex:398-416`) states that `a_N ≍ √t_rel` is
polynomial in `N`, and that `T = N ⌊y₀ a_N⌋ ≤ N^m` for a fixed integer `m` and all
large `N`.  Here the polynomial lower bound on the spectral gap,
`1 / (2 N³) ≤ 1 - λ₂(N)`, is a premise.  The normalisation
`a_N √(2(1 - λ₂(N))) → γ₂ ∈ (0, ∞)` (`NormalisedAt`, `tex:318-320`) then bounds
`a_N` by a multiple of `N^{3/2}`, which bounds the time by `N³`.
-/

namespace IdlaCyl

open IdlaCyl.Defs Filter

/-- For all large `N` the GFF time `T = N ⌊y₀ a_N⌋` is at most `N³`, given the
lower bound `1 / (2 N³) ≤ 1 - λ₂(N)` on the spectral gap and the normalisation
`a_N √(2(1 - λ₂(N))) → γ₂ > 0`. -/
theorem time_le_card_rpow_three (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀) (γ : ℕ → ℝ)
    (hγ : U.NormalisedAt γ)
    (hgap : ∀ N, 1 / (2 * ((U.B N).card : ℝ) ^ 3) ≤ (U.S N).gap) :
    ∀ᶠ N in atTop, (time U y₀ N : ℝ) ≤ ((U.B N).card : ℝ) ^ (3 : ℝ) := by
  have hlim : Tendsto (fun N => U.a N * Real.sqrt (2 * (1 - (U.S N).lam 2)))
      atTop (nhds (γ 2)) := hγ.1
  obtain ⟨K, hK⟩ := exists_nat_ge (y₀ ^ 2 * (γ 2 + 1) ^ 2)
  filter_upwards [hlim.eventually (gt_mem_nhds (lt_add_one (γ 2))), eventually_ge_atTop 2,
    eventually_ge_atTop K] with N hlt hN2 hNK
  have hlt' : U.a N * Real.sqrt (2 * (1 - (U.S N).lam 2)) < γ 2 + 1 := hlt
  have hcard : (U.B N).card = N := U.card_eq N hN2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hg : 1 / (2 * (N : ℝ) ^ 3) ≤ 1 - (U.S N).lam 2 := by
    have h := hgap N
    rw [hcard] at h
    exact h
  have hinv : 1 / (N : ℝ) ^ 3 ≤ 2 * (1 - (U.S N).lam 2) := by
    have h2 : 1 / (N : ℝ) ^ 3 = 2 * (1 / (2 * (N : ℝ) ^ 3)) := by ring
    rw [h2]
    linarith
  have hs2 : Real.sqrt (2 * (1 - (U.S N).lam 2)) ^ 2 = 2 * (1 - (U.S N).lam 2) := by
    apply Real.sq_sqrt
    exact le_trans (by positivity) hinv
  have hA0 : 0 ≤ U.a N * Real.sqrt (2 * (1 - (U.S N).lam 2)) :=
    mul_nonneg (U.a_pos N).le (Real.sqrt_nonneg _)
  have hsq : (U.a N * Real.sqrt (2 * (1 - (U.S N).lam 2))) ^ 2 ≤ (γ 2 + 1) ^ 2 := by
    nlinarith [hA0, hlt']
  have hsq' : (U.a N) ^ 2 * (2 * (1 - (U.S N).lam 2)) ≤ (γ 2 + 1) ^ 2 := by
    rw [← hs2, ← mul_pow]
    exact hsq
  have hA : (U.a N) ^ 2 ≤ (γ 2 + 1) ^ 2 * (N : ℝ) ^ 3 := by
    have h := (mul_le_mul_of_nonneg_left hinv (sq_nonneg (U.a N))).trans hsq'
    rw [mul_one_div, div_le_iff₀ (by positivity)] at h
    linarith
  have hfl : ((Nat.floor (y₀ * U.a N) : ℕ) : ℝ) ≤ y₀ * U.a N :=
    Nat.floor_le (mul_pos hy₀ (U.a_pos N)).le
  have hNK' : y₀ ^ 2 * (γ 2 + 1) ^ 2 ≤ (N : ℝ) :=
    le_trans hK (by exact_mod_cast hNK)
  have hy : y₀ * U.a N ≤ (N : ℝ) ^ 2 := by
    have hsq2 : (y₀ * U.a N) ^ 2 ≤ ((N : ℝ) ^ 2) ^ 2 := by
      have h2 : y₀ ^ 2 * (U.a N) ^ 2 ≤ y₀ ^ 2 * ((γ 2 + 1) ^ 2 * (N : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hA (sq_nonneg y₀)
      have h3 : y₀ ^ 2 * ((γ 2 + 1) ^ 2 * (N : ℝ) ^ 3) ≤ (N : ℝ) * (N : ℝ) ^ 3 := by
        calc y₀ ^ 2 * ((γ 2 + 1) ^ 2 * (N : ℝ) ^ 3)
            = (y₀ ^ 2 * (γ 2 + 1) ^ 2) * (N : ℝ) ^ 3 := by ring
          _ ≤ (N : ℝ) * (N : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hNK' (by positivity)
      calc (y₀ * U.a N) ^ 2 = y₀ ^ 2 * (U.a N) ^ 2 := by ring
        _ ≤ y₀ ^ 2 * ((γ 2 + 1) ^ 2 * (N : ℝ) ^ 3) := h2
        _ ≤ (N : ℝ) * (N : ℝ) ^ 3 := h3
        _ = ((N : ℝ) ^ 2) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (mul_pos hy₀ (U.a_pos N)).le (by positivity) two_ne_zero).mp hsq2
  have hpow : ((U.B N).card : ℝ) ^ (3 : ℝ) = (N : ℝ) ^ 3 := by
    rw [hcard, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hpow]
  unfold time height
  rw [hcard]
  push_cast
  calc (N : ℝ) * ((Nat.floor (y₀ * U.a N) : ℕ) : ℝ) ≤ (N : ℝ) * (y₀ * U.a N) :=
        mul_le_mul_of_nonneg_left hfl hNpos.le
    _ ≤ (N : ℝ) * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hy hNpos.le
    _ = (N : ℝ) ^ 3 := by ring

end IdlaCyl
