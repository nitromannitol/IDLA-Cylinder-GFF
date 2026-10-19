/-
The analytic half of `clm:Q-W` (`paper/idla-cylinder-gff.tex:1019-1035`).

`Support/ClmQWBound.lean` proves the deterministic slab estimate: on the good
event `E = {R_{T/N-d} ⊆ A(T) ⊆ R_{T/N+d}}` the quadratic masses over `A_+(T)` and
over the rectangle `R_{T/N} \ R_0` differ by at most the quadratic mass of the
paper's slab `R_{T/N+d} \ R_{⌊T/N-d⌋}`.  This file lands the remaining analytic
step of `tex:1019-1035`:

* the canonical good event `goodEvent`, and the quadratic functionals
  `QN`, `WN` (`tex:1005-1007`);
* `clm_q_w_analytic`: on `goodEvent`,
  `|QN - WN| ≤ (1/(N a_N)) ∑_{slab} ψ²` (`tex:1016-1019`);
* `modeSum_slab_le` / `slabFinset_modeSum_le`: for the harmonic-extension mode
  sum the slab mass is at most `N (2Δ+1) ∑_{k=2}^K α_k² e^{2 q_k Δ}`
  (`tex:1019-1026`), via `modeSum_layerMeanSquare` (`Support/LeReplaceInputs.lean`)
  and the layer-count bound `#slab-levels ≤ 2Δ+1`;
* `clm_q_w_analytic_modeSum` and its `psiExt` corollary: on `goodEvent`,
  `|QN - WN| ≤ (2Δ+1)/a_N ∑_{k=2}^K α_k(T/(N a_N))² e^{2 q_k Δ}`
  (`tex:1023-1026`).

## The rate convention

The paper writes the exponent at `tex:1025` as `e^{2 q_k^N Δ_N/a_N}`, where
`cosh(q_k^N/a_N) = 2 - λ_k` (`def:qkN`, `tex:730`), so `q_k^N/a_N = q_k` is the
*un-rescaled* rate.  The Lean `SpectralData.qk k` (`Support/Spectral.lean`) is
exactly that un-rescaled root, `cosh(S.qk k) = 2 - λ_k`, so the final exponent is
`Real.exp (2 * S.qk k * Δ)`.  Written with the rescaled `q_k^N`, the exponent is
`exp(2 q_k^N Δ/a)`; the two agree after `q_k^N Δ_N/a_N = S.qk k · Δ`.

## The normaliser

`a : ℕ → ℝ` is the paper's `a_N`; since the ambient base `B` has `N = B.card`
vertices, the value used is `a B.card`, matching `Setup.a` (`Support/Spectral.lean`).
-/
import IdlaCyl.Support.ClmQWBound
import IdlaCyl.Support.LeReplaceInputs
import IdlaCyl.Support.HarmonicExtension

namespace IdlaCyl

open MeasureTheory
open scoped BigOperators

variable (B : Base)

/-- The canonical good event of `clm:Q-W` (`tex:1005-1007`, `tex:1017`):
`R_{T/N-Δ} ⊆ A(T) ⊆ R_{T/N+Δ}`. -/
noncomputable def goodEvent (T : ℕ) (Δ : ℝ) : Set (TrajSeq B) :=
  {ω | R B ((T : ℝ) / (B.card : ℝ) - Δ) ⊆ clusterTraj B ω T ∧
       clusterTraj B ω T ⊆ R B ((T : ℝ) / (B.card : ℝ) + Δ)}

/-- `Q_N = (1/(N a_N)) ∑_{A_+(T)} |ψ|²` (`tex:1005-1007`). -/
noncomputable def QN (a : ℕ → ℝ) (T : ℕ) (ψ : Site B → ℝ) (ω : TrajSeq B) : ℝ :=
  1 / ((B.card : ℝ) * a B.card) * ∑ p ∈ clusterPlusFinset B ω T, ψ p ^ 2

/-- `W_N = (1/(N a_N)) ∑_{R_{T/N}\setminus R_0} |ψ|²` (`tex:1005-1007`). -/
noncomputable def WN (a : ℕ → ℝ) (T : ℕ) (ψ : Site B → ℝ) (_ω : TrajSeq B) : ℝ :=
  1 / ((B.card : ℝ) * a B.card) * ∑ p ∈ rectangleFinset B T, ψ p ^ 2

/-- The mode sum `∑_{k=2}^K α_k f_k(x) e^{q_k(y-h)}` of `tex:820-821`, `tex:941-948`.
For `K = B.card` this is `psiExt` (`Support/HarmonicExtension.lean`). -/
noncomputable def modeSumPsi (S : SpectralData B) (h : ℤ) (K : ℕ) (α : ℕ → ℝ) :
    Site B → ℝ :=
  fun p => ∑ k ∈ Finset.Icc 2 K,
    α k * exponentialMode B (S.f k) (S.qk k) (h : ℝ) p

/-- `modeSum_layerMeanSquare` restated for `modeSumPsi` (`tex:820-821`,
`tex:941-948`). -/
theorem modeSumPsi_layerMeanSquare (S : SpectralData B) (h : ℤ) (K : ℕ) (α : ℕ → ℝ)
    (hK : K ≤ B.card) (y : ℤ) :
    layerMeanSquare B (modeSumPsi B S h K α) y
      = ∑ k ∈ Finset.Icc 2 K, α k ^ 2 *
          Real.exp (2 * S.qk k * ((y : ℝ) - (h : ℝ))) := by
  change layerMeanSquare B
      (fun p => ∑ k ∈ Finset.Icc 2 K,
        α k * exponentialMode B (S.f k) (S.qk k) (h : ℝ) p) y = _
  exact modeSum_layerMeanSquare B S h K α hK y

/-- **`clm:Q-W`, analytic first step** (`tex:1016-1019`): on the good event the
two quadratic masses differ by at most the normalised slab mass. -/
theorem clm_q_w_analytic (a : ℕ → ℝ) (T : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (ha : 0 ≤ a B.card) (ψ : Site B → ℝ) (ω : TrajSeq B)
    (hω : ω ∈ goodEvent B T Δ) :
    |QN B a T ψ ω - WN B a T ψ ω|
      ≤ 1 / ((B.card : ℝ) * a B.card) * ∑ p ∈ slabFinset B T Δ, ψ p ^ 2 := by
  obtain ⟨hsub, hsup⟩ := hω
  have h := clm_q_w_bound B ω T Δ hΔ hsub hsup ψ
  have hN : (0 : ℝ) < (B.card : ℝ) := by
    have h2 : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
    linarith
  have hnonneg : 0 ≤ 1 / ((B.card : ℝ) * a B.card) :=
    div_nonneg zero_le_one (mul_nonneg (le_of_lt hN) ha)
  unfold QN WN
  rw [← mul_sub, abs_mul, abs_of_nonneg hnonneg]
  exact mul_le_mul_of_nonneg_left h hnonneg

/-- **The slab mass of the mode sum** (`tex:1019-1026`): for any finite set of
heights `Y` lying within `Δ` of the reference height `h`, the total `ℓ²` mass of
the mode sum over `Y` is at most `#Y · N · ∑_{k=2}^K α_k² e^{2 q_k Δ}`. -/
theorem modeSum_slab_le (S : SpectralData B) (h : ℤ) (K : ℕ) (α : ℕ → ℝ)
    (hK : K ≤ B.card) (Y : Finset ℤ) (Δ : ℝ)
    (hY : ∀ y ∈ Y, |(y : ℝ) - (h : ℝ)| ≤ Δ) :
    (∑ y ∈ Y, ∑ x : B.V, modeSumPsi B S h K α (x, y) ^ 2)
      ≤ Y.card * (B.card : ℝ) *
        ∑ k ∈ Finset.Icc 2 K, α k ^ 2 * Real.exp (2 * S.qk k * Δ) := by
  have hψy : ∀ y : ℤ,
      (∑ x : B.V, modeSumPsi B S h K α (x, y) ^ 2)
        = (B.card : ℝ) *
            ∑ k ∈ Finset.Icc 2 K, α k ^ 2 * Real.exp (2 * S.qk k * ((y : ℝ) - (h : ℝ))) := by
    intro y
    rw [← card_mul_layerMeanSquare B (modeSumPsi B S h K α) y,
      modeSumPsi_layerMeanSquare B S h K α hK y]
  calc
    (∑ y ∈ Y, ∑ x : B.V, modeSumPsi B S h K α (x, y) ^ 2)
        = ∑ y ∈ Y, (B.card : ℝ) *
            ∑ k ∈ Finset.Icc 2 K, α k ^ 2 *
              Real.exp (2 * S.qk k * ((y : ℝ) - (h : ℝ))) := by
          exact Finset.sum_congr rfl fun y _ => hψy y
    _ = (B.card : ℝ) * ∑ y ∈ Y,
            ∑ k ∈ Finset.Icc 2 K, α k ^ 2 *
              Real.exp (2 * S.qk k * ((y : ℝ) - (h : ℝ))) := by
          rw [Finset.mul_sum]
    _ ≤ (B.card : ℝ) * ∑ y ∈ Y,
            ∑ k ∈ Finset.Icc 2 K, α k ^ 2 * Real.exp (2 * S.qk k * Δ) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg B.card)
          apply Finset.sum_le_sum
          intro y hy
          apply Finset.sum_le_sum
          intro k hk
          apply mul_le_mul_of_nonneg_left
          · apply Real.exp_le_exp.mpr
            have hk' := Finset.mem_Icc.mp hk
            have hq : 0 ≤ S.qk k :=
              le_of_lt (S.qk_pos hk'.1 (le_trans hk'.2 hK))
            have hyh : (y : ℝ) - (h : ℝ) ≤ Δ := (abs_le.mp (hY y hy)).2
            have : 2 * S.qk k * ((y : ℝ) - (h : ℝ)) ≤ 2 * S.qk k * Δ :=
              mul_le_mul_of_nonneg_left hyh (by linarith)
            linarith
          · exact sq_nonneg _
    _ = Y.card * (B.card : ℝ) *
          ∑ k ∈ Finset.Icc 2 K, α k ^ 2 * Real.exp (2 * S.qk k * Δ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring

/-- The number of levels in the paper's slab is at most `2Δ+1`. -/
theorem slabLevels_card_le (T : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ) :
    ((Finset.Icc (⌊(T : ℝ) / (B.card : ℝ) - Δ⌋ + 1)
        ⌊(T : ℝ) / (B.card : ℝ) + Δ⌋ : Finset ℤ).card : ℝ) ≤ 2 * Δ + 1 := by
  have hgap :
      ((⌊(T : ℝ) / (B.card : ℝ) + Δ⌋ - ⌊(T : ℝ) / (B.card : ℝ) - Δ⌋ : ℤ) : ℝ) < 2 * Δ + 1 := by
    have h1 : ((⌊(T : ℝ) / (B.card : ℝ) + Δ⌋ : ℤ) : ℝ) ≤ (T : ℝ) / (B.card : ℝ) + Δ :=
      Int.floor_le ((T : ℝ) / (B.card : ℝ) + Δ)
    have h2 : (T : ℝ) / (B.card : ℝ) - Δ < ((⌊(T : ℝ) / (B.card : ℝ) - Δ⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one ((T : ℝ) / (B.card : ℝ) - Δ)
    push_cast
    linarith
  rw [Int.card_Icc]
  rw [show ⌊(T : ℝ) / (B.card : ℝ) + Δ⌋ + 1 - (⌊(T : ℝ) / (B.card : ℝ) - Δ⌋ + 1)
        = ⌊(T : ℝ) / (B.card : ℝ) + Δ⌋ - ⌊(T : ℝ) / (B.card : ℝ) - Δ⌋ from by ring]
  by_cases hpos : 0 < ⌊(T : ℝ) / (B.card : ℝ) + Δ⌋ - ⌊(T : ℝ) / (B.card : ℝ) - Δ⌋
  · have hnn : 0 ≤ ⌊(T : ℝ) / (B.card : ℝ) + Δ⌋ - ⌊(T : ℝ) / (B.card : ℝ) - Δ⌋ :=
      le_of_lt hpos
    have hcast : ((⌊(T : ℝ) / (B.card : ℝ) + Δ⌋ - ⌊(T : ℝ) / (B.card : ℝ) - Δ⌋).toNat : ℝ)
        = ((⌊(T : ℝ) / (B.card : ℝ) + Δ⌋ - ⌊(T : ℝ) / (B.card : ℝ) - Δ⌋ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hnn
    rw [hcast]
    exact le_of_lt hgap
  · have hz : (⌊(T : ℝ) / (B.card : ℝ) + Δ⌋ - ⌊(T : ℝ) / (B.card : ℝ) - Δ⌋).toNat = 0 :=
      Int.toNat_of_nonpos (by omega)
    rw [hz]
    simp only [Nat.cast_zero]
    linarith [hΔ]

/-- **The slab mass for the paper's slab** (`tex:1019-1026`), specialised to
`Y = {⌊T/N-Δ⌋+1, …, ⌊T/N+Δ⌋}`.  The hypothesis `hcenter` records the paper's
`h = T/N` (`T = N⌊y₀ a_N⌋`). -/
theorem slabFinset_modeSum_le (S : SpectralData B) (h : ℤ) (K : ℕ) (α : ℕ → ℝ)
    (hK : K ≤ B.card) (T : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hcenter : (T : ℝ) / (B.card : ℝ) = (h : ℝ)) :
    (∑ p ∈ slabFinset B T Δ, modeSumPsi B S h K α p ^ 2)
      ≤ (2 * Δ + 1) * (B.card : ℝ) *
        ∑ k ∈ Finset.Icc 2 K, α k ^ 2 * Real.exp (2 * S.qk k * Δ) := by
  have hY : ∀ y ∈ Finset.Icc (⌊(T : ℝ) / (B.card : ℝ) - Δ⌋ + 1)
        ⌊(T : ℝ) / (B.card : ℝ) + Δ⌋, |(y : ℝ) - (h : ℝ)| ≤ Δ := by
    intro y hy
    have hy' := Finset.mem_Icc.mp hy
    have hy_le : (y : ℝ) ≤ (h : ℝ) + Δ := by
      have h1 : (y : ℝ) ≤ ((⌊(T : ℝ) / (B.card : ℝ) + Δ⌋ : ℤ) : ℝ) := by
        exact_mod_cast hy'.2
      have h2 : ((⌊(T : ℝ) / (B.card : ℝ) + Δ⌋ : ℤ) : ℝ) ≤ (T : ℝ) / (B.card : ℝ) + Δ :=
        Int.floor_le ((T : ℝ) / (B.card : ℝ) + Δ)
      rw [hcenter] at h1 h2
      linarith
    have hy_ge : (h : ℝ) - Δ ≤ (y : ℝ) := by
      have h1 : (((⌊(T : ℝ) / (B.card : ℝ) - Δ⌋ + 1 : ℤ)) : ℝ) ≤ (y : ℝ) := by
        exact_mod_cast hy'.1
      have h2 : (T : ℝ) / (B.card : ℝ) - Δ < ((⌊(T : ℝ) / (B.card : ℝ) - Δ⌋ : ℤ) : ℝ) + 1 :=
        Int.lt_floor_add_one ((T : ℝ) / (B.card : ℝ) - Δ)
      rw [hcenter] at h1 h2
      push_cast at h1
      linarith
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hprod : (∑ p ∈ slabFinset B T Δ, modeSumPsi B S h K α p ^ 2)
      = ∑ y ∈ Finset.Icc (⌊(T : ℝ) / (B.card : ℝ) - Δ⌋ + 1)
          ⌊(T : ℝ) / (B.card : ℝ) + Δ⌋, ∑ x : B.V, modeSumPsi B S h K α (x, y) ^ 2 := by
    rw [slabFinset]
    exact (Finset.sum_product (Finset.univ : Finset B.V)
      (Finset.Icc (⌊(T : ℝ) / (B.card : ℝ) - Δ⌋ + 1)
        ⌊(T : ℝ) / (B.card : ℝ) + Δ⌋)
      (fun p => modeSumPsi B S h K α p ^ 2)).trans Finset.sum_comm
  rw [hprod]
  have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.Icc 2 K, α k ^ 2 * Real.exp (2 * S.qk k * Δ) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _))
  have hbound := modeSum_slab_le B S h K α hK
    (Finset.Icc (⌊(T : ℝ) / (B.card : ℝ) - Δ⌋ + 1)
      ⌊(T : ℝ) / (B.card : ℝ) + Δ⌋) Δ hY
  have hcard := slabLevels_card_le B T Δ hΔ
  calc
    (∑ y ∈ Finset.Icc (⌊(T : ℝ) / (B.card : ℝ) - Δ⌋ + 1)
        ⌊(T : ℝ) / (B.card : ℝ) + Δ⌋, ∑ x : B.V, modeSumPsi B S h K α (x, y) ^ 2)
        ≤ (Finset.Icc (⌊(T : ℝ) / (B.card : ℝ) - Δ⌋ + 1)
            ⌊(T : ℝ) / (B.card : ℝ) + Δ⌋).card * (B.card : ℝ) *
            ∑ k ∈ Finset.Icc 2 K, α k ^ 2 * Real.exp (2 * S.qk k * Δ) := hbound
    _ = (Finset.Icc (⌊(T : ℝ) / (B.card : ℝ) - Δ⌋ + 1)
            ⌊(T : ℝ) / (B.card : ℝ) + Δ⌋).card *
          ((B.card : ℝ) * ∑ k ∈ Finset.Icc 2 K, α k ^ 2 * Real.exp (2 * S.qk k * Δ)) := by
          ring
    _ ≤ (2 * Δ + 1) *
          ((B.card : ℝ) * ∑ k ∈ Finset.Icc 2 K, α k ^ 2 * Real.exp (2 * S.qk k * Δ)) :=
          mul_le_mul_of_nonneg_right hcard
            (mul_nonneg (Nat.cast_nonneg B.card) hsum_nonneg)
    _ = (2 * Δ + 1) * (B.card : ℝ) *
          ∑ k ∈ Finset.Icc 2 K, α k ^ 2 * Real.exp (2 * S.qk k * Δ) := by
          ring

/-- **The analytic half of `clm:Q-W`** (`tex:1019-1026`): on the good event,
`|Q_N - W_N|` is at most `(2Δ+1)/a_N` times the spectral sum
`∑_{k=2}^K α_k² e^{2 q_k Δ}`. -/
theorem clm_q_w_analytic_modeSum (a : ℕ → ℝ) (ha : 0 ≤ a B.card)
    (S : SpectralData B) (h : ℤ) (K : ℕ) (α : ℕ → ℝ) (hK : K ≤ B.card)
    (T : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hcenter : (T : ℝ) / (B.card : ℝ) = (h : ℝ))
    (ω : TrajSeq B) (hω : ω ∈ goodEvent B T Δ) :
    |QN B a T (modeSumPsi B S h K α) ω - WN B a T (modeSumPsi B S h K α) ω|
      ≤ (2 * Δ + 1) / a B.card *
        ∑ k ∈ Finset.Icc 2 K, α k ^ 2 * Real.exp (2 * S.qk k * Δ) := by
  have hN : (0 : ℝ) < (B.card : ℝ) := by
    have h2 : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
    linarith
  have hnonneg : 0 ≤ 1 / ((B.card : ℝ) * a B.card) :=
    div_nonneg zero_le_one (mul_nonneg (le_of_lt hN) ha)
  have h1 := clm_q_w_analytic B a T Δ hΔ ha (modeSumPsi B S h K α) ω hω
  have h2 := slabFinset_modeSum_le B S h K α hK T Δ hΔ hcenter
  calc
    |QN B a T (modeSumPsi B S h K α) ω - WN B a T (modeSumPsi B S h K α) ω|
        ≤ 1 / ((B.card : ℝ) * a B.card) * ∑ p ∈ slabFinset B T Δ,
            modeSumPsi B S h K α p ^ 2 := h1
    _ ≤ 1 / ((B.card : ℝ) * a B.card) *
          ((2 * Δ + 1) * (B.card : ℝ) *
            ∑ k ∈ Finset.Icc 2 K, α k ^ 2 * Real.exp (2 * S.qk k * Δ)) :=
          mul_le_mul_of_nonneg_left h2 hnonneg
    _ = (2 * Δ + 1) / a B.card *
          ∑ k ∈ Finset.Icc 2 K, α k ^ 2 * Real.exp (2 * S.qk k * Δ) := by
          rcases eq_or_ne (a B.card) 0 with ha0 | ha0
          · simp [ha0]
          · field_simp [hN.ne', ha0]

/-- **`clm:Q-W` for `psiExt`** (`tex:1019-1026`): the mode sum truncated at
`K = N` is the harmonic extension `psiExt` (`Support/HarmonicExtension.lean`). -/
theorem clm_q_w_analytic_psiExt (a : ℕ → ℝ) (ha : 0 ≤ a B.card)
    (S : SpectralData B) (h : ℤ) (α : ℕ → ℝ)
    (T : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hcenter : (T : ℝ) / (B.card : ℝ) = (h : ℝ))
    (ω : TrajSeq B) (hω : ω ∈ goodEvent B T Δ) :
    |QN B a T (psiExt B S h α) ω - WN B a T (psiExt B S h α) ω|
      ≤ (2 * Δ + 1) / a B.card *
        ∑ k ∈ Finset.Icc 2 B.card, α k ^ 2 * Real.exp (2 * S.qk k * Δ) :=
  clm_q_w_analytic_modeSum B a ha S h B.card α le_rfl T Δ hΔ hcenter ω hω

end IdlaCyl
