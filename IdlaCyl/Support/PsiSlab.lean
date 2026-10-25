module

/-
The `psiExt` slab estimate of `clm:Q-W` (`paper/idla-cylinder-gff.tex:1019-1026`).

On the good event `E`, the quadratic mass of the harmonic extension
`ψ(x,y) = ∑_{k=2}^K α_k(T/(N a_N)) f_k(x) e^{q_k (y - T/N)}` over the slab
`{⌈T/N - Δ⌉, …, ⌊T/N + Δ⌋}` is bounded by the per-mode layer estimate
`eqn:psi squared`: for `h = T/N`,

  `∑_{(x,y) ∈ slab} ψ(x,y)²`
    `= N ∑_{k=2}^K α_k(T/(N a))² ∑_{y ∈ slab} e^{2 q_k (y-h)}`
    `≤ (2Δ+1) · N · ∑_{k=2}^K α_k(T/(N a))² e^{2 q_k Δ}`.

## Rate convention (`ClmQWAnalytic` §"The rate convention")

The paper writes the exponent at `tex:1025` as `e^{2 q_k^N Δ_N/a_N}`, with
`cosh(q_k^N/a_N) = 2 - λ_k` (`def:qkN`, `tex:730`).  Thus `q_k^N/a_N = q_k` is the
*un-rescaled* root, and the Lean `SpectralData.qk k` (`Support/Spectral.lean`) is
exactly that root, `cosh(S.qk k) = 2 - λ_k`.  In the repo's `psiExt`
(`Support/HarmonicExtension.lean`) the mode reads `e^{S.qk k (y-h)}`, so the
correct slab exponent is `2 · S.qk k · Δ`, not `2 · S.qk k · Δ / a`.

## The layer factor

`eqn:psi squared` (`Support/SpectralModes.lean:psiExt_layer_sq`) gives the full
layer mass `N ∑_k α_k² e^{2 q_k (y-h)}`; the factor `N = B.card` is present and is
kept here.  A statement without it would be false.

## The normaliser

`a` is the paper's positive `a_N` at `N = B.card`; the coefficient argument
`T/(N a)` is written `(h:ℝ)/a` with `h = T/N`.
-/
public import IdlaCyl.Support.ClmQWAnalytic
public import IdlaCyl.Support.HarmonicExtension
public import IdlaCyl.Support.LeReplaceInputs

@[expose] public section

namespace IdlaCyl

open scoped BigOperators

variable (B : Base)

/-- The coefficient sequence of `le:replace` (`tex:1023-1025`): `k ↦ α_k(h/a)`
for `2 ≤ k ≤ K`, and `0` outside the mode range.  Kept as a sequence so that it
can be fed to `psiExt`, which sums over `Finset.Icc 2 B.card`. -/
noncomputable def psiCoeff (K : ℕ) (α : ℕ → ℝ → ℝ) (a : ℝ) (h : ℤ) : ℕ → ℝ :=
  fun k => if k ∈ Finset.Icc 2 K then α k ((h : ℝ) / a) else 0

/-- The truncated coefficient sequence gives the `K`-mode sum of `tex:1023`
inside `psiExt`. -/
theorem psiExt_psiCoeff_eq_modeSumPsi (S : SpectralData B) (h : ℤ) (K : ℕ)
    (α : ℕ → ℝ → ℝ) (hK : K ≤ B.card) (a : ℝ) :
    psiExt B S h (psiCoeff K α a h)
      = modeSumPsi B S h K (fun k => α k ((h : ℝ) / a)) := by
  funext p
  show (∑ k ∈ Finset.Icc 2 B.card,
      (if k ∈ Finset.Icc 2 K then α k ((h : ℝ) / a) else 0) *
        exponentialMode B (S.f k) (S.qk k) (h : ℝ) p)
    = ∑ k ∈ Finset.Icc 2 K, α k ((h : ℝ) / a) *
        exponentialMode B (S.f k) (S.qk k) (h : ℝ) p
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hK)
    (fun k _ hk => by rw [if_neg hk, zero_mul])]
  exact Finset.sum_congr rfl fun k hk => by rw [if_pos hk]

/-- **The `psiExt` slab estimate** (`tex:1019-1026`), over an arbitrary finite
set of heights `Y` lying within `Δ` of the reference height `h`.  The
coefficients are the paper's `α_k(h/a)` and the layer factor `N = B.card` is
kept. -/
theorem psiExt_slab_le (S : SpectralData B) (h : ℤ) (K : ℕ) (α : ℕ → ℝ → ℝ)
    (hK : K ≤ B.card) (a : ℝ) (Y : Finset ℤ) (Δ : ℝ)
    (hY : ∀ y ∈ Y, |(y : ℝ) - (h : ℝ)| ≤ Δ) :
    (∑ y ∈ Y, ∑ x : B.V, (psiExt B S h (psiCoeff K α a h) (x, y)) ^ 2)
      ≤ Y.card * (B.card : ℝ) *
        ∑ k ∈ Finset.Icc 2 K,
          (α k ((h : ℝ) / a)) ^ 2 * Real.exp (2 * S.qk k * Δ) := by
  rw [psiExt_psiCoeff_eq_modeSumPsi B S h K α hK a]
  exact modeSum_slab_le B S h K (fun k => α k ((h : ℝ) / a)) hK Y Δ hY

/-- **The `psiExt` slab estimate for the paper's slab** (`tex:1023-1026`):
with `h = T/N` and `Δ ≥ 0`, the quadratic mass over
`slabFinset B T Δ` is at most `(2Δ+1) · N · ∑_{k=2}^K α_k(h/a)² e^{2 q_k Δ}`. -/
theorem slabFinset_psiExt_le (S : SpectralData B) (h : ℤ) (K : ℕ) (α : ℕ → ℝ → ℝ)
    (hK : K ≤ B.card) (a : ℝ) (T : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hcenter : (T : ℝ) / (B.card : ℝ) = (h : ℝ)) :
    (∑ p ∈ slabFinset B T Δ, (psiExt B S h (psiCoeff K α a h) p) ^ 2)
      ≤ (2 * Δ + 1) * (B.card : ℝ) *
        ∑ k ∈ Finset.Icc 2 K,
          (α k ((h : ℝ) / a)) ^ 2 * Real.exp (2 * S.qk k * Δ) := by
  rw [psiExt_psiCoeff_eq_modeSumPsi B S h K α hK a]
  exact slabFinset_modeSum_le B S h K (fun k => α k ((h : ℝ) / a)) hK T Δ hΔ hcenter

/-- The `K = B.card` form: the coefficient sequence is the paper's
`α_k(h/a)` and the sum runs over the full spectral range `2, …, N`, so
`psiCoeff` introduces no truncation. -/
theorem slabFinset_psiExt_le_card (S : SpectralData B) (h : ℤ) (α : ℕ → ℝ → ℝ)
    (a : ℝ) (T : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hcenter : (T : ℝ) / (B.card : ℝ) = (h : ℝ)) :
    (∑ p ∈ slabFinset B T Δ,
        (psiExt B S h (fun k => if k ∈ Finset.Icc 2 B.card then α k ((h : ℝ) / a)
          else 0) p) ^ 2)
      ≤ (2 * Δ + 1) * (B.card : ℝ) *
        ∑ k ∈ Finset.Icc 2 B.card,
          (α k ((h : ℝ) / a)) ^ 2 * Real.exp (2 * S.qk k * Δ) :=
  slabFinset_psiExt_le B S h B.card α le_rfl a T Δ hΔ hcenter

end IdlaCyl
