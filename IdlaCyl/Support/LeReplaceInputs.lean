module

/-
The canonical layer-`L²` input of `le:replace` (`tex:820-826`, `eq:layerL2`).

For `ψ : V_N × ℤ → ℝ` the mean square of `ψ` over the *complete* horizontal
layer `V_N × {y}` is

  `layerMeanSquare ψ y = (1/N) ∑_{x ∈ V_N} ψ(x,y)²`,

so that the full layer mass is `N` times it (`tex:820-821`).  Summing this over
a finite slab `Y` of heights gives the finite-slab form of `eq:layerL2`:
if every layer in `Y` has mean square at most `M`, then

  `∑_{y ∈ Y} ∑_{x ∈ V_N} ψ(x,y)² ≤ N · |Y| · M`   (`tex:823-826`),

with `M` any upper bound for the layer mean square — in particular the maximum
over `Y`.

The section also records the two structural facts the paper uses alongside
this estimate:

* `ZeroHorizontalAverage.sum_layer_eq_zero`: a function with the zero
  horizontal average property sums to zero on every complete layer
  (`tex:794`, `tex:819`), which is what makes the layer norms the relevant
  quantity in `le:replace`;
* `modeSum_layerMeanSquare`: for the harmonic-extension mode sum, the layer
  mean square is *exactly* the spectral sum
  `∑_{k=2}^K α_k² e^{2 q_k (y-h)}`, by `psiExt_layer_sq`
  (`Support/SpectralModes.lean`, `tex:941-948`).
-/
public import IdlaCyl.Support.Idla
public import IdlaCyl.Support.SpectralModes

@[expose] public section

namespace IdlaCyl

open scoped BigOperators

variable (B : Base)

/-- The mean square of `ψ` over the complete horizontal layer at height `y`,
`(1/N) ∑_{x ∈ V} ψ(x,y)²` (`tex:820-823`). -/
noncomputable def layerMeanSquare (ψ : Site B → ℝ) (y : ℤ) : ℝ :=
  (B.card : ℝ)⁻¹ * ∑ x : B.V, ψ (x, y) ^ 2

/-- Multiplying the layer mean square by `N` recovers the full layer `ℓ²` mass
(`tex:820-821`). -/
theorem card_mul_layerMeanSquare (ψ : Site B → ℝ) (y : ℤ) :
    (B.card : ℝ) * layerMeanSquare B ψ y = ∑ x : B.V, ψ (x, y) ^ 2 := by
  have hN : (B.card : ℝ) ≠ 0 := by
    have : 0 < B.card := lt_of_lt_of_le (by norm_num) B.nontrivial
    exact_mod_cast this.ne'
  unfold layerMeanSquare
  rw [← mul_assoc, mul_inv_cancel₀ hN, one_mul]

/-- The layer mean square is nonnegative. -/
theorem layerMeanSquare_nonneg (ψ : Site B → ℝ) (y : ℤ) :
    0 ≤ layerMeanSquare B ψ y := by
  unfold layerMeanSquare
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The zero horizontal average property is exactly the statement that every
complete horizontal layer sums to zero (`tex:794`, `tex:819`). -/
theorem ZeroHorizontalAverage.sum_layer_eq_zero {ψ : Site B → ℝ}
    (h : ZeroHorizontalAverage B ψ) (y : ℤ) : (∑ x : B.V, ψ (x, y)) = 0 := h y

/-- **`eq:layerL2`, finite-slab form** (`tex:823-826`): if the mean square of
`ψ` is at most `M` on each layer of a finite slab `Y`, then the total `ℓ²` mass
over the slab is at most `N · |Y| · M`. -/
theorem slab_layer_sq_le (ψ : Site B → ℝ) (Y : Finset ℤ) (M : ℝ)
    (hM : ∀ y ∈ Y, layerMeanSquare B ψ y ≤ M) :
    (∑ y ∈ Y, ∑ x : B.V, ψ (x, y) ^ 2) ≤ (B.card : ℝ) * Y.card * M := by
  calc
    (∑ y ∈ Y, ∑ x : B.V, ψ (x, y) ^ 2)
        = ∑ y ∈ Y, (B.card : ℝ) * layerMeanSquare B ψ y := by
          apply Finset.sum_congr rfl
          intro y _
          rw [card_mul_layerMeanSquare]
    _ = (B.card : ℝ) * ∑ y ∈ Y, layerMeanSquare B ψ y := by rw [Finset.mul_sum]
    _ ≤ (B.card : ℝ) * ∑ y ∈ Y, M := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg B.card)
          exact Finset.sum_le_sum fun y hy => hM y hy
    _ = (B.card : ℝ) * Y.card * M := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring

/-- **`eqn:psi squared` for the mode sum** (`tex:820-821`, `tex:941-948`): the
layer mean square of `∑_{k=2}^K α_k f_k(x) e^{q_k(y-h)}` is exactly the
spectral sum `∑_{k=2}^K α_k² e^{2 q_k (y-h)}`.  This is `psiExt_layer_sq`
divided by `N`. -/
theorem modeSum_layerMeanSquare (S : SpectralData B) (h : ℤ) (K : ℕ) (α : ℕ → ℝ)
    (hK : K ≤ B.card) (y : ℤ) :
    layerMeanSquare B
        (fun p => ∑ k ∈ Finset.Icc 2 K,
          α k * exponentialMode B (S.f k) (S.qk k) (h : ℝ) p) y
      = ∑ k ∈ Finset.Icc 2 K,
          α k ^ 2 * Real.exp (2 * S.qk k * ((y : ℝ) - (h : ℝ))) := by
  have hN : (B.card : ℝ) ≠ 0 := by
    have : 0 < B.card := lt_of_lt_of_le (by norm_num) B.nontrivial
    exact_mod_cast this.ne'
  unfold layerMeanSquare
  rw [psiExt_layer_sq B S h K α hK y]
  rw [← mul_assoc, inv_mul_cancel₀ hN, one_mul]

end IdlaCyl
