/-
The finite rectangular-variance identity (`tex:1005-1007`, `tex:941-948`).

For the harmonic-extension mode sum `modeSumPsi B S h K α` with `2 ≤ k ≤ K ≤ N`,
the rectangular quadratic mass `W_N` at time `N * h` is exactly the closed
geometric form

  `∑_{k=2}^K α_k² (1 - e^{-2 q_k h}) / (a (1 - e^{-2 q_k}))`,

in words: the normalised mass of the mode sum over the rectangle
`V_N × {1, …, h}` equals, mode by mode, `α_k²` times the finite geometric sum
of the layer weights `e^{2 q_k (y - h)}` over `y = 1, …, h`, divided by `a`.

The proof splits the rectangle into its `h` complete layers (each of mass
`N` times the layer mean square, `card_mul_layerMeanSquare`), swaps the finite
sums over heights and modes, and sums each geometric series in the ratio
`e^{-2 q_k}`, which is not `1` because `q_k > 0` for `k ≥ 2`.  Nothing here is
asymptotic: it is a finite identity valid for every `N ≥ 2` and every `h`.
-/
import IdlaCyl.Support.ClmQWAnalytic
import IdlaCyl.Support.DiscreteVariance

namespace IdlaCyl

open scoped BigOperators

/-- The layer geometric sum: `∑_{y=1}^{h} e^{2q(y-h)}` times `1 - e^{-2q}` equals
`1 - e^{-2qh}`.  Proved by the one-step recursion in `h`, with no reindexing. -/
theorem rectangle_layer_geom (q : ℝ) (h : ℕ) :
    (∑ y ∈ Finset.Icc (1 : ℤ) (h : ℤ), Real.exp (2 * q * ((y : ℝ) - (h : ℝ))))
        * (1 - Real.exp (-2 * q))
      = 1 - Real.exp (-2 * q * (h : ℝ)) := by
  induction h with
  | zero => simp
  | succ n ih =>
    have hI : Finset.Icc (1 : ℤ) ((n + 1 : ℕ) : ℤ)
        = insert ((n : ℤ) + 1) (Finset.Icc (1 : ℤ) (n : ℤ)) := by
      ext y
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : ((n : ℤ) + 1) ∉ Finset.Icc (1 : ℤ) (n : ℤ) := by
      simp only [Finset.mem_Icc, not_and, not_le]
      intro _
      omega
    have hE : Real.exp (-2 * q * ((n + 1 : ℕ) : ℝ))
        = Real.exp (-2 * q * (n : ℝ)) * Real.exp (-2 * q) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    have hsum : ∑ y ∈ Finset.Icc (1 : ℤ) (n : ℤ),
          Real.exp (2 * q * ((y : ℝ) - ((n + 1 : ℕ) : ℝ)))
        = Real.exp (-2 * q)
          * ∑ y ∈ Finset.Icc (1 : ℤ) (n : ℤ), Real.exp (2 * q * ((y : ℝ) - (n : ℝ))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    have hlast : Real.exp (2 * q * ((((n : ℤ) + 1 : ℤ) : ℝ) - ((n + 1 : ℕ) : ℝ))) = 1 := by
      push_cast
      simp
    rw [hI, Finset.sum_insert hnot, hlast, hsum, hE]
    linear_combination Real.exp (-2 * q) * ih

/-- **Rectangular variance, closed form.** For `2 ≤ k ≤ K ≤ N`, with `a > 0`, the
rectangular quadratic mass `W_N` of the mode sum at height `h`, taken at time
`N * h`, equals `∑_{k=2}^K α_k² (1 - e^{-2 q_k h}) / (a (1 - e^{-2 q_k}))`
(`tex:1005-1007`, `tex:941-948`). -/
theorem rectangle_WN_eq_closedForm (B : Base) (S : SpectralData B)
    (a : ℝ) (ha : 0 < a) (h K : ℕ) (hK : K ≤ B.card)
    (α : ℕ → ℝ) (ω : TrajSeq B) :
  WN B (fun _ => a) (B.card * h) (modeSumPsi B S (h : ℤ) K α) ω =
    ∑ k ∈ Finset.Icc 2 K, α k ^ 2 *
      (1 - Real.exp (-2 * S.qk k * (h : ℝ))) /
        (a * (1 - Real.exp (-2 * S.qk k))) := by
  have hNpos : (0 : ℝ) < (B.card : ℝ) := by
    have h2 : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
    linarith
  -- The rectangle at time `N * h` is `V_N × {1, …, h}`.
  have hrect : rectangleFinset B (B.card * h) = Finset.univ ×ˢ Finset.Icc (1 : ℤ) (h : ℤ) := by
    have hfl : ((B.card * h : ℕ) : ℝ) / (B.card : ℝ) = (h : ℝ) := by
      push_cast
      field_simp
    unfold rectangleFinset
    rw [hfl, Int.floor_natCast]
    rfl
  -- Each complete layer has mass `N` times its mean square (`tex:820-821`).
  have hlayer : ∀ y : ℤ, ∑ x : B.V, modeSumPsi B S (h : ℤ) K α (x, y) ^ 2
      = (B.card : ℝ) * ∑ k ∈ Finset.Icc 2 K,
          α k ^ 2 * Real.exp (2 * S.qk k * ((y : ℝ) - (h : ℝ))) := by
    intro y
    rw [← card_mul_layerMeanSquare B (modeSumPsi B S (h : ℤ) K α) y,
      modeSumPsi_layerMeanSquare B S (h : ℤ) K α hK y]
    simp only [Int.cast_natCast]
  -- Each mode's layer sum is the closed geometric factor (`q_k > 0`, so the ratio is not `1`).
  have hS : ∀ k ∈ Finset.Icc 2 K,
      (∑ y ∈ Finset.Icc (1 : ℤ) (h : ℤ), Real.exp (2 * S.qk k * ((y : ℝ) - (h : ℝ))))
        = (1 - Real.exp (-2 * S.qk k * (h : ℝ))) / (1 - Real.exp (-2 * S.qk k)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hq : 0 < S.qk k := S.qk_pos hk.1 (le_trans hk.2 hK)
    have hr : Real.exp (-2 * S.qk k) < 1 := by
      have := Real.exp_lt_exp.mpr (show -2 * S.qk k < 0 by linarith)
      simpa using this
    exact eq_div_of_mul_eq (by linarith : (0 : ℝ) < 1 - Real.exp (-2 * S.qk k)).ne'
      (rectangle_layer_geom (S.qk k) h)
  -- Swap the finite sums over heights and modes.
  have hswap : ∑ y ∈ Finset.Icc (1 : ℤ) (h : ℤ), ∑ k ∈ Finset.Icc 2 K,
        α k ^ 2 * Real.exp (2 * S.qk k * ((y : ℝ) - (h : ℝ)))
      = ∑ k ∈ Finset.Icc 2 K, α k ^ 2 *
          ∑ y ∈ Finset.Icc (1 : ℤ) (h : ℤ), Real.exp (2 * S.qk k * ((y : ℝ) - (h : ℝ))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
  have hsum2 : ∑ k ∈ Finset.Icc 2 K, α k ^ 2 *
        ∑ y ∈ Finset.Icc (1 : ℤ) (h : ℤ), Real.exp (2 * S.qk k * ((y : ℝ) - (h : ℝ)))
      = ∑ k ∈ Finset.Icc 2 K, α k ^ 2 *
          ((1 - Real.exp (-2 * S.qk k * (h : ℝ))) / (1 - Real.exp (-2 * S.qk k))) :=
    Finset.sum_congr rfl fun k hk => by rw [hS k hk]
  have hfac : ∀ x : ℝ, 1 / ((B.card : ℝ) * a) * ((B.card : ℝ) * x) = 1 / a * x := by
    intro x
    field_simp
  unfold WN
  rw [hrect, Finset.sum_product_right]
  simp only [hlayer]
  rw [← Finset.mul_sum, hswap, hsum2, hfac, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Nonvacuity: at `h = 0` the rectangle is empty and both sides vanish, so the
identity is a consumer that actually fires on a concrete base and spectrum. -/
example (B : Base) (S : SpectralData B) (a : ℝ) (ha : 0 < a) (K : ℕ) (hK : K ≤ B.card)
    (α : ℕ → ℝ) (ω : TrajSeq B) :
    WN B (fun _ => a) (B.card * 0) (modeSumPsi B S ((0 : ℕ) : ℤ) K α) ω = 0 := by
  rw [rectangle_WN_eq_closedForm B S a ha 0 K hK α ω]
  simp

end IdlaCyl
