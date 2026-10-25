module

/-
Accounting for a two-comparison raw-layer reduction with a canonical buffer.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453; consumer tex:1119-1136.

The first seed is R_ℓ and the auxiliary makes exactly T-Nℓ additions.
Canonical buffer growth uses deep additions already in this count. These
lemmas assert no probability law, successful filling, or stochastic coupling.
-/
public import IdlaCyl.Support.RestartAccounting

@[expose] public section

namespace IdlaCyl.Reduction

/-- The raw-shift residual contains the deep, shallow and unreleased particles. -/
theorem auxiliary_additions_eq (N M β T : ℕ) (hNM : N ≤ M)
    (hβ : β ≤ Restart.layers M T) :
    Restart.remaining N M T =
      Restart.deep N M β (Restart.layers M T) + Restart.shallow N M β +
        (T - M * Restart.layers M T) :=
  Restart.remaining_decomposition N M β T hNM hβ

/-- The raw rectangle, all deep additions and all remaining additions conserve volume. -/
theorem canonical_growth_accounting (N M β T : ℕ) (hNM : N ≤ M)
    (hβ : β ≤ Restart.layers M T) :
    N * Restart.layers M T + Restart.deep N M β (Restart.layers M T) +
      (Restart.shallow N M β + (T - M * Restart.layers M T)) = T := by
  have hv := Restart.volume_identity N M T hNM
  have hd := auxiliary_additions_eq N M β T hNM hβ
  omega

/-- Mβ initial canonical additions are a part of the deep reserve, not extra particles. -/
theorem deep_buffer_split (N M β ℓ : ℕ) (hM : 2 * N ≤ M) (hℓ : 3 * β ≤ ℓ) :
    M * β + (Restart.deep N M β ℓ - M * β) = Restart.deep N M β ℓ :=
  Nat.add_sub_of_le (Restart.deep_reserve N M β ℓ hM hℓ)

/-- After filling β additional layers, exactly D-Nβ deep additions remain above them. -/
theorem canonical_buffer_excess_accounting (N M β T : ℕ)
    (hM : 2 * N ≤ M) (hgo : 3 * β ≤ Restart.layers M T) :
    N * (Restart.layers M T + β) +
        (Restart.deep N M β (Restart.layers M T) - N * β) +
        (Restart.shallow N M β + (T - M * Restart.layers M T)) = T := by
  have hNM : N ≤ M := by omega
  have hβ : β ≤ Restart.layers M T := by omega
  have hreserve := Restart.deep_reserve N M β (Restart.layers M T) hM hgo
  have hsmall : N * β ≤ Restart.deep N M β (Restart.layers M T) :=
    (Nat.mul_le_mul_right β hNM).trans hreserve
  have hv := canonical_growth_accounting N M β T hNM hβ
  rw [Nat.mul_add]
  omega

/-- A strict batch surplus and a positive layer count keep the residual time positive. -/
theorem remaining_pos (N M T : ℕ) (hNM : N < M)
    (hℓ : 0 < Restart.layers M T) : 0 < Restart.remaining N M T := by
  have hb := Restart.batch_budget M T
  have hlt : N * Restart.layers M T < M * Restart.layers M T :=
    Nat.mul_lt_mul_of_pos_right hNM hℓ
  unfold Restart.remaining
  omega

/-- Every intermediate time, including the terminal time, remains positive. -/
theorem reduce_pos (N M β fuel T : ℕ) (hNM : N < M) (hβ : 0 < β)
    (hT : 0 < T) : 0 < (Restart.reduce N M β fuel T).1 := by
  induction fuel generalizing T with
  | zero => exact hT
  | succ fuel ih =>
    by_cases hgo : 3 * β ≤ Restart.layers M T
    · simp only [Restart.reduce, if_pos hgo]
      exact ih _ (remaining_pos N M T hNM (by omega))
    · simpa only [Restart.reduce, if_neg hgo] using hT

/-- Number of active reduction rounds, with the same explicit fuel as `Restart.reduce`. -/
def roundCount (N M β : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, T =>
    if 3 * β ≤ Restart.layers M T then
      roundCount N M β fuel (Restart.remaining N M T) + 1
    else 0

/-- Each active round contributes at least one to the accumulated raw shift. -/
theorem roundCount_le_shift (N M β fuel T : ℕ) (hβ : 0 < β) :
    roundCount N M β fuel T ≤ (Restart.reduce N M β fuel T).2 := by
  induction fuel generalizing T with
  | zero => exact Nat.le_refl 0
  | succ fuel ih =>
    by_cases hgo : 3 * β ≤ Restart.layers M T
    · simp only [roundCount, Restart.reduce, if_pos hgo]
      have hi := ih (Restart.remaining N M T)
      omega
    · simp only [roundCount, Restart.reduce, if_neg hgo, le_refl]

/-- The total number of rounds is bounded by the available complete N-particle layers. -/
theorem roundCount_mul_le (N M β fuel T : ℕ) (hNM : N ≤ M) (hβ : 0 < β) :
    N * roundCount N M β fuel T ≤ T := by
  have hc := Nat.mul_le_mul_left N (roundCount_le_shift N M β fuel T hβ)
  have hv := Restart.reduce_volume N M β fuel T hNM
  omega

/-- Division gives the deterministic round bound needed by the union bound. -/
theorem roundCount_le_div (N M β fuel T : ℕ) (hN : 0 < N)
    (hNM : N ≤ M) (hβ : 0 < β) :
    roundCount N M β fuel T ≤ T / N := by
  apply (Nat.le_div_iff_mul_le hN).mpr
  simpa only [Nat.mul_comm] using roundCount_mul_le N M β fuel T hNM hβ

/-- Arithmetic termination with a positive residual and exact accumulated shift. -/
theorem terminal_pair (N M β T : ℕ) (hN : 0 < N) (hNM : N < M)
    (hβ : 0 < β) (hT : 0 < T) :
    ∃ T' k : ℕ, 1 ≤ T' ∧ T' < 3 * β * M ∧ T' + N * k = T := by
  let z := Restart.reduce N M β T T
  refine ⟨z.1, z.2, reduce_pos N M β T T hNM hβ hT, ?_, ?_⟩
  · exact Restart.reduce_terminal_bound N M β T hN hβ hNM.le
  · have hv := Restart.reduce_volume N M β T T hNM.le
    simpa only [Nat.add_comm] using hv.symm

/-- Product estimate converting the integer terminal cutoff to a finite scale coefficient. -/
theorem batch_buffer_scale_bound (N M β : ℕ) (a b H L : ℝ)
    (hb : 0 ≤ b) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hM : (M : ℝ) ≤ a * (N : ℝ) * L) (hβ : (β : ℝ) ≤ b * H * L) :
    ((3 * β * M : ℕ) : ℝ) ≤ (3 * a * b) * ((N : ℝ) * H * L ^ 2) := by
  calc
    ((3 * β * M : ℕ) : ℝ) = 3 * (β : ℝ) * (M : ℝ) := by push_cast; rfl
    _ ≤ 3 * (b * H * L) * (a * (N : ℝ) * L) := by gcongr
    _ = (3 * a * b) * ((N : ℝ) * H * L ^ 2) := by ring

/-- The nonzero-buffer test retains six canonical sites above the newly filled layer. -/
example :
    Restart.layers 6 19 = 3 ∧ Restart.deep 2 6 1 3 = 8 ∧
    Restart.shallow 2 6 1 = 4 ∧ 19 - 6 * 3 = 1 ∧
    Restart.remaining 2 6 19 = 13 ∧ 13 + 2 * 3 = 19 ∧
    2 * (3 + 1) + (8 - 2 * 1) + (4 + 1) = 19 := by decide

/-- The reserve hypothesis holds in that test; its six growth particles are retained. -/
example : 6 * 1 + (Restart.deep 2 6 1 3 - 6 * 1) = Restart.deep 2 6 1 3 :=
  deep_buffer_split 2 6 1 3 (by decide) (by decide)

/-- The buffer threshold stops the original test after one valid round. -/
example : Restart.reduce 2 6 1 19 19 = (13, 3) ∧ roundCount 2 6 1 19 19 = 1 := by decide

/-- A larger example takes two valid rounds, conserving the accumulated raw shift. -/
example : Restart.reduce 2 6 1 37 37 = (17, 10) ∧ roundCount 2 6 1 37 37 = 2 := by decide

/-- Cross-pairing the two different conventions for the shift gives wrong sizes. -/
example : (13 : ℕ) + 2 * 2 ≠ 19 ∧ (15 : ℕ) + 2 * 3 ≠ 19 := by decide

end IdlaCyl.Reduction
