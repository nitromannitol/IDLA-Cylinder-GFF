/-
Uniform scalar allowance over the complete deterministic reduction trace.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.
-/
import IdlaCyl.Support.Reduction.TraceBudget
import IdlaCyl.Support.Reduction.ErrorBudget
import IdlaCyl.Support.Reduction.Laws

namespace IdlaCyl.Reduction

open scoped BigOperators

/-- The sum of the explicit four-term round allowances fits the final confidence exponent. -/
theorem trace_error_budget (B : Base) (M β T R r : ℕ)
    (t : Fin (R + 1) → ℕ) (ℓ : Fin R → ℕ) (ν : ℝ)
    (hM : B.card ≤ M) (hr : 1 ≤ r) (hT : T ≤ B.card ^ r)
    (ht : ∀ i, t i ≤ T)
    (hactive : ∀ i : Fin R, ℓ i = t i.castSucc / M ∧ 3 * β ≤ ℓ i)
    (hR : R ≤ T / B.card) :
    (∑ i, roundError B (ν + (r : ℝ) + 2) (ν + 2 * (r : ℝ) + 1) (ℓ i) β) ≤
      (B.card : ℝ) ^ (-(ν + 1)) := by
  have hN : 0 < B.card := lt_of_lt_of_le (by decide : 0 < 2) B.nontrivial
  have hNreal : (0 : ℝ) < B.card := by exact_mod_cast hN
  have hNtwo : (2 : ℝ) ≤ B.card := by exact_mod_cast B.nontrivial
  have hpow : B.card * B.card ^ (r - 1) = B.card ^ r := by
    rw [← pow_succ', Nat.sub_add_cancel hr]
  have hRn : R ≤ B.card ^ (r - 1) :=
    hR.trans (Nat.div_le_of_le_mul (hpow.symm ▸ hT))
  have hexp : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub hr, Nat.cast_one]
  have hRreal : (R : ℝ) ≤ (B.card : ℝ) ^ ((r : ℝ) - 1) := by
    rw [← hexp, Real.rpow_natCast]
    exact_mod_cast hRn
  apply summed_error_budget (B.card : ℝ) ν (r : ℝ) R _ hNtwo hRreal
  intro i
  have hsize := active_round_size B.card M β (t i.castSucc) r hN hM hr
    ((ht i.castSucc).trans hT) (by rw [← (hactive i).1]; exact (hactive i).2)
  rw [← (hactive i).1] at hsize
  exact round_error_budget (B.card : ℝ) ν (r : ℝ) ((ℓ i + β : ℕ) : ℝ) hNreal hsize

end IdlaCyl.Reduction
