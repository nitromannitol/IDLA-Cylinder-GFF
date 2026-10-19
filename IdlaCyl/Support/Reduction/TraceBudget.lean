/-
Uniform size of an active deterministic reduction round.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.
-/
import IdlaCyl.Support.Reduction.Accounting

namespace IdlaCyl.Reduction

/-- Polynomial time bounds give a uniform bound on each active layer count. -/
theorem active_round_size (N M β t r : ℕ) (hN : 0 < N) (hM : N ≤ M)
    (hr : 1 ≤ r) (ht : t ≤ N ^ r) (hgo : 3 * β ≤ t / M) :
    (((t / M + β : ℕ) : ℝ)) ≤ 2 * (N : ℝ) ^ ((r : ℝ) - 1) := by
  have hpow : N * N ^ (r - 1) = N ^ r := by
    rw [← pow_succ', Nat.sub_add_cancel hr]
  have hd : t / M ≤ N ^ (r - 1) :=
    (Nat.div_le_div_left hM hN).trans (Nat.div_le_of_le_mul (hpow.symm ▸ ht))
  have hs : t / M + β ≤ 2 * N ^ (r - 1) := by omega
  have he : (N : ℝ) ^ ((r : ℝ) - 1) = (N ^ (r - 1) : ℕ) := by
    have hexp : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub hr, Nat.cast_one]
    rw [← hexp, Real.rpow_natCast, Nat.cast_pow]
  rw [he]
  exact_mod_cast hs

end IdlaCyl.Reduction
