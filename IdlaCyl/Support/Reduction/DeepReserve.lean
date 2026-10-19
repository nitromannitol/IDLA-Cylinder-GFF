/-
Positive comparison lengths and the reserve for canonical buffer growth.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.
-/
import IdlaCyl.Support.Reduction.Accounting

namespace IdlaCyl.Reduction

/-- Both citation calls have positive length, and the deep call pays for the buffer. -/
theorem comparison_counts (N M β ℓ ρ : ℕ) (hN : 0 < N)
    (hM : 2 * N ≤ M) (hβ : 0 < β) (hℓ : 3 * β ≤ ℓ) :
    M * β ≤ (M - N) * (ℓ - β) ∧
    0 < (M - N) * (ℓ - β) ∧ 0 < (M - N) * β + ρ := by
  have hMN : 0 < M - N := by omega
  have hlb : 0 < ℓ - β := by omega
  exact ⟨Restart.deep_reserve N M β ℓ hM hℓ,
    Nat.mul_pos hMN hlb, Nat.add_pos_left (Nat.mul_pos hMN hβ) ρ⟩

end IdlaCyl.Reduction
