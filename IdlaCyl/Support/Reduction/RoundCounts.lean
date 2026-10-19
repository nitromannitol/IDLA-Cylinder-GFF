/-
The exact two-comparison lengths for an active raw-layer round.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.
-/
import IdlaCyl.Support.Reduction.DeepReserve

namespace IdlaCyl.Reduction

/-- Both comparison calls fit within the original time and exhaust its raw-shift residual. -/
theorem round_comparison_counts (N M β t : ℕ) (hN : 0 < N)
    (hM : 2 * N ≤ M) (hβ : 0 < β) (hgo : 3 * β ≤ t / M) :
    let D := (M - N) * (t / M - β)
    let Q := (M - N) * β + t % M
    0 < D ∧ 0 < Q ∧ M * β ≤ D ∧ D ≤ t ∧ Q ≤ t ∧
      D + Q = t - N * (t / M) ∧ (t - N * (t / M)) + N * (t / M) = t := by
  dsimp only
  have hNM : N ≤ M := by omega
  have hβℓ : β ≤ Restart.layers M t := by change β ≤ t / M; omega
  have hc := comparison_counts N M β (t / M) (t % M) hN hM hβ hgo
  have hv := canonical_growth_accounting N M β t hNM hβℓ
  have hr := auxiliary_additions_eq N M β t hNM hβℓ
  have hmod : t - M * Restart.layers M t = t % M := by
    have h := Nat.mod_add_div t M
    unfold Restart.layers
    omega
  rw [hmod] at hv hr
  change N * (t / M) + (M - N) * (t / M - β) +
    ((M - N) * β + t % M) = t at hv
  change t - N * (t / M) = (M - N) * (t / M - β) +
    (M - N) * β + t % M at hr
  exact ⟨hc.2.1, hc.2.2, hc.1, by omega, by omega, by omega, by omega⟩

end IdlaCyl.Reduction
