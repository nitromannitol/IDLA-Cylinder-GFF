/-
Deterministic finite trace of the raw-layer reduction, with positive times.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.
-/
import IdlaCyl.Support.Reduction.Accounting

namespace IdlaCyl.Reduction

/-- The arithmetic restart terminates and retains every exact shift and time. -/
theorem reduction_trace (N M β T : ℕ) (hN : 0 < N) (hM : N < M)
    (hβ : 0 < β) (hT : 0 < T) :
    ∃ R : ℕ, ∃ t : Fin (R + 1) → ℕ, ∃ ℓ : Fin R → ℕ,
      t 0 = T ∧ (∀ i, 0 < t i ∧ t i ≤ T) ∧
      (∀ i : Fin R, 3 * β ≤ ℓ i ∧ ℓ i = t i.castSucc / M ∧
        t i.succ + N * ℓ i = t i.castSucc) ∧
      t (Fin.last R) / M < 3 * β ∧ R ≤ T / N := by
  induction T using Nat.strong_induction_on with
  | h T ih =>
    by_cases hgo : 3 * β ≤ T / M
    · have hlt := Restart.remaining_lt N M β T hN hβ hM.le hgo
      have hpos := remaining_pos N M T hM (by change 0 < T / M; omega)
      obtain ⟨R, t, ℓ, hzero, htimes, hsteps, hterm, hR⟩ := ih _ hlt hpos
      have hvol : Restart.remaining N M T + N * (T / M) = T := by
        have hv := Restart.volume_identity N M T hM.le
        change N * (T / M) + Restart.remaining N M T = T at hv
        omega
      refine ⟨R + 1, Fin.cons T t, Fin.cons (T / M) ℓ, rfl, ?_, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact ⟨hT, le_rfl⟩
        · exact ⟨(htimes j).1, (htimes j).2.trans (Restart.remaining_le N M T)⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa only [Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero,
            hzero] using (show 3 * β ≤ T / M ∧ T / M = T / M ∧
              Restart.remaining N M T + N * (T / M) = T from ⟨hgo, rfl, hvol⟩)
        · simpa only [Fin.cons_succ, Fin.castSucc_succ] using hsteps j
      · simpa only [Fin.cons_last] using hterm
      · apply (Nat.le_div_iff_mul_le hN).mpr
        have hc : R * N ≤ Restart.remaining N M T :=
          (Nat.le_div_iff_mul_le hN).mp hR
        have hactive : 1 ≤ T / M := by omega
        have hdecr := Nat.mul_le_mul_left N hactive
        rw [Nat.succ_mul]
        omega
    · refine ⟨0, fun _ => T, Fin.elim0, rfl, fun _ => ⟨hT, le_rfl⟩,
        fun i => Fin.elim0 i, ?_, Nat.zero_le _⟩
      exact Nat.lt_of_not_ge hgo

end IdlaCyl.Reduction
