/-
Exact telescoping of the deterministic volume ledger.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.
-/
import IdlaCyl.Support.Reduction.Accounting

namespace IdlaCyl.Reduction

open scoped BigOperators

/-- The raw shifts and final time conserve the initial particle count. -/
theorem trace_volume (N R : ℕ) (t : Fin (R + 1) → ℕ) (ℓ : Fin R → ℕ)
    (hstep : ∀ i : Fin R, t i.succ + N * ℓ i = t i.castSucc) :
    t (Fin.last R) + N * (∑ i, ℓ i) = t 0 := by
  induction R with
  | zero => simp only [Fin.sum_univ_zero, Nat.mul_zero, Nat.add_zero, Fin.last_zero]
  | succ R ih =>
    have hi := ih (fun i => t i.succ) (fun i => ℓ i.succ)
      (fun i => hstep i.succ)
    have hfirst := hstep 0
    have hi' : t (Fin.last (R + 1)) + N * (∑ i : Fin R, ℓ i.succ) =
        t (0 : Fin (R + 1)).succ := hi
    calc
      t (Fin.last (R + 1)) + N * (∑ i, ℓ i) =
          (t (Fin.last (R + 1)) + N * (∑ i : Fin R, ℓ i.succ)) + N * ℓ 0 := by
            rw [Fin.sum_univ_succ]
            ring
      _ = t (0 : Fin (R + 1)).succ + N * ℓ 0 := congrArg (fun x => x + N * ℓ 0) hi'
      _ = t 0 := hfirst

end IdlaCyl.Reduction
