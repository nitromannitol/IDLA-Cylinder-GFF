import IdlaCyl.Support.CanonicalExchange

/-!
Proposition `pr:exchange` (Stability under trajectory swap), `tex:773-776`:

"If ω and ω̃ differ in exactly one coordinate,
then |A_+(T;ω) △ A_+(T;ω̃)| ≤ 2."

Lean reads this pathwise, for any two trajectory sequences that differ in
exactly one of the first T coordinates.

The proof uses first-exit contraction in the original labelled order
(`tex:778-782`), without the printed reordering step.
-/

namespace IdlaCyl.Frozen

-- FROZEN-STATEMENT-BEGIN
theorem pr_exchange_v2 (B : Base) (T : ℕ) (ω ω' : TrajSeq B)
    (h : ∃ j, j < T ∧ ω j ≠ ω' j ∧
      ∀ i, i < T → i ≠ j → ω i = ω' i) :
    Set.encard (symmDiff (clusterPlusTraj B ω T) (clusterPlusTraj B ω' T)) ≤ 2
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨j, _, _, hshared⟩ := h
  exact CanonicalExchange.clusterPlusTraj_symmDiff_encard_le_two B ω ω' T j hshared

/-- Concrete sequences on any base: all paths stay at height one, except
the replacement of coordinate zero by a path staying at height two. -/
theorem pr_exchange_v2_nonvacuity (B : Base) :
    Set.encard (symmDiff
      (clusterPlusTraj B (fun _ _ => (B.pt, 1)) 1)
      (clusterPlusTraj B (fun i _ => if i = 0 then (B.pt, 2) else (B.pt, 1)) 1)) ≤ 2 := by
  apply pr_exchange_v2
  refine ⟨0, by omega, ?_, ?_⟩
  · intro heq
    have hsite := congrArg (fun X => (X 0).2) heq
    norm_num at hsite
  · intro i _ hi
    simp only [hi, if_false]

end IdlaCyl.Frozen
