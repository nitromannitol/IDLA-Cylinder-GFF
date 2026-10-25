module

/-
Literal balanced queues and chronological frozen multiplicities.
Source: paper/idla-cylinder-gff.tex, tex:1331-1337,1391-1396.
The queue retains every copy of a release at each site.
-/
public import IdlaCyl.Support.Outer.SeedDomination
public import IdlaCyl.Support.Outer.ResumePaused
public import IdlaCyl.Support.Outer.BalancedRelease
public import Mathlib.Data.List.FinRange

@[expose] public section

attribute [local instance] Classical.propDecidable
namespace IdlaCyl
open MeasureTheory ProbabilityTheory
noncomputable section

/-- The fixed balanced enumeration, now released at the stopping layer. -/
def outerBalancedQueue (B : Base) (h : ℤ) (m : ℕ) : List (Site B) :=
  List.ofFn (fun i : Fin (B.card * m) => ((balancedIndex B m i).1, h))

private theorem outer_count_map {α β : Type*} [DecidableEq α] [DecidableEq β] [BEq β] [LawfulBEq β]
    (L : List α) (hL : L.Nodup) (f : α → β) (z : β) :
    (L.map f).count z = (L.toFinset.filter (fun i => f i = z)).card := by
  rw [List.count, List.countP_map, List.countP_eq_length_filter,
    ← List.toFinset_card_of_nodup (hL.filter _), List.toFinset_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Function.comp_apply, beq_iff_eq]

/-- Exactly m copies at each layer-h site, in the literal balanced order. -/
theorem outerBalancedQueue_count (B : Base) (h : ℤ) (m : ℕ) (x : B.V) :
    (outerBalancedQueue B h m).count (x, h) = m := by
  rw [outerBalancedQueue, List.ofFn_eq_map,
    outer_count_map _ (List.nodup_finRange _) ]
  have hfin : (List.finRange (B.card * m)).toFinset = Finset.univ := by
    ext i
    simp only [List.mem_toFinset, List.mem_finRange, Finset.mem_univ]
  rw [hfin]
  simpa only [Prod.mk.injEq, and_true] using balanced_start_count B m x

/-- Every actual queued copy starts on the stopping layer, even on null inputs. -/
theorem outerResumeQueue_ver (B : Base) (h : ℤ) (T : ℕ) (ω : TrajSeq B)
    (z : Site B) (hz : z ∈ resumeQueue B h T ω) : z.2 = h := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hz
  exact of_decide_eq_true (List.mem_filter.mp hj).2

/-- Queue multiplicities agree exactly with the finite frozen particle counts. -/
theorem outerResumeQueue_count (B : Base) (h : ℤ) (T : ℕ) (ω : TrajSeq B) (x : B.V) :
    (resumeQueue B h T ω).count (x, h) = frozenCount B h T ω x := by
  unfold resumeQueue pauseList
  rw [outer_count_map _ ((show (List.range T).Nodup from List.nodup_range).filter _) ]
  unfold frozenCount
  have hrange : (List.range T).toFinset = Finset.range T := by
    ext j
    simp only [List.mem_toFinset, List.mem_range, Finset.mem_range]
  rw [List.toFinset_filter, hrange, Finset.filter_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hj, _, heq⟩
    exact ⟨hj, heq⟩
  · rintro ⟨hj, heq⟩
    exact ⟨hj, congrArg Prod.snd heq, heq⟩

/-- The bounded-count condition embeds the actual queue as a submultiset of Nm starts. -/
theorem outerResumeQueue_subperm (B : Base) (h : ℤ) (T m : ℕ) (ω : TrajSeq B)
    (hcount : ∀ x : B.V, frozenCount B h T ω x ≤ m) :
    (resumeQueue B h T ω).Subperm (outerBalancedQueue B h m) := by
  apply List.subperm_ext_iff.mpr
  intro z hz
  have heq : z = (z.1, h) := Prod.ext rfl (outerResumeQueue_ver B h T ω z hz)
  rw [heq, outerResumeQueue_count, outerBalancedQueue_count]
  exact hcount z.1

example (x : PrInnerTail.K2.V) : (outerBalancedQueue PrInnerTail.K2 2 1).count (x, 2) = 1 :=
  outerBalancedQueue_count PrInnerTail.K2 2 1 x

example (ω : TrajSeq PrInnerTail.K2) :
    (resumeQueue PrInnerTail.K2 2 0 ω).Subperm (outerBalancedQueue PrInnerTail.K2 2 0) := by
  apply outerResumeQueue_subperm
  intro x
  simp only [frozenCount, Finset.range_zero, Finset.filter_empty, Finset.card_empty, le_refl]

end
end IdlaCyl
