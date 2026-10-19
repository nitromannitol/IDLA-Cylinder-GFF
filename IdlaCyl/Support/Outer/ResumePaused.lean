/-
The literal chronological paused process as a countable Markov state.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396.
Repeated pause locations are retained as distinct list entries.
-/
import IdlaCyl.Support.Outer.ResumeGrowth
import Mathlib.Data.List.OfFn

attribute [local instance] Classical.propDecidable

namespace IdlaCyl
open MeasureTheory ProbabilityTheory
noncomputable section

instance resumeSiteListMeasurableSpace (B : Base) : MeasurableSpace (List (Site B)) := ⊤

instance resumeSiteListMeasurableSingleton (B : Base) :
    MeasurableSingletonClass (List (Site B)) := ⟨fun _ => trivial⟩

/-- Occupied sites below the cap and the chronological queue of paused copies. -/
abbrev ResumeState (B : Base) := ResumeFinite B × List (Site B)

def resumePauseUpdate (B : Base) (h : ℤ) (s : ResumeState B) (z : Site B) :
    ResumeState B :=
  (if z.2 < h then resumeInsert B s.1 z else s.1,
    if z.2 = h then s.2 ++ [z] else s.2)

def resumePausePathStep (B : Base) (h : ℤ) (s : ResumeState B)
    (X : ℕ → Site B) : ResumeState B :=
  resumePauseUpdate B h s (exitSite' B (resumeSeed B s.1) X)

theorem measurable_resumePausePathStep (B : Base) (h : ℤ) :
    Measurable (fun sX : ResumeState B × (ℕ → Site B) =>
      resumePausePathStep B h sX.1 sX.2) := by
  apply measurable_from_prod_countable_right
  intro s
  exact (measurable_of_countable (resumePauseUpdate B h s)).comp
    (measurable_exitSite' B (resumeSeed B s.1))

theorem measurable_resumePausePathStep_fixed (B : Base) (h : ℤ) (s : ResumeState B) :
    Measurable (resumePausePathStep B h s) := by
  change Measurable ((resumePauseUpdate B h s) ∘ (exitSite' B (resumeSeed B s.1)))
  exact (measurable_of_countable (resumePauseUpdate B h s)).comp
    (measurable_exitSite' B (resumeSeed B s.1))

/-- First-stage state driven by exactly the original alive trajectories. -/
def resumePauseGrow (B : Base) (h : ℤ) (ω : TrajSeq B) : ℕ → ResumeState B
  | 0 => (resumeEmpty B, [])
  | n + 1 => resumePausePathStep B h (resumePauseGrow B h ω n) (ω n)

theorem measurable_resumePauseGrow (B : Base) (h : ℤ) (n : ℕ) :
    Measurable (fun ω : TrajSeq B => resumePauseGrow B h ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      change Measurable (fun ω : TrajSeq B =>
        resumePausePathStep B h (resumePauseGrow B h ω n) (ω n))
      have hin : Measurable (fun ω : TrajSeq B => (resumePauseGrow B h ω n, ω n)) :=
        ih.prodMk (measurable_pi_apply n)
      change Measurable ((fun sX : ResumeState B × (ℕ → Site B) =>
        resumePausePathStep B h sX.1 sX.2) ∘
          (fun ω : TrajSeq B => (resumePauseGrow B h ω n, ω n)))
      exact (measurable_resumePausePathStep B h).comp hin

theorem resumePauseGrow_congr (B : Base) (h : ℤ) (ω η : TrajSeq B)
    (n : ℕ) (hω : ∀ j < n, ω j = η j) :
    resumePauseGrow B h ω n = resumePauseGrow B h η n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change resumePausePathStep B h _ _ = _
      rw [ih (fun j hj => hω j (by omega)), hω n (by omega)]
      rfl

/-- The queue uses the same chronological labels and the same multiplicities as `pauseList`. -/
def resumeQueue (B : Base) (h : ℤ) (T : ℕ) (ω : TrajSeq B) : List (Site B) :=
  (pauseList B h T ω).map (fun j => stoppedSettleSite B h ω j)

theorem resumeQueue_succ (B : Base) (h : ℤ) (T : ℕ) (ω : TrajSeq B) :
    resumeQueue B h (T + 1) ω = resumeQueue B h T ω ++
      (if (stoppedSettleSite B h ω T).2 = h then [stoppedSettleSite B h ω T] else []) := by
  by_cases hz : (stoppedSettleSite B h ω T).2 = h <;>
    simp [resumeQueue, pauseList, List.range_succ, hz]

theorem resumeQueue_eq_ofFn_pausedStart (B : Base) (h : ℤ) (T : ℕ) (ω : TrajSeq B) :
    resumeQueue B h T ω =
      List.ofFn (fun i : Fin (pauseList B h T ω).length => pausedStart B h T ω i) := by
  apply List.ext_getElem
  · simp only [resumeQueue, List.length_map, List.length_ofFn]
  · intro i _ hi'
    have hi : i < (pauseList B h T ω).length := by
      simpa only [List.length_ofFn] using hi'
    simp only [resumeQueue, List.getElem_map, List.getElem_ofFn, pausedStart, dif_pos hi]

/-- The finite representation agrees with the literal paused cluster on every input. -/
theorem resumePauseGrow_seed_queue (B : Base) (h : ℤ) (hh : 1 ≤ h)
    (ω : TrajSeq B) (T : ℕ) :
    resumeSeed B (resumePauseGrow B h ω T).1 = pausedCluster B h ω T ∧
      (resumePauseGrow B h ω T).2 = resumeQueue B h T ω := by
  induction T with
  | zero =>
      constructor
      · exact (resumeSeed_empty B).trans (pausedCluster_zero B h hh ω).symm
      · rfl
  | succ T ih =>
      have hz : exitSite' B (resumeSeed B (resumePauseGrow B h ω T).1) (ω T) =
          stoppedSettleSite B h ω T := by
        rw [ih.1]
        unfold stoppedSettleSite pausedCluster
        rw [Int.cast_sub, Int.cast_one]
      constructor
      · change resumeSeed B (if _ then _ else _) = _
        rw [hz, pausedCluster_succ]
        split_ifs with hlt
        · rw [resumeSeed_insert, ih.1]
        · exact ih.1
      · change (if _ then _ else _) = _
        rw [hz, ih.2, resumeQueue_succ]
        split_ifs with heq
        · rfl
        · exact (List.append_nil _).symm

/-- The region exposed by every first-stage state stays below the stopping layer. -/
theorem resumePauseGrow_below (B : Base) (h : ℤ) (hh : 1 ≤ h)
    (ω : TrajSeq B) (T : ℕ) :
    resumeSeed B (resumePauseGrow B h ω T).1 ⊆ R B ((h : ℝ) - 1) := by
  rw [(resumePauseGrow_seed_queue B h hh ω T).1]
  simpa only [Int.cast_sub, Int.cast_one] using pausedCluster_subset B h ω T

/-- The next independent alive path drives the paused state transition. -/
def resumePauseStep (B : Base) (h : ℤ) (s : ResumeState B) : Measure (ResumeState B) :=
  (walkLawUniform B).map (resumePausePathStep B h s)

instance resumePauseStep_isProbability (B : Base) (h : ℤ) (s : ResumeState B) :
    IsProbabilityMeasure (resumePauseStep B h s) :=
  Measure.isProbabilityMeasure_map ((measurable_resumePausePathStep B h).comp
    measurable_prodMk_left).aemeasurable

/-- This is a derived transition law at the actual chronological pause times. -/
theorem idlaMeasure_map_resumePauseGrow_succ (B : Base) (h : ℤ) (T : ℕ) :
    (idlaMeasure B).map (fun ω => resumePauseGrow B h ω (T + 1)) =
      ((idlaMeasure B).map (fun ω => resumePauseGrow B h ω T)).bind (resumePauseStep B h) := by
  have hj := IndepFun.map_prod_eq_prod_map_map
    (measurable_resumePauseGrow B h T).aemeasurable (measurable_pi_apply T).aemeasurable
    (resume_indep_past B (fun _ => walkLawUniform B) T _ (measurable_resumePauseGrow B h T)
      (fun ω η hω => resumePauseGrow_congr B h ω η T hω))
  rw [Measure.infinitePi_map_eval] at hj
  change (idlaMeasure B).map (fun ω => (resumePauseGrow B h ω T, ω T)) =
    ((idlaMeasure B).map (fun ω => resumePauseGrow B h ω T)).prod (walkLawUniform B) at hj
  calc
    _ = ((idlaMeasure B).map (fun ω => (resumePauseGrow B h ω T, ω T))).map
        (fun sX => resumePausePathStep B h sX.1 sX.2) :=
      (Measure.map_map (measurable_resumePausePathStep B h)
        ((measurable_resumePauseGrow B h T).prodMk (measurable_pi_apply T))).symm
    _ = (((idlaMeasure B).map (fun ω => resumePauseGrow B h ω T)).prod (walkLawUniform B)).map
        (fun sX => resumePausePathStep B h sX.1 sX.2) := by rw [hj]
    _ = _ := resume_prod_map _ _ _ (measurable_resumePausePathStep B h)

example : resumePauseGrow PrInnerTail.K2 2 (fun _ _ => (PrInnerTail.K2.pt, 0)) 0 =
    (resumeEmpty PrInnerTail.K2, []) := rfl

example (ω : TrajSeq PrInnerTail.K2) :
    resumeSeed PrInnerTail.K2 (resumePauseGrow PrInnerTail.K2 2 ω 0).1 =
      pausedCluster PrInnerTail.K2 2 ω 0 :=
  (resumePauseGrow_seed_queue PrInnerTail.K2 2 (by norm_num) ω 0).1

end
end IdlaCyl
