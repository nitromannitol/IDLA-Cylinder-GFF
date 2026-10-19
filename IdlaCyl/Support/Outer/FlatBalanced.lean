/-
Enlargement to the flat stopping-layer seed and the exact translated height law.
Source: paper/idla-cylinder-gff.tex, tex:1400-1431.
-/
import IdlaCyl.Support.Outer.BalancedQueueLaw

attribute [local instance] Classical.propDecidable
namespace IdlaCyl
open MeasureTheory ProbabilityTheory
noncomputable section

/-- The height-h flat seed represented as an actual finite extension of R₀. -/
def outerFlatSeed (B : Base) (h : ℤ) : ResumeFinite B :=
  ⟨outerInterior B (h + 1), fun z hz => ((mem_outerInterior B (h + 1) z).mp hz).2⟩

theorem outerFlatSeed_eq (B : Base) (h : ℤ) (hh : 0 ≤ h) :
    resumeSeed B (outerFlatSeed B h) = R B (h : ℝ) := by
  ext z
  change (z ∈ R B 0 ∨ z ∈ outerInterior B (h + 1)) ↔ _
  rw [mem_outerInterior]
  have heq : h + 1 - 1 = h := by omega
  rw [heq]
  constructor
  · rintro (h0 | ⟨hz, _⟩)
    · exact R_mono (B := B) (by exact_mod_cast hh) h0
    · exact hz
  · intro hz
    by_cases h0 : z ∈ R B 0
    · exact Or.inl h0
    · exact Or.inr ⟨hz, h0⟩

/-- Every paused seed is contained in the enlarged flat seed, on all inputs. -/
theorem outerPausedSeed_subset_flat (B : Base) (h : ℤ) (hh : 1 ≤ h)
    (T : ℕ) (ω : TrajSeq B) :
    resumeSeed B (resumePauseGrow B h ω T).1 ⊆ resumeSeed B (outerFlatSeed B h) := by
  rw [outerFlatSeed_eq B h (by omega)]
  exact (resumePauseGrow_below B h hh ω T).trans (R_mono (B := B) (by linarith))

/-- Under the literal balanced product law, the enlarged output is the translated cluster. -/
theorem outerFlatBalanced_grow (B : Base) (h : ℤ) (hh : 0 ≤ h) (m : ℕ)
    (η : BalancedDriver B m) :
    resumeSeed B (resumeGrow B (outerFlatSeed B h)
      (outerShiftTraj B h (balancedTrajSeq B m η)) (B.card * m)) =
        outerShift B h '' balancedCluster B m η := by
  rw [resumeSeed_grow, outerFlatSeed_eq B h hh]
  have hR : R B (h : ℝ) = outerShift B h '' R B 0 := by
    rw [outerShift_image_R, zero_add]
  rw [hR, clusterFrom_outerShift]
  rfl

/-- Exact height-failure probabilities after enlarging the seed and translating. -/
theorem outerFlatBalanced_height_law (B : Base) (h : ℤ) (hh : 0 ≤ h) (m : ℕ) (r : ℝ) :
    resumeRun B (outerFlatSeed B h) (outerBalancedQueue B h m)
      (outerHeightEvent B ((h : ℝ) + r)) =
        balancedLaw B m {η : BalancedDriver B m | ¬ balancedCluster B m η ⊆ R B r} := by
  have hm : Measurable (fun η : BalancedDriver B m =>
      resumeGrow B (outerFlatSeed B h)
        (outerShiftTraj B h (balancedTrajSeq B m η)) (B.card * m)) :=
    (measurable_resumeGrow B _ _).comp
      ((measurable_outerShiftTraj B h).comp (measurable_balancedTrajSeq B m))
  rw [← outerBalancedQueue_law B h m (outerFlatSeed B h),
    Measure.map_apply hm (Set.to_countable _).measurableSet]
  congr 1
  ext η
  change (¬ resumeSeed B (resumeGrow B (outerFlatSeed B h)
    (outerShiftTraj B h (balancedTrajSeq B m η)) (B.card * m)) ⊆ R B ((h : ℝ) + r)) ↔ _
  rw [outerFlatBalanced_grow B h hh, add_comm (h : ℝ) r, outerShift_subset_R_iff]
  rfl

/-- Conditional domination uses the actual queue, its multiplicities, and proved fresh laws. -/
theorem outerPaused_height_le (B : Base) (h : ℤ) (hh : 1 ≤ h) (T m : ℕ)
    (r : ℝ) (ω : TrajSeq B) (hcount : ∀ x : B.V, frozenCount B h T ω x ≤ m) :
    resumeRun B (resumePauseGrow B h ω T).1 (resumePauseGrow B h ω T).2
      (outerHeightEvent B ((h : ℝ) + r)) ≤
        balancedLaw B m {η : BalancedDriver B m | ¬ balancedCluster B m η ⊆ R B r} := by
  rw [(resumePauseGrow_seed_queue B h hh ω T).2]
  calc
    _ ≤ resumeRun B (resumePauseGrow B h ω T).1 (outerBalancedQueue B h m)
        (outerHeightEvent B ((h : ℝ) + r)) :=
      outerRun_subperm_le B _ (outerHeightEvent_upward B _) _
        (outerResumeQueue_subperm B h T m ω hcount)
    _ ≤ resumeRun B (outerFlatSeed B h) (outerBalancedQueue B h m)
        (outerHeightEvent B ((h : ℝ) + r)) :=
      outerRun_seed_le B _ (outerHeightEvent_upward B _) _ _
        (outerPausedSeed_subset_flat B h hh T ω) _
    _ = _ := outerFlatBalanced_height_law B h (by omega) m r

example : resumeSeed PrInnerTail.K2 (outerFlatSeed PrInnerTail.K2 2) =
    R PrInnerTail.K2 2 := outerFlatSeed_eq PrInnerTail.K2 2 (by norm_num)

example : resumeRun PrInnerTail.K2 (outerFlatSeed PrInnerTail.K2 2)
      (outerBalancedQueue PrInnerTail.K2 2 0) (outerHeightEvent PrInnerTail.K2 (2 + 0)) =
    balancedLaw PrInnerTail.K2 0 {η | ¬ balancedCluster PrInnerTail.K2 0 η ⊆ R PrInnerTail.K2 0} :=
  outerFlatBalanced_height_law PrInnerTail.K2 2 (by norm_num) 0 0

end
end IdlaCyl
