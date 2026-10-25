module

/-
Stopped-prefix continuation factorization for fresh resumption.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396.
The record contains the stopping time and every exposed position. This module
does not identify growth along the original labelled tails with ordinary IDLA.
-/
public import IdlaCyl.Support.Outer.ResumeMeasurable
public import IdlaCyl.Support.Outer.GhostMarkov

@[expose] public section

attribute [local instance] Classical.propDecidable

namespace IdlaCyl
open MeasureTheory ProbabilityTheory
noncomputable section

/-- The finite-cut convention is used only after proving almost-sure finite exit. -/
def resumeCut (B : Base) (S : Set (Site B)) (X : ℕ → Site B) : ℕ :=
  WithTop.untopA (exitTime' B S X)

/-- A stopped record: cut time and prefix, extended constantly after the cut. -/
def resumeRecord (B : Base) (S : Set (Site B)) (X : ℕ → Site B) :
    ℕ × (ℕ → Site B) :=
  (resumeCut B S X, fun n => X (min n (resumeCut B S X)))

/-- The continuation includes the exit site at its time zero. -/
def resumeTail (B : Base) (S : Set (Site B)) (X : ℕ → Site B) : ℕ → Site B :=
  fun n => X (resumeCut B S X + n)

theorem measurable_resumeCut (B : Base) (S : Set (Site B)) :
    Measurable (resumeCut B S) := measurable_ghostExitIndex B S

theorem measurable_resumeRecord (B : Base) (S : Set (Site B)) :
    Measurable (resumeRecord B S) := by
  have heval : Measurable (fun kX : ℕ × (ℕ → Site B) =>
      fun n => kX.2 (min n kX.1)) := by
    apply measurable_from_prod_countable_right
    intro k
    exact measurable_pi_iff.mpr (fun n => measurable_pi_apply (min n k))
  exact (measurable_resumeCut B S).prodMk
    (heval.comp ((measurable_resumeCut B S).prodMk measurable_id))

theorem measurable_resumeTail (B : Base) (S : Set (Site B)) :
    Measurable (resumeTail B S) := by
  have heval : Measurable (fun kX : ℕ × (ℕ → Site B) => fun n => kX.2 (kX.1 + n)) := by
    apply measurable_from_prod_countable_right
    intro k
    exact measurable_pi_iff.mpr (fun n => measurable_pi_apply (k + n))
  exact heval.comp ((measurable_resumeCut B S).prodMk measurable_id)

/-- Agreement through a finite exit determines the entire stopped record. -/
theorem resumeRecord_eq_of_prefix (B : Base) (S : Set (Site B))
    (k : ℕ) (f X : ℕ → Site B) (hcut : exitTime' B S f = (k : ℕ∞))
    (hX : X ∈ pathCyl B k f) : resumeRecord B S X = resumeRecord B S f := by
  have ht := ghostExitTime_eq_of_prefix B S k f X hcut hX
  have hx : resumeCut B S X = k := by simp only [resumeCut, ht, untopA_natCast]
  have hf : resumeCut B S f = k := by simp only [resumeCut, hcut, untopA_natCast]
  apply Prod.ext
  · exact hx.trans hf.symm
  · change (fun n => X (min n (resumeCut B S X))) =
      (fun n => f (min n (resumeCut B S f)))
    rw [hx, hf]
    exact funext (fun n => hX (min n k) (min_le_right n k))

private theorem resume_splice_prefix (B : Base) (k : ℕ) (f Y : ℕ → Site B) :
    ghostSplicePath B f Y k ∈ pathCyl B k f := by
  intro n hn
  exact if_pos hn

private theorem resumeTail_splice (B : Base) (S : Set (Site B)) (k : ℕ)
    (f Y : ℕ → Site B) (hcut : exitTime' B S f = (k : ℕ∞)) (hY : Y 0 = f k) :
    resumeTail B S (ghostSplicePath B f Y k) = Y := by
  have ht := ghostExitTime_eq_of_prefix B S k f _ hcut (resume_splice_prefix B k f Y)
  funext n
  change ghostSplicePath B f Y k (WithTop.untopA
    (exitTime' B S (ghostSplicePath B f Y k)) + n) = Y n
  rw [ht, untopA_natCast]
  by_cases hn : n = 0
  · subst n
    simp only [Nat.add_zero, ghostSplicePath, if_pos le_rfl]
    exact hY.symm
  · simp only [ghostSplicePath, if_neg (by omega : ¬ k + n ≤ k),
      Nat.add_sub_cancel_left]

private def resumeContinuationKernel (B : Base) (S : Set (Site B)) :
    Kernel (ℕ → Site B) (ℕ → Site B) where
  toFun X := walkPathLaw B (exitSite' B S X)
  measurable' := (measurable_of_countable (walkPathLaw B)).comp (measurable_exitSite' B S)

private instance resumeContinuationKernel_isMarkov (B : Base) (S : Set (Site B)) :
    IsMarkovKernel (resumeContinuationKernel B S) :=
  ⟨fun X => walkPathLaw_isProbability B (exitSite' B S X)⟩

/-- Retain the exposed record and sample an independent continuation at its exit site. -/
def resumeRecordKernel (B : Base) (S : Set (Site B)) :
    Kernel (ℕ → Site B) ((ℕ × (ℕ → Site B)) × (ℕ → Site B)) :=
  (Kernel.id.prod (resumeContinuationKernel B S)).map
    (fun XY => (resumeRecord B S XY.1, XY.2))

instance resumeRecordKernel_isMarkov (B : Base) (S : Set (Site B)) :
    IsMarkovKernel (resumeRecordKernel B S) :=
  Kernel.IsMarkovKernel.map _
    (((measurable_resumeRecord B S).comp measurable_fst).prodMk measurable_snd)

theorem resumeRecordKernel_apply (B : Base) (S : Set (Site B)) (X : ℕ → Site B) :
    resumeRecordKernel B S X = (walkPathLaw B (exitSite' B S X)).map
      (fun Y => (resumeRecord B S X, Y)) := by
  have hm : Measurable (fun XY : (ℕ → Site B) × (ℕ → Site B) =>
      (resumeRecord B S XY.1, XY.2)) :=
    ((measurable_resumeRecord B S).comp measurable_fst).prodMk measurable_snd
  rw [resumeRecordKernel, Kernel.map_apply _ hm, Kernel.prod_apply, Kernel.id_apply,
    Measure.dirac_prod, Measure.map_map hm measurable_prodMk_left]
  rfl

private theorem resumeRecordKernel_eq_of_prefix (B : Base) (S : Set (Site B))
    (k : ℕ) (f X : ℕ → Site B) (hcut : exitTime' B S f = (k : ℕ∞))
    (hX : X ∈ pathCyl B k f) :
    resumeRecordKernel B S X = (walkPathLaw B (f k)).map
      (fun Y => (resumeRecord B S f, Y)) := by
  have ht := ghostExitTime_eq_of_prefix B S k f X hcut hX
  have hsite : exitSite' B S X = f k := by
    change X (WithTop.untopA (exitTime' B S X)) = f k
    rw [ht, untopA_natCast]
    exact hX k le_rfl
  rw [resumeRecordKernel_apply, hsite, resumeRecord_eq_of_prefix B S k f X hcut hX]

/-- On each valid finite stopped cylinder, the full record and the continuation factor. -/
theorem walkPathLaw_restrict_map_resumeRecord_tail (B : Base) (p : Site B)
    (S : Set (Site B)) (k : ℕ) (f : ℕ → Site B)
    (hcut : exitTime' B S f = (k : ℕ∞)) :
    ((walkPathLaw B p).restrict (pathCyl B k f)).map
        (fun X => (resumeRecord B S X, resumeTail B S X)) =
      (walkPathLaw B p (pathCyl B k f)) •
        (walkPathLaw B (f k)).map (fun Y => (resumeRecord B S f, Y)) := by
  have hj := (measurable_resumeRecord B S).prodMk (measurable_resumeTail B S)
  have hsplice : Measurable (fun Y => ghostSplicePath B f Y k) :=
    (measurable_ghostSplicePath B).comp
      ((measurable_const.prodMk measurable_id).prodMk measurable_const)
  rw [walkPathLaw_restrict_pathCyl_splice, Measure.map_smul, Measure.map_map hj hsplice]
  congr 1
  apply Measure.map_congr
  filter_upwards [walkPathLaw_ae_start B (f k)] with Y hY
  exact Prod.ext
    (resumeRecord_eq_of_prefix B S k f _ hcut (resume_splice_prefix B k f Y))
    (resumeTail_splice B S k f Y hcut hY)

private theorem walkPathLaw_restrict_bind_resumeRecord (B : Base) (p : Site B)
    (S : Set (Site B)) (k : ℕ) (f : ℕ → Site B)
    (hcut : exitTime' B S f = (k : ℕ∞)) :
    ((walkPathLaw B p).restrict (pathCyl B k f)).bind (resumeRecordKernel B S) =
      (walkPathLaw B p (pathCyl B k f)) •
        (walkPathLaw B (f k)).map (fun Y => (resumeRecord B S f, Y)) := by
  have hconst : (resumeRecordKernel B S : _ → Measure _) =ᵐ[
      (walkPathLaw B p).restrict (pathCyl B k f)]
      (fun _ => (walkPathLaw B (f k)).map (fun Y => (resumeRecord B S f, Y))) := by
    filter_upwards [ae_restrict_mem (measurableSet_pathCyl B k f)] with X hX
    exact resumeRecordKernel_eq_of_prefix B S k f X hcut hX
  rw [Measure.bind_congr_right hconst, Measure.bind_const,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]

/-- The actual finite first exit has a fresh continuation conditional on its entire record.
Finite exit is derived from the height cap and the proved recurrence theorem. -/
theorem walkPathLaw_map_resumeRecord_tail (B : Base) (p : Site B)
    (S : Set (Site B)) (h : ℤ) (hS : S ⊆ R B ((h : ℝ) - 1)) :
    (walkPathLaw B p).map (fun X => (resumeRecord B S X, resumeTail B S X)) =
      (walkPathLaw B p).bind (resumeRecordKernel B S) := by
  have hfin : ∀ᵐ X ∂walkPathLaw B p, exitTime' B S X ≠ ⊤ := by
    filter_upwards [ae_exists_ver_eq External.lazyRwRecurrent_holds B p h] with X hX
    obtain ⟨n, hn⟩ := hX
    exact exitTime'_ne_top_of_height B hS hn.ge
  have hsum := walkPathLaw_eq_sum_ghostStoppedPrefix B p S hfin
  have hj := (measurable_resumeRecord B S).prodMk (measurable_resumeTail B S)
  rw [← hsum, Measure.map_sum hj.aemeasurable,
    Measure.bind_sum _ _ (resumeRecordKernel B S).measurable.aemeasurable]
  congr 1
  funext c
  unfold ghostStoppedPrefixEvent
  split_ifs with hc
  · rw [walkPathLaw_restrict_map_resumeRecord_tail B p S c.1 _ hc,
      walkPathLaw_restrict_bind_resumeRecord B p S c.1 _ hc]
  · rw [Measure.restrict_empty, Measure.map_zero, Measure.bind_zero_left]

example (B : Base) (p : Site B) :
    (walkPathLaw B p).map (fun X => (resumeRecord B ∅ X, resumeTail B ∅ X)) =
      (walkPathLaw B p).bind (resumeRecordKernel B ∅) :=
  walkPathLaw_map_resumeRecord_tail B p ∅ 1 (Set.empty_subset _)

example : IsMarkovKernel (resumeRecordKernel PrInnerTail.K2 (R PrInnerTail.K2 0)) :=
  inferInstance

end
end IdlaCyl
