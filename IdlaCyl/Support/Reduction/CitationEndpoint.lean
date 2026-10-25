module

/-
The cited finite-history coupling implies the fixed-start endpoint form.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453; Silvestri Proposition 2,
silvestri2020.txt:334-344. The citation is an explicit hypothesis throughout.
-/
public import IdlaCyl.External.SilvestriProp2
public import IdlaCyl.Support.Reduction.CouplingBasic

@[expose] public section

namespace IdlaCyl.Reduction

open MeasureTheory

/-- The cited history law's last coordinate is exactly the prescribed finite release queue. -/
theorem silvestri_endpoint_law (B : Base) (T : ℕ) (F : ResumeFinite B)
    (s : Fin T → Site B) :
    (External.silvestriProcessLaw B T F s).map (fun H => H (Fin.last T)) =
      resumeRun B F (List.ofFn s) := by
  rw [External.silvestriProcessLaw, Measure.map_map (measurable_pi_apply (Fin.last T))
    (External.measurable_silvestriHistory B T F)]
  have hqueue : List.ofFn (fun i : Fin T => External.silvestriStarts B T s i) =
      List.ofFn s := by
    congr 1
    funext i
    exact dif_pos i.isLt
  exact (prescribedMeasure_map_resumeGrow B F (External.silvestriStarts B T s) T).trans
    (congrArg (resumeRun B F) hqueue)

/-- Fixed-start endpoint specialization with exactly the source's polynomial time bound. -/
theorem silvestri_endpoint (hsil : External.silvestri_prop2)
    (m : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    ∃ b : ℝ, 0 < b ∧ ∃ N₀ : ℕ, ∀ (B : Base), N₀ ≤ B.card → ∀ (T : ℕ),
      0 < T → T ≤ B.card ^ m →
      ∀ (F : ResumeFinite B) (s s' : Fin T → Site B),
        SeedConnected B (resumeSeed B F) →
        (∀ i, (s i).2 ≤ 0) → (∀ i, (s' i).2 ≤ 0) →
        R B (b * Real.sqrt (External.silvestriMixingTime B) *
          Real.log (B.card : ℝ)) ⊆ resumeSeed B F →
        ClusterCoupling B
          (resumeRun B F (List.ofFn s))
          (resumeRun B F (List.ofFn s')) 0 ((B.card : ℝ) ^ (-γ)) := by
  obtain ⟨J, hJ, hconf⟩ := hsil m
  obtain ⟨b, hb, N₀, hbound⟩ := hconf γ hγ
  refine ⟨b, hb, N₀, fun B hN T hT hTm F s s' hconn hs hs' hF => ?_⟩
  let μ := J B T F s s'
  have hmarg := hJ B T hT hTm F s s' hconn hs hs'
  haveI : IsProbabilityMeasure μ := probability_of_first_marginal μ _ hmarg.1
  let e : External.SilvestriHistory B T × External.SilvestriHistory B T →
      ResumeFinite B × ResumeFinite B := fun p => (p.1 (Fin.last T), p.2 (Fin.last T))
  have he : Measurable e := (measurable_pi_apply (Fin.last T) |>.comp measurable_fst).prodMk
    ((measurable_pi_apply (Fin.last T)).comp measurable_snd)
  refine ⟨μ.map e, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst he]
    have hm := Measure.map_map (measurable_pi_apply (Fin.last T)) measurable_fst (μ := μ)
    rw [hmarg.1, silvestri_endpoint_law] at hm
    exact hm.symm
  · rw [Measure.map_map measurable_snd he]
    have hm := Measure.map_map (measurable_pi_apply (Fin.last T)) measurable_snd (μ := μ)
    rw [hmarg.2, silvestri_endpoint_law] at hm
    exact hm.symm
  · rw [Measure.map_apply he (Set.to_countable _).measurableSet]
    have hsub : e ⁻¹' (matchShift B 0)ᶜ ⊆ {p : External.SilvestriHistory B T ×
        External.SilvestriHistory B T | p.1 = p.2}ᶜ := by
      intro p hp heq
      apply hp
      rw [mem_matchShift_zero]
      exact congrFun heq (Fin.last T)
    apply (measure_mono hsub).trans
    exact failure_le_of_success μ _ (Set.to_countable _).measurableSet _
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hbound B hN T hT hTm F s s' hconn hs hs' hF)

end IdlaCyl.Reduction
