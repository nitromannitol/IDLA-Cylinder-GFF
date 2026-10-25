module

/-
Completing the chronological paused queue preserves the ordinary cluster law.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396.
The proof uses commuting release kernels and the independently sampled resumed
walks. It never reorders saved labelled trajectories pathwise.
-/
public import IdlaCyl.Support.Outer.ResumePaused

@[expose] public section

attribute [local instance] Classical.propDecidable

namespace IdlaCyl
open MeasureTheory ProbabilityTheory
noncomputable section

/-- Tonelli's interchange for two independent countable inputs and a measurable kernel. -/
theorem resume_bind_swap {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [Countable α] [Countable β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (κ : α → β → Measure γ) :
    μ.bind (fun a => ν.bind (κ a)) = ν.bind (fun b => μ.bind (fun a => κ a b)) := by
  ext S hS
  rw [Measure.bind_apply hS (measurable_of_countable _).aemeasurable,
    Measure.bind_apply hS (measurable_of_countable _).aemeasurable]
  simp_rw [Measure.bind_apply hS (measurable_of_countable _).aemeasurable]
  exact lintegral_lintegral_swap (measurable_of_countable (fun ab : α × β => κ ab.1 ab.2 S)).aemeasurable

/-- A release started outside the seed settles at time zero, almost surely. -/
theorem resumeStep_outside (B : Base) (F : ResumeFinite B) (p : Site B)
    (hp : p ∉ resumeSeed B F) :
    resumeStep B p F = Measure.dirac (resumeInsert B F p) := by
  have hout : (fun X => resumeInsert B F (exitSite' B (resumeSeed B F) X)) =ᵐ[
      walkPathLaw B p] (fun _ => resumeInsert B F p) := by
    filter_upwards [walkPathLaw_ae_zero B p] with X hX
    have ht : exitTime' B (resumeSeed B F) X = (0 : ℕ∞) := by
      apply (exitTime'_eq_coe_iff B _ X 0).mpr
      exact ⟨by rw [hX]; exact hp, by intro j hj; omega⟩
    change resumeInsert B F (X (WithTop.untopA (exitTime' B (resumeSeed B F) X))) = _
    rw [ht]
    change resumeInsert B F (X 0) = _
    rw [hX]
  rw [resumeStep, Measure.map_congr hout, Measure.map_const, measure_univ, one_smul]

/-- A finite first exit from a region below h cannot jump above h. -/
theorem resume_exit_ver_le (B : Base) (h : ℤ) (hh : 1 ≤ h) (A : Set (Site B))
    (hA : A ⊆ R B ((h : ℝ) - 1)) (X : ℕ → Site B)
    (hadm : CylAdmissible B X) (h0 : X 0 ∈ R B 0)
    (hfin : exitTime' B A X ≠ ⊤) : (exitSite' B A X).2 ≤ h := by
  obtain ⟨k, ht⟩ : ∃ k : ℕ, exitTime' B A X = (k : ℕ∞) :=
    ⟨_, (ENat.coe_toNat hfin).symm⟩
  change (X (WithTop.untopA (exitTime' B A X))).2 ≤ h
  rw [ht, untopA_natCast]
  cases k with
  | zero =>
      have hzero : (X 0).2 ≤ 0 := by exact_mod_cast (mem_R.mp h0)
      omega
  | succ k =>
      have hbefore := (exitTime'_eq_coe_iff B A X (k + 1)).mp ht
      have hprev : (X k).2 ≤ h - 1 := by
        have hv := mem_R.mp (hA (hbefore.2 k (by omega)))
        exact_mod_cast hv
      rcases CylAdmissible.ver_step B hadm k with hs | hs | hs <;> omega

/-- Actual uniform-start pause exits are finite, fresh, and no higher than the cap. -/
theorem resumeUniform_ae_exit (B : Base) (h : ℤ) (hh : 1 ≤ h) (F : ResumeFinite B)
    (hF : resumeSeed B F ⊆ R B ((h : ℝ) - 1)) :
    ∀ᵐ X ∂walkLawUniform B,
      exitSite' B (resumeSeed B F) X ∉ resumeSeed B F ∧
        (exitSite' B (resumeSeed B F) X).2 ≤ h := by
  filter_upwards [walkLawUniform_ae_hits_level B h,
    walkLawUniformAt_ae_admissible B 0, walkLawUniform_ae_ver_zero B] with X hhit hadm hzero
  obtain ⟨n, hn⟩ := hhit
  have hfin := exitTime'_ne_top_of_height B hF hn.ge
  exact ⟨exitSite'_mem_compl B _ hfin,
    resume_exit_ver_le B h hh _ hF X hadm (mem_R.mpr (by rw [hzero]; norm_num)) hfin⟩

/-- Finishing after one pause update equals inserting its fresh exit before the old queue. -/
theorem resumePauseUpdate_finish (B : Base) (h : ℤ) (F : ResumeFinite B)
    (L : List (Site B)) (z : Site B) (hz : z ∉ resumeSeed B F) (hzle : z.2 ≤ h) :
    resumeRun B (resumePauseUpdate B h (F, L) z).1
        (resumePauseUpdate B h (F, L) z).2 =
      resumeRun B (resumeInsert B F z) L := by
  by_cases hlt : z.2 < h
  · have hne : z.2 ≠ h := by omega
    simp only [resumePauseUpdate, if_pos hlt, if_neg hne]
  · have heq : z.2 = h := by omega
    simp only [resumePauseUpdate, if_neg hlt, if_pos heq]
    rw [resumeRun_append]
    have hsingle : (fun G => resumeRun B G [z]) = resumeStep B z := by
      funext G
      exact Measure.bind_dirac
    rw [hsingle, ← resumeStep_commute_run, resumeStep_outside B F z hz]
    exact Measure.dirac_bind (measurable_of_countable (fun G => resumeRun B G L))
      (resumeInsert B F z)

theorem resumeUniformStep_eq_bind (B : Base) (F : ResumeFinite B) :
    resumeUniformStep B F = (layerLaw B).bind (fun p => resumeStep B p F) := by
  unfold resumeUniformStep walkLawUniform
  rw [walkLawUniformAt_eq_bind, resume_map_bind _ _ _ (measurable_of_countable _)
    (measurable_resumeStep_output B F)]
  rfl

/-- Uniform releases commute with every finite queue of prescribed independent releases. -/
theorem resumeUniformStep_commute_run (B : Base) (F : ResumeFinite B)
    (L : List (Site B)) :
    (resumeUniformStep B F).bind (fun G => resumeRun B G L) =
      (resumeRun B F L).bind (resumeUniformStep B) := by
  rw [resumeUniformStep_eq_bind, Measure.bind_bind
    (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
  simp_rw [resumeStep_commute_run]
  rw [resume_bind_swap]
  congr 1
  funext G
  exact (resumeUniformStep_eq_bind B G).symm

/-- The single-stage kernel identity underlying the whole pause/resume induction. -/
theorem resumePauseStep_finish (B : Base) (h : ℤ) (hh : 1 ≤ h) (s : ResumeState B)
    (hs : resumeSeed B s.1 ⊆ R B ((h : ℝ) - 1)) :
    (resumePauseStep B h s).bind (fun t => resumeRun B t.1 t.2) =
      (resumeRun B s.1 s.2).bind (resumeUniformStep B) := by
  rw [resumePauseStep, resume_bind_map (walkLawUniform B) (resumePausePathStep B h s)
    (fun t => resumeRun B t.1 t.2)
    (measurable_resumePausePathStep_fixed B h s)
    (measurable_of_countable _)]
  have hreplace : (fun X => resumeRun B (resumePausePathStep B h s X).1
      (resumePausePathStep B h s X).2) =ᵐ[walkLawUniform B]
      (fun X => resumeRun B (resumeInsert B s.1
        (exitSite' B (resumeSeed B s.1) X)) s.2) := by
    filter_upwards [resumeUniform_ae_exit B h hh s.1 hs] with X hX
    exact resumePauseUpdate_finish B h s.1 s.2 _ hX.1 hX.2
  rw [Measure.bind_congr_right hreplace]
  rw [← resume_bind_map (walkLawUniform B)
    (fun X => resumeInsert B s.1 (exitSite' B (resumeSeed B s.1) X))
    (fun G => resumeRun B G s.2) (measurable_resumeStep_output B s.1)
    (measurable_of_countable _)]
  exact resumeUniformStep_commute_run B s.1 s.2

/-- Completing the actual paused state has exactly the ordinary finite-cluster law. -/
theorem resumePauseGrow_finish_law (B : Base) (h : ℤ) (hh : 1 ≤ h) (T : ℕ) :
    ((idlaMeasure B).map (fun ω => resumePauseGrow B h ω T)).bind
        (fun s => resumeRun B s.1 s.2) =
      (idlaMeasure B).map (fun ω => resumeGrow B (resumeEmpty B) ω T) := by
  induction T with
  | zero =>
      simp only [resumePauseGrow, resumeGrow, Measure.map_const, measure_univ, one_smul,
        Measure.dirac_bind (measurable_of_countable
          (fun s : ResumeState B => resumeRun B s.1 s.2)), resumeRun]
  | succ T ih =>
      rw [idlaMeasure_map_resumePauseGrow_succ,
        Measure.bind_bind (measurable_of_countable _).aemeasurable
          (measurable_of_countable _).aemeasurable]
      have hae : ∀ᵐ s ∂(idlaMeasure B).map (fun ω => resumePauseGrow B h ω T),
          resumeSeed B s.1 ⊆ R B ((h : ℝ) - 1) := by
        apply ae_map_iff (measurable_resumePauseGrow B h T).aemeasurable
          ((Set.to_countable _).measurableSet)|>.mpr
        exact Filter.Eventually.of_forall (fun ω => resumePauseGrow_below B h hh ω T)
      have heq : (fun s => (resumePauseStep B h s).bind (fun t => resumeRun B t.1 t.2)) =ᵐ[
          (idlaMeasure B).map (fun ω => resumePauseGrow B h ω T)]
          (fun s => (resumeRun B s.1 s.2).bind (resumeUniformStep B)) :=
        hae.mono (fun s hs => resumePauseStep_finish B h hh s hs)
      rw [Measure.bind_congr_right heq,
        ← Measure.bind_bind (measurable_of_countable _).aemeasurable
          (measurable_of_countable _).aemeasurable, ih]
      exact (idlaMeasure_map_resumeGrow_succ B (resumeEmpty B) T).symm

example : ((idlaMeasure PrInnerTail.K2).map
      (fun ω => resumePauseGrow PrInnerTail.K2 2 ω 0)).bind
        (fun s => resumeRun PrInnerTail.K2 s.1 s.2) =
    (idlaMeasure PrInnerTail.K2).map
      (fun ω => resumeGrow PrInnerTail.K2 (resumeEmpty PrInnerTail.K2) ω 0) :=
  resumePauseGrow_finish_law PrInnerTail.K2 2 (by norm_num) 0

end
end IdlaCyl
