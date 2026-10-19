/-
One freezing update followed by fresh completion preserves the ordinary law.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396,1440-1453.
Commutation is used only for independent release kernels.
-/
import IdlaCyl.Support.Reduction.LayerPause
import IdlaCyl.Support.Outer.ResumeFinish

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Completing one coupon update equals a fresh release from that coupon, then the old queue. -/
theorem freezeCoupon_finish (B : Base) (F : ResumeFinite B) (L : List (Site B))
    (z : Site B) :
    resumeRun B (freezeCoupon B (F, L) z).1 (freezeCoupon B (F, L) z).2 =
      (resumeStep B z F).bind (fun G => resumeRun B G L) := by
  unfold freezeCoupon
  split_ifs with hz
  · rw [resumeRun_append]
    have hsingle : (fun G => resumeRun B G [z]) = resumeStep B z := by
      funext G
      exact Measure.bind_dirac
    rw [hsingle]
    exact (resumeStep_commute_run B F z L).symm
  · rw [resumeStep_outside B F z hz,
      Measure.dirac_bind (measurable_of_countable (fun G => resumeRun B G L))]

/-- A release from zero first reaches j+1 with the correct fresh continuation, even if empty. -/
theorem uniformStep_entrance_bind (B : Base) (j : ℕ) (F : ResumeFinite B)
    (hF : R B (j : ℝ) ⊆ resumeSeed B F) :
    resumeUniformStep B F = (layerLawAt B (j + 1 : ℕ)).bind (fun z => resumeStep B z F) := by
  have hlower : R B (((j + 1 : ℕ) : ℝ) - 1) ⊆ resumeSeed B F := by
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hF
  have hstep := below_next_layer_release_step B F 0 (j + 1 : ℕ) (by omega) hlower
  change (walkLawUniformAt B 0).map
    (fun X => resumeInsert B F (exitSite' B (resumeSeed B F) X)) = _
  rw [hstep, walkLawUniformAt_eq_bind,
    resume_map_bind _ _ _ (measurable_of_countable _) (measurable_resumeStep_output B F)]
  rfl

/-- A whole new particle can be frozen at the next layer and freshly completed without bias. -/
theorem freezeLayer_finish (B : Base) (j : ℕ) (F : ResumeFinite B)
    (L : List (Site B)) (hF : R B (j : ℝ) ⊆ resumeSeed B F) :
    (freezeLayerStep B (j + 1 : ℕ) (F, L)).bind
        (fun s => resumeRun B s.1 s.2) =
      (resumeRun B F L).bind (resumeUniformStep B) := by
  have hmap : freezeLayerStep B (j + 1 : ℕ) (F, L) =
      (layerLawAt B (j + 1 : ℕ)).map (freezeCoupon B (F, L)) := by
    change (walkLawUniformAt B 0).map
      (freezeCoupon B (F, L) ∘ firstHitSite B (j + 1 : ℕ)) = _
    rw [← Measure.map_map (measurable_of_countable (freezeCoupon B (F, L)))
        (measurable_firstHitSite B (j + 1 : ℕ))]
    rw [stationary_entrance]
  rw [hmap, resume_bind_map _ _ _ (measurable_of_countable _) (measurable_of_countable _)]
  simp_rw [freezeCoupon_finish]
  rw [← Measure.bind_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable, ← uniformStep_entrance_bind B j F hF]
  exact resumeUniformStep_commute_run B F L

/-- A frozen step retains every previously filled rectangle almost surely. -/
theorem freezeLayer_ae_seed (B : Base) (j : ℤ) (s : ResumeState B) :
    ∀ᵐ t ∂freezeLayerStep B j s, resumeSeed B s.1 ⊆ resumeSeed B t.1 := by
  apply (ae_map_iff ((measurable_of_countable (freezeCoupon B s)).comp
    (measurable_firstHitSite B j)).aemeasurable (Set.to_countable _).measurableSet).mpr
  exact Filter.Eventually.of_forall (fun X => freezeCoupon_seed_mono B s (firstHitSite B j X))

/-- One ordinary release is the one-addition growth kernel. -/
theorem uniformStep_eq_layerGrowth_one (B : Base) (F : ResumeFinite B) :
    resumeUniformStep B F = layerGrowthLaw B F 0 1 := by
  rw [layerGrowthLaw_succ, layerGrowthLaw_zero,
    Measure.dirac_bind (measurable_of_countable _)]
  rfl

/-- Completing a batch yields the same law as exactly that many ordinary fresh additions. -/
theorem freezeBatch_finish (B : Base) (j M : ℕ) (F : ResumeFinite B)
    (L : List (Site B)) (hF : R B (j : ℝ) ⊆ resumeSeed B F) :
    (freezeBatch B (j + 1 : ℕ) M (F, L)).bind (fun s => resumeRun B s.1 s.2) =
      (resumeRun B F L).bind (fun G => layerGrowthLaw B G 0 M) := by
  induction M generalizing F L with
  | zero =>
      simp only [freezeBatch, Measure.dirac_bind (measurable_of_countable
        (fun s : ResumeState B => resumeRun B s.1 s.2)), layerGrowthLaw_zero,
        Measure.bind_dirac]
  | succ M ih =>
      rw [freezeBatch, Measure.bind_bind (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable]
      have heq : (fun s => (freezeBatch B (j + 1 : ℕ) M s).bind
          (fun t => resumeRun B t.1 t.2)) =ᵐ[freezeLayerStep B (j + 1 : ℕ) (F, L)]
          (fun s => (resumeRun B s.1 s.2).bind (fun G => layerGrowthLaw B G 0 M)) := by
        filter_upwards [freezeLayer_ae_seed B (j + 1 : ℕ) (F, L)] with s hs
        exact ih s.1 s.2 (hF.trans hs)
      rw [Measure.bind_congr_right heq,
        ← Measure.bind_bind (measurable_of_countable _).aemeasurable
          (measurable_of_countable _).aemeasurable, freezeLayer_finish B j F L hF,
        Measure.bind_bind (measurable_of_countable _).aemeasurable
          (measurable_of_countable _).aemeasurable]
      congr 1
      funext G
      rw [uniformStep_eq_layerGrowth_one, ← layerGrowthLaw_add, Nat.add_comm 1 M]

end IdlaCyl.Reduction
