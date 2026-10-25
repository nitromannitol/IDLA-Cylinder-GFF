module

/-
Fresh entrance tails and the exact release-layer transition identity.
Source: paper/idla-cylinder-gff.tex, tex:246-265,595-610,1385-1396,1440-1453.
The whole occupied prefix is ignored only after its actual
finite stopping time has been identified. This is an equality in law.
-/
public import IdlaCyl.Support.Reduction.CouponGrowth
public import IdlaCyl.Support.Outer.ResumeStopped

@[expose] public section

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Exiting the lower half-cylinder is exactly the first entrance to its next layer. -/
theorem exit_lower_eq_hit (B : Base) (L : ℤ) (X : ℕ → Site B)
    (ha : CylAdmissible B X) (h0 : (X 0).2 ≤ L) (hf : hitLevel B L X ≠ ⊤) :
    exitTime' B (R B ((L : ℝ) - 1)) X = hitLevel B L X := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hf
  have hhit : hitLevel B L X = (k : ℕ∞) := hk.symm
  rw [hhit]
  apply (exitTime'_eq_coe_iff B _ X k).mpr
  constructor
  · intro hmem
    have hv := ((hitLevel_eq_coe_iff B L X k).mp hhit).1
    have hr := mem_R.mp hmem
    rw [hv] at hr
    linarith
  · intro n hn
    exact mem_R.mpr (by exact_mod_cast (before_first_entrance B L X ha h0 k hhit n hn))

/-- The actual lower-half-cylinder exit and first-entrance sites agree. -/
theorem exit_lower_site_eq (B : Base) (L : ℤ) (X : ℕ → Site B)
    (ha : CylAdmissible B X) (h0 : (X 0).2 ≤ L) (hf : hitLevel B L X ≠ ⊤) :
    exitSite' B (R B ((L : ℝ) - 1)) X = firstHitSite B L X := by
  change X (WithTop.untopA (exitTime' B _ X)) = X (WithTop.untopA (hitLevel B L X))
  rw [exit_lower_eq_hit B L X ha h0 hf]

/-- Removing a finite occupied prefix does not alter the later finite exit site. -/
theorem exitSite_skip_prefix (B : Base) (S : Set (Site B)) (X : ℕ → Site B)
    (k : ℕ) (hk : ∀ i < k, X i ∈ S) (hf : exitTime' B S X ≠ ⊤) :
    exitSite' B S X = exitSite' B S (fun n => X (k + n)) := by
  obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.mp hf
  have hexit : exitTime' B S X = (l : ℕ∞) := hl.symm
  obtain ⟨hnot, hbefore⟩ := (exitTime'_eq_coe_iff B S X l).mp hexit
  have hkl : k ≤ l := by
    by_contra h
    exact hnot (hk l (by omega))
  have htail : exitTime' B S (fun n => X (k + n)) = ((l - k : ℕ) : ℕ∞) := by
    apply (exitTime'_eq_coe_iff B S _ (l - k)).mpr
    constructor
    · rwa [Nat.add_sub_of_le hkl]
    · intro n hn
      exact hbefore (k + n) (by omega)
  change X (WithTop.untopA (exitTime' B S X)) =
    X (k + WithTop.untopA (exitTime' B S (fun n => X (k + n))))
  rw [hexit, htail, untopA_natCast, untopA_natCast, Nat.add_sub_of_le hkl]

/-- The stopped-record factorization holds at every uniform starting layer. -/
theorem layerWalk_map_record_tail (B : Base) (h : ℤ) (S : Set (Site B))
    (j : ℤ) (hS : S ⊆ R B ((j : ℝ) - 1)) :
    (walkLawUniformAt B h).map (fun X => (resumeRecord B S X, resumeTail B S X)) =
      (walkLawUniformAt B h).bind (resumeRecordKernel B S) := by
  have hj := (measurable_resumeRecord B S).prodMk (measurable_resumeTail B S)
  rw [walkLawUniformAt_eq_bind,
    resume_map_bind _ _ _ (measurable_of_countable _) hj,
    Measure.bind_bind (measurable_of_countable _).aemeasurable
      (resumeRecordKernel B S).measurable.aemeasurable]
  exact Measure.bind_congr_right (Filter.Eventually.of_forall
    (fun p => walkPathLaw_map_resumeRecord_tail B p S j hS))

/-- After dropping the record, the tail is the mixture of fresh walks from the exit. -/
theorem layerWalk_map_tail (B : Base) (h : ℤ) (S : Set (Site B))
    (j : ℤ) (hS : S ⊆ R B ((j : ℝ) - 1)) :
    (walkLawUniformAt B h).map (resumeTail B S) =
      (walkLawUniformAt B h).bind (fun X => walkPathLaw B (exitSite' B S X)) := by
  have heq := congrArg (fun μ : Measure ((ℕ × (ℕ → Site B)) × (ℕ → Site B)) =>
    μ.map Prod.snd) (layerWalk_map_record_tail B h S j hS)
  rw [Measure.map_map measurable_snd
    ((measurable_resumeRecord B S).prodMk (measurable_resumeTail B S)),
    resume_map_bind _ _ _ (resumeRecordKernel B S).measurable measurable_snd] at heq
  have hkernel (X : ℕ → Site B) :
      (resumeRecordKernel B S X).map Prod.snd = walkPathLaw B (exitSite' B S X) := by
    rw [resumeRecordKernel_apply, Measure.map_map measurable_snd measurable_prodMk_left]
    exact Measure.map_id
  simp_rw [hkernel] at heq
  exact heq

/-- The entire post-entrance trajectory has the stationary-layer walk law. -/
theorem entrance_tail_law (B : Base) (h L : ℤ) (hhL : h ≤ L) :
    (walkLawUniformAt B h).map (resumeTail B (R B ((L : ℝ) - 1))) =
      walkLawUniformAt B L := by
  rw [layerWalk_map_tail B h _ L Set.Subset.rfl]
  calc
    _ = (walkLawUniformAt B h).bind (fun X => walkPathLaw B (firstHitSite B L X)) := by
      apply Measure.bind_congr_right
      filter_upwards [walkLawUniformAt_ae_admissible B h, layerWalk_ae_start B h,
        layerWalk_ae_hit_finite B h L] with X ha hs hf
      rw [exit_lower_site_eq B L X ha (by rw [hs]; exact hhL) hf]
    _ = ((walkLawUniformAt B h).map (firstHitSite B L)).bind (walkPathLaw B) :=
      (resume_bind_map _ _ _ (measurable_firstHitSite B L) (measurable_of_countable _)).symm
    _ = walkLawUniformAt B L := by rw [stationary_entrance, walkLawUniformAt_eq_bind]

/-- Releases below L agree with releases at L when every strictly lower site is occupied. -/
theorem below_next_layer_release_step (B : Base) (F : ResumeFinite B)
    (h L : ℤ) (hhL : h ≤ L) (hF : R B ((L : ℝ) - 1) ⊆ resumeSeed B F) :
    (walkLawUniformAt B h).map
        (fun X => resumeInsert B F (exitSite' B (resumeSeed B F) X)) =
      (walkLawUniformAt B L).map
        (fun X => resumeInsert B F (exitSite' B (resumeSeed B F) X)) := by
  let S := R B ((L : ℝ) - 1)
  let out := fun X => resumeInsert B F (exitSite' B (resumeSeed B F) X)
  have hsame : out =ᵐ[walkLawUniformAt B h] (fun X => out (resumeTail B S X)) := by
    filter_upwards [walkLawUniformAt_ae_admissible B h, layerWalk_ae_start B h,
      layerWalk_ae_hit_finite B h L, ae_all_iff.mpr (layerWalk_ae_hits B h)] with X ha hs hf hall
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hf
    have hhit : hitLevel B L X = (k : ℕ∞) := hk.symm
    have hexit : exitTime' B S X = (k : ℕ∞) :=
      (exit_lower_eq_hit B L X ha (by rw [hs]; exact hhL) hf).trans hhit
    have hpre : ∀ n < k, X n ∈ resumeSeed B F := by
      intro n hn
      apply hF
      have hv := before_first_entrance B L X ha (by rw [hs]; exact hhL) k hhit n hn
      exact mem_R.mpr (by exact_mod_cast hv)
    have hfin : exitTime' B (resumeSeed B F) X ≠ ⊤ := by
      simpa only [resumeSeed, Int.cast_zero] using
        outer_exit_ne_top_of_hits B 0 F.val X hall
    have hskip := exitSite_skip_prefix B (resumeSeed B F) X k hpre hfin
    have htail : resumeTail B S X = fun n => X (k + n) := by
      funext n
      change X (WithTop.untopA (exitTime' B S X) + n) = _
      rw [hexit, untopA_natCast]
    change resumeInsert B F (exitSite' B (resumeSeed B F) X) = _
    rw [htail, hskip]
  calc
    _ = (walkLawUniformAt B h).map (fun X => out (resumeTail B S X)) :=
      Measure.map_congr hsame
    _ = ((walkLawUniformAt B h).map (resumeTail B S)).map out :=
      (Measure.map_map (measurable_resumeStep_output B F) (measurable_resumeTail B S)).symm
    _ = _ := by rw [entrance_tail_law B h L hhL]

/-- Releasing uniformly below a filled layer has exactly its canonical transition kernel. -/
theorem below_layer_release_step (B : Base) (F : ResumeFinite B)
    (h L : ℤ) (hhL : h ≤ L) (hF : R B (L : ℝ) ⊆ resumeSeed B F) :
    (walkLawUniformAt B h).map
        (fun X => resumeInsert B F (exitSite' B (resumeSeed B F) X)) =
      (walkLawUniformAt B L).map
        (fun X => resumeInsert B F (exitSite' B (resumeSeed B F) X)) :=
  below_next_layer_release_step B F h L hhL ((R_mono (by linarith)).trans hF)

end IdlaCyl.Reduction
