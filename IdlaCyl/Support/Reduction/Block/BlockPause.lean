module

public import IdlaCyl.Support.Reduction.FreezeFinish
public import IdlaCyl.Support.Reduction.LayeredFinish
public import IdlaCyl.Support.Outer.GhostMarkov
public import IdlaCyl.Support.StoppedAe

@[expose] public section

/-!
Block pause kernels for the reduction.

A block of `H` layers is filled by releasing uniform walkers and stopping each one at its first
exit from the occupied sites strictly below the block top. A walker that lands on an empty site
settles there; otherwise it is kept as a mobile copy in the queue. The main results show that a
stopped release, freshly resumed from its stopping site, has the law of an unstopped release,
so that completing any block schedule, followed by the remaining uniform releases, yields the
ordinary flat-start cluster law.
-/

attribute [local instance] Classical.propDecidable

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Release a uniform walker from layer `0` and stop it at its first exit from the occupied
sites strictly below height `h`. -/
noncomputable def freezeBlockStep (B : Base) (h : ℤ) (s : ResumeState B) :
    Measure (ResumeState B) :=
  (walkLawUniform B).map
    (fun X => freezeCoupon B s (exitSite' B (resumeSeed B s.1 ∩ R B ((h : ℝ) - 1)) X))

instance freezeBlockStep_isProbability (B : Base) (h : ℤ) (s : ResumeState B) :
    IsProbabilityMeasure (freezeBlockStep B h s) :=
  Measure.isProbabilityMeasure_map ((measurable_of_countable (freezeCoupon B s)).comp
    (measurable_exitSite' B _)).aemeasurable

/-- Exactly `M` stopped block releases, each one at the same stopping height `h`. -/
noncomputable def blockBatch (B : Base) (h : ℤ) : ℕ → ResumeState B → Measure (ResumeState B)
  | 0, s => Measure.dirac s
  | M + 1, s => (freezeBlockStep B h s).bind (blockBatch B h M)

instance blockBatch_isProbability (B : Base) (h : ℤ) (M : ℕ) (s : ResumeState B) :
    IsProbabilityMeasure (blockBatch B h M s) := by
  induction M generalizing s with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac s))
  | succ M ih =>
      apply isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
      exact Filter.Eventually.of_forall (fun t => ih t)

/-- Blocks of `H` layers: block `j + 1` stops at height `(j + 1) H` and runs only if the
rectangle `R_{jH}` is already filled. Each block uses `M` releases. -/
noncomputable def blockPause (B : Base) (M H : ℕ) : ℕ → ℕ → ResumeState B → ℕ →
    Measure (ResumeState B × ℕ)
  | 0, _, s, r => Measure.dirac (s, r)
  | n + 1, j, s, r =>
      if R B ((j * H : ℕ) : ℝ) ⊆ resumeSeed B s.1 then
        (blockBatch B ((j + 1) * H : ℕ) M s).bind
          (fun s' => blockPause B M H n (j + 1) s' (r - M))
      else Measure.dirac (s, r)

instance blockPause_isProbability (B : Base) (M H n j : ℕ) (s : ResumeState B) (r : ℕ) :
    IsProbabilityMeasure (blockPause B M H n j s r) := by
  induction n generalizing j s r with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (s, r)))
  | succ n ih =>
      unfold blockPause
      split_ifs
      · apply isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
        exact Filter.Eventually.of_forall (fun t => ih (j + 1) t (r - M))
      · infer_instance

/-- The seed of a finite extension is contained in some half-cylinder, so a walk from any
site leaves it almost surely. -/
theorem freezeBlock_seed_exit_ae (B : Base) (F : ResumeFinite B) (p : Site B) :
    ∀ᵐ Y ∂(walkPathLaw B p), exitTime' B (resumeSeed B F) Y ≠ ⊤ := by
  obtain ⟨H, hH⟩ : ∃ H : ℤ, ∀ z ∈ F.val, z.2 ≤ H := by
    obtain ⟨H, hH⟩ := (F.val.image (fun z : Site B => z.2)).bddAbove
    exact ⟨H, fun z hz => hH (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hz))⟩
  obtain ⟨h, hS⟩ : ∃ h : ℤ, resumeSeed B F ⊆ R B ((h : ℝ) - 1) := by
    refine ⟨max H 0 + 1, ?_⟩
    have hcast : ((max H 0 + 1 : ℤ) : ℝ) - 1 = ((max H 0 : ℤ) : ℝ) := by push_cast; ring
    rw [hcast]
    rintro q (hq | hq)
    · have h0 : (0 : ℝ) ≤ ((max H 0 : ℤ) : ℝ) := by exact_mod_cast le_max_right H 0
      exact (mem_R.mp hq).trans h0
    · have hq' := Finset.mem_coe.mp hq
      have hle : q.2 ≤ max H 0 := (hH q hq').trans (le_max_left H 0)
      rw [mem_R]
      exact_mod_cast hle
  filter_upwards [ae_exists_ver_eq External.lazyRwRecurrent_holds B p h] with Y hY
  obtain ⟨n, hn⟩ := hY
  exact exitTime'_ne_top_of_height B hS hn.ge

/-- A finite exit time gives the exit site as the value of the path at that time. -/
theorem exitSite'_eq_at_coe (B : Base) (S : Set (Site B)) (X : ℕ → Site B) (k : ℕ)
    (hk : exitTime' B S X = (k : ℕ∞)) : exitSite' B S X = X k := by
  change X (WithTop.untopA (exitTime' B S X)) = X k
  rw [hk, untopA_natCast]

/-- Splicing a continuation after a prefix that stays in `S ⊆ T` leaves the exit site from `T`
unchanged, provided the continuation starts at the splice point and exits `T` in finite time. -/
theorem resumeSeed_exit_splice (B : Base) (S T : Set (Site B)) (hST : S ⊆ T)
    (X Y : ℕ → Site B) (k : ℕ) (hτ : exitTime' B S X = (k : ℕ∞)) (hX : X k = Y 0)
    (hY : exitTime' B T Y ≠ ⊤) :
    exitSite' B T (ghostSplicePath B X Y k) = exitSite' B T Y := by
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hY
  have hexit : exitTime' B T Y = (m : ℕ∞) := hm.symm
  obtain ⟨hnot, hbefore⟩ := (exitTime'_eq_coe_iff B T Y m).mp hexit
  have hpre : ∀ i < k, X i ∈ T := fun i hi =>
    hST (((exitTime'_eq_coe_iff B S X k).mp hτ).2 i hi)
  have hWY : ∀ n, ghostSplicePath B X Y k (k + n) = Y n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ghostSplicePath, hX]
    · unfold ghostSplicePath
      rw [if_neg (by omega), Nat.add_sub_cancel_left]
  have hW : exitTime' B T (ghostSplicePath B X Y k) = ((k + m : ℕ) : ℕ∞) := by
    refine (exitTime'_eq_coe_iff B T _ (k + m)).mpr ⟨?_, ?_⟩
    · rw [hWY m]
      exact hnot
    · intro n hn
      by_cases hnk : n < k
      · unfold ghostSplicePath
        rw [if_pos (by omega)]
        exact hpre n hnk
      · by_cases hkn : n = k
        · rw [hkn]
          unfold ghostSplicePath
          rw [if_pos le_rfl, hX]
          exact hbefore 0 (by omega)
        · unfold ghostSplicePath
          rw [if_neg (by omega)]
          exact hbefore _ (by omega)
  rw [exitSite'_eq_at_coe B T _ (k + m) hW, exitSite'_eq_at_coe B T Y m hexit, hWY m]

/-- **One stopped block release, freshly resumed, has the ordinary uniform-release law.**
The walker stopped at its first exit from `S := resumeSeed ∩ R(h-1)` and continued by a fresh
walk from that site: the spliced path is again a uniform walk (ghost refresh invariance), and
its exit from the whole seed equals the exit of the fresh continuation. -/
theorem freezeBlockStep_finish (B : Base) (h : ℤ) (F : ResumeFinite B)
    (L : List (Site B)) :
    (freezeBlockStep B h (F, L)).bind (fun s => resumeRun B s.1 s.2) =
      (resumeRun B F L).bind (resumeUniformStep B) := by
  have hS : resumeSeed B F ∩ R B ((h : ℝ) - 1) ⊆ R B ((h : ℝ) - 1) := Set.inter_subset_right
  have hSseed : resumeSeed B F ∩ R B ((h : ℝ) - 1) ⊆ resumeSeed B F := Set.inter_subset_left
  have hκ : ∀ x, (walkPathLaw B x).bind (ghostExitRefreshKernel B (resumeSeed B F ∩ R B ((h : ℝ) - 1)))
      = walkPathLaw B x := fun x =>
    walkPathLaw_bind_ghostExitRefresh_of_subset B x _ h hS
  have hmu : (walkLawUniform B).bind (ghostExitRefreshKernel B (resumeSeed B F ∩ R B ((h : ℝ) - 1)))
      = walkLawUniform B := by
    unfold walkLawUniform
    rw [walkLawUniformAt_eq_bind B 0, Measure.bind_bind (measurable_of_countable _).aemeasurable
      (ghostExitRefreshKernel B _).measurable.aemeasurable]
    simp only [hκ]
  have hg : Measurable (fun X : ℕ → Site B =>
      resumeRun B (resumeInsert B F (exitSite' B (resumeSeed B F) X)) L) :=
    (measurable_of_countable (fun G => resumeRun B G L)).comp (measurable_resumeStep_output B F)
  have hfinX : ∀ᵐ X ∂(walkLawUniform B), exitTime' B (resumeSeed B F ∩ R B ((h : ℝ) - 1)) X ≠ ⊤ := by
    filter_upwards [walkLawUniform_ae_hits_level B h] with X hX
    obtain ⟨n, hn⟩ := hX
    exact exitTime'_ne_top_of_height B hS hn.ge
  have hstep : (walkLawUniform B).bind (fun X => (resumeStep B
        (exitSite' B (resumeSeed B F ∩ R B ((h : ℝ) - 1)) X) F).bind (fun G => resumeRun B G L)) =
      (walkLawUniform B).bind (fun X => (ghostExitRefreshKernel B
        (resumeSeed B F ∩ R B ((h : ℝ) - 1)) X).bind
          (fun W => resumeRun B (resumeInsert B F (exitSite' B (resumeSeed B F) W)) L)) := by
    apply Measure.bind_congr_right
    filter_upwards [hfinX] with X hX
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hX
    have hk' : exitTime' B (resumeSeed B F ∩ R B ((h : ℝ) - 1)) X = (k : ℕ∞) := hk.symm
    have hXk : X k = exitSite' B (resumeSeed B F ∩ R B ((h : ℝ) - 1)) X :=
      (exitSite'_eq_at_coe B _ X k hk').symm
    have hσ : Measurable (fun Y : ℕ → Site B => ghostSplicePath B X Y k) :=
      (measurable_ghostSplicePath B).comp
        ((measurable_const.prodMk measurable_id).prodMk measurable_const)
    rw [resumeStep, resume_bind_map _ _ _ (measurable_resumeStep_output B F)
        (measurable_of_countable _), ghostExitRefreshKernel_apply, hk', untopA_natCast,
      resume_bind_map _ _ _ hσ hg]
    apply Measure.bind_congr_right
    filter_upwards [walkPathLaw_ae_start B (exitSite' B (resumeSeed B F ∩ R B ((h : ℝ) - 1)) X),
      freezeBlock_seed_exit_ae B F (exitSite' B (resumeSeed B F ∩ R B ((h : ℝ) - 1)) X)]
      with Y hY0 hYfin
    show resumeRun B (resumeInsert B F (exitSite' B (resumeSeed B F) Y)) L =
      resumeRun B (resumeInsert B F (exitSite' B (resumeSeed B F)
        (ghostSplicePath B X Y k))) L
    rw [resumeSeed_exit_splice B _ _ hSseed X Y k hk' (by rw [hY0, hXk]) hYfin]
  have hbb : (walkLawUniform B).bind (fun X => (ghostExitRefreshKernel B
        (resumeSeed B F ∩ R B ((h : ℝ) - 1)) X).bind
          (fun W => resumeRun B (resumeInsert B F (exitSite' B (resumeSeed B F) W)) L)) =
      ((walkLawUniform B).bind (ghostExitRefreshKernel B
        (resumeSeed B F ∩ R B ((h : ℝ) - 1)))).bind
          (fun W => resumeRun B (resumeInsert B F (exitSite' B (resumeSeed B F) W)) L) :=
    (Measure.bind_bind (ghostExitRefreshKernel B _).measurable.aemeasurable
      hg.aemeasurable).symm
  have hμφ : (walkLawUniform B).bind (fun X =>
      resumeRun B (resumeInsert B F (exitSite' B (resumeSeed B F) X)) L) =
      (resumeUniformStep B F).bind (fun G => resumeRun B G L) :=
    (resume_bind_map (walkLawUniform B) (fun X => resumeInsert B F
      (exitSite' B (resumeSeed B F) X)) (fun G => resumeRun B G L)
      (measurable_resumeStep_output B F) (measurable_of_countable _)).symm
  have hf : Measurable (fun X : ℕ → Site B =>
      freezeCoupon B (F, L) (exitSite' B (resumeSeed B F ∩ R B ((h : ℝ) - 1)) X)) :=
    (measurable_of_countable (freezeCoupon B (F, L))).comp (measurable_exitSite' B _)
  unfold freezeBlockStep
  dsimp only
  rw [resume_bind_map _ _ _ hf (measurable_of_countable _)]
  simp_rw [freezeCoupon_finish]
  rw [hstep, hbb, hmu, hμφ]
  exact resumeUniformStep_commute_run B F L

/-- Completing one stopped block batch, then every resumed queue entry, gives `M` ordinary
uniform additions. No hypothesis on the heights is needed. -/
theorem blockBatch_finish (B : Base) (h : ℤ) (M : ℕ) (F : ResumeFinite B)
    (L : List (Site B)) :
    (blockBatch B h M (F, L)).bind (fun s => resumeRun B s.1 s.2) =
      (resumeRun B F L).bind (fun G => layerGrowthLaw B G 0 M) := by
  induction M generalizing F L with
  | zero =>
      simp only [blockBatch, Measure.dirac_bind (measurable_of_countable
        (fun s : ResumeState B => resumeRun B s.1 s.2)), layerGrowthLaw_zero, Measure.bind_dirac]
  | succ M ih =>
      rw [blockBatch, Measure.bind_bind (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable]
      have heq : (fun s : ResumeState B => (blockBatch B h M s).bind
          (fun t => resumeRun B t.1 t.2)) =ᵐ[freezeBlockStep B h (F, L)]
          (fun s => (resumeRun B s.1 s.2).bind (fun G => layerGrowthLaw B G 0 M)) :=
        Filter.Eventually.of_forall (fun s => ih s.1 s.2)
      rw [Measure.bind_congr_right heq,
        ← Measure.bind_bind (measurable_of_countable _).aemeasurable
          (measurable_of_countable _).aemeasurable, freezeBlockStep_finish B h F L,
        Measure.bind_bind (measurable_of_countable _).aemeasurable
          (measurable_of_countable _).aemeasurable]
      congr 1
      funext G
      rw [uniformStep_eq_layerGrowth_one, ← layerGrowthLaw_add, Nat.add_comm 1 M]

/-- A stopped block batch, completed and followed by the remaining hidden uniform starts, is
the ordinary completion with the same total count. -/
theorem blockBatch_finishUniform (B : Base) (h : ℤ) (M : ℕ) (s : ResumeState B) (r : ℕ)
    (hr : M ≤ r) :
    (blockBatch B h M s).bind (fun t => finishUniform B t (r - M)) = finishUniform B s r := by
  unfold finishUniform
  rw [← Measure.bind_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable, blockBatch_finish B h M s.1 s.2,
    Measure.bind_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
  congr 1
  funext F
  rw [← layerGrowthLaw_add, Nat.add_sub_of_le hr]

/-- Interrupted block schedules are completed without bias, for any budget covering them. -/
theorem blockPause_finishUniform (B : Base) (M H n j : ℕ) (s : ResumeState B) (r : ℕ)
    (hr : M * n ≤ r) :
    (blockPause B M H n j s r).bind (fun t => finishUniform B t.1 t.2) =
      finishUniform B s r := by
  induction n generalizing j s r with
  | zero =>
      exact Measure.dirac_bind (measurable_of_countable
        (fun t : ResumeState B × ℕ => finishUniform B t.1 t.2)) (s, r)
  | succ n ih =>
      have hbudget : M * n ≤ r - M := by
        rw [Nat.mul_succ] at hr
        omega
      have hM : M ≤ r := by
        rw [Nat.mul_succ] at hr
        omega
      unfold blockPause
      split_ifs
      · rw [Measure.bind_bind (measurable_of_countable _).aemeasurable
          (measurable_of_countable _).aemeasurable]
        have heq : (fun t : ResumeState B =>
            (blockPause B M H n (j + 1) t (r - M)).bind
              (fun u => finishUniform B u.1 u.2)) =
            (fun t => finishUniform B t (r - M)) := by
          funext t
          exact ih (j + 1) t (r - M) hbudget
        rw [heq]
        exact blockBatch_finishUniform B _ M s r hM
      · exact Measure.dirac_bind (measurable_of_countable
          (fun t : ResumeState B × ℕ => finishUniform B t.1 t.2)) (s, r)

/-- **The completed block pause is the ordinary flat-start cluster law.** The schedule of
`ℓ` block stages, each of `M` releases, with `ρ` further releases, has no bias. -/
theorem blockPause_finish (B : Base) (M H ℓ ρ : ℕ) :
    (blockPause B M H ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ)).bind
        (fun s => finishUniform B s.1 s.2) =
      flatClusterLaw B (M * ℓ + ρ) := by
  rw [blockPause_finishUniform B M H ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ) (by omega),
    finishUniform_empty]

end IdlaCyl.Reduction
