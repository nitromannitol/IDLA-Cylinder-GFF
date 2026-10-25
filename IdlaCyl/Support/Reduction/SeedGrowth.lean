module

/-
Connectedness of the seeds used by the reduction.

The reduction applies Silvestri's Proposition 2, which concerns IDLA from a connected initial set
(`IdlaCyl/Support/CylGraph.lean`), to two kinds of seed: exact half-cylinders, which are
connected, and seeds grown by IDLA from a connected seed with walkers started inside it. This
file proves that translation keeps a seed connected, that the exit site of an admissible walk
started in a seed is adjacent to that seed, and that growth from a connected seed containing the
starting layer stays connected almost surely (`layerGrowthLaw_not_seedConnected`).
-/
public import IdlaCyl.Support.CylGraph
public import IdlaCyl.Support.Admissible
public import IdlaCyl.Support.CanonicalIdla
public import IdlaCyl.Support.Outer.ResumeGrowth
public import IdlaCyl.Support.Reduction.Laws
public import IdlaCyl.Support.Reduction.ShiftFinite
public import IdlaCyl.Support.Silvestri.TimeShift

@[expose] public section

namespace IdlaCyl

open MeasureTheory

/-- Translating a connected finite extension by `L` layers, in the form used by
`Reduction.shiftFinite`, gives a connected seed (`Reduction.resumeSeed_shiftFinite`). -/
theorem seedConnected_resumeSeed_shiftFinite (B : Base) (L : ℕ) (F : ResumeFinite B)
    (hF : SeedConnected B (resumeSeed B F)) :
    SeedConnected B (resumeSeed B (Reduction.shiftFinite B L F)) := by
  rw [Reduction.resumeSeed_shiftFinite]
  have hfun : ⇑(outerShift B (L : ℤ)) = vshift B (L : ℤ) := by
    funext p
    rfl
  rw [hfun]
  exact seedConnected_image_vshift (L : ℤ) hF

/-- Connectedness transfers back along a vertical translation of the cylinder. -/
theorem seedConnected_of_image_outerShift (B : Base) (L : ℤ) {S : Set (Site B)}
    (h : SeedConnected B (outerShift B L '' S)) : SeedConnected B S := by
  have hS : vshift B (-L) '' (outerShift B L '' S) = S := by
    rw [Set.image_image]
    have hid : (fun p => vshift B (-L) (outerShift B L p)) = id := by
      funext p
      change (p.1, p.2 + L + -L) = p
      simp
    rw [hid, Set.image_id]
  rw [← hS]
  exact seedConnected_image_vshift (-L) h

/-- If an admissible walk starts in a seed and leaves it at a finite time, its exit site is
adjacent in the cylinder graph to a site of the seed (`tex:1412-1425`). -/
theorem exitSite'_adj {B : Base} {S : Set (Site B)} {X : ℕ → Site B} (hS0 : X 0 ∈ S)
    (hadm : CylAdmissible B X) (hfin : exitTime' B S X ≠ ⊤) :
    ∃ q ∈ S, (cylGraph B).Adj q (exitSite' B S X) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, exitTime' B S X = n := ⟨_, (ENat.coe_toNat hfin).symm⟩
  have hexit : exitSite' B S X = X n := by
    rw [exitSite'_eq_apply_toNat B S hfin, hn]
    simp
  obtain ⟨hout, hin⟩ := (exitTime'_eq_coe_iff B S X n).mp hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hout hS0
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hqS : X m ∈ S := hin m (Nat.lt_succ_self m)
  refine ⟨X m, hqS, ?_⟩
  rw [hexit]
  exact cylGraph_adj_of_cylKernel_pos (hadm m) (fun heq => hout (heq ▸ hqS))

/-- A walk drawn from `walkLawUniformAt B k` almost surely visits height `m`. -/
theorem walkLawUniformAt_ae_hits (B : Base) (k m : ℤ) :
    ∀ᵐ X ∂walkLawUniformAt B k, ∃ n, (X n).2 = m := by
  rw [ae_iff, walkLawUniformAt_eq_bind]
  have hmeas : MeasurableSet (⋃ n : ℕ, (fun X : ℕ → Site B => (X n).2) ⁻¹' {m}) :=
    MeasurableSet.iUnion fun n =>
      (measurableSet_singleton m).preimage (measurable_snd.comp (measurable_pi_apply n))
  have hset : (⋃ n : ℕ, (fun X : ℕ → Site B => (X n).2) ⁻¹' {m})
      = {X : ℕ → Site B | ∃ n, (X n).2 = m} := by
    ext X
    simp
  rw [hset] at hmeas
  have hbad : MeasurableSet {X : ℕ → Site B | ¬ ∃ n, (X n).2 = m} := hmeas.compl
  rw [Measure.bind_apply hbad (measurable_of_countable (walkPathLaw B)).aemeasurable]
  have hzero : ∀ p : Site B, walkPathLaw B p {X : ℕ → Site B | ¬ ∃ n, (X n).2 = m} = 0 := by
    intro p
    have h := ae_exists_ver_eq External.lazyRwRecurrent_holds B p m
    rwa [ae_iff] at h
  rw [lintegral_congr hzero, lintegral_zero]

/-- Layer `k` of the cylinder carries the uniform start: `layerLawAt B k` is concentrated on
sites of height `k`. -/
theorem layerLawAt_ae_height (B : Base) (k : ℤ) : ∀ᵐ p ∂layerLawAt B k, p.2 = k := by
  unfold layerLawAt
  rw [Measure.ae_sum_iff]
  intro x
  have hm : MeasurableSet {q : Site B | q.2 = k} :=
    (measurableSet_singleton k).preimage measurable_snd
  exact Measure.ae_smul_measure ((ae_dirac_iff (a := ((x, k) : Site B)) hm).mpr rfl) _

/-- A walk drawn from `walkLawUniformAt B k` starts at height `k` almost surely. -/
theorem walkLawUniformAt_ae_start (B : Base) (k : ℤ) :
    ∀ᵐ X ∂walkLawUniformAt B k, (X 0).2 = k := by
  rw [ae_iff, walkLawUniformAt_eq_bind]
  have hmeas : MeasurableSet {X : ℕ → Site B | (X 0).2 = k} :=
    (measurableSet_singleton k).preimage (measurable_snd.comp (measurable_pi_apply 0))
  have hbad : MeasurableSet {X : ℕ → Site B | ¬ (X 0).2 = k} := hmeas.compl
  rw [Measure.bind_apply hbad (measurable_of_countable (walkPathLaw B)).aemeasurable]
  have hzero : ∀ p : Site B, p.2 = k →
      walkPathLaw B p {X : ℕ → Site B | ¬ (X 0).2 = k} = 0 := by
    intro p hp
    refine ae_iff.mp ?_
    filter_upwards [walkPathLaw_ae_start B p] with X hX
    rw [hX]
    exact hp
  rw [lintegral_congr_ae ((layerLawAt_ae_height B k).mono fun p hp => hzero p hp), lintegral_zero]

/-- Almost surely every walker of the layer driving law is admissible, starts on layer `h`,
and visits every height. -/
theorem layerDrivingLaw_ae_walks (B : Base) (h : ℤ) :
    ∀ᵐ ω ∂ Reduction.layerDrivingLaw B h, ∀ j : ℕ,
      CylAdmissible B (ω j) ∧ (ω j 0).2 = h ∧ ∀ k : ℤ, ∃ n, (ω j n).2 = k := by
  have hstep : ∀ j : ℕ, ∀ᵐ ω ∂ Reduction.layerDrivingLaw B h,
      CylAdmissible B (ω j) ∧ (ω j 0).2 = h ∧ ∀ k : ℤ, ∃ n, (ω j n).2 = k := by
    intro j
    have hmarg : ∀ᵐ X ∂walkLawUniformAt B h,
        CylAdmissible B X ∧ (X 0).2 = h ∧ ∀ k : ℤ, ∃ n, (X n).2 = k := by
      filter_upwards [walkLawUniformAt_ae_admissible B h, walkLawUniformAt_ae_start B h,
        ae_all_iff.mpr (walkLawUniformAt_ae_hits B h)] with X h1 h2 h3
      exact ⟨h1, h2, h3⟩
    have heval : (Reduction.layerDrivingLaw B h).map (fun ω : TrajSeq B => ω j)
        = walkLawUniformAt B h :=
      Measure.infinitePi_map_eval (fun _ : ℕ => walkLawUniformAt B h) j
    rw [← heval] at hmarg
    exact ae_of_ae_map (measurable_pi_apply j).aemeasurable hmarg
  exact ae_all_iff.mpr hstep

/-- Growth only adds sites, so the seed of every finite extension contains `F`'s seed. -/
theorem resumeSeed_subset_resumeGrow (B : Base) (F : ResumeFinite B) (ω : TrajSeq B) (n : ℕ) :
    resumeSeed B F ⊆ resumeSeed B (resumeGrow B F ω n) := by
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih =>
      rw [resumeGrow, resumeSeed_insert]
      exact ih.trans Set.subset_union_left

/-- If the seed is connected and contains the layer-`h` half-cylinder, then for almost every
driving sequence, every stage of the growth from the seed stays connected.  The walker
of stage `n` starts on layer `h`, which lies in the seed, and exits in finite time because
the seed is bounded above while the walker reaches every height; the exit site is then
adjacent to the seed (`exitSite'_adj`) and is inserted by `SeedConnected.insert_of_adj`. -/
theorem seedConnected_resumeGrow_ae (B : Base) (F : ResumeFinite B) (h : ℤ)
    (hF : SeedConnected B (resumeSeed B F)) (hR : R B (h : ℝ) ⊆ resumeSeed B F) :
    ∀ᵐ ω ∂ Reduction.layerDrivingLaw B h, ∀ n : ℕ,
      SeedConnected B (resumeSeed B (resumeGrow B F ω n)) := by
  filter_upwards [layerDrivingLaw_ae_walks B h] with ω hω
  intro n
  induction n with
  | zero => exact hF
  | succ n ih =>
      have hS0 : ω n 0 ∈ resumeSeed B (resumeGrow B F ω n) := by
        refine resumeSeed_subset_resumeGrow B F ω n (hR ?_)
        exact mem_R.mpr (le_of_eq (congrArg (fun z : ℤ => (z : ℝ)) (hω n).2.1))
      have hfin : exitTime' B (resumeSeed B (resumeGrow B F ω n)) (ω n) ≠ ⊤ := by
        obtain ⟨M, hM⟩ := Silvestri.resumeSeed_subset_bounded B (resumeGrow B F ω n)
        obtain ⟨m, hm⟩ := (hω n).2.2 (M + 1)
        exact Silvestri.exitTime'_ne_top_of_unbounded B hM ⟨m, by rw [hm]; omega⟩
      obtain ⟨q, hq, hadj⟩ := exitSite'_adj hS0 (hω n).1 hfin
      rw [resumeGrow, resumeSeed_insert]
      exact ih.insert_of_adj hq hadj

/-- Corollary: the law of the finite extension after `n` growth stages gives no mass to
disconnected seeds. -/
theorem layerGrowthLaw_not_seedConnected (B : Base) (F : ResumeFinite B) (h : ℤ)
    (hF : SeedConnected B (resumeSeed B F)) (hR : R B (h : ℝ) ⊆ resumeSeed B F) (n : ℕ) :
    Reduction.layerGrowthLaw B F h n {c | ¬ SeedConnected B (resumeSeed B c)} = 0 := by
  unfold Reduction.layerGrowthLaw
  have hmeas : MeasurableSet {c : ResumeFinite B | ¬ SeedConnected B (resumeSeed B c)} :=
    (Set.to_countable _).measurableSet
  rw [Measure.map_apply (measurable_resumeGrow B F n) hmeas]
  refine ae_iff.mp ?_
  filter_upwards [seedConnected_resumeGrow_ae B F h hF hR] with ω hω
  exact hω n

end IdlaCyl
