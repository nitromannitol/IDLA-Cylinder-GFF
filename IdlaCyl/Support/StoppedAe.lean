/-
Almost-sure finite exits and containments for the stopped cluster `Ā_h` under the canonical
driver `idlaMeasure` (`tex:1147-1158`).

The walks `ω t` are independent and uniformly started on layer `0` (`tex:265`).  The recurrence
input `External.LazyRwRecurrent` (`tex:600-604`) is not assumed: its proof
`External.lazyRwRecurrent_holds` is applied where the walks are first used, so the almost-sure
results below take no recurrence hypothesis.  A walk that visits every height leaves every set
contained in `R_{h-1}`, and it leaves the cluster `A(t)`, which lies in `R_0` together with finitely
many sites.  The pathwise containments of `Exit.lean` and `Stopped.lean` therefore hold on one event
of full measure, simultaneously for all times and all integer heights.
-/
import IdlaCyl.Support.Stopped
import IdlaCyl.Support.CanonicalExit
import IdlaCyl.Support.ExitIntegral
import IdlaCyl.Support.FirstHit
import IdlaCyl.External.Basic
import IdlaCyl.Support.Recurrence.Discharge

open MeasureTheory ProbabilityTheory

namespace IdlaCyl

/-- A walk drawn from `walkLawUniform B` almost surely visits height `m` (`tex:600-604`), by the
recurrence proof `External.lazyRwRecurrent_holds`. -/
theorem walkLawUniform_ae_hits_level (B : Base) (m : ℤ) :
    ∀ᵐ X ∂walkLawUniform B, ∃ n, (X n).2 = m := by
  rw [ae_iff]
  unfold walkLawUniform
  have hbad : MeasurableSet {X : ℕ → Site B | ¬ ∃ n, (X n).2 = m} :=
    (exitTraj_ae_finite_measurableSet_hits B m).compl
  rw [walkLawUniformAt_eq_bind, Measure.bind_apply hbad
    (measurable_of_countable (walkPathLaw B)).aemeasurable]
  have hzero : ∀ p : Site B, walkPathLaw B p {X : ℕ → Site B | ¬ ∃ n, (X n).2 = m} = 0 := by
    intro p
    have h := ae_exists_ver_eq External.lazyRwRecurrent_holds B p m
    rwa [ae_iff] at h
  rw [lintegral_congr hzero, lintegral_zero]

/-- The `t`-th walk of `idlaMeasure B` almost surely visits height `m`. -/
theorem idlaMeasure_ae_coord_hits_level (B : Base) (t : ℕ) (m : ℤ) :
    ∀ᵐ ω ∂idlaMeasure B, ∃ n, (ω t n).2 = m := by
  have hmap : (idlaMeasure B).map (fun ω : TrajSeq B => ω t) = walkLawUniform B :=
    Measure.infinitePi_map_eval (fun _ : ℕ => walkLawUniform B) t
  have h := walkLawUniform_ae_hits_level B m
  rw [← hmap] at h
  exact (ae_map_iff (measurable_pi_apply t).aemeasurable
    (exitTraj_ae_finite_measurableSet_hits B m)).mp h

/-- Almost surely, every walk of `idlaMeasure B` visits every integer height. -/
theorem idlaMeasure_ae_coord_hits_all (B : Base) :
    ∀ᵐ ω ∂idlaMeasure B, ∀ t : ℕ, ∀ m : ℤ, ∃ n, (ω t n).2 = m :=
  ae_all_iff.mpr fun t => ae_all_iff.mpr fun m => idlaMeasure_ae_coord_hits_level B t m

/-- A walk that reaches height `h` leaves every set contained in `R_{h-1}`, so its exit time from
that set is finite (`tex:1151`). -/
theorem exitTime'_ne_top_of_height (B : Base) {S : Set (Site B)} {h : ℤ}
    (hS : S ⊆ R B ((h : ℝ) - 1)) {X : ℕ → Site B} {n : ℕ} (hn : h ≤ (X n).2) :
    exitTime' B S X ≠ ⊤ := by
  have hmem : X n ∈ Sᶜ := fun hX => by
    have h1 : ((X n).2 : ℝ) ≤ (h : ℝ) - 1 := mem_R.mp (hS hX)
    have h2 : (h : ℝ) ≤ ((X n).2 : ℝ) := by exact_mod_cast hn
    linarith
  have hle : exitTime' B S X ≤ (n : ℕ∞) :=
    MeasureTheory.hittingAfter_le_of_mem (u := fun (k : ℕ) (Y : ℕ → Site B) => Y k)
      (s := Sᶜ) (n := 0) (i := n) (ω := X) (Nat.zero_le n) hmem
  exact ne_top_of_le_ne_top (ENat.coe_ne_top n) hle

/-- The stopped process leaves every set `Ā_h(t) ∩ R_{h-1}` in finite time, almost surely, for
every time `t` and every height `h ≥ 1` (`tex:1151`, `tex:600-604`). -/
theorem stoppedCluster_ae_exit_ne_top (B : Base) :
    ∀ᵐ ω ∂idlaMeasure B, ∀ t : ℕ, ∀ h : ℤ, 1 ≤ h →
      exitTime' B (stoppedCluster B h ω t ∩ R B ((h : ℝ) - 1)) (ω t) ≠ ⊤ := by
  filter_upwards [idlaMeasure_ae_coord_hits_all B] with ω hω
  intro t h _
  obtain ⟨n, hn⟩ := hω t h
  exact exitTime'_ne_top_of_height B (X := ω t) (n := n) Set.inter_subset_right hn.ge

/-- The IDLA cluster `A(t)` is left by the `t`-th walk in finite time, almost surely, for every `t`
(`tex:265`, `tex:696`). -/
theorem clusterTraj_ae_exit_ne_top (B : Base) :
    ∀ᵐ ω ∂idlaMeasure B, ∀ t : ℕ, exitTime' B (clusterTraj B ω t) (ω t) ≠ ⊤ := by
  filter_upwards [idlaMeasure_ae_coord_hits_all B] with ω hω t
  exact exitTraj_ae_finite_of_hits_all B ω t (hω t)

/-- Almost surely, the walk of every index starts in `R_0`: the starts are uniform on layer `0`
(`tex:265`, `tex:1147-1148`). -/
theorem idlaMeasure_ae_start_mem (B : Base) :
    ∀ᵐ ω ∂idlaMeasure B, ∀ j : ℕ, ω j 0 ∈ R B 0 := by
  have hstep : ∀ j : ℕ, ∀ᵐ ω ∂idlaMeasure B, ω j 0 ∈ R B 0 := by
    intro j
    have hmarg : ∀ᵐ X ∂walkLawUniform B, X 0 ∈ R B 0 := by
      filter_upwards [walkLawUniform_ae_ver_zero B] with X hX
      exact mem_R.mpr (by rw [hX]; norm_num)
    have hmap : (idlaMeasure B).map (fun ω : TrajSeq B => ω j) = walkLawUniform B :=
      Measure.infinitePi_map_eval (fun _ : ℕ => walkLawUniform B) j
    rw [← hmap] at hmarg
    exact ae_of_ae_map (measurable_pi_apply j).aemeasurable hmarg
  exact ae_all_iff.mpr hstep

/-- The pathwise hypotheses of the stopped-cluster lemmas hold almost surely under `idlaMeasure B`:
admissible steps, starts in `R_0`, and finite exit times of the stopped and of the uncapped
clusters. -/
theorem idlaMeasure_ae_stopped_hyp (B : Base) :
    ∀ᵐ ω ∂idlaMeasure B, (∀ j, CylAdmissible B (ω j)) ∧ (∀ j : ℕ, ω j 0 ∈ R B 0) ∧
      (∀ t : ℕ, ∀ h : ℤ, 1 ≤ h →
        exitTime' B (stoppedCluster B h ω t ∩ R B ((h : ℝ) - 1)) (ω t) ≠ ⊤) ∧
      (∀ t : ℕ, exitTime' B (clusterTraj B ω t) (ω t) ≠ ⊤) := by
  filter_upwards [idlaMeasure_ae_admissible B, idlaMeasure_ae_start_mem B,
    stoppedCluster_ae_exit_ne_top B, clusterTraj_ae_exit_ne_top B] with ω h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- `Ā_{h₁}(t) ⊆ Ā_{h₂}(t)` for all `1 ≤ h₁ ≤ h₂` and all `t`, almost surely (`tex:1155-1158`,
`eq:monotone_stop`).  One event of full measure serves every time and every pair of heights. -/
theorem stoppedCluster_ae_mono (B : Base) :
    ∀ᵐ ω ∂idlaMeasure B, ∀ t : ℕ, ∀ h₁ h₂ : ℤ, 1 ≤ h₁ → h₁ ≤ h₂ →
      stoppedCluster B h₁ ω t ⊆ stoppedCluster B h₂ ω t := by
  filter_upwards [stoppedCluster_ae_exit_ne_top B] with ω hω
  intro t h₁ h₂ hh₁ hh₁₂
  exact stoppedCluster_mono_height B hh₁₂ ω (fun s => hω s h₂ (le_trans hh₁ hh₁₂)) t

/-- `Ā_h(t) ⊆ A(t)` for all `h ≥ 1` and all `t`, almost surely (`tex:1153-1155`). -/
theorem stoppedCluster_ae_subset_clusterTraj (B : Base) :
    ∀ᵐ ω ∂idlaMeasure B, ∀ t : ℕ, ∀ h : ℤ, 1 ≤ h →
      stoppedCluster B h ω t ⊆ clusterTraj B ω t := by
  filter_upwards [clusterTraj_ae_exit_ne_top B] with ω hω
  intro t h _
  exact stoppedCluster_subset_clusterTraj B h ω hω t

/-- `Ā_h(t) ⊆ R_h` for all `h ≥ 1` and all `t`, almost surely (`tex:1154`). -/
theorem stoppedCluster_ae_subset_R (B : Base) :
    ∀ᵐ ω ∂idlaMeasure B, ∀ t : ℕ, ∀ h : ℤ, 1 ≤ h → stoppedCluster B h ω t ⊆ R B (h : ℝ) := by
  filter_upwards [idlaMeasure_ae_stopped_hyp B] with ω hω
  intro t h hh
  exact stoppedCluster_subset B h hh ω hω.1 hω.2.1 (fun s => hω.2.2.1 s h hh) t

end IdlaCyl
