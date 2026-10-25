module

/-
Stationary layer entrance, with almost-sure finiteness and independent coupons.
Source: paper/idla-cylinder-gff.tex, tex:246-265,595-610,1440-1453.
The recurrence premise of the first-hit theorem is discharged here.
-/
public import IdlaCyl.Support.Reduction.Laws
public import IdlaCyl.Support.Recurrence.Discharge
public import IdlaCyl.Support.ExitIntegral

@[expose] public section

namespace IdlaCyl.Reduction

open MeasureTheory ProbabilityTheory

/-- A stationary release first enters every fixed layer with the uniform law.
This includes the requested h≤L case and the time-zero case h=L. -/
theorem stationary_entrance (B : Base) (h L : ℤ) :
    (walkLawUniformAt B h).map (firstHitSite B L) = layerLawAt B L :=
  unif_first_hit B h L External.lazyRwRecurrent_holds

/-- All entrance coupons from independently released walks are independent uniform sites. -/
theorem entrance_sequence_law (B : Base) (h L : ℤ) :
    (layerDrivingLaw B h).map
        (fun ω : TrajSeq B => fun i => firstHitSite B L (ω i)) =
      Measure.infinitePi (fun _ : ℕ => layerLawAt B L) := by
  unfold layerDrivingLaw
  rw [Measure.infinitePi_map_pi (μ := fun _ : ℕ => walkLawUniformAt B h)
    (f := fun _ : ℕ => firstHitSite B L) (fun _ => measurable_firstHitSite B L)]
  simp_rw [stationary_entrance]

/-- Every height is reached almost surely under any stationary-layer release. -/
theorem layerWalk_ae_hits (B : Base) (h j : ℤ) :
    ∀ᵐ X ∂walkLawUniformAt B h, ∃ n, (X n).2 = j := by
  rw [walkLawUniformAt_eq_bind, ae_iff]
  have hbad : MeasurableSet {X : ℕ → Site B | ¬ ∃ n, (X n).2 = j} :=
    (exitTraj_ae_finite_measurableSet_hits B j).compl
  rw [Measure.bind_apply hbad (measurable_of_countable (walkPathLaw B)).aemeasurable]
  have hzero : ∀ p : Site B, walkPathLaw B p {X | ¬ ∃ n, (X n).2 = j} = 0 := by
    intro p
    exact ae_iff.mp (ae_exists_ver_eq External.lazyRwRecurrent_holds B p j)
  rw [lintegral_congr hzero, lintegral_zero]

/-- Hitting times are finite before any first-hit location is consumed. -/
theorem layerWalk_ae_hit_finite (B : Base) (h j : ℤ) :
    ∀ᵐ X ∂walkLawUniformAt B h, hitLevel B j X ≠ ⊤ := by
  filter_upwards [layerWalk_ae_hits B h j] with X hX
  intro htop
  obtain ⟨n, hn⟩ := hX
  exact (hitLevel_eq_top_iff B j X).mp htop n hn

/-- Uniform-layer trajectories really start on the indicated layer. -/
theorem layerWalk_ae_start (B : Base) (h : ℤ) :
    ∀ᵐ X ∂walkLawUniformAt B h, (X 0).2 = h := by
  rw [walkLawUniformAt_eq_bind, ae_iff]
  have hs : MeasurableSet {X : ℕ → Site B | (X 0).2 ≠ h} :=
    ((measurable_pi_apply 0).snd (measurableSet_singleton h)).compl
  rw [Measure.bind_apply hs (measurable_of_countable (walkPathLaw B)).aemeasurable]
  have hzero : (fun p : Site B => walkPathLaw B p {X | (X 0).2 ≠ h}) =ᵐ[
      layerLawAt B h] (fun _ => 0) := by
    filter_upwards [layerLawAt_ae_ver B h] with p hp
    refine measure_mono_null ?_ (walkPathLaw_ae_zero B p)
    intro X hX hXp
    exact hX (by rw [hXp]; exact hp)
  rw [lintegral_congr_ae hzero, lintegral_zero]

/-- Every released walk simultaneously has its canonical support and reaches every level. -/
theorem layerDriving_ae_good (B : Base) (h : ℤ) :
    ∀ᵐ ω ∂layerDrivingLaw B h, ∀ i,
      CylAdmissible B (ω i) ∧ (ω i 0).2 = h ∧
        ∀ j : ℤ, ∃ n, (ω i n).2 = j := by
  apply ae_all_iff.mpr
  intro i
  have hcoord : (layerDrivingLaw B h).map (fun ω : TrajSeq B => ω i) =
      walkLawUniformAt B h :=
    Measure.infinitePi_map_eval (fun _ : ℕ => walkLawUniformAt B h) i
  have hwalk : ∀ᵐ X ∂walkLawUniformAt B h,
      CylAdmissible B X ∧ (X 0).2 = h ∧ ∀ j : ℤ, ∃ n, (X n).2 = j := by
    filter_upwards [walkLawUniformAt_ae_admissible B h, layerWalk_ae_start B h,
      ae_all_iff.mpr (layerWalk_ae_hits B h)] with X ha hs hh
    exact ⟨ha, hs, hh⟩
  rw [← hcoord] at hwalk
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hwalk

end IdlaCyl.Reduction
