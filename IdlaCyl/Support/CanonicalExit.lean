/-
The `t`-th walk of the canonical IDLA process almost surely leaves the cluster `A(t)`.

`tex:265` (the cluster recursion uses the exit site of each walk, which needs the exit time to
be finite) and `tex:697-699` (the walk reaches every height almost surely, hence leaves any
cluster contained in a half-cylinder together with finitely many further sites).
-/
import IdlaCyl.Support.Recurrence.Discharge
import IdlaCyl.Support.CanonicalMeas

namespace IdlaCyl

open MeasureTheory

/-- The event that a trajectory visits the height `m` is measurable. -/
theorem exitTraj_ae_finite_measurableSet_hits (B : Base) (m : ℤ) :
    MeasurableSet {X : ℕ → Site B | ∃ n, (X n).2 = m} := by
  have hset : {X : ℕ → Site B | ∃ n, (X n).2 = m}
      = ⋃ n : ℕ, (fun X : ℕ → Site B => (X n).2) ⁻¹' {m} := by
    ext X
    simp
  rw [hset]
  exact MeasurableSet.iUnion fun n =>
    (measurable_snd.comp (measurable_pi_apply n)) (measurableSet_singleton m)

/-- The event that a trajectory visits every height is measurable. -/
theorem exitTraj_ae_finite_measurableSet_hits_all (B : Base) :
    MeasurableSet {X : ℕ → Site B | ∀ m : ℤ, ∃ n, (X n).2 = m} := by
  have hset : {X : ℕ → Site B | ∀ m : ℤ, ∃ n, (X n).2 = m}
      = ⋂ m : ℤ, {X : ℕ → Site B | ∃ n, (X n).2 = m} := by
    ext X
    simp
  rw [hset]
  exact MeasurableSet.iInter fun m => exitTraj_ae_finite_measurableSet_hits B m

/-- A walk drawn from `walkLawUniform B` almost surely visits every height `m`. -/
theorem exitTraj_ae_finite_hits_level (B : Base) (m : ℤ) :
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

/-- A walk drawn from `walkLawUniform B` almost surely visits every height at once. -/
theorem exitTraj_ae_finite_hits_all_levels (B : Base) :
    ∀ᵐ X ∂walkLawUniform B, ∀ m : ℤ, ∃ n, (X n).2 = m :=
  ae_all_iff.mpr (exitTraj_ae_finite_hits_level B)

/-- The `t`-th trajectory of the canonical process almost surely visits every height. -/
theorem exitTraj_ae_finite_coord_hits_all_levels (B : Base) (t : ℕ) :
    ∀ᵐ ω ∂idlaMeasure B, ∀ m : ℤ, ∃ n, ((ω t) n).2 = m := by
  have hmap : (idlaMeasure B).map (fun ω : TrajSeq B => ω t) = walkLawUniform B :=
    Measure.infinitePi_map_eval (fun _ : ℕ => walkLawUniform B) t
  have h := exitTraj_ae_finite_hits_all_levels B
  rw [← hmap] at h
  exact (ae_map_iff (measurable_pi_apply t).aemeasurable
    (exitTraj_ae_finite_measurableSet_hits_all B)).mp h

/-- A trajectory that visits every height leaves the cluster `A(t)`: the cluster is contained
in the half-cylinder `R_0` together with the finitely many sites `settleSite B ω j`, `j < t`,
and the trajectory visits a height above all of them. -/
theorem exitTraj_ae_finite_of_hits_all (B : Base) (ω : TrajSeq B) (t : ℕ) {X : ℕ → Site B}
    (hX : ∀ m : ℤ, ∃ n, (X n).2 = m) : exitTime' B (clusterTraj B ω t) X ≠ ⊤ := by
  set m : ℤ := 1 + ∑ j ∈ Finset.range t, |(settleSite B ω j).2| with hm
  have hsum : 0 ≤ ∑ j ∈ Finset.range t, |(settleSite B ω j).2| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  obtain ⟨n, hn⟩ := hX m
  have hnot : X n ∉ clusterTraj B ω t := by
    rw [clusterTraj_eq_union]
    simp only [Set.mem_union, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio,
      not_or, not_exists, not_and]
    refine ⟨?_, fun j hj hjX => ?_⟩
    · intro hR
      have : ((X n).2 : ℝ) ≤ 0 := hR
      have h2 : (X n).2 ≤ 0 := by exact_mod_cast this
      omega
    · have hle : |(settleSite B ω j).2| ≤ ∑ i ∈ Finset.range t, |(settleSite B ω i).2| :=
        Finset.single_le_sum (f := fun i => |(settleSite B ω i).2|)
          (fun i _ => abs_nonneg _) (Finset.mem_range.mpr hj)
      have h1 : (X n).2 = (settleSite B ω j).2 := by rw [hjX]
      have h2 := le_abs_self (settleSite B ω j).2
      omega
  intro htop
  have hall := (MeasureTheory.hittingAfter_eq_top_iff.mp htop) n (Nat.zero_le n)
  exact hall hnot

/-- **The `t`-th walk leaves the cluster `A(t)` almost surely** (`tex:265`, `tex:697-699`). -/
theorem exitTraj_ae_finite (B : Base) (t : ℕ) :
    ∀ᵐ ω ∂idlaMeasure B, exitTime' B (clusterTraj B ω t) (ω t) ≠ ⊤ := by
  filter_upwards [exitTraj_ae_finite_coord_hits_all_levels B t] with ω hω
  exact exitTraj_ae_finite_of_hits_all B ω t hω

end IdlaCyl
