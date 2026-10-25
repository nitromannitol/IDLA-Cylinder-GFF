module

public import IdlaCyl.Support.Idla
public import LatticeProb.Prob.InfinitePiSplit
public import IdlaCyl.Support.Recurrence.BoundedHarmonic

@[expose] public section

/-!
Almost-sure finite exit for the driven IDLA process (`tex:229-265`, `tex:338-340`).

The cluster height bound holds for every driver, including trajectories that never
exit. The vertical coordinate reaches each upper level almost surely under the
actual walk-driver law, by its lazy increment law and the bounded harmonic
half-line argument. Projection to the current particle then gives finite exit.
-/

namespace IdlaCyl.Obligation.ExitAeFinite
open MeasureTheory Filter
open scoped ENNReal

theorem step_height_le (B : Base) (p : Site B) (u : ℝ × ℝ) :
    (cylStep B p u).2 ≤ p.2 + 1 := by
  unfold cylStep
  split_ifs <;> omega

theorem first_exit (B : Base) (S : Set (Site B)) (X : ℕ → Site B)
    (h : ∃ n, X n ∉ S) :
    ∃ n : ℕ, exitTime B S X = n ∧ X n ∉ S ∧ ∀ k < n, X k ∈ S := by
  classical
  let n := Nat.find h
  have hn : X n ∉ S := Nat.find_spec h
  refine ⟨n, le_antisymm ?_ ?_, hn, ?_⟩
  · exact sInf_le ⟨n, rfl, hn⟩
  · refine le_sInf ?_
    rintro a ⟨k, rfl, hk⟩
    exact_mod_cast Nat.find_min' h hk
  · intro k hk
    exact not_not.mp (Nat.find_min h hk)

theorem exit_finite_iff (B : Base) (S : Set (Site B)) (X : ℕ → Site B) :
    exitTime B S X ≠ ⊤ ↔ ∃ n, X n ∉ S := by
  classical
  constructor
  · contrapose!
    intro h
    have he : {a : ℕ∞ | ∃ n : ℕ, a = n ∧ X n ∉ S} = ∅ := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨n, _, hn⟩
      exact hn (h n)
    simp only [exitTime, he, sInf_empty]
  · rintro ⟨n, hn⟩ he
    have hb : exitTime B S X ≤ (n : ℕ∞) := sInf_le ⟨n, rfl, hn⟩
    rw [he] at hb
    exact (ENat.coe_ne_top n) (top_le_iff.mp hb)

theorem exitSite_outside (B : Base) (S : Set (Site B)) (d : StepDriver)
    (h : exitTime B S (stepWalk B d) ≠ ⊤) : exitSite B S d ∉ S := by
  obtain ⟨n, he, hn, _⟩ := first_exit B S (stepWalk B d) ((exit_finite_iff B S _).mp h)
  simpa only [exitSite, he, ENat.toNat_coe] using hn

theorem exitSite_height_le (B : Base) (S : Set (Site B)) (d : StepDriver)
    (t : ℕ) (hS : S ⊆ R B t) : (exitSite B S d).2 ≤ (t : ℤ) + 1 := by
  classical
  by_cases h : ∃ n, stepWalk B d n ∉ S
  · obtain ⟨n, he, _, hprev⟩ := first_exit B S (stepWalk B d) h
    change (stepWalk B d (exitTime B S (stepWalk B d)).toNat).2 ≤ _
    rw [he, ENat.toNat_coe]
    cases n with
    | zero => simp only [stepWalk, cylPath_zero]; omega
    | succ k =>
      have hp : (stepWalk B d k).2 ≤ (t : ℤ) := by
        have hr := hS (hprev k (Nat.lt_succ_self k))
        change ((stepWalk B d k).2 : ℝ) ≤ (t : ℝ) at hr
        exact_mod_cast hr
      exact (step_height_le B (stepWalk B d k) (d.2 k)).trans (by omega)
  · have he := (not_iff_not.mpr (exit_finite_iff B S (stepWalk B d))).mpr h
    have ht : exitTime B S (stepWalk B d) = ⊤ := not_not.mp he
    unfold exitSite
    rw [ht]
    change (0 : ℤ) ≤ (t : ℤ) + 1
    omega

theorem cluster_height (B : Base) (ω : Driver) (t : ℕ) : cluster B ω t ⊆ R B t := by
  induction t with
  | zero => simpa only [cluster_zero, Nat.cast_zero] using (Set.Subset.refl (R B 0))
  | succ t ih =>
    rw [cluster_succ]
    rintro p (hp | hp)
    · exact R_mono (by exact_mod_cast Nat.le_succ t) (ih hp)
    · have he : p = exitSite B (cluster B ω t) (ω t) := Set.mem_singleton_iff.mp hp
      rw [he]
      have hh := exitSite_height_le B (cluster B ω t) (ω t) t ih
      change ((exitSite B (cluster B ω t) (ω t)).2 : ℝ) ≤ ((t + 1 : ℕ) : ℝ)
      exact_mod_cast hh

theorem finite_of_upper_hit (B : Base) (ω : Driver) (t : ℕ)
    (h : ∃ n, (t : ℤ) < (stepWalk B (ω t) n).2) :
    exitTime B (cluster B ω t) (stepWalk B (ω t)) ≠ ⊤ := by
  apply (exit_finite_iff B _ _).mpr
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  intro hm
  have hh := cluster_height B ω t hm
  change ((stepWalk B (ω t) n).2 : ℝ) ≤ (t : ℝ) at hh
  have hh' : (stepWalk B (ω t) n).2 ≤ (t : ℤ) := by exact_mod_cast hh
  exact (not_lt_of_ge hh') hn

end IdlaCyl.Obligation.ExitAeFinite

namespace IdlaCyl.Obligation.ExitAeFinite
open MeasureTheory Filter
open scoped ENNReal

local instance uniform_probability : IsProbabilityMeasure stepLaw := by
  constructor
  norm_num [stepLaw, Measure.restrict_apply_univ]
local instance walk_probability : IsProbabilityMeasure walkDriverLaw := by
  unfold walkDriverLaw
  infer_instance
local instance step_probability : IsProbabilityMeasure stepDriverLaw := by
  unfold stepDriverLaw
  infer_instance
local instance driver_probability : IsProbabilityMeasure driverLaw := by
  unfold driverLaw
  infer_instance

noncomputable def inc (u : ℝ × ℝ) : ℤ :=
  if u.1 < 1/2 then (if u.2 < 1/2 then -1 else 1) else 0

theorem measurable_inc : Measurable inc := by
  unfold inc
  exact Measurable.ite (measurableSet_lt measurable_fst measurable_const)
    (Measurable.ite (measurableSet_lt measurable_snd measurable_const)
      measurable_const measurable_const) measurable_const

theorem inc_law : (stepLaw.prod stepLaw).map inc =
    (1/4 : ℝ≥0∞) • Measure.dirac (-1 : ℤ) +
      (1/4 : ℝ≥0∞) • Measure.dirac (1 : ℤ) +
      (1/2 : ℝ≥0∞) • Measure.dirac (0 : ℤ) := by
  have atom (z : ℤ) (a b c d : ℝ)
      (he : (inc ⁻¹' {z}) ∩ (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1)
        = Set.Ico a b ×ˢ Set.Ico c d) :
      ((stepLaw.prod stepLaw).map inc) {z} =
        ENNReal.ofReal (b-a) * ENNReal.ofReal (d-c) := by
    rw [Measure.map_apply measurable_inc (measurableSet_singleton z),
      stepLaw, Measure.prod_restrict, Measure.restrict_apply
        (measurable_inc (measurableSet_singleton z)), he, Measure.prod_prod]
    simp only [Real.volume_Ico]
  apply Measure.ext_of_singleton
  intro z
  by_cases hd : z = -1
  · subst z
    have h := atom (-1) 0 (1/2) 0 (1/2) (by
      ext ⟨r,s⟩
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_prod, Set.mem_Ico]
      unfold inc
      split_ifs with hr hs
      · constructor
        · rintro ⟨_, ⟨hr0,_⟩, ⟨hs0,_⟩⟩
          exact ⟨⟨hr0,hr⟩,⟨hs0,hs⟩⟩
        · rintro ⟨⟨hr0,_⟩,⟨hs0,_⟩⟩
          exact ⟨rfl,⟨hr0,by linarith⟩,⟨hs0,by linarith⟩⟩
      · constructor
        · rintro ⟨h,_,_⟩; norm_num at h
        · rintro ⟨⟨_,_⟩,⟨_,hs'⟩⟩
          exact False.elim (hs hs')
      · constructor
        · rintro ⟨h,_,_⟩; norm_num at h
        · rintro ⟨⟨_,hr'⟩,_⟩
          exact False.elim (hr hr'))
    rw [← ENNReal.ofReal_mul (by norm_num)] at h
    norm_num [ENNReal.ofReal_div_of_pos] at h ⊢
    exact h
  by_cases hu : z = 1
  · subst z
    have h := atom 1 0 (1/2) (1/2) 1 (by
      ext ⟨r,s⟩
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_prod, Set.mem_Ico]
      unfold inc
      split_ifs with hr hs
      · constructor
        · rintro ⟨h,_,_⟩; norm_num at h
        · rintro ⟨_,⟨hs',_⟩⟩
          exact False.elim ((not_le_of_gt hs) hs')
      · constructor
        · rintro ⟨_,⟨hr0,_⟩,⟨_,hs1⟩⟩
          exact ⟨⟨hr0,hr⟩,⟨le_of_not_gt hs,hs1⟩⟩
        · rintro ⟨⟨hr0,_⟩,⟨hs0,hs1⟩⟩
          exact ⟨rfl,⟨hr0,by linarith⟩,⟨by linarith,hs1⟩⟩
      · constructor
        · rintro ⟨h,_,_⟩; norm_num at h
        · rintro ⟨⟨_,hr'⟩,_⟩
          exact False.elim (hr hr'))
    rw [← ENNReal.ofReal_mul (by norm_num)] at h
    norm_num [ENNReal.ofReal_div_of_pos] at h ⊢
    exact h
  by_cases hz : z = 0
  · subst z
    have h := atom 0 (1/2) 1 0 1 (by
      ext ⟨r,s⟩
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_prod, Set.mem_Ico]
      unfold inc
      split_ifs with hr hs
      · constructor
        · rintro ⟨h,_,_⟩; norm_num at h
        · rintro ⟨⟨hr',_⟩,_⟩
          exact False.elim ((not_le_of_gt hr) hr')
      · constructor
        · rintro ⟨h,_,_⟩; norm_num at h
        · rintro ⟨⟨hr',_⟩,_⟩
          exact False.elim ((not_le_of_gt hr) hr')
      · constructor
        · rintro ⟨_,⟨_,hr1⟩,hs⟩
          exact ⟨⟨le_of_not_gt hr,hr1⟩,hs⟩
        · rintro ⟨⟨hr0,hr1⟩,hs⟩
          exact ⟨rfl,⟨by linarith,hr1⟩,hs⟩)
    norm_num [ENNReal.ofReal_div_of_pos] at h ⊢
    exact h
  · have he : (inc ⁻¹' {z}) ∩ (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) = ∅ := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      unfold inc
      split_ifs with hr hs
      · intro h; exact False.elim (hd h.symm)
      · intro h; exact False.elim (hu h.symm)
      · intro h; exact False.elim (hz h.symm)
    rw [Measure.map_apply measurable_inc (measurableSet_singleton z), stepLaw,
      Measure.prod_restrict, Measure.restrict_apply (measurable_inc (measurableSet_singleton z)),
      he, measure_empty]
    simp [hd,hu,hz]

noncomputable def verticalPath (y : ℤ) (w : WalkDriver) : ℕ → ℤ
  | 0 => y
  | n+1 => verticalPath y w n + inc (w n)

theorem actual_vertical (B : Base) (p : Site B) (w : WalkDriver) (n : ℕ) :
    (cylPath B p w n).2 = verticalPath p.2 w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (cylStep B (cylPath B p w n) (w n)).2 = verticalPath p.2 w n + inc (w n)
    unfold cylStep inc
    split_ifs <;> rw [ih] <;> omega

theorem measurable_vertical (y : ℤ) (n : ℕ) :
    Measurable (fun w : WalkDriver => verticalPath y w n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact ih.add (measurable_inc.comp (measurable_pi_apply n))

theorem vertical_restart (y : ℤ) (u : ℝ × ℝ) (w : WalkDriver) (n : ℕ) :
    verticalPath y (LatticeProb.consNat u w) (n+1) = verticalPath (y+inc u) w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change verticalPath y (LatticeProb.consNat u w) (n+1) + inc (w n) = _
    rw [ih]
    rfl

noncomputable def never (k y : ℤ) : Set WalkDriver := {w | ∀ n, verticalPath y w n < k}

theorem measurable_never (k y : ℤ) : MeasurableSet (never k y) := by
  have he : never k y = ⋂ n : ℕ, (fun w : WalkDriver => verticalPath y w n) ⁻¹' Set.Iio k := by
    ext w
    simp only [never, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Iio]
  rw [he]
  exact MeasurableSet.iInter fun n => (measurable_vertical y n) measurableSet_Iio

theorem never_first_step (k y : ℤ) (hy : y < k) :
    walkDriverLaw (never k y) =
      (1/4 : ℝ≥0∞) * walkDriverLaw (never k (y-1)) +
      (1/4 : ℝ≥0∞) * walkDriverLaw (never k (y+1)) +
      (1/2 : ℝ≥0∞) * walkDriverLaw (never k y) := by
  have he : (fun q : (ℝ × ℝ) × WalkDriver => LatticeProb.consNat q.1 q.2) ⁻¹' never k y
      = {q | q.2 ∈ never k (y + inc q.1)} := by
    ext ⟨u,w⟩
    change (∀ n, verticalPath y (LatticeProb.consNat u w) n < k) ↔
      ∀ n, verticalPath (y + inc u) w n < k
    constructor
    · intro h n; rw [← vertical_restart]; exact h (n+1)
    · intro h n; cases n with
      | zero => exact hy
      | succ n => rw [vertical_restart]; exact h n
  have hm := LatticeProb.map_consNat (stepLaw.prod stepLaw)
  change ((stepLaw.prod stepLaw).prod walkDriverLaw).map
    (fun q : (ℝ × ℝ) × WalkDriver => LatticeProb.consNat q.1 q.2) = walkDriverLaw at hm
  conv_lhs => rw [← hm]
  rw [Measure.map_apply LatticeProb.measurable_consNat (measurable_never k y),
    Measure.prod_apply (LatticeProb.measurable_consNat (measurable_never k y)), he]
  change (∫⁻ u, walkDriverLaw (never k (y+inc u)) ∂(stepLaw.prod stepLaw)) = _
  rw [← lintegral_map (measurable_of_countable (fun z : ℤ => walkDriverLaw (never k (y+z))))
      measurable_inc, inc_law]
  simp only [lintegral_add_measure, lintegral_smul_measure, lintegral_dirac,
    smul_eq_mul, add_zero]
  have hsub : y + -1 = y - 1 := by omega
  rw [hsub]

theorem vertical_reaches (y k : ℤ) :
    ∀ᵐ w ∂walkDriverLaw, ∃ n, k ≤ verticalPath y w n := by
  let g : ℤ → ℝ := fun y => (walkDriverLaw (never k y)).toReal
  have hzero (y : ℤ) (hy : k ≤ y) : walkDriverLaw (never k y) = 0 := by
    have he : never k y = ∅ := by
      ext w
      simp only [never, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have hh := h 0
      change y < k at hh
      omega
    rw [he, measure_empty]
  have hk : g k = 0 := by simp only [g, hzero k le_rfl, ENNReal.toReal_zero]
  have hb : ∀ y ≤ k, 0 ≤ g y ∧ g y ≤ 1 := by
    intro y _
    exact ⟨ENNReal.toReal_nonneg, by
      simpa only [g, ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
        (show walkDriverLaw (never k y) ≤ 1 from prob_le_one)⟩
  have hh : ∀ y < k, 2 * g y = g (y+1) + g (y-1) := by
    intro y hy
    have h := congrArg ENNReal.toReal (never_first_step k y hy)
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_add (by finiteness) (by finiteness)] at h
    simp only [ENNReal.toReal_mul] at h
    norm_num at h
    dsimp only [g]
    linarith
  have hz : walkDriverLaw (never k y) = 0 := by
    by_cases hy : k ≤ y
    · exact hzero y hy
    · have hg := Recurrence.bounded_harmonic_halfline g k hk hb hh y (by omega)
      exact (ENNReal.toReal_eq_zero_iff _).mp hg |>.resolve_right (measure_ne_top _ _)
  rw [ae_iff]
  have he : {w : WalkDriver | ¬ ∃ n, k ≤ verticalPath y w n} = never k y := by
    ext w
    simp only [never, Set.mem_setOf_eq, not_exists, not_le]
  rw [he]
  exact hz

end IdlaCyl.Obligation.ExitAeFinite

namespace IdlaCyl.Obligation
open MeasureTheory Filter
open scoped ENNReal
local instance uniform_probability : IsProbabilityMeasure stepLaw := by
  constructor
  norm_num [stepLaw, Measure.restrict_apply_univ]
local instance walk_probability : IsProbabilityMeasure walkDriverLaw := by
  unfold walkDriverLaw
  infer_instance
local instance step_probability : IsProbabilityMeasure stepDriverLaw := by
  unfold stepDriverLaw
  infer_instance
local instance driver_probability : IsProbabilityMeasure driverLaw := by
  unfold driverLaw
  infer_instance

theorem exit_ae_finite (B : Base) (t : ℕ) :
    ∀ᵐ ω ∂driverLaw, exitTime B (cluster B ω t) (stepWalk B (ω t)) ≠ ⊤ := by
  have hp : MeasurePreserving (fun ω : Driver => (ω t).2) driverLaw walkDriverLaw :=
    (measurePreserving_snd (μ := stepLaw) (ν := walkDriverLaw)).comp
      (measurePreserving_eval_infinitePi (fun _ : ℕ => stepDriverLaw) t)
  have hh := hp.quasiMeasurePreserving.ae (ExitAeFinite.vertical_reaches 0 ((t : ℤ) + 1))
  filter_upwards [hh] with ω hω
  apply ExitAeFinite.finite_of_upper_hit B ω t
  obtain ⟨n, hn⟩ := hω
  refine ⟨n, ?_⟩
  have he := ExitAeFinite.actual_vertical B (startVertex B (ω t).1, 0) (ω t).2 n
  change (cylPath B (startVertex B (ω t).1, 0) (ω t).2 n).2 > (t : ℤ)
  rw [he]
  change (t : ℤ) < ExitAeFinite.verticalPath 0 (ω t).2 n
  omega

end IdlaCyl.Obligation
