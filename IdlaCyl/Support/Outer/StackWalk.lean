/-
Fresh site-stack construction of one cylinder walk.
Source: paper/idla-cylinder-gff.tex, tex:246-265,1331-1351,1391-1396.
The arrow array is independent over (site, departure number), with row law
cylMeasure. The finite-exploration identity is proved before any use of exits.
-/
import IdlaCyl.Support.Outer.CommuteMeasurable
import IdlaCyl.Support.Recurrence.Discharge

attribute [local instance] Classical.propDecidable

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

/-- Independent site stacks, flattened into a countable product. -/
abbrev OuterStacks (B : Base) := (Site B × ℕ) → Site B

/-- Each unused arrow at s has precisely the cylinder transition law from s. -/
def outerStackLaw (B : Base) : Measure (OuterStacks B) := by
  letI : ∀ e : Site B × ℕ, IsProbabilityMeasure (cylMeasure B e.1) :=
    fun e => cylMeasure_isProbability B e.1
  exact Measure.infinitePi (fun e : Site B × ℕ => cylMeasure B e.1)

instance outerStackLaw_isProbability (B : Base) : IsProbabilityMeasure (outerStackLaw B) := by
  letI : ∀ e : Site B × ℕ, IsProbabilityMeasure (cylMeasure B e.1) :=
    fun e => cylMeasure_isProbability B e.1
  unfold outerStackLaw
  infer_instance

/-- Number of departures from x strictly before time n along f. -/
def outerVisits (B : Base) (f : ℕ → Site B) : ℕ → Site B → ℕ
  | 0 => fun _ => 0
  | n + 1 => fun x => outerVisits B f n x + if f n = x then 1 else 0

/-- The current position and reversed departure history of the explorer. -/
def outerStackState (B : Base) (p : Site B) (r : OuterStacks B) :
    ℕ → Site B × List (Site B)
  | 0 => (p, [])
  | n + 1 =>
      let s := outerStackState B p r n
      (r (s.1, s.2.count s.1), s.1 :: s.2)

/-- A walk reads the next unconsumed arrow whenever it leaves a site. -/
def outerStackWalk (B : Base) (p : Site B) (r : OuterStacks B) : ℕ → Site B :=
  fun n => (outerStackState B p r n).1

private instance outerHistoryMeasurableSpace (B : Base) : MeasurableSpace (List (Site B)) := ⊤
private instance outerHistoryMeasurableSingleton (B : Base) :
    MeasurableSingletonClass (List (Site B)) := ⟨fun _ => trivial⟩

private theorem measurable_outerStackState (B : Base) (p : Site B) (n : ℕ) :
    Measurable (fun r => outerStackState B p r n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hstep : Measurable (fun sr : (Site B × List (Site B)) × OuterStacks B =>
          (sr.2 (sr.1.1, sr.1.2.count sr.1.1), sr.1.1 :: sr.1.2)) := by
        apply measurable_from_prod_countable_right
        intro s
        change Measurable (fun r : OuterStacks B =>
          (r (s.1, s.2.count s.1), s.1 :: s.2))
        exact (measurable_pi_apply (s.1, s.2.count s.1)).prodMk measurable_const
      exact hstep.comp (ih.prodMk measurable_id)

/-- The whole explored trajectory is measurable, including infinite trajectories. -/
theorem measurable_outerStackWalk (B : Base) (p : Site B) :
    Measurable (outerStackWalk B p) := by
  apply measurable_pi_iff.mpr
  intro n
  exact measurable_fst.comp (measurable_outerStackState B p n)

private theorem outerStackState_count (B : Base) (p : Site B) (r : OuterStacks B)
    (n : ℕ) (x : Site B) :
    (outerStackState B p r n).2.count x = outerVisits B (outerStackWalk B p r) n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [outerStackState, List.count_cons, outerVisits, ← ih, outerStackWalk,
        beq_iff_eq]
      split_ifs <;> omega

/-- The deterministic one-step explorer equation uses the visit count, not the time. -/
theorem outerStackWalk_succ (B : Base) (p : Site B) (r : OuterStacks B) (n : ℕ) :
    outerStackWalk B p r (n + 1) =
      r (outerStackWalk B p r n, outerVisits B (outerStackWalk B p r) n
        (outerStackWalk B p r n)) := by
  change r ((outerStackState B p r n).1, (outerStackState B p r n).2.count _) = _
  rw [outerStackState_count]
  rfl

private theorem outerVisits_congr (B : Base) (f g : ℕ → Site B) (n : ℕ)
    (h : ∀ i < n, f i = g i) : outerVisits B f n = outerVisits B g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [outerVisits, ih (fun i hi => h i (by omega)), h n (by omega)]

/-- Finite exploration exposes exactly one distinct stack coordinate per step. -/
theorem outerStackWalk_prefix_iff (B : Base) (p : Site B) (r : OuterStacks B)
    (n : ℕ) (f : ℕ → Site B) :
    (∀ i ≤ n, outerStackWalk B p r i = f i) ↔
      f 0 = p ∧ ∀ i < n, r (f i, outerVisits B f i (f i)) = f (i + 1) := by
  induction n with
  | zero =>
      simp only [Nat.le_zero, forall_eq, outerStackWalk, outerStackState,
        Nat.not_lt_zero, IsEmpty.forall_iff, implies_true, and_true, eq_comm]
  | succ n ih =>
      constructor
      · intro h
        have hp := ih.mp (fun i hi => h i (by omega))
        refine ⟨hp.1, fun i hi => ?_⟩
        by_cases hin : i < n
        · exact hp.2 i hin
        · have hieq : i = n := by omega
          subst i
          have hv := outerVisits_congr B (outerStackWalk B p r) f n
            (fun i hi => h i (by omega))
          have hs := outerStackWalk_succ B p r n
          rw [hv, h n (by omega), h (n + 1) le_rfl] at hs
          exact hs.symm
      · rintro ⟨hp, hr⟩
        have hprev := ih.mpr ⟨hp, fun i hi => hr i (by omega)⟩
        intro i hi
        by_cases hin : i ≤ n
        · exact hprev i hin
        · have hieq : i = n + 1 := by omega
          subst i
          rw [outerStackWalk_succ,
            outerVisits_congr B (outerStackWalk B p r) f n (fun i hi => hprev i (by omega)),
            hprev n le_rfl]
          exact hr n (by omega)

private theorem outerVisits_mono (B : Base) (f : ℕ → Site B) (x : Site B)
    {i j : ℕ} (hij : i ≤ j) : outerVisits B f i x ≤ outerVisits B f j x := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
      simp only [outerVisits]
      omega

/-- Visits to the same site read strictly increasing indices. -/
theorem outerStack_coordinate_injective (B : Base) (f : ℕ → Site B) :
    Function.Injective (fun i => (f i, outerVisits B f i (f i))) := by
  intro i j h
  have hsite : f i = f j := congrArg Prod.fst h
  have hcount : outerVisits B f i (f i) = outerVisits B f j (f j) := congrArg Prod.snd h
  have hnot (i j : ℕ) (hij : i < j) (hs : f i = f j)
      (hc : outerVisits B f i (f i) = outerVisits B f j (f j)) : False := by
    have hm := outerVisits_mono B f (f i) (Nat.succ_le_of_lt hij)
    simp only [outerVisits, ite_true] at hm
    rw [← hs] at hc
    omega
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hnot i j hij hsite hcount
  · exact hnot j i hji hsite.symm hcount.symm


/-- A fixed arrow has the required row law. -/
theorem outerStackLaw_map_eval (B : Base) (e : Site B × ℕ) :
    (outerStackLaw B).map (fun r => r e) = cylMeasure B e.1 := by
  letI : ∀ e : Site B × ℕ, IsProbabilityMeasure (cylMeasure B e.1) :=
    fun e => cylMeasure_isProbability B e.1
  exact Measure.infinitePi_map_eval (fun e : Site B × ℕ => cylMeasure B e.1) e

/-- Distinct site/departure coordinates are independent. -/
theorem outerStackLaw_iIndepFun (B : Base) :
    iIndepFun (fun e (r : OuterStacks B) => r e) (outerStackLaw B) := by
  letI : ∀ e : Site B × ℕ, IsProbabilityMeasure (cylMeasure B e.1) :=
    fun e => cylMeasure_isProbability B e.1
  exact iIndepFun_infinitePi (P := fun e : Site B × ℕ => cylMeasure B e.1)
    (X := fun _ => (id : Site B → Site B)) (fun _ => measurable_id)

/-- Finite exploration has exactly the canonical walk's cylinder weights. -/
theorem outerStackWalk_pathCyl (B : Base) (p : Site B) (n : ℕ) (f : ℕ → Site B) :
    outerStackLaw B ((outerStackWalk B p) ⁻¹' pathCyl B n f) =
      (if f 0 = p then 1 else 0) * pathWeight B n f := by
  by_cases hp : f 0 = p
  · have heq : (outerStackWalk B p) ⁻¹' pathCyl B n f =
        ⋂ i ∈ Finset.range n, {r : OuterStacks B |
          r (f i, outerVisits B f i (f i)) = f (i + 1)} := by
      ext r
      simp only [Set.mem_preimage, pathCyl, Set.mem_setOf_eq, Set.mem_iInter,
        Finset.mem_range]
      exact (outerStackWalk_prefix_iff B p r n f).trans (and_iff_right hp)
    rw [heq, if_pos hp, one_mul]
    have hind := iIndepFun.precomp (outerStack_coordinate_injective B f)
      (outerStackLaw_iIndepFun B)
    have hi := hind.meas_biInter (S := Finset.range n)
      (s := fun i => {r : OuterStacks B |
        r (f i, outerVisits B f i (f i)) = f (i + 1)})
      (fun i _ => ⟨{f (i + 1)}, measurableSet_singleton _, rfl⟩)
    rw [hi]
    apply Finset.prod_congr rfl
    intro i _
    change outerStackLaw B ((fun r => r (f i, outerVisits B f i (f i))) ⁻¹' {f (i + 1)}) = _
    rw [← Measure.map_apply (measurable_pi_apply _) (measurableSet_singleton _),
      outerStackLaw_map_eval]
    exact cylMeasure_singleton B (f i) (f (i + 1))
  · have heq : (outerStackWalk B p) ⁻¹' pathCyl B n f = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro r hr
      exact hp ((outerStackWalk_prefix_iff B p r n f).mp hr).1
    rw [heq, measure_empty, if_neg hp, zero_mul]

/-- The complete trajectory read from fresh site stacks has the cylinder-walk law. -/
theorem outerStackWalk_law (B : Base) (p : Site B) :
    (outerStackLaw B).map (outerStackWalk B p) = walkPathLaw B p := by
  haveI : IsProbabilityMeasure ((outerStackLaw B).map (outerStackWalk B p)) :=
    Measure.isProbabilityMeasure_map (measurable_outerStackWalk B p).aemeasurable
  apply measure_ext_of_pathCyl B
  intro n f
  rw [Measure.map_apply (measurable_outerStackWalk B p) (measurableSet_pathCyl B n f),
    outerStackWalk_pathCyl, walkPathLaw_pathCyl]

/-- One walk added to any fixed seed has the same occupation law under the stack explorer. -/
theorem addWalk_stack_law (B : Base) (A : Set (Site B)) (p : Site B) :
    (outerStackLaw B).map
        (fun r => clusterCode B (addWalk B A (outerStackWalk B p r))) =
      (walkPathLaw B p).map (fun X => clusterCode B (addWalk B A X)) := by
  rw [← outerStackWalk_law B p,
    Measure.map_map (measurable_clusterCode_addWalk B A) (measurable_outerStackWalk B p)]
  rfl


/-- A trajectory visiting every level exits every finite extension of a half-cylinder. -/
theorem outer_exit_ne_top_of_hits (B : Base) (a : ℤ) (F : Finset (Site B))
    (X : ℕ → Site B) (hX : ∀ h : ℤ, ∃ n, (X n).2 = h) :
    exitTime' B (R B (a : ℝ) ∪ (F : Set (Site B))) X ≠ ⊤ := by
  let m : ℤ := |a| + 1 + ∑ z ∈ F, |z.2|
  obtain ⟨n, hn⟩ := hX m
  have hnot : X n ∉ R B (a : ℝ) ∪ (F : Set (Site B)) := by
    rintro (hR | hF)
    · have ha : (X n).2 ≤ a := by exact_mod_cast (mem_R.mp hR)
      have hsum : 0 ≤ ∑ z ∈ F, |z.2| := Finset.sum_nonneg (fun z _ => abs_nonneg z.2)
      have habs := le_abs_self a
      dsimp [m] at hn
      omega
    · have hle : |(X n).2| ≤ ∑ z ∈ F, |z.2| :=
        Finset.single_le_sum (fun z _ => abs_nonneg z.2) hF
      have habs := le_abs_self (X n).2
      have haabs := abs_nonneg a
      dsimp [m] at hn
      omega
  intro htop
  exact (MeasureTheory.hittingAfter_eq_top_iff.mp htop n (Nat.zero_le n)) hnot

/-- Under the constructed stack law, the explored walk visits every level almost surely. -/
theorem outerStackWalk_ae_hits_all (B : Base) (p : Site B) :
    ∀ᵐ r ∂outerStackLaw B, ∀ h : ℤ, ∃ n, (outerStackWalk B p r n).2 = h := by
  have hwalk : ∀ᵐ X ∂walkPathLaw B p, ∀ h : ℤ, ∃ n, (X n).2 = h :=
    ae_all_iff.mpr (fun h => ae_exists_ver_eq External.lazyRwRecurrent_holds B p h)
  rw [← outerStackWalk_law B p] at hwalk
  exact ae_of_ae_map (measurable_outerStackWalk B p).aemeasurable hwalk

/-- Stabilization of one release is a conclusion of the stack law and recurrence. -/
theorem outerStackWalk_ae_exit_ne_top (B : Base) (a : ℤ) (F : Finset (Site B))
    (p : Site B) :
    ∀ᵐ r ∂outerStackLaw B,
      exitTime' B (R B (a : ℝ) ∪ (F : Set (Site B))) (outerStackWalk B p r) ≠ ⊤ := by
  filter_upwards [outerStackWalk_ae_hits_all B p] with r hr
  exact outer_exit_ne_top_of_hits B a F _ hr

example (B : Base) (p : Site B) : outerStackWalk B p (fun _ => p) 0 = p := rfl

example (B : Base) (p : Site B) :
    outerStackLaw B {r | outerStackWalk B p r 0 = p} = 1 := by
  have heq : {r : OuterStacks B | outerStackWalk B p r 0 = p} = Set.univ := by
    ext r
    simp only [outerStackWalk, outerStackState, Set.mem_setOf_eq, Set.mem_univ]
  rw [heq, measure_univ]

example (B : Base) (A : Set (Site B)) (p : Site B) :
    IsProbabilityMeasure ((outerStackLaw B).map
      (fun r => clusterCode B (addWalk B A (outerStackWalk B p r)))) :=
  Measure.isProbabilityMeasure_map
    ((measurable_clusterCode_addWalk B A).comp (measurable_outerStackWalk B p)).aemeasurable

end
end IdlaCyl
