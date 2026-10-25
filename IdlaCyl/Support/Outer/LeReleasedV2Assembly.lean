module

/-
Assembly of the height bound for the balanced release (`le:released`).
Source: paper/idla-cylinder-gff.tex, tex:1328-1372 (Lemma `le:released` and its proof).

Proved here: the integration over the uniform start vector (`idlaMeasure_eq_bind_prescribed`),
the a priori bound `pr_apriori_part_b` at β = e³ on the chronological process at τ = 4mN,
the exponential arithmetic, and the fixed-start comparison `le_released_v2_fixed` (`hfix`), by
the balanced reordering `exists_balancedStartList_perm` and monotonicity of the finite releases
(`outerRun_subperm_le`) on the upward height event `outerHeightEvent`.
`le_released_v2_of_fixed_comparison` keeps `hfix` as an explicit hypothesis; the frozen proof
applies it to `le_released_v2_fixed`. Nothing here is a binder of any frozen statement.
-/
public import IdlaCyl.Support.AprioriFinal
public import IdlaCyl.Support.Outer.BalancedRelease
public import IdlaCyl.Support.Outer.ResumeKernels
public import IdlaCyl.Support.Outer.ResumeGrowth
public import IdlaCyl.Support.Outer.HeightComparison

@[expose] public section

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Step (a) of `le_released_v2`: releasing the same prescribed starts in any order gives the
same law on finite cluster states. Induction on the permutation; the swap case is
`resumeStep_commute` followed by `Measure.bind_bind`. -/
theorem resumeRun_perm (B : Base) (F : ResumeFinite B) {L L' : List (Site B)}
    (h : List.Perm L L') : resumeRun B F L = resumeRun B F L' := by
  induction h generalizing F with
  | nil => rfl
  | cons x _ ih =>
      change (resumeStep B x F).bind (fun G => resumeRun B G _) =
        (resumeStep B x F).bind (fun G => resumeRun B G _)
      exact congrArg (fun k => (resumeStep B x F).bind k) (funext ih)
  | swap x y l =>
      change (resumeStep B y F).bind (fun G => (resumeStep B x G).bind (fun H => resumeRun B H l)) =
        (resumeStep B x F).bind (fun G => (resumeStep B y G).bind (fun H => resumeRun B H l))
      rw [← Measure.bind_bind (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable, resumeStep_commute,
        Measure.bind_bind (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable]
  | trans _ _ ih₁ ih₂ => exact (ih₁ F).trans (ih₂ F)

noncomputable section

/-- The event that the chronological cluster at time `t` leaves `R r` is measurable. -/
theorem measurableSet_clusterTraj_not_subset (B : Base) (t : ℕ) (r : ℝ) :
    MeasurableSet {ω : TrajSeq B | ¬ clusterTraj B ω t ⊆ R B r} := by
  have hset : {ω : TrajSeq B | ¬ clusterTraj B ω t ⊆ R B r} =
      ⋃ p : Site B, {ω : TrajSeq B | p ∈ clusterTraj B ω t ∧ p ∉ R B r} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.not_subset]
  rw [hset]
  apply MeasurableSet.iUnion
  intro p
  exact (measurableSet_mem_clusterTraj B t p).inter (MeasurableSet.const _)

/-- The start count of the first `t` prescribed releases is a measurable function of the starts. -/
theorem measurable_outerStartCount (B : Base) (t : ℕ) (x : B.V) :
    Measurable (fun s : ℕ → Site B => outerStartCount B t s x) := by
  let g : Site B → ℕ := fun p => if p = (x, 0) then 1 else 0
  have hg : Measurable g := measurable_of_countable g
  have heq : (fun s : ℕ → Site B => outerStartCount B t s x) =
      fun s => ∑ j ∈ Finset.range t, g (s j) := by
    funext s
    simp only [outerStartCount, Finset.card_filter, g]
  rw [heq]
  exact Finset.measurable_sum _ fun j _ => hg.comp (measurable_pi_apply j)

/-- The event that some vertex receives fewer than `m` of the first `t` starts is measurable. -/
theorem measurableSet_outerStartBad (B : Base) (t m : ℕ) :
    MeasurableSet {s : ℕ → Site B | ∃ x : B.V, outerStartCount B t s x < m} := by
  have hset : {s : ℕ → Site B | ∃ x : B.V, outerStartCount B t s x < m} =
      ⋃ x : B.V, {s : ℕ → Site B | outerStartCount B t s x < m} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [hset]
  exact MeasurableSet.iUnion fun x =>
    measurableSet_lt (measurable_outerStartCount B t x) measurable_const

/-- A multiset domination `M ≤ L` makes `L` a permutation of `M` followed by some rest. -/
theorem perm_append_of_multiset_le {α : Type*} (L M : List α)
    (h : (M : Multiset α) ≤ (L : Multiset α)) : ∃ rest : List α, L.Perm (M ++ rest) := by
  obtain ⟨u, hu⟩ := Multiset.le_iff_exists_add.mp h
  refine ⟨u.toList, ?_⟩
  apply Multiset.coe_eq_coe.mp
  rw [hu]
  conv_lhs => rw [← Multiset.coe_toList u]
  rw [← Multiset.coe_add]

/-- The count of `(x,0)` in the first `T` starts is `outerStartCount`. -/
theorem count_map_range_eq_outerStartCount (B : Base) [DecidableEq (Site B)] (T : ℕ)
    (s : ℕ → Site B) (x : B.V) :
    Multiset.count (x, 0) ((List.range T).map s : Multiset (Site B)) =
      outerStartCount B T s x := by
  unfold outerStartCount
  rw [Finset.card_filter]
  induction T with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, ← Multiset.coe_add, Multiset.count_add, ih,
        Finset.sum_range_succ]
      by_cases h : s n = (x, 0)
      · simp [h]
      · simp [h, Ne.symm h]

/-- `m` releases at each `(x,0)`, as a multiset. -/
def balancedStartMS (B : Base) (m : ℕ) : Multiset (Site B) :=
  ∑ x : B.V, Multiset.replicate m (x, 0)

theorem count_balancedStartMS (B : Base) [DecidableEq (Site B)] (m : ℕ) (a : Site B) :
    Multiset.count a (balancedStartMS B m) = if a.2 = 0 then m else 0 := by
  obtain ⟨y, q⟩ := a
  unfold balancedStartMS
  rw [Multiset.count_sum']
  by_cases hq : q = 0
  · subst hq
    simp [Multiset.count_replicate]
  · simp [Multiset.count_replicate, hq, Ne.symm hq]

/-- Step (c2): with at least `m` releases at each vertex among the first `T` starts, the start
list is a permutation of the balanced `m`-per-vertex list followed by some rest. -/
theorem exists_balancedStartList_perm (B : Base) [DecidableEq (Site B)] (m T : ℕ)
    (s : ℕ → Site B) (hs : ∀ x : B.V, m ≤ outerStartCount B T s x) :
    ∃ rest : List (Site B), ((List.range T).map s).Perm ((balancedStartMS B m).toList ++ rest) := by
  refine perm_append_of_multiset_le _ _ ?_
  rw [Multiset.coe_toList]
  refine Multiset.le_iff_count.2 fun a => ?_
  rw [count_balancedStartMS]
  obtain ⟨y, q⟩ := a
  by_cases hq : q = 0
  · subst hq
    dsimp only
    rw [if_pos rfl, count_map_range_eq_outerStartCount B T s y]
    exact hs y
  · dsimp only
    rw [if_neg hq]
    exact Nat.zero_le _

/-- Integrating the prescribed-walk law over the uniform start vector (`tex:1340-1347`).
The fixed-start comparison `hfix` is used on the complement of the bad start event. -/
theorem balancedLaw_le_idla_add_starts (B : Base) (m : ℕ) (r : ℝ)
    (hfix : ∀ s : ℕ → Site B, (∀ x : B.V, m ≤ outerStartCount B (4 * m * B.card) s x) →
      balancedLaw B m {ω : BalancedDriver B m | ¬ balancedCluster B m ω ⊆ R B r} ≤
        prescribedMeasure B s {ω : TrajSeq B | ¬ clusterTraj B ω (4 * m * B.card) ⊆ R B r}) :
    balancedLaw B m {ω : BalancedDriver B m | ¬ balancedCluster B m ω ⊆ R B r} ≤
      idlaMeasure B {ω : TrajSeq B | ¬ clusterTraj B ω (4 * m * B.card) ⊆ R B r} +
        outerStartLaw B {s : ℕ → Site B | ∃ x : B.V,
          outerStartCount B (4 * m * B.card) s x < m} := by
  set c := balancedLaw B m {ω : BalancedDriver B m | ¬ balancedCluster B m ω ⊆ R B r}
  set S := {ω : TrajSeq B | ¬ clusterTraj B ω (4 * m * B.card) ⊆ R B r}
  set E := {s : ℕ → Site B | ∃ x : B.V, outerStartCount B (4 * m * B.card) s x < m}
  have hSmeas : MeasurableSet S := measurableSet_clusterTraj_not_subset B _ r
  have hEmeas : MeasurableSet E := measurableSet_outerStartBad B _ m
  have hf : Measurable fun s : ℕ → Site B => prescribedMeasure B s S :=
    (Measure.measurable_coe hSmeas).comp (measurable_prescribedMeasure B)
  have hbind : idlaMeasure B S = ∫⁻ s, prescribedMeasure B s S ∂(outerStartLaw B) := by
    show idlaMeasure B S =
      ∫⁻ s, prescribedMeasure B s S ∂(Measure.infinitePi fun _ : ℕ => layerLaw B)
    rw [idlaMeasure_eq_bind_prescribed,
      Measure.bind_apply hSmeas (measurable_prescribedMeasure B).aemeasurable]
  have hc1 : c ≤ 1 := prob_le_one
  have hpt : ∀ s : ℕ → Site B, c ≤ prescribedMeasure B s S + E.indicator 1 s := by
    intro s
    by_cases hs : s ∈ E
    · rw [Set.indicator_of_mem hs, Pi.one_apply]
      exact hc1.trans le_add_self
    · rw [Set.indicator_of_notMem hs, add_zero]
      apply hfix s
      intro x
      by_contra hx
      exact hs ⟨x, not_le.mp hx⟩
  have hconst : c = ∫⁻ _s, c ∂(outerStartLaw B) := by
    rw [lintegral_const, measure_univ, mul_one]
  rw [hbind]
  calc c = ∫⁻ _s, c ∂(outerStartLaw B) := hconst
    _ ≤ ∫⁻ s, (prescribedMeasure B s S + E.indicator 1 s) ∂(outerStartLaw B) :=
        lintegral_mono fun s => hpt s
    _ = (∫⁻ s, prescribedMeasure B s S ∂(outerStartLaw B)) +
          ∫⁻ s, E.indicator 1 s ∂(outerStartLaw B) :=
        lintegral_add_left hf _
    _ = (∫⁻ s, prescribedMeasure B s S ∂(outerStartLaw B)) + outerStartLaw B E := by
        rw [lintegral_indicator_one hEmeas]

/-- Monotonicity (`tex:1400-1425`): once a prescribed stream agrees with the balanced release on
its first `Nm` walks, the balanced cluster lies in every later cluster of that stream. -/
theorem balancedCluster_subset_of_extension (B : Base) (m : ℕ) (ω : BalancedDriver B m)
    (η : TrajSeq B) (hη : ∀ j < B.card * m, η j = balancedTrajSeq B m ω j)
    (t : ℕ) (ht : B.card * m ≤ t) :
    balancedCluster B m ω ⊆ clusterTraj B η t := by
  rw [← balancedCluster_eq_of_prefix B m ω η hη]
  exact clusterFrom_mono B (R B 0) η ht

/-- The exponential arithmetic of `le:released`: both tails are at most `N^{-(ν+3)}`, and
`N^{-(ν+2)} = N^{-(ν+3)} · N`. -/
theorem released_tail_arith (ν K₁ : ℝ) (hK₁b : 16 * (ν + 4) / 9 ≤ K₁)
    (hK₁e : ν + 3 ≤ 4 * Real.exp 3 * K₁) (N : ℝ) (hN : 2 ≤ N) (m : ℝ)
    (hm : K₁ * Real.log N ≤ m) :
    Real.exp (-(4 * Real.exp 3 * m)) + N * Real.exp (-(9 / 16 * m)) ≤ N ^ (-(ν + 2)) := by
  have hNpos : 0 < N := by linarith
  have h4 : 0 < 4 * Real.exp 3 := by positivity
  have hA0 : 0 ≤ N ^ (-(ν + 3)) := (Real.rpow_pos_of_pos hNpos _).le
  have hP : N ^ (-(ν + 2)) = N ^ (-(ν + 3)) * N := by
    rw [show -(ν + 2) = -(ν + 3) + 1 by ring, Real.rpow_add hNpos, Real.rpow_one]
  have hterm1 : Real.exp (-(4 * Real.exp 3 * m)) ≤ N ^ (-(ν + 3)) := by
    have hL : 4 * Real.exp 3 * (K₁ * Real.log N) ≤ 4 * Real.exp 3 * m :=
      mul_le_mul_of_nonneg_left hm h4.le
    have e1 : Real.exp (-(4 * Real.exp 3 * K₁ * Real.log N)) = N ^ (-(4 * Real.exp 3 * K₁)) := by
      rw [Real.rpow_def_of_pos hNpos]
      congr 1
      ring
    calc Real.exp (-(4 * Real.exp 3 * m))
        ≤ Real.exp (-(4 * Real.exp 3 * K₁ * Real.log N)) := Real.exp_le_exp.mpr (by linarith)
      _ = N ^ (-(4 * Real.exp 3 * K₁)) := e1
      _ ≤ N ^ (-(ν + 3)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hterm2 : N * Real.exp (-(9 / 16 * m)) ≤ N ^ (-(ν + 3)) := by
    have hL : 9 / 16 * (K₁ * Real.log N) ≤ 9 / 16 * m :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    have e2 : Real.exp (-(9 / 16 * K₁ * Real.log N)) = N ^ (-(9 / 16 * K₁)) := by
      rw [Real.rpow_def_of_pos hNpos]
      congr 1
      ring
    calc N * Real.exp (-(9 / 16 * m))
        ≤ N * Real.exp (-(9 / 16 * K₁ * Real.log N)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hNpos.le
      _ = N * N ^ (-(9 / 16 * K₁)) := by rw [e2]
      _ = N ^ (1 + -(9 / 16 * K₁)) := by rw [Real.rpow_add hNpos, Real.rpow_one]
      _ ≤ N ^ (-(ν + 3)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  rw [hP]
  linarith [mul_le_mul_of_nonneg_left hN hA0]

/-- Instance bridge: `List.count` for the `DecidableEq`-induced `BEq` agrees with the ambient one. -/
theorem list_count_beq_decEq {α : Type*} [BEq α] [LawfulBEq α] [DecidableEq α] (a : α)
    (l : List α) : @List.count α instBEqOfDecidableEq a l = List.count a l := by
  unfold List.count
  congr 1
  funext x
  cases h1 : (x == a) <;> cases h2 : (@BEq.beq α instBEqOfDecidableEq x a) <;>
    simp_all [beq_iff_eq]

/-- The balanced queue is a permutation of the balanced `m`-per-vertex start list at height `0`. -/
theorem outerBalancedQueue_perm_balancedStart (B : Base) [DecidableEq (Site B)] (m : ℕ) :
    (outerBalancedQueue B 0 m).Perm (balancedStartMS B m).toList := by
  have hzero : ∀ a ∈ outerBalancedQueue B 0 m, a.2 = 0 := by
    intro a ha
    unfold outerBalancedQueue at ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    rfl
  rw [List.perm_iff_count]
  intro a
  obtain ⟨y, q⟩ := a
  have hc : (balancedStartMS B m).toList.count (y, q) =
      Multiset.count (y, q) (balancedStartMS B m) := by
    rw [← list_count_beq_decEq]
    conv_rhs => rw [← Multiset.coe_toList (balancedStartMS B m)]
    exact (Multiset.coe_count (y, q) _).symm
  have hL : (outerBalancedQueue B 0 m).count (y, q) =
      Multiset.count (y, q) (balancedStartMS B m) := by
    rw [count_balancedStartMS]
    dsimp only
    by_cases hq : q = 0
    · subst hq
      rw [if_pos rfl, outerBalancedQueue_count]
    · rw [if_neg hq, List.count_eq_zero]
      intro hmem
      exact hq (hzero _ hmem)
  rw [hL, hc]

/-- **Fixed-start comparison (`hfix`).** With at least `m` starts at every vertex among the
first `4mN` starts, the balanced height law is at most the prescribed height law. Proof: the
balanced tail is the finite release of the balanced queue from the flat seed of height `0`
(`outerFlatBalanced_height_law`); that queue is a subperm of the prescribed start list
(`exists_balancedStartList_perm`); releases are monotone in the queue (`outerRun_subperm_le`) on
the upward event `outerHeightEvent`; and the prescribed release of the same list is the
prescribed height event (`prescribedMeasure_map_resumeGrow`). -/
theorem le_released_v2_fixed (B : Base) (m : ℕ) (s : ℕ → Site B)
    (hs : ∀ x : B.V, m ≤ outerStartCount B (4 * m * B.card) s x) (r : ℝ) :
    balancedLaw B m {ω : BalancedDriver B m | ¬ balancedCluster B m ω ⊆ R B r} ≤
      prescribedMeasure B s {ω : TrajSeq B | ¬ clusterTraj B ω (4 * m * B.card) ⊆ R B r} := by
  classical
  have hbal := outerFlatBalanced_height_law B 0 le_rfl m r
  simp only [Int.cast_zero, zero_add] at hbal
  obtain ⟨rest, hperm⟩ := exists_balancedStartList_perm B m (4 * m * B.card) s hs
  have hLM : (outerBalancedQueue B 0 m).Subperm ((List.range (4 * m * B.card)).map s) :=
    ((outerBalancedQueue_perm_balancedStart B m).subperm.trans
      (List.sublist_append_left _ _).subperm).trans hperm.symm.subperm
  have hseed : resumeSeed B (outerFlatSeed B 0) = R B 0 := by
    rw [outerFlatSeed_eq B 0 le_rfl]
    simp
  have hset : (fun ω : TrajSeq B => resumeGrow B (outerFlatSeed B 0) ω (4 * m * B.card)) ⁻¹'
      outerHeightEvent B r = {ω : TrajSeq B | ¬ clusterTraj B ω (4 * m * B.card) ⊆ R B r} := by
    ext ω
    simp only [Set.mem_preimage, outerHeightEvent, Set.mem_setOf_eq, resumeSeed_grow, hseed,
      clusterTraj]
  have hlist : List.ofFn (fun i : Fin (4 * m * B.card) => s i) =
      (List.range (4 * m * B.card)).map s := by
    apply List.ext_getElem <;> simp
  have hpres : prescribedMeasure B s {ω : TrajSeq B |
      ¬ clusterTraj B ω (4 * m * B.card) ⊆ R B r} =
        resumeRun B (outerFlatSeed B 0) ((List.range (4 * m * B.card)).map s)
          (outerHeightEvent B r) := by
    rw [← hset, ← Measure.map_apply (measurable_resumeGrow B _ _)
      (Set.to_countable _).measurableSet, prescribedMeasure_map_resumeGrow, hlist]
  rw [← hbal, hpres]
  exact outerRun_subperm_le B _ (outerHeightEvent_upward B r) _ hLM

/-- **Height of the balanced release (`le:released`, tex:1328-1372), with the fixed-start
comparison as an explicit hypothesis.** The constant `C₃ = 4e³` and `K₁` are chosen from
`ν` and the a priori constant `K₀(e³)`. -/
theorem le_released_v2_of_fixed_comparison
    (hfix : ∀ (B : Base) (m : ℕ) (s : ℕ → Site B),
      (∀ x : B.V, m ≤ outerStartCount B (4 * m * B.card) s x) →
      ∀ r : ℝ, balancedLaw B m {ω : BalancedDriver B m | ¬ balancedCluster B m ω ⊆ R B r} ≤
        prescribedMeasure B s {ω : TrajSeq B | ¬ clusterTraj B ω (4 * m * B.card) ⊆ R B r})
    (ν : ℝ) (hν : 0 < ν) :
    ∃ C₃ K₁ : ℝ, 0 < C₃ ∧ 0 < K₁ ∧ ∃ N₀ : ℕ,
      ∀ B : Base, N₀ ≤ B.card → ∀ m : ℕ,
        K₁ * Real.log (B.card : ℝ) ≤ (m : ℝ) →
        balancedLaw B m {ω : BalancedDriver B m |
          ¬ (balancedCluster B m ω ⊆ R B (C₃ * (m : ℝ)))} ≤
            ENNReal.ofReal ((B.card : ℝ) ^ (-(ν + 2))) := by
  obtain ⟨K₀, _hK₀, N₀, hK⟩ :=
    pr_apriori_part_b (Real.exp 3) (Real.exp_lt_exp.mpr (by norm_num))
  obtain ⟨K₁, hK₁a, hK₁b, hK₁c⟩ : ∃ K₁ : ℝ, K₀ / 4 ≤ K₁ ∧ 16 * (ν + 4) / 9 ≤ K₁ ∧
      (ν + 3) / (4 * Real.exp 3) ≤ K₁ :=
    ⟨max (K₀ / 4) (max (16 * (ν + 4) / 9) ((ν + 3) / (4 * Real.exp 3))),
      le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  have hK₁pos : 0 < K₁ := by linarith
  have hK₁e : ν + 3 ≤ 4 * Real.exp 3 * K₁ := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Real.exp 3)).mp hK₁c
    linarith
  refine ⟨4 * Real.exp 3, K₁, by positivity, hK₁pos, N₀, ?_⟩
  intro B hNB m hm
  have hN2 : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
  have hNpos : (0 : ℝ) < (B.card : ℝ) := by linarith
  have hNne : (B.card : ℝ) ≠ 0 := hNpos.ne'
  have hL0 : 0 ≤ Real.log (B.card : ℝ) := Real.log_nonneg (by linarith)
  -- The chronological time τ = 4mN meets the a priori threshold K₀ N log N.
  have hT : K₀ * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ ((4 * m * B.card : ℕ) : ℝ) := by
    push_cast
    have h1 : K₀ ≤ 4 * K₁ := by linarith
    have h2 : K₀ * (B.card : ℝ) * Real.log (B.card : ℝ) ≤
        4 * K₁ * (B.card : ℝ) * Real.log (B.card : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hNpos.le) hL0
    have h3 := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 4 * (B.card : ℝ))
    nlinarith [h2, h3]
  have hw := hK B hNB (4 * m * B.card) hT
  have hre : Real.exp 3 * ((4 * m * B.card : ℕ) : ℝ) / (B.card : ℝ) = 4 * Real.exp 3 * m := by
    have e : Real.exp 3 * ((4 * m * B.card : ℕ) : ℝ) = (4 * Real.exp 3 * m) * (B.card : ℝ) := by
      push_cast
      ring
    rw [e, mul_div_assoc, div_self hNne, mul_one]
  rw [hre] at hw
  have hcomp := balancedLaw_le_idla_add_starts B m (4 * Real.exp 3 * m)
    (fun s hs => hfix B m s hs (4 * Real.exp 3 * m))
  have hc := outerStartCount_exists_lower_tail B m
  refine hcomp.trans ((add_le_add hw hc).trans ?_)
  rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (mul_nonneg hNpos.le (Real.exp_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (released_tail_arith ν K₁ hK₁b hK₁e (B.card : ℝ) hN2 m hm)

end
end IdlaCyl
