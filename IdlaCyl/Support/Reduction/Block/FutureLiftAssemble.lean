module

public import IdlaCyl.Support.Reduction.Block.FutureLift
public import IdlaCyl.Support.Reduction.Block.FutureLiftCoupling
public import IdlaCyl.Support.Reduction.DrivingLift

@[expose] public section

/-!
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.

# The future-lift coupling of whole driving sequences

This file assembles a coupling of two whole driving sequences whose clusters at times `T` and
`T'` agree up to a vertical shift `k` at the endpoint, from an endpoint coupling of their finite
clusters. The first `T` walkers of the first sequence and the first `T'` walkers of the second are
taken from the endpoint coupling (`lift_cluster_coupling`). Every later walker index `s` is driven
by an independent copy of the future pair law (`futurePair`). Concatenating prefix and future gives
the full driving laws (`infinitePi_split`), the future pairs are spliced almost surely
(`futurePair_splice`), and the endpoint bound propagates to all later times
(`future_cluster_bound`).

The main result is `IdlaCyl.Reduction.lift_cluster_coupling_future`.
-/

namespace IdlaCyl.Reduction

open MeasureTheory ProbabilityTheory

/-- A measure whose first marginal is a probability measure is a probability measure. -/
theorem isProbabilityMeasure_of_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure (α × β)) (ν : Measure α) [IsProbabilityMeasure ν] (h : μ.map Prod.fst = ν) :
    IsProbabilityMeasure μ := by
  refine ⟨?_⟩
  have h1 : μ.map Prod.fst Set.univ = μ Set.univ := by
    rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
  rw [h, measure_univ] at h1
  exact h1.symm

/-- The future pair law is a probability measure, since its first marginal is. -/
instance futurePair_isProbability (B : Base) (k : ℕ) : IsProbabilityMeasure (futurePair B k) :=
  isProbabilityMeasure_of_map_fst (futurePair B k) (walkLawUniform B) (futurePair_fst B k)

/-- A pair of walks is spliced at height `k` when the first walk, from some time `τ` on, is the
translate by `k` of the second, and its prefix before `τ` stays at height at most `k`. -/
def SplicedPair (B : Base) (k : ℕ) (p : (ℕ → Site B) × (ℕ → Site B)) : Prop :=
  ∃ τ : ℕ, (∀ i < τ, (p.1 i).2 ≤ (k : ℤ)) ∧ ∀ n : ℕ, p.1 (τ + n) = outerShift B (k : ℤ) (p.2 n)

/-- The set of driving-sequence pairs whose walkers `a` and `b` are spliced at height `k`. -/
theorem measurableSet_splice_pair (B : Base) (k a b : ℕ) :
    MeasurableSet {p : TrajSeq B × TrajSeq B | ∃ τ : ℕ, (∀ i < τ, (p.1 a i).2 ≤ (k : ℤ)) ∧
      ∀ n : ℕ, p.1 a (τ + n) = outerShift B (k : ℤ) (p.2 b n)} := by
  have hsplit : {p : TrajSeq B × TrajSeq B | ∃ τ : ℕ, (∀ i < τ, (p.1 a i).2 ≤ (k : ℤ)) ∧
      ∀ n : ℕ, p.1 a (τ + n) = outerShift B (k : ℤ) (p.2 b n)} =
      ⋃ τ : ℕ, ((⋂ i : ℕ, {p : TrajSeq B × TrajSeq B | i < τ → (p.1 a i).2 ≤ (k : ℤ)}) ∩
        ⋂ n : ℕ, {p : TrajSeq B × TrajSeq B | p.1 a (τ + n) = outerShift B (k : ℤ) (p.2 b n)}) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter]
  rw [hsplit]
  refine MeasurableSet.iUnion fun τ => MeasurableSet.inter (MeasurableSet.iInter fun i => ?_)
    (MeasurableSet.iInter fun n => ?_)
  · by_cases hi : i < τ
    · simp only [hi, true_implies]
      exact measurableSet_le
        (measurable_snd.comp ((measurable_pi_apply i).comp ((measurable_pi_apply a).comp measurable_fst)))
        measurable_const
    · simp [hi]
  · exact measurableSet_eq_fun ((measurable_pi_apply (τ + n)).comp ((measurable_pi_apply a).comp measurable_fst))
      ((measurable_of_countable (outerShift B (k : ℤ))).comp
        ((measurable_pi_apply n).comp ((measurable_pi_apply b).comp measurable_snd)))

/-- A site lies in a vertical shift of a set exactly when its inverse shift lies in the set. -/
theorem mem_shiftCluster_iff (B : Base) (k : ℕ) (A : Set (Site B)) (z : Site B) :
    z ∈ shiftCluster B k A ↔ (z.1, z.2 - (k : ℤ)) ∈ A := by
  unfold shiftCluster
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro h
    exact ⟨(z.1, z.2 - (k : ℤ)), h, by simp⟩

/-- The set of points that agree on a membership test is measurable when both tests are. -/
theorem measurableSet_iff_sets {α : Type*} [MeasurableSpace α] {s t : Set α}
    (hs : MeasurableSet s) (ht : MeasurableSet t) : MeasurableSet {x | x ∈ s ↔ x ∈ t} := by
  have h : {x | x ∈ s ↔ x ∈ t} = (s ∩ t) ∪ (sᶜ ∩ tᶜ) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
    tauto
  rw [h]
  exact (hs.inter ht).union (hs.compl.inter ht.compl)

/-- The endpoint event of the two cluster trajectories is measurable. -/
theorem measurableSet_shift_endpoint (B : Base) (T T' k : ℕ) :
    MeasurableSet {p : TrajSeq B × TrajSeq B |
      clusterTraj B p.1 T = shiftCluster B k (clusterTraj B p.2 T')} := by
  have hset : {p : TrajSeq B × TrajSeq B | clusterTraj B p.1 T = shiftCluster B k (clusterTraj B p.2 T')} =
      ⋂ z : Site B, {p : TrajSeq B × TrajSeq B |
        z ∈ clusterTraj B p.1 T ↔ z ∈ shiftCluster B k (clusterTraj B p.2 T')} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.ext_iff]
  rw [hset]
  refine MeasurableSet.iInter fun z => ?_
  have hA : MeasurableSet {p : TrajSeq B × TrajSeq B | z ∈ clusterTraj B p.1 T} :=
    (measurableSet_mem_clusterTraj B T z).preimage measurable_fst
  have hB : MeasurableSet {p : TrajSeq B × TrajSeq B |
      z ∈ shiftCluster B k (clusterTraj B p.2 T')} := by
    have heq : {p : TrajSeq B × TrajSeq B | z ∈ shiftCluster B k (clusterTraj B p.2 T')} =
        {p : TrajSeq B × TrajSeq B | (z.1, z.2 - (k : ℤ)) ∈ clusterTraj B p.2 T'} := by
      ext p
      exact mem_shiftCluster_iff B k _ z
    rw [heq]
    exact (measurableSet_mem_clusterTraj B T' _).preimage measurable_snd
  exact measurableSet_iff_sets
    (s := {p : TrajSeq B × TrajSeq B | z ∈ clusterTraj B p.1 T})
    (t := {p : TrajSeq B × TrajSeq B | z ∈ shiftCluster B k (clusterTraj B p.2 T')}) hA hB

/-- The prefix of the uniform driving law is the product of uniform walk laws. -/
theorem idlaMeasure_prefix (B : Base) (T : ℕ) :
    (idlaMeasure B).map (fun ω : TrajSeq B => fun i : Fin T => ω i) =
      Measure.pi fun _ : Fin T => walkLawUniform B := by
  have hD : Measurable (fun ω : TrajSeq B => ((fun i : Fin T => ω i), (fun s : ℕ => ω (T + s)))) :=
    (measurable_pi_iff.mpr fun i => measurable_pi_apply _).prodMk
      (measurable_pi_iff.mpr fun s => measurable_pi_apply _)
  have h := congrArg (Measure.map Prod.fst)
    (infinitePi_split_map (X := ℕ → Site B) T (walkLawUniform B))
  rw [Measure.map_map measurable_fst hD, Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

/-- The first `T` walkers of a driving-sequence coupling are product-distributed when the first
marginal is the driving law. -/
theorem prefix_map_fst (B : Base) (T : ℕ) (μ : Measure (TrajSeq B × TrajSeq B))
    (hμ : μ.map Prod.fst = idlaMeasure B) :
    μ.map (fun y : TrajSeq B × TrajSeq B => fun i : Fin T => y.1 i) =
      Measure.pi fun _ : Fin T => walkLawUniform B := by
  have hm : Measurable (fun ω : TrajSeq B => fun i : Fin T => ω i) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  rw [show (fun y : TrajSeq B × TrajSeq B => fun i : Fin T => y.1 i) =
      (fun ω : TrajSeq B => fun i : Fin T => ω i) ∘ Prod.fst from rfl,
    ← Measure.map_map hm measurable_fst, hμ]
  exact idlaMeasure_prefix B T

/-- The first `T'` walkers of a driving-sequence coupling are product-distributed when the second
marginal is the driving law. -/
theorem prefix_map_snd (B : Base) (T : ℕ) (μ : Measure (TrajSeq B × TrajSeq B))
    (hμ : μ.map Prod.snd = idlaMeasure B) :
    μ.map (fun y : TrajSeq B × TrajSeq B => fun i : Fin T => y.2 i) =
      Measure.pi fun _ : Fin T => walkLawUniform B := by
  have hm : Measurable (fun ω : TrajSeq B => fun i : Fin T => ω i) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  rw [show (fun y : TrajSeq B × TrajSeq B => fun i : Fin T => y.2 i) =
      (fun ω : TrajSeq B => fun i : Fin T => ω i) ∘ Prod.snd from rfl,
    ← Measure.map_map hm measurable_snd, hμ]
  exact idlaMeasure_prefix B T

/-- The first walks of independent future pairs are independent uniform walks. -/
theorem futureTail_fst (B : Base) (k : ℕ) :
    (Measure.infinitePi fun _ : ℕ => futurePair B k).map
      (fun q : ℕ → (ℕ → Site B) × (ℕ → Site B) => fun s : ℕ => (q s).1) =
      Measure.infinitePi fun _ : ℕ => walkLawUniform B := by
  have h := Measure.infinitePi_map_pi (μ := fun _ : ℕ => futurePair B k)
    (f := fun _ : ℕ => (Prod.fst : (ℕ → Site B) × (ℕ → Site B) → ℕ → Site B))
    (fun _ => measurable_fst)
  simpa only [futurePair_fst] using h

/-- The second walks of independent future pairs are independent uniform walks. -/
theorem futureTail_snd (B : Base) (k : ℕ) :
    (Measure.infinitePi fun _ : ℕ => futurePair B k).map
      (fun q : ℕ → (ℕ → Site B) × (ℕ → Site B) => fun s : ℕ => (q s).2) =
      Measure.infinitePi fun _ : ℕ => walkLawUniform B := by
  have h := Measure.infinitePi_map_pi (μ := fun _ : ℕ => futurePair B k)
    (f := fun _ : ℕ => (Prod.snd : (ℕ → Site B) × (ℕ → Site B) → ℕ → Site B))
    (fun _ => measurable_snd)
  simpa only [futurePair_snd] using h

/-- Concatenating independent prefixes, with the law of the prefix, and independent tails gives
the infinite product of uniform walk laws. -/
theorem splice_map_law {Y Z : Type*} [MeasurableSpace Y] [MeasurableSpace Z] (B : Base) (T : ℕ)
    (μ₀ : Measure Y) (P : Measure Z) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure P]
    (pre : Y → Fin T → ℕ → Site B) (tl : Z → ℕ → ℕ → Site B)
    (hpre : Measurable pre) (htl : Measurable tl)
    (hpre_law : μ₀.map pre = Measure.pi fun _ : Fin T => walkLawUniform B)
    (htl_law : P.map tl = Measure.infinitePi fun _ : ℕ => walkLawUniform B) :
    (μ₀.prod P).map (fun x : Y × Z => splitAppend T (pre x.1, tl x.2)) =
      Measure.infinitePi fun _ : ℕ => walkLawUniform B := by
  have hf : (fun x : Y × Z => splitAppend T (pre x.1, tl x.2)) =
      splitAppend T ∘ Prod.map pre tl := rfl
  rw [hf, ← Measure.map_map (measurable_splitAppend (X := ℕ → Site B) T) (hpre.prodMap htl),
    ← Measure.map_prod_map μ₀ P hpre htl, hpre_law, htl_law]
  exact infinitePi_split (X := ℕ → Site B) T (walkLawUniform B)

/-- The coupled driving pair: the first `T` walkers of the first sequence and the first `T'` walkers
of the second come from a prefix coupling, and each later walker index is driven by the future
pair at that index. -/
def futureSplice (B : Base) (T T' : ℕ)
    (x : (TrajSeq B × TrajSeq B) × (ℕ → (ℕ → Site B) × (ℕ → Site B))) :
    TrajSeq B × TrajSeq B :=
  (splitAppend T ((fun i : Fin T => x.1.1 i), fun s => (x.2 s).1),
    splitAppend T' ((fun i : Fin T' => x.1.2 i), fun s => (x.2 s).2))

/-- The coupled driving pair is measurable. -/
theorem measurable_futureSplice (B : Base) (T T' : ℕ) : Measurable (futureSplice B T T') := by
  have m1 : Measurable (fun x : (TrajSeq B × TrajSeq B) × (ℕ → (ℕ → Site B) × (ℕ → Site B)) =>
      ((fun i : Fin T => x.1.1 i), fun s => (x.2 s).1)) := by
    fun_prop
  have m2 : Measurable (fun x : (TrajSeq B × TrajSeq B) × (ℕ → (ℕ → Site B) × (ℕ → Site B)) =>
      ((fun i : Fin T' => x.1.2 i), fun s => (x.2 s).2)) := by
    fun_prop
  exact ((measurable_splitAppend (X := ℕ → Site B) T).comp m1).prodMk
    ((measurable_splitAppend (X := ℕ → Site B) T').comp m2)

/-- The first walk of the coupled pair agrees with the first walk of the prefix coupling before
time `T`. -/
theorem futureSplice_fst_lt (B : Base) (T T' : ℕ)
    (x : (TrajSeq B × TrajSeq B) × (ℕ → (ℕ → Site B) × (ℕ → Site B))) (j : ℕ) (hj : j < T) :
    (futureSplice B T T' x).1 j = x.1.1 j :=
  splitAppend_lt T _ ⟨j, hj⟩

/-- The second walk of the coupled pair agrees with the second prefix before time `T'`. -/
theorem futureSplice_snd_lt (B : Base) (T T' : ℕ)
    (x : (TrajSeq B × TrajSeq B) × (ℕ → (ℕ → Site B) × (ℕ → Site B))) (j : ℕ) (hj : j < T') :
    (futureSplice B T T' x).2 j = x.1.2 j :=
  splitAppend_lt T' _ ⟨j, hj⟩

/-- At the later walker `T + s` the first walk of the coupled pair is the first walk of the
`s`-th future pair. -/
theorem futureSplice_fst_ge (B : Base) (T T' : ℕ)
    (x : (TrajSeq B × TrajSeq B) × (ℕ → (ℕ → Site B) × (ℕ → Site B))) (s : ℕ) :
    (futureSplice B T T' x).1 (T + s) = (x.2 s).1 := by
  show splitAppend T _ (T + s) = (x.2 s).1
  rw [splitAppend_ge T _ (Nat.le_add_right T s), Nat.add_sub_cancel_left]

/-- At the later walker `T' + s` the second walk of the coupled pair is the second walk of the
`s`-th future pair. -/
theorem futureSplice_snd_ge (B : Base) (T T' : ℕ)
    (x : (TrajSeq B × TrajSeq B) × (ℕ → (ℕ → Site B) × (ℕ → Site B))) (s : ℕ) :
    (futureSplice B T T' x).2 (T' + s) = (x.2 s).2 := by
  show splitAppend T' _ (T' + s) = (x.2 s).2
  rw [splitAppend_ge T' _ (Nat.le_add_right T' s), Nat.add_sub_cancel_left]

/-- Lift an endpoint coupling of two finite clusters to a coupling of whole driving sequences whose
clusters agree up to the shift `k` at every later time, except on an event of the same endpoint
bound. The two marginals are the driving law `idlaMeasure B`. -/
theorem lift_cluster_coupling_future (B : Base) (T T' k : ℕ) (ε : ℝ)
    (hc : ClusterCoupling B (flatClusterLaw B T) (flatClusterLaw B T') k ε) :
    ∃ μ : Measure (TrajSeq B × TrajSeq B), μ.map Prod.fst = idlaMeasure B ∧
      μ.map Prod.snd = idlaMeasure B ∧
      μ {p | ∀ s : ℕ, clusterTraj B p.1 (T + s) = shiftCluster B k (clusterTraj B p.2 (T' + s))}ᶜ
        ≤ ENNReal.ofReal ε := by
  obtain ⟨μ₀, hμf, hμg, hμe⟩ := lift_cluster_coupling B T T' k ε hc
  haveI : IsProbabilityMeasure μ₀ := isProbabilityMeasure_of_map_fst μ₀ (idlaMeasure B) hμf
  have hpre1 : Measurable (fun y : TrajSeq B × TrajSeq B => fun i : Fin T => y.1 i) :=
    measurable_pi_iff.mpr fun i => (measurable_pi_apply (i : ℕ)).comp measurable_fst
  have hpre2 : Measurable (fun y : TrajSeq B × TrajSeq B => fun i : Fin T' => y.2 i) :=
    measurable_pi_iff.mpr fun i => (measurable_pi_apply (i : ℕ)).comp measurable_snd
  have htl1 : Measurable (fun q : ℕ → (ℕ → Site B) × (ℕ → Site B) => fun s : ℕ => (q s).1) :=
    measurable_pi_iff.mpr fun s => measurable_fst.comp (measurable_pi_apply s)
  have htl2 : Measurable (fun q : ℕ → (ℕ → Site B) × (ℕ → Site B) => fun s : ℕ => (q s).2) :=
    measurable_pi_iff.mpr fun s => measurable_snd.comp (measurable_pi_apply s)
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (TrajSeq B × TrajSeq B),
      μ = (μ₀.prod (Measure.infinitePi fun _ : ℕ => futurePair B k)).map (futureSplice B T T') :=
    ⟨_, rfl⟩
  have hfst : μ.map Prod.fst = idlaMeasure B := by
    rw [hμ, Measure.map_map measurable_fst (measurable_futureSplice B T T')]
    exact splice_map_law B T μ₀ _ (fun y : TrajSeq B × TrajSeq B => fun i : Fin T => y.1 i)
      (fun q : ℕ → (ℕ → Site B) × (ℕ → Site B) => fun s : ℕ => (q s).1) hpre1 htl1
      (prefix_map_fst B T μ₀ hμf) (futureTail_fst B k)
  have hsnd : μ.map Prod.snd = idlaMeasure B := by
    rw [hμ, Measure.map_map measurable_snd (measurable_futureSplice B T T')]
    exact splice_map_law B T' μ₀ _ (fun y : TrajSeq B × TrajSeq B => fun i : Fin T' => y.2 i)
      (fun q : ℕ → (ℕ → Site B) × (ℕ → Site B) => fun s : ℕ => (q s).2) hpre2 htl2
      (prefix_map_snd B T' μ₀ hμg) (futureTail_snd B k)
  have hend : μ {p : TrajSeq B × TrajSeq B |
      clusterTraj B p.1 T = shiftCluster B k (clusterTraj B p.2 T')}ᶜ ≤ ENNReal.ofReal ε := by
    rw [hμ, Measure.map_apply (measurable_futureSplice B T T') (measurableSet_shift_endpoint B T T' k).compl]
    have hset : futureSplice B T T' ⁻¹' {p : TrajSeq B × TrajSeq B |
        clusterTraj B p.1 T = shiftCluster B k (clusterTraj B p.2 T')}ᶜ =
        {p : TrajSeq B × TrajSeq B | clusterTraj B p.1 T = shiftCluster B k (clusterTraj B p.2 T')}ᶜ ×ˢ
          (Set.univ : Set (ℕ → (ℕ → Site B) × (ℕ → Site B))) := by
      ext x
      have h1 : clusterTraj B (futureSplice B T T' x).1 T = clusterTraj B x.1.1 T :=
        clusterTraj_congr B (fun j hj => futureSplice_fst_lt B T T' x j hj)
      have h2 : clusterTraj B (futureSplice B T T' x).2 T' = clusterTraj B x.1.2 T' :=
        clusterTraj_congr B (fun j hj => futureSplice_snd_lt B T T' x j hj)
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_prod, Set.mem_univ, and_true,
        Set.mem_setOf_eq, h1, h2]
    rw [hset, Measure.prod_prod, measure_univ, mul_one]
    exact hμe
  have hsp : ∀ s : ℕ, ∀ᵐ p ∂μ, ∃ τ : ℕ, (∀ i < τ, (p.1 (T + s) i).2 ≤ (k : ℤ)) ∧
      ∀ n : ℕ, p.1 (T + s) (τ + n) = outerShift B (k : ℤ) (p.2 (T' + s) n) := by
    intro s
    have hG : ∀ᵐ q ∂(Measure.infinitePi fun _ : ℕ => futurePair B k), SplicedPair B k (q s) := by
      have hev : Measurable (fun q : ℕ → (ℕ → Site B) × (ℕ → Site B) => q s) :=
        measurable_pi_apply s
      refine ae_of_ae_map (p := fun y : (ℕ → Site B) × (ℕ → Site B) => SplicedPair B k y)
        hev.aemeasurable ?_
      rw [Measure.infinitePi_map_eval]
      exact futurePair_splice B k
    have hGμ : ∀ᵐ x ∂(μ₀.prod (Measure.infinitePi fun _ : ℕ => futurePair B k)),
        SplicedPair B k (x.2 s) := by
      refine ae_of_ae_map (p := fun y : ℕ → (ℕ → Site B) × (ℕ → Site B) => SplicedPair B k (y s))
        measurable_snd.aemeasurable ?_
      rw [Measure.map_snd_prod, measure_univ, one_smul]
      exact hG
    rw [hμ]
    refine (ae_map_iff (measurable_futureSplice B T T').aemeasurable
      (measurableSet_splice_pair B k (T + s) (T' + s))).mpr ?_
    filter_upwards [hGμ] with x hx
    obtain ⟨τ, h1, h2⟩ := hx
    simp only [futureSplice_fst_ge, futureSplice_snd_ge]
    exact ⟨τ, h1, h2⟩
  exact ⟨μ, hfst, hsnd, future_cluster_bound B T T' k ε μ hfst hsp hend⟩

end IdlaCyl.Reduction
