/-
Finite-coefficient replacement target for the large-time reduction.
Source: paper/idla-cylinder-gff.tex, tex:270-282,1119-1136,1440-1453.

`pr_reduction_alpha` records an exact proposition, not an asserted theorem.
Its constants precede the base and the time. The scale is `Defs.sharp` and
both marginals are the full canonical driving law. No stochastic reduction
is assumed or proved in this file. The equality event is measurable.
-/
import IdlaCyl.Definitions.ShapeEvent
import IdlaCyl.Support.CanonicalMeas

namespace IdlaCyl

open MeasureTheory
open scoped ENNReal

namespace Reduction

/-- Translate an entire cluster vertically by a nonnegative integer. -/
def shiftCluster (B : Base) (k : ℕ) (A : Set (Site B)) : Set (Site B) :=
  (fun q : Site B => (q.1, q.2 + (k : ℤ))) '' A

@[simp] theorem shiftCluster_zero (B : Base) (A : Set (Site B)) :
    shiftCluster B 0 A = A := by
  simp only [shiftCluster, Nat.cast_zero, add_zero, Prod.eta, Set.image_id']

/-- Membership after translation is tested at the unique translated-back site. -/
theorem mem_shiftCluster (B : Base) (k : ℕ) (A : Set (Site B)) (q : Site B) :
    q ∈ shiftCluster B k A ↔ (q.1, q.2 - (k : ℤ)) ∈ A := by
  constructor
  · rintro ⟨x, hx, hxq⟩
    have hfst := congrArg Prod.fst hxq
    have hsnd := congrArg Prod.snd hxq
    have heq : x = (q.1, q.2 - (k : ℤ)) :=
      Prod.ext hfst (by dsimp only at hsnd; dsimp only; omega)
    rwa [← heq]
  · intro hq
    refine ⟨(q.1, q.2 - (k : ℤ)), hq, ?_⟩
    exact Prod.ext rfl (by dsimp only; omega)

/-- Integer restart shifts compose without rounding. -/
theorem shiftCluster_add (B : Base) (a b : ℕ) (A : Set (Site B)) :
    shiftCluster B a (shiftCluster B b A) = shiftCluster B (a + b) A := by
  ext q
  simp only [mem_shiftCluster, Nat.cast_add, sub_sub]

/-- The coupling's equality event is measurable, so its lower bound is a probability. -/
theorem measurableSet_cluster_eq_shift (B : Base) (T T' k : ℕ) :
    MeasurableSet {p : TrajSeq B × TrajSeq B |
      clusterTraj B p.1 T = shiftCluster B k (clusterTraj B p.2 T')} := by
  have hE : {p : TrajSeq B × TrajSeq B |
      clusterTraj B p.1 T = shiftCluster B k (clusterTraj B p.2 T')} =
      ⋂ q : Site B, {p : TrajSeq B × TrajSeq B |
        (q ∈ clusterTraj B p.1 T) ↔
          ((q.1, q.2 - (k : ℤ)) ∈ clusterTraj B p.2 T')} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.ext_iff, mem_shiftCluster]
  rw [hE]
  apply MeasurableSet.iInter
  intro q
  exact ((measurableSet_mem_clusterTraj B T q).preimage measurable_fst).iff
    ((measurableSet_mem_clusterTraj B T' (q.1, q.2 - (k : ℤ))).preimage measurable_snd)

/-- A correct first driving marginal already forces the coupling to be a probability measure. -/
theorem coupling_isProbability (B : Base) (μ : Measure (TrajSeq B × TrajSeq B))
    (hfst : μ.map (Prod.fst : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B) :
    IsProbabilityMeasure μ := by
  constructor
  calc
    μ Set.univ = (μ.map (Prod.fst : TrajSeq B × TrajSeq B → TrajSeq B)) Set.univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ]
    _ = 1 := by rw [hfst, measure_univ]

/-- A genuine full-driving-law coupling at zero shift, for every base and time. -/
theorem diagonal_coupling (B : Base) (T : ℕ) :
    ∃ μ : Measure (TrajSeq B × TrajSeq B),
      μ.map (Prod.fst : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
      μ.map (Prod.snd : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
      μ {p | clusterTraj B p.1 T = shiftCluster B 0 (clusterTraj B p.2 T)} = 1 := by
  let μ := (idlaMeasure B).map (fun ω : TrajSeq B => (ω, ω))
  have hdiag : Measurable (fun ω : TrajSeq B => (ω, ω)) :=
    measurable_id.prodMk measurable_id
  refine ⟨μ, ?_, ?_, ?_⟩
  · change ((idlaMeasure B).map (fun ω : TrajSeq B => (ω, ω))).map Prod.fst = _
    rw [Measure.map_map measurable_fst hdiag]
    exact Measure.map_id
  · change ((idlaMeasure B).map (fun ω : TrajSeq B => (ω, ω))).map Prod.snd = _
    rw [Measure.map_map measurable_snd hdiag]
    exact Measure.map_id
  · change (idlaMeasure B).map (fun ω : TrajSeq B => (ω, ω)) _ = 1
    rw [Measure.map_apply hdiag (measurableSet_cluster_eq_shift B T T 0)]
    have hpre : (fun ω : TrajSeq B => (ω, ω)) ⁻¹'
        {p : TrajSeq B × TrajSeq B |
          clusterTraj B p.1 T = shiftCluster B 0 (clusterTraj B p.2 T)} = Set.univ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_setOf_eq, shiftCluster_zero, Set.mem_univ]
    rw [hpre, measure_univ]

/-- A positive-time instance of the full-law coupling conclusion. -/
example (B : Base) :
    ∃ μ : Measure (TrajSeq B × TrajSeq B),
      μ.map (Prod.fst : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
      μ.map (Prod.snd : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
      μ {p | clusterTraj B p.1 1 = shiftCluster B 0 (clusterTraj B p.2 1)} = 1 :=
  diagonal_coupling B 1

end Reduction

/-- Exact unproved target, encoded as a proposition to check its header without a hole.
The real constant α is finite by its type; positivity prevents a vacuous negative scale.
The polynomial exponent is real, as in the requested large-time reduction. -/
def pr_reduction_alpha : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ m : ℝ, 1 ≤ m →
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℕ,
      ∀ B : Base, N₀ ≤ B.card → ∀ T : ℕ,
        α * Defs.sharp B ≤ (T : ℝ) → (T : ℝ) ≤ (B.card : ℝ) ^ m →
        ∃ T' k : ℕ,
          1 ≤ T' ∧ (T' : ℝ) ≤ α * Defs.sharp B ∧ T' + B.card * k = T ∧
          ∃ μ : Measure (TrajSeq B × TrajSeq B),
            μ.map (Prod.fst : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
            μ.map (Prod.snd : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
            ENNReal.ofReal (1 - (B.card : ℝ) ^ (-(ν + 1))) ≤
              μ {p | clusterTraj B p.1 T =
                Reduction.shiftCluster B k (clusterTraj B p.2 T')}

end IdlaCyl
