module

/-
Measurable outputs of the paused and fresh-resumed experiment.
Source: paper/idla-cylinder-gff.tex, tex:1385-1400.
Membership coordinates suffice even for a varying, infinite initial seed.
-/
public import IdlaCyl.Support.Outer.CommuteMeasurable

@[expose] public section

attribute [local instance] Classical.propDecidable

namespace IdlaCyl
open MeasureTheory ProbabilityTheory
noncomputable section

/-- Evaluating a varying measurable seed at a varying site is measurable. -/
theorem measurableSet_mem_seed (B : Base) {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Set (Site B)) (p : Ω → Site B)
    (hA : ∀ z, MeasurableSet {ω | z ∈ A ω}) (hp : Measurable p) :
    MeasurableSet {ω | p ω ∈ A ω} := by
  have heq : {ω | p ω ∈ A ω} = ⋃ z : Site B, p ⁻¹' {z} ∩ {ω | z ∈ A ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff]
    exact ⟨fun h => ⟨p ω, rfl, h⟩, by rintro ⟨z, rfl, h⟩; exact h⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun z => (hp (measurableSet_singleton z)).inter (hA z))

/-- Exit time is jointly measurable in a coordinatewise measurable seed and a walk. -/
theorem measurable_exitTime'_seed (B : Base) {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Set (Site B)) (X : Ω → (ℕ → Site B))
    (hA : ∀ z, MeasurableSet {ω | z ∈ A ω}) (hX : Measurable X) :
    Measurable (fun ω => exitTime' B (A ω) (X ω)) := by
  have hmem (n : ℕ) : MeasurableSet {ω | X ω n ∈ A ω} :=
    measurableSet_mem_seed B A (fun ω => X ω n) hA ((measurable_pi_apply n).comp hX)
  apply measurable_to_countable'
  intro t
  cases t with
  | coe n =>
      have heq : (fun ω => exitTime' B (A ω) (X ω)) ⁻¹' {(n : ℕ∞)} =
          {ω | X ω n ∉ A ω} ∩ ⋂ j : Fin n, {ω | X ω j ∈ A ω} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff,
          Set.mem_setOf_eq, Set.mem_iInter]
        rw [exitTime'_eq_coe_iff]
        exact and_congr_right (fun _ => ⟨fun h j => h j j.2,
          fun h j hj => h ⟨j, hj⟩⟩)
      rw [heq]
      exact (hmem n).compl.inter (MeasurableSet.iInter (fun j : Fin n => hmem j))
  | top =>
      have heq : (fun ω => exitTime' B (A ω) (X ω)) ⁻¹' {⊤} =
          ⋂ n : ℕ, {ω | X ω n ∈ A ω} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter,
          Set.mem_setOf_eq]
        constructor
        · intro h n
          exact not_not.mp (hittingAfter_eq_top_iff.mp h n (Nat.zero_le n))
        · intro h
          exact hittingAfter_eq_top_iff.mpr (fun n _ => not_not.mpr (h n))
      rw [heq]
      exact MeasurableSet.iInter hmem

/-- The total exit-site map remains measurable when the seed varies. -/
theorem measurable_exitSite'_seed (B : Base) {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Set (Site B)) (X : Ω → (ℕ → Site B))
    (hA : ∀ z, MeasurableSet {ω | z ∈ A ω}) (hX : Measurable X) :
    Measurable (fun ω => exitSite' B (A ω) (X ω)) := by
  have ht : Measurable (fun ω => WithTop.untopA (exitTime' B (A ω) (X ω))) :=
    (measurable_of_countable (fun t : ℕ∞ => WithTop.untopA t)).comp
      (measurable_exitTime'_seed B A X hA hX)
  have heval : Measurable (fun nY : ℕ × (ℕ → Site B) => nY.2 nY.1) := by
    apply measurable_from_prod_countable_right
    intro n
    exact measurable_pi_apply n
  exact heval.comp (ht.prodMk hX)

/-- Finite growth from any measurable seed has measurable membership coordinates. -/
theorem measurableSet_mem_clusterFrom_seed (B : Base) {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Set (Site B)) (ω : Ω → TrajSeq B)
    (hA : ∀ z, MeasurableSet {s | z ∈ A s}) (hω : Measurable ω)
    (n : ℕ) (z : Site B) :
    MeasurableSet {s | z ∈ clusterFrom B (A s) (ω s) n} := by
  induction n generalizing z with
  | zero => exact hA z
  | succ n ih =>
      have hexit : Measurable (fun s =>
          exitSite' B (clusterFrom B (A s) (ω s) n) (ω s n)) :=
        measurable_exitSite'_seed B _ _ (fun z => ih z)
          ((measurable_pi_apply n).comp hω)
      have heq : {s | z ∈ clusterFrom B (A s) (ω s) (n + 1)} =
          {s | z ∈ clusterFrom B (A s) (ω s) n} ∪
            (fun s => exitSite' B (clusterFrom B (A s) (ω s) n) (ω s n)) ⁻¹' {z} := by
        ext s
        simp only [clusterFrom_succ, Set.mem_setOf_eq, Set.mem_union,
          Set.mem_singleton_iff, Set.mem_preimage, eq_comm]
      rw [heq]
      exact (ih z).union (hexit (measurableSet_singleton z))

/-- The ordinary finite cluster has a measurable Boolean occupation output. -/
theorem measurable_clusterCode_clusterTraj (B : Base) (T : ℕ) :
    Measurable (fun ω : TrajSeq B => clusterCode B (clusterTraj B ω T)) := by
  apply measurable_pi_iff.mpr
  intro z
  exact Measurable.ite (measurableSet_mem_clusterTraj B T z) measurable_const measurable_const

/-- The first-stage paused seed has measurable membership coordinates. -/
theorem measurableSet_mem_pausedCluster (B : Base) (h : ℤ) (T : ℕ) (z : Site B) :
    MeasurableSet {ω : TrajSeq B | z ∈ pausedCluster B h ω T} := by
  exact (((stoppedFiltration B h).le T) _
    (measurableSet_mem_stoppedCluster_filtration B h (le_refl T) z)).inter
      (MeasurableSet.const _)

/-- Fresh resumption has a measurable output, including exceptional input paths. -/
theorem measurable_clusterCode_resumedCluster (B : Base) (h : ℤ) (T : ℕ) :
    Measurable (fun p : TrajSeq B × TrajSeq B =>
      clusterCode B (resumedCluster B h T p.1 p.2)) := by
  have hn : Measurable (fun p : TrajSeq B × TrajSeq B =>
      (pauseList B h T p.1).length) :=
    (measurable_of_countable List.length).comp ((measurable_pauseList B h T).comp measurable_fst)
  have hfixed (n : ℕ) (z : Site B) :
      MeasurableSet {p : TrajSeq B × TrajSeq B |
        z ∈ clusterFrom B (pausedCluster B h p.1 T) p.2 n} :=
    measurableSet_mem_clusterFrom_seed B _ _
      (fun z => measurable_fst (measurableSet_mem_pausedCluster B h T z)) measurable_snd n z
  apply measurable_pi_iff.mpr
  intro z
  have heq : {p : TrajSeq B × TrajSeq B | z ∈ resumedCluster B h T p.1 p.2} =
      ⋃ n : ℕ, (fun p : TrajSeq B × TrajSeq B => (pauseList B h T p.1).length) ⁻¹' {n} ∩
        {p | z ∈ clusterFrom B (pausedCluster B h p.1 T) p.2 n} := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_setOf_eq, resumedCluster]
    exact ⟨fun hp => ⟨_, rfl, hp⟩, by rintro ⟨n, rfl, hp⟩; exact hp⟩
  have hmem : MeasurableSet {p : TrajSeq B × TrajSeq B |
      z ∈ resumedCluster B h T p.1 p.2} := by
    rw [heq]
    exact MeasurableSet.iUnion (fun n => (hn (measurableSet_singleton n)).inter (hfixed n z))
  exact Measurable.ite hmem measurable_const measurable_const

/-- All four probability/measurability clauses of the task-7 contract. -/
theorem resumedCluster_law_interfaces (B : Base) (h : ℤ) (T : ℕ) :
    IsProbabilityMeasure (resumeLaw B h T) ∧
    (resumeLaw B h T).map Prod.fst = idlaMeasure B ∧
    Measurable (fun p : TrajSeq B × TrajSeq B =>
      clusterCode B (resumedCluster B h T p.1 p.2)) ∧
    Measurable (fun ω : TrajSeq B => clusterCode B (clusterTraj B ω T)) :=
  ⟨inferInstance, resumeLaw_map_fst B h T,
    measurable_clusterCode_resumedCluster B h T, measurable_clusterCode_clusterTraj B T⟩

example : IsProbabilityMeasure (resumeLaw PrInnerTail.K2 1 0) := inferInstance

example : Measurable (fun p : TrajSeq PrInnerTail.K2 × TrajSeq PrInnerTail.K2 =>
    clusterCode PrInnerTail.K2 (resumedCluster PrInnerTail.K2 2 3 p.1 p.2)) :=
  measurable_clusterCode_resumedCluster PrInnerTail.K2 2 3

end
end IdlaCyl
