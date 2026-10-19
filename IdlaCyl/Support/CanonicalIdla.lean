/-
Canonical IDLA clusters, from an arbitrary seed and from the flat configuration.

`tex:1330-1331`, `tex:1402`, `tex:1406-1410`, `tex:265`, `tex:263-265`.
-/
import IdlaCyl.Support.Exit
import IdlaCyl.Support.Canonical
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IdlaCyl

/-- A sequence of independent walk trajectories, indexed by the order they are released
(`tex:1402`, "`ω = (ω_1, ω_2, …)`"). -/
abbrev TrajSeq (B : Base) : Type := ℕ → (ℕ → Site B)

/-- The uniform law on layer `k` of the cylinder (`tex:265`, "chosen uniformly from
`V_N × {0}`", generalised to an arbitrary layer so `walkLawUniform` can be obtained by
induction from `walkLawUniformAt`). -/
noncomputable def layerLawAt (B : Base) (k : ℤ) : Measure (Site B) :=
  Measure.sum fun x : B.V => ((B.card : ℝ≥0∞))⁻¹ • Measure.dirac ((x, k) : Site B)

/-- The uniform law on layer `0` (`tex:265`). -/
noncomputable def layerLaw (B : Base) : Measure (Site B) := layerLawAt B 0

instance layerLawAt_isProbability (B : Base) (k : ℤ) : IsProbabilityMeasure (layerLawAt B k) := by
  have hcard_pos : 0 < B.card := lt_of_lt_of_le (by norm_num) B.nontrivial
  constructor
  unfold layerLawAt
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  show (B.card : ℝ≥0∞) * (B.card : ℝ≥0∞)⁻¹ = 1
  rw [ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr hcard_pos.ne') (ENNReal.natCast_ne_top _)]

instance layerLaw_isProbability (B : Base) : IsProbabilityMeasure (layerLaw B) :=
  layerLawAt_isProbability B 0

/-- The law of a cylinder walk started uniformly on layer `k` (generalisation of
`walkLawUniform`, needed for the induction underlying `walkLawUniformAt_eq_bind`). -/
noncomputable def walkLawUniformAt (B : Base) (k : ℤ) : Measure (ℕ → Site B) :=
  ProbabilityTheory.Kernel.trajMeasure (layerLawAt B k) (cylITKernel B)

/-- The law of a cylinder walk started uniformly on layer `0` (`tex:265`). -/
noncomputable def walkLawUniform (B : Base) : Measure (ℕ → Site B) := walkLawUniformAt B 0

instance walkLawUniformAt_isProbability (B : Base) (k : ℤ) :
    IsProbabilityMeasure (walkLawUniformAt B k) := by
  unfold walkLawUniformAt
  infer_instance

instance walkLawUniform_isProbability (B : Base) : IsProbabilityMeasure (walkLawUniform B) :=
  walkLawUniformAt_isProbability B 0

/-- Unfolding `walkPathLaw` through the definition of `Kernel.trajMeasure`: the law of the
walk from `x` is literally the Ionescu-Tulcea kernel `traj (cylITKernel B) 0` evaluated at the
(trivial, length-one) trajectory corresponding to `x`. -/
theorem walkPathLaw_eq_traj (B : Base) (x : Site B) :
    walkPathLaw B x
      = (Kernel.traj (cylITKernel B) 0)
          ((MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => Site B)).symm x) := by
  unfold walkPathLaw Kernel.trajMeasure
  rw [Measure.map_dirac'
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => Site B)).symm.measurable,
    Measure.dirac_bind
      (Kernel.traj (X := fun _ : ℕ => Site B) (cylITKernel B) 0).measurable]

/-- **The one-step disintegration of the release law.** The law of a walk started uniformly
on layer `k` is the mixture, over the uniform starting site, of the walk laws from each site
(`tex:1330-1331`, `tex:1402`). -/
theorem walkLawUniformAt_eq_bind (B : Base) (k : ℤ) :
    walkLawUniformAt B k = (layerLawAt B k).bind (walkPathLaw B) := by
  unfold walkLawUniformAt Kernel.trajMeasure
  set e := (MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => Site B)).symm
  set κ := cylITKernel B
  have hf : Measurable (fun x => Measure.dirac (e x)) :=
    Measure.measurable_dirac.comp e.measurable
  have hstep2 : (layerLawAt B k).map e
      = (layerLawAt B k).bind (fun x => Measure.dirac (e x)) :=
    (Measure.bind_dirac_eq_map (layerLawAt B k) e.measurable).symm
  rw [hstep2, Measure.bind_bind hf.aemeasurable
    (Kernel.traj (X := fun _ : ℕ => Site B) κ 0).measurable.aemeasurable]
  refine Measure.bind_congr_right (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [Measure.dirac_bind (Kernel.traj (X := fun _ : ℕ => Site B) κ 0).measurable]
  exact (walkPathLaw_eq_traj B x).symm

/-- `idlaMeasure` is the paper's driving law of independent cylinder walks, each started
uniformly on layer `0` (`tex:265`): the law of `Ã^{(m)}` at `m = ∞` before any site is
prescribed. -/
noncomputable def idlaMeasure (B : Base) : Measure (TrajSeq B) :=
  Measure.infinitePi fun _ : ℕ => walkLawUniform B

instance idlaMeasure_isProbability (B : Base) : IsProbabilityMeasure (idlaMeasure B) := by
  unfold idlaMeasure
  infer_instance

theorem idlaMeasure_univ (B : Base) : idlaMeasure B Set.univ = 1 := measure_univ

/-- Independent walks with *prescribed* starting sites: the driving law of the balanced
release `Ã^{(m)}` (`tex:1330-1331`) and of `le:mono-init`'s `ω = (ω_1, ω_2, …)` "with
prescribed starting sites" (`tex:1402`). -/
noncomputable def prescribedMeasure (B : Base) (start : ℕ → Site B) : Measure (TrajSeq B) :=
  Measure.infinitePi fun j => walkPathLaw B (start j)

instance prescribedMeasure_isProbability (B : Base) (start : ℕ → Site B) :
    IsProbabilityMeasure (prescribedMeasure B start) := by
  unfold prescribedMeasure
  infer_instance

theorem iIndepFun_traj (B : Base) :
    ProbabilityTheory.iIndepFun (fun j (ω : TrajSeq B) => ω j) (idlaMeasure B) := by
  have h := iIndepFun_infinitePi (P := fun _ : ℕ => walkLawUniform B)
    (X := fun _ : ℕ => (id : (ℕ → Site B) → ℕ → Site B)) (fun _ => measurable_id)
  exact h

/-- **Measurability of the finite-index product of walk laws in the start vector.**
For a fixed finite set `t` of "which walk" indices, the map sending a start vector to the
product of the corresponding walk laws is measurable: each factor is measurable because it is
a function *from* the countable, discrete space `Site B`, and a finite product of measurable
`ℝ≥0∞`-valued functions is measurable. -/
theorem measurable_pi_walkPathLaw (B : Base) (t : Finset ℕ) :
    Measurable (fun start : ℕ → Site B => Measure.pi fun j : t => walkPathLaw B (start j)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure generateFrom_pi.symm isPiSystem_pi
  rintro s ⟨u, -, rfl⟩
  simp_rw [Measure.pi_pi]
  exact Finset.measurable_prod Finset.univ fun j _ =>
    (measurable_of_countable fun x : Site B => walkPathLaw B x (u j)).comp
      (measurable_pi_apply (j : ℕ))

/-- **Measurability of `prescribedMeasure` in the start vector.** Needed to make sense of
`(Measure.infinitePi fun _ ↦ layerLaw B).bind (prescribedMeasure B)` in
`idlaMeasure_eq_bind_prescribed`. Reduces, cylinder set by cylinder set, to
`measurable_pi_walkPathLaw`. -/
theorem measurable_prescribedMeasure (B : Base) : Measurable (prescribedMeasure B) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  rintro s hs
  obtain ⟨t, T, hT, rfl⟩ := (mem_measurableCylinders s).mp hs
  have heq : (fun start : ℕ → Site B => prescribedMeasure B start (cylinder t T))
      = fun start => Measure.pi (fun j : t => walkPathLaw B (start j)) T :=
    funext fun start => Measure.infinitePi_cylinder (fun j => walkPathLaw B (start j)) hT
  rw [heq]
  exact (Measure.measurable_coe hT).comp (measurable_pi_walkPathLaw B t)

/-- **Disintegration over the start vector** (`tex:265`, "started at a site chosen
uniformly from `V_N × {0}`"). Conditionally on the starts, the walks are independent with
prescribed law. Required by `le:released`. -/
theorem idlaMeasure_eq_bind_prescribed (B : Base) :
    idlaMeasure B
      = (Measure.infinitePi fun _ : ℕ => layerLaw B).bind (prescribedMeasure B) := by
  symm
  unfold idlaMeasure
  apply Measure.eq_infinitePi
  intro s t ht
  have hmeas_pi : MeasurableSet (Set.pi s t) :=
    MeasurableSet.pi s.countable_toSet fun i _ => ht i
  rw [Measure.bind_apply hmeas_pi (measurable_prescribedMeasure B).aemeasurable]
  have hpt : ∀ start : ℕ → Site B,
      prescribedMeasure B start (Set.pi s t) = ∏ i ∈ s, walkPathLaw B (start i) (t i) :=
    fun start => Measure.infinitePi_pi (fun j => walkPathLaw B (start j)) (fun i _ => ht i)
  simp_rw [hpt]
  have hIndep : iIndepFun (fun i (start : ℕ → Site B) => walkPathLaw B (start i) (t i))
      (Measure.infinitePi fun _ : ℕ => layerLaw B) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => layerLaw B)
      (X := fun i (x : Site B) => walkPathLaw B x (t i))
      (fun i => measurable_of_countable _)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun s
    (fun i (start : ℕ → Site B) => walkPathLaw B (start i) (t i)) hIndep
    (fun i => (measurable_of_countable fun x : Site B => walkPathLaw B x (t i)).comp
      (measurable_pi_apply i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [(measurePreserving_eval_infinitePi (fun _ : ℕ => layerLaw B) i).lintegral_comp
      (measurable_of_countable fun x : Site B => walkPathLaw B x (t i)),
    ← Measure.bind_apply (ht i) (measurable_of_countable (walkPathLaw B)).aemeasurable]
  exact congrArg (fun μ => μ (t i)) (walkLawUniformAt_eq_bind B 0).symm

/-- `Φ_k(𝓑)` (`tex:1406-1410`): the cluster from seed `S` after `k` prescribed walks have
settled. -/
noncomputable def clusterFrom (B : Base) (S : Set (Site B)) (ω : TrajSeq B) :
    ℕ → Set (Site B)
  | 0 => S
  | k + 1 => clusterFrom B S ω k ∪ {exitSite' B (clusterFrom B S ω k) (ω k)}

/-- `A(t)`, the IDLA cluster from the flat configuration (`tex:263-265`). -/
noncomputable def clusterTraj (B : Base) (ω : TrajSeq B) (t : ℕ) : Set (Site B) :=
  clusterFrom B (R B 0) ω t

noncomputable def settleSite (B : Base) (ω : TrajSeq B) (t : ℕ) : Site B :=
  exitSite' B (clusterTraj B ω t) (ω t)

@[simp] theorem clusterFrom_zero (B : Base) (S : Set (Site B)) (ω : TrajSeq B) :
    clusterFrom B S ω 0 = S := rfl

theorem clusterFrom_succ (B : Base) (S : Set (Site B)) (ω : TrajSeq B) (k : ℕ) :
    clusterFrom B S ω (k + 1)
      = clusterFrom B S ω k ∪ {exitSite' B (clusterFrom B S ω k) (ω k)} := rfl

theorem clusterFrom_mono (B : Base) (S : Set (Site B)) (ω : TrajSeq B) {j k : ℕ} (h : j ≤ k) :
    clusterFrom B S ω j ⊆ clusterFrom B S ω k := by
  induction k, h using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ n _ ih => exact ih.trans Set.subset_union_left

theorem clusterFrom_congr (B : Base) (S : Set (Site B)) (ω ω' : TrajSeq B) :
    ∀ {k : ℕ}, (∀ j < k, ω j = ω' j) → clusterFrom B S ω k = clusterFrom B S ω' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    have hn : ∀ j < n, ω j = ω' j := fun j hj => h j (by omega)
    have heq : clusterFrom B S ω n = clusterFrom B S ω' n := ih hn
    have hωn : ω n = ω' n := h n (by omega)
    rw [clusterFrom_succ, clusterFrom_succ, heq, hωn]

theorem clusterTraj_eq_union (B : Base) (ω : TrajSeq B) (t : ℕ) :
    clusterTraj B ω t = R B 0 ∪ (Finset.range t).image (settleSite B ω) := by
  induction t with
  | zero => simp [clusterTraj]
  | succ n ih =>
    have hstep : clusterTraj B ω (n + 1) = clusterTraj B ω n ∪ {settleSite B ω n} :=
      clusterFrom_succ B (R B 0) ω n
    rw [hstep, ih, Finset.range_add_one, Finset.image_insert]
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Finset.coe_insert, Set.mem_insert_iff]
    tauto

end IdlaCyl
