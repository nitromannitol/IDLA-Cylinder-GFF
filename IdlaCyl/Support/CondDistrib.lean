/-
The conditional law of the next settling site given the past.

`paper/idla-cylinder-gff.tex:895-897`: the martingale increments of the
fluctuation CLT are with respect to the natural filtration
`𝓕_k = σ(A(0),…,A(k))`, so the settling site `(X_{k+1},Y_{k+1})` is
conditionally independent of `𝓕_k` with the law of the next walk.  Building on
`IdlaCyl.indep_settleSite_omega` (`Support/CondLaw.lean`), this file gives

* `condDistrib_settleSites_omega`: under `idlaMeasure B`, the regular
  conditional distribution of the `k`-th walk `ω k` given the settle-site tuple
  `(settleSite B ω j)_{j<k}` is a.s. the constant kernel `walkLawUniform B`;
* `condExp_settleSite_eq_integral`: consequently the conditional expectation of
  `f (settleSite B · k)` given `𝓕_k` is the `ω`-dependent integral of `f` at the
  exit site of an independent walk from the current cluster,
  `∫ w, f (exitSite' B (clusterTraj B ω k) w) ∂(walkLawUniform B)`.

This is the input of the optional-stopping core `condExp_settleSite_eq_zero`:
feeding a discrete-harmonic, zero-horizontal-average
`ψ` makes the integral vanish, which is the martingale property of `le:martingale`.
-/
import IdlaCyl.Support.CondLaw
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Independence.Basic

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable (B : Base)

/-- **The conditional law of the next walk given the past.**  Under
`idlaMeasure B`, `condDistrib (ω ↦ ω k) (ω ↦ (settleSite B ω j)_{j<k})` is a.s.
the constant kernel `walkLawUniform B`: the `k`-th walk is independent of the
settle-site tuple, so conditioning on the tuple leaves its law unchanged. -/
theorem condDistrib_settleSites_omega (B : Base) (k : ℕ) :
    condDistrib (fun ω : TrajSeq B => ω k)
      (fun ω : TrajSeq B => fun j : {j : ℕ // j < k} => settleSite B ω j)
      (idlaMeasure B)
      =ᵐ[(idlaMeasure B).map
        (fun ω : TrajSeq B => fun j : {j : ℕ // j < k} => settleSite B ω j)]
      fun _ => walkLawUniform B := by
  let X : TrajSeq B → ({j : ℕ // j < k} → Site B) := fun ω j => settleSite B ω j
  let Y : TrajSeq B → (ℕ → Site B) := fun ω => ω k
  change condDistrib Y X (idlaMeasure B)
    =ᵐ[Measure.map X (idlaMeasure B)] fun _ => walkLawUniform B
  have hX : Measurable X := measurable_pi_iff.mpr fun j => measurable_settleSite B j
  have hY : AEMeasurable Y (idlaMeasure B) := (measurable_pi_apply k).aemeasurable
  have hmapY : Measure.map Y (idlaMeasure B) = walkLawUniform B := by
    rw [idlaMeasure]
    exact Measure.infinitePi_map_eval _ k
  have hindep : IndepFun X Y (idlaMeasure B) := by
    simpa only [X, Y] using indep_settleSite_omega B k
  have hprod : Measure.map (fun ω => (X ω, Y ω)) (idlaMeasure B)
      = (Measure.map X (idlaMeasure B)).prod (Measure.map Y (idlaMeasure B)) :=
    IndepFun.map_prod_eq_prod_map_map hX.aemeasurable hY hindep
  have hκ : Measure.map (fun ω => (X ω, Y ω)) (idlaMeasure B)
      = Measure.map X (idlaMeasure B) ⊗ₘ Kernel.const _ (walkLawUniform B) := by
    rw [hprod, hmapY, Measure.compProd_const]
  have hres := condDistrib_ae_eq_of_measure_eq_compProd (μ := idlaMeasure B) X hY hκ
  have hconst : (⇑(Kernel.const ({j : ℕ // j < k} → Site B) (walkLawUniform B))
      : ({j : ℕ // j < k} → Site B) → Measure (ℕ → Site B)) = fun _ => walkLawUniform B :=
    funext fun x => Kernel.const_apply _ x
  rwa [hconst] at hres

/-- **The next settle site is determined by the past tuple and the next walk.**
`clusterTraj B ω k` is `R_0` together with the previous settling sites
(`clusterTraj_eq_union`, equivalently `measurable_settleSite_cluster_eq`), so
`settleSite B ω k` is a function of `(settleSite B ω j)_{j<k}` and `ω k` alone. -/
theorem clusterTraj_eq_union_settleTuple (B : Base) (k : ℕ) (ω : TrajSeq B) :
    R B 0 ∪ Set.range (fun j : {j : ℕ // j < k} => settleSite B ω j)
      = clusterTraj B ω k := by
  have h := measurable_settleSite_cluster_eq B (t := k) (ω := ω)
    (s := fun j : Fin k => settleSite B ω j) (fun _ => rfl)
  rw [h]
  congr 1
  ext p
  simp only [Set.mem_range]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨⟨j.1, j.2⟩, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨⟨j.1, j.2⟩, rfl⟩

/-- **The conditional-expectation form of the next settle site.**  For an
integrable `f (settleSite B · k)`, the conditional expectation given
`𝓕_k = σ(A(0),…,A(k))` is the integral of `f` at the exit site of an independent
uniform-start cylinder walk from the current cluster `clusterTraj B ω k`. -/
theorem condExp_settleSite_eq_integral (B : Base) (k : ℕ) (f : Site B → ℝ)
    (hf : StronglyMeasurable f)
    (hint : Integrable (fun ω : TrajSeq B => f (settleSite B ω k)) (idlaMeasure B)) :
    (idlaMeasure B)[fun ω : TrajSeq B => f (settleSite B ω k) | idlaFiltration B k]
      =ᵐ[idlaMeasure B]
      fun ω : TrajSeq B =>
        ∫ w : ℕ → Site B, f (exitSite' B (clusterTraj B ω k) w) ∂(walkLawUniform B) := by
  let X : TrajSeq B → ({j : ℕ // j < k} → Site B) := fun ω j => settleSite B ω j
  let Y : TrajSeq B → (ℕ → Site B) := fun ω => ω k
  have hX : Measurable X := measurable_pi_iff.mpr fun j => measurable_settleSite B j
  have hY : AEMeasurable Y (idlaMeasure B) := (measurable_pi_apply k).aemeasurable
  -- the next settle site as a function of the past tuple and the next walk
  let g : ({j : ℕ // j < k} → Site B) × (ℕ → Site B) → ℝ :=
    fun p => f (exitSite' B (R B 0 ∪ Set.range p.1) p.2)
  have hg_meas : Measurable g := by
    refine measurable_of_Iio fun c => ?_
    have hset : g ⁻¹' Set.Iio c
        = ⋃ s : ({j : ℕ // j < k} → Site B),
            ({s} : Set ({j : ℕ // j < k} → Site B)) ×ˢ
              {w : ℕ → Site B | f (exitSite' B (R B 0 ∪ Set.range s) w) < c} := by
      ext p
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_iUnion, Set.mem_prod,
        Set.mem_singleton_iff, Set.mem_setOf_eq, g]
      constructor
      · intro hp
        exact ⟨p.1, rfl, hp⟩
      · rintro ⟨s, hs, hp⟩
        rw [← hs] at hp
        exact hp
    rw [hset]
    refine MeasurableSet.iUnion fun s => ?_
    exact MeasurableSet.prod (measurableSet_singleton s)
      ((measurableSet_Iio (a := c)).preimage
        (hf.measurable.comp (measurable_exitSite' B (R B 0 ∪ Set.range s))))
  have hg_eq (ω : TrajSeq B) : g (X ω, Y ω) = f (settleSite B ω k) := by
    dsimp only [g, Y]
    rw [clusterTraj_eq_union_settleTuple B k ω]
    rfl
  have hint' : Integrable (fun ω : TrajSeq B => g (X ω, Y ω)) (idlaMeasure B) :=
    hint.congr (Filter.Eventually.of_forall fun ω => (hg_eq ω).symm)
  have hf_int : Integrable g (Measure.map (fun ω => (X ω, Y ω)) (idlaMeasure B)) :=
    (integrable_map_measure hg_meas.aestronglyMeasurable (hX.aemeasurable.prodMk hY)).mpr hint'
  have hcond := condExp_prod_ae_eq_integral_condDistrib'
    (μ := idlaMeasure B) (X := X) (Y := Y) (f := g) hX hY hf_int
  have hcd : condDistrib Y X (idlaMeasure B)
      =ᵐ[Measure.map X (idlaMeasure B)] fun _ => walkLawUniform B := by
    simpa only [X, Y] using condDistrib_settleSites_omega B k
  have hcd_pull : ∀ᵐ ω ∂(idlaMeasure B),
      condDistrib Y X (idlaMeasure B) (X ω) = walkLawUniform B :=
    ae_of_ae_map hX.aemeasurable hcd
  have hR : (fun ω : TrajSeq B =>
        ∫ y, g (X ω, y) ∂(condDistrib Y X (idlaMeasure B) (X ω)))
      =ᵐ[idlaMeasure B] (fun ω : TrajSeq B => ∫ y, g (X ω, y) ∂(walkLawUniform B)) := by
    filter_upwards [hcd_pull] with ω hω
    rw [hω]
  have hB : (fun ω : TrajSeq B => ∫ y, g (X ω, y) ∂(walkLawUniform B))
      =ᵐ[idlaMeasure B]
      (fun ω : TrajSeq B =>
        ∫ w, f (exitSite' B (clusterTraj B ω k) w) ∂(walkLawUniform B)) := by
    filter_upwards with ω
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    dsimp only [g]
    rw [clusterTraj_eq_union_settleTuple B k ω]
  have hmono : (idlaMeasure B)[fun ω : TrajSeq B => f (settleSite B ω k) | idlaFiltration B k]
      =ᵐ[idlaMeasure B]
      (idlaMeasure B)[fun ω : TrajSeq B => g (X ω, Y ω) |
        MeasurableSpace.comap X inferInstance] := by
    rw [idlaFiltration_eq_comap_tuple B k]
    exact condExp_congr_ae (Filter.Eventually.of_forall fun ω => (hg_eq ω).symm)
  exact hmono.trans (hcond.trans (hR.trans hB))

end IdlaCyl
