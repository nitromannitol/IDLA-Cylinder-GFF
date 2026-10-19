/-
Measure-level transitivity invariance of the IDLA driving law (`tex:832-836`).

For a base automorphism `σ : B.graph ≃g B.graph`, the lifted horizontal
bijection `horIso B σ (x, y) = (σ x, y)` of `Support/FirstHit.lean` transports a
whole trajectory family coordinatewise:

  `transportTraj σ w = fun j n => horIso σ (w j n)`.

The paper's vertex-transitivity step (`tex:832-836`, the measure statement
missing from the pathwise half in `Support/Equivariance.lean`) is

  `(idlaMeasure B).map (transportTraj σ) = idlaMeasure B`.

We prove it by pushing the invariance through the canonical construction:
`layerLawAt` is uniform on the layer and so `horIso`-invariant, and
`walkPathLaw` is equivariant under any `cylKernel`-preserving bijection
(`walkPathLaw_map_siteEquiv`); the infinite-product law is then invariant by
`Measure.infinitePi_map_pi`.  The horizontal-invariance corollary for the law of
the cluster is recorded at the end.
-/
import IdlaCyl.Support.CanonicalIdla
import IdlaCyl.Support.FirstHit
import IdlaCyl.Support.CanonicalMeas

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IdlaCyl

variable (B : Base)

/-- The uniform law on a layer is invariant under a horizontal graph
automorphism (`tex:229`, `tex:832-836`). -/
theorem layerLawAt_map (σ : B.graph ≃g B.graph) (k : ℤ) :
    (layerLawAt B k).map (horIso B σ) = layerLawAt B k := by
  unfold layerLawAt
  rw [Measure.map_sum (measurable_of_countable (horIso B σ)).aemeasurable]
  simp_rw [Measure.map_smul, Measure.map_dirac' (measurable_of_countable (horIso B σ))]
  ext s hs
  rw [Measure.sum_apply _ hs, Measure.sum_apply _ hs]
  exact Equiv.tsum_eq σ.toEquiv
    (fun y : B.V => (((B.card : ℝ≥0∞))⁻¹ • Measure.dirac (((y, k)) : Site B)) s)

/-- Transport one walk by the lifted automorphism. -/
noncomputable def walkTransport (σ : B.graph ≃g B.graph) : (ℕ → Site B) → (ℕ → Site B) :=
  fun X n => horIso B σ (X n)

/-- Transport a whole trajectory family by the lifted automorphism
(`tex:832-836`). -/
noncomputable def transportTraj (σ : B.graph ≃g B.graph) (w : TrajSeq B) : TrajSeq B :=
  fun j => walkTransport B σ (w j)

theorem walkTransport_measurable (σ : B.graph ≃g B.graph) : Measurable (walkTransport B σ) :=
  measurable_pi_lambda _ fun n =>
    (measurable_of_countable (horIso B σ)).comp (measurable_pi_apply n)

theorem walkPathLaw_walkTransport (σ : B.graph ≃g B.graph) (p : Site B) :
    (walkPathLaw B p).map (walkTransport B σ) = walkPathLaw B (horIso B σ p) :=
  walkPathLaw_map_siteEquiv B (horIso B σ) (cylKernel_horIso B σ) p

/-- **Measure-level horizontal invariance of the release law** (`tex:832-836`):
the law of one walk started uniformly on a layer is invariant under the lifted
automorphism. -/
theorem walkLawUniform_map (σ : B.graph ≃g B.graph) :
    (walkLawUniform B).map (walkTransport B σ) = walkLawUniform B := by
  ext s hs
  have hmeas : Measurable (walkTransport B σ) := walkTransport_measurable B σ
  have hwp : Measurable (walkPathLaw B) := measurable_of_countable (walkPathLaw B)
  have hlayer : (layerLawAt B 0).map (horIso B σ) = layerLawAt B 0 := layerLawAt_map B σ 0
  calc
    ((walkLawUniform B).map (walkTransport B σ)) s
        = ∫⁻ p, walkPathLaw B p ((walkTransport B σ) ⁻¹' s) ∂(layerLawAt B 0) := by
          rw [Measure.map_apply hmeas hs, walkLawUniform, walkLawUniformAt_eq_bind,
            Measure.bind_apply (hmeas hs) hwp.aemeasurable]
    _ = ∫⁻ p, walkPathLaw B (horIso B σ p) s ∂(layerLawAt B 0) := by
          apply lintegral_congr
          intro p
          rw [← walkPathLaw_walkTransport B σ p, Measure.map_apply hmeas hs]
    _ = ∫⁻ q, walkPathLaw B q s ∂((layerLawAt B 0).map (horIso B σ)) := by
          rw [lintegral_map (f := fun q : Site B => (walkPathLaw B q) s)
            ((Measure.measurable_coe hs).comp hwp)
            (measurable_of_countable (horIso B σ))]
    _ = ∫⁻ q, walkPathLaw B q s ∂(layerLawAt B 0) := by rw [hlayer]
    _ = (walkLawUniform B) s := by
          rw [walkLawUniform, walkLawUniformAt_eq_bind, Measure.bind_apply hs hwp.aemeasurable]

/-- **Measure-level transitivity invariance of the whole driving law**
(`tex:832-836`). -/
theorem idlaMeasure_map_transportTraj (σ : B.graph ≃g B.graph) :
    (idlaMeasure B).map (transportTraj B σ) = idlaMeasure B := by
  unfold idlaMeasure transportTraj
  rw [Measure.infinitePi_map_pi (μ := fun _ : ℕ => walkLawUniform B)
    (f := fun _ : ℕ => walkTransport B σ) (fun _ => walkTransport_measurable B σ)]
  simp_rw [walkLawUniform_map B σ]


/-! ### Pathwise equivariance of the canonical cluster and the horizontal-invariance corollary -/

theorem exitTime'_eq_top_iff' (S : Set (Site B)) (X : ℕ → Site B) :
    exitTime' B S X = ⊤ ↔ ∀ j, X j ∈ S := by
  change MeasureTheory.hittingAfter (fun (k : ℕ) (X : ℕ → Site B) => X k) Sᶜ 0 X = ⊤ ↔ ∀ j, X j ∈ S
  rw [MeasureTheory.hittingAfter_eq_top_iff]
  simp only [Set.mem_compl_iff]
  constructor
  · intro h j; by_contra hj; exact h j (Nat.zero_le j) hj
  · intro h j _ hj; exact hj (h j)

theorem exitTime'_walkTransport (σ : B.graph ≃g B.graph) (S : Set (Site B)) (X : ℕ → Site B) :
    exitTime' B (horIso B σ '' S) (walkTransport B σ X) = exitTime' B S X := by
  have himg : ∀ j : ℕ, (walkTransport B σ X) j ∉ (horIso B σ '' S) ↔ X j ∉ S := by
    intro j
    simp only [walkTransport]
    constructor
    · intro h hx; exact h ⟨X j, hx, rfl⟩
    · intro hxS hmem
      rcases hmem with ⟨y, hy, hyx⟩
      exact hxS ((horIso B σ).injective hyx ▸ hy)
  have htop_iff : ∀ T : Set (Site B), ∀ Y : ℕ → Site B, exitTime' B T Y = ⊤ ↔ ∀ j, Y j ∈ T :=
    fun T Y => exitTime'_eq_top_iff' B T Y
  rcases eq_or_ne (exitTime' B S X) ⊤ with hb | hb
  · rw [hb, htop_iff]
    intro j
    by_contra hc
    exact absurd ((htop_iff S X).mp hb j) ((himg j).mp hc)
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hb
    have hb_eq : exitTime' B S X = (m : ℕ∞) := hm.symm
    refine le_antisymm ?_ ?_
    · rw [hb_eq]
      change exitTime' B (horIso B σ '' S) (walkTransport B σ X) ≤ ((m : ℕ) : ℕ∞)
      rw [exitTime'_le_iff]
      exact ⟨m, le_rfl, (himg m).mpr ((exitTime'_eq_coe_iff B S X m).mp hb_eq).1⟩
    · by_cases hb' : exitTime' B (horIso B σ '' S) (walkTransport B σ X) = ⊤
      · rw [hb']; exact le_top
      · obtain ⟨m', hm'⟩ := WithTop.ne_top_iff_exists.mp hb'
        rw [← hm']
        change exitTime' B S X ≤ ((m' : ℕ) : ℕ∞)
        rw [exitTime'_le_iff]
        exact ⟨m', le_rfl, (himg m').mp
          ((exitTime'_eq_coe_iff B (horIso B σ '' S) (walkTransport B σ X) m').mp hm'.symm).1⟩

theorem exitSite'_walkTransport (σ : B.graph ≃g B.graph) (S : Set (Site B)) (X : ℕ → Site B) :
    exitSite' B (horIso B σ '' S) (walkTransport B σ X)
      = horIso B σ (exitSite' B S X) := by
  unfold exitSite' MeasureTheory.stoppedValue
  rw [exitTime'_walkTransport B σ S X]
  simp only [walkTransport]

theorem clusterFrom_horIso (σ : B.graph ≃g B.graph) (S : Set (Site B)) (ω : TrajSeq B) (k : ℕ) :
    clusterFrom B (horIso B σ '' S) (transportTraj B σ ω) k
      = horIso B σ '' clusterFrom B S ω k := by
  induction k with
  | zero => rfl
  | succ n ih =>
      have hL := clusterFrom_succ B (horIso B σ '' S) (transportTraj B σ ω) n
      have hR := clusterFrom_succ B S ω n
      rw [hL, hR, ih]
      rw [show transportTraj B σ ω n = walkTransport B σ (ω n) from rfl]
      rw [exitSite'_walkTransport B σ (clusterFrom B S ω n) (ω n)]
      rw [Set.image_union, Set.image_singleton]

theorem horIso_image_R (σ : B.graph ≃g B.graph) (k : ℝ) :
    horIso B σ '' R B k = R B k := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [horIso_apply, mem_R] using hq
  · intro hp
    refine ⟨horIso B σ.symm p, ?_, ?_⟩
    · simpa only [horIso_apply, mem_R] using hp
    · exact Prod.ext (RelIso.apply_symm_apply σ p.1) rfl

theorem clusterTraj_horIso (σ : B.graph ≃g B.graph) (ω : TrajSeq B) (t : ℕ) :
    clusterTraj B (transportTraj B σ ω) t = horIso B σ '' clusterTraj B ω t := by
  have h := clusterFrom_horIso B σ (R B 0) ω t
  rwa [horIso_image_R] at h

theorem transportTraj_measurable (σ : B.graph ≃g B.graph) : Measurable (transportTraj B σ) :=
  measurable_pi_lambda _ fun j =>
    (walkTransport_measurable B σ).comp (measurable_pi_apply j)

/-- **Horizontal invariance of the law of the cluster** (`tex:832-836`): for
`x, x'` in the same orbit of a base automorphism, the probability that `(x,y)`
lies in `A(T)` equals the probability that `(x',y)` does. -/
theorem idlaMeasure_real_clusterTraj_orbit (σ : B.graph ≃g B.graph) (x x' : B.V) (T : ℕ)
    (hσ : σ x = x') (y : ℤ) :
    (idlaMeasure B).real {w | (x, y) ∈ clusterTraj B w T}
      = (idlaMeasure B).real {w | (x', y) ∈ clusterTraj B w T} := by
  have hE : MeasurableSet {w : TrajSeq B | (x, y) ∈ clusterTraj B w T} :=
    measurableSet_mem_clusterTraj B T (x, y)
  have hE' : MeasurableSet {w : TrajSeq B | (x', y) ∈ clusterTraj B w T} :=
    measurableSet_mem_clusterTraj B T (x', y)
  have hpre : {w : TrajSeq B | (x, y) ∈ clusterTraj B w T}
      = (transportTraj B σ) ⁻¹' {w : TrajSeq B | (x', y) ∈ clusterTraj B w T} := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [clusterTraj_horIso B σ w T]
    constructor
    · intro hw
      exact ⟨(x, y), hw, by simp only [horIso_apply, hσ]⟩
    · rintro ⟨q, hq, hqeq⟩
      have h1 : horIso B σ q = horIso B σ (x, y) := by
        rw [hqeq]; simp only [horIso_apply, hσ]
      have : q = (x, y) := (horIso B σ).injective h1
      rwa [this] at hq
  have hmeasure : (idlaMeasure B) {w | (x, y) ∈ clusterTraj B w T}
      = (idlaMeasure B) {w | (x', y) ∈ clusterTraj B w T} := by
    calc
      (idlaMeasure B) {w | (x, y) ∈ clusterTraj B w T}
          = (idlaMeasure B)
              ((transportTraj B σ) ⁻¹' {w | (x', y) ∈ clusterTraj B w T}) := by rw [hpre]
      _ = ((idlaMeasure B).map (transportTraj B σ))
              {w | (x', y) ∈ clusterTraj B w T} := by
            rw [Measure.map_apply (transportTraj_measurable B σ) hE']
      _ = (idlaMeasure B) {w | (x', y) ∈ clusterTraj B w T} := by
            rw [idlaMeasure_map_transportTraj B σ]
  exact congrArg ENNReal.toReal hmeasure

end IdlaCyl
