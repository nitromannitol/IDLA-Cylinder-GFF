/-
The canonical one-step occupation bound behind `pr:apriori` (`tex:583-600`,
`eq:mu-recurrence`).

Write `Z_m(t) = |A(t) ∩ (V_N × {m})|` (`layerCount` below) for the number of
occupied sites at level `m`.  The paper's recurrence is
`μ_m(t+1) − μ_m(t) ≤ (1/N) μ_{m-1}(t)`, `m ≥ 2`, and its heart is the one-step
bound
  `P(Y_{t+1} = m | 𝓕_t) ≤ Z_{m-1}(t)/N`.
The two ingredients are:

* the **no-gap** observation (`tex:596-600`): to settle at level `m` the walk
  must first pass through level `m-1` at a site already in the cluster, so the
  first hit of level `m-1` lies in `A(t)`
  (`firstHitSite_pred_mem_of_exitSite_eq`);
* **uniformity of the first hit** (`tex:604-610`, `IdlaCyl.unif_first_hit`): the
  horizontal coordinate at that first hit is uniform on `V_N`, so the
  probability that it lands in `A(t)` is `Z_{m-1}(t)/N`
  (`measure_firstHit_mem_clusterTraj`).

`condExp_settleSite_level_le_layerCount` assembles them through the conditional
law `IdlaCyl.condExp_settleSite_eq_integral` into the per-level form of the
recurrence.
-/
import IdlaCyl.Support.CondDistrib
import IdlaCyl.Support.ExitIntegral

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

open Classical in
/-- `Z_m(t) = |A(t) ∩ (V_N × {m})|` (`tex:583`): the number of occupied sites at
vertical level `m`.  A `Finset.card`, so the infinite-set junk branch of
`Set.ncard` is removed by construction. -/
noncomputable def layerCount (B : Base) (ω : TrajSeq B) (t : ℕ) (m : ℤ) : ℕ :=
  (Finset.univ.filter fun x : B.V => (x, m) ∈ clusterTraj B ω t).card

/-- **No gaps** (`tex:596-600`).  On an admissible path, if the walk exits `S`
at level `m`, then its first visit to level `m - 1` is still inside `S`: it
happens strictly before the exit, since the exit is at level `m`. -/
theorem firstHitSite_pred_mem_of_exitSite_eq (B : Base) (S : Set (Site B)) (m : ℤ)
    {X : ℕ → Site B} (hadm : CylAdmissible B X)
    (h0 : (X 0).2 ≤ m - 1) (hfin : exitTime' B S X ≠ ⊤)
    (hmem : (exitSite' B S X).2 = m) :
    firstHitSite B (m - 1) X ∈ S := by
  set τ : ℕ := (exitTime' B S X).toNat with hτ
  have hXτ : X τ = exitSite' B S X := by
    rw [hτ, exitSite'_eq_apply_toNat B S hfin]
  have hreach : ∃ n ≤ τ, (X n).2 = m - 1 :=
    hadm.exists_eq_level B (k := m - 1) h0 (by rw [hXτ]; omega)
  obtain ⟨n, hnτ, hn⟩ := hreach
  have hhit : hitLevel B (m - 1) X ≤ ((τ : ℕ) : ℕ∞) :=
    (hitLevel_le_iff B (m - 1) X τ).mpr ⟨n, hnτ, hn⟩
  have hne : hitLevel B (m - 1) X ≠ ⊤ := ne_top_of_le_ne_top (by simp) hhit
  set σ : ℕ := (hitLevel B (m - 1) X).toNat with hσ
  have hσeq : ((σ : ℕ) : ℕ∞) = hitLevel B (m - 1) X := by
    rw [hσ]; exact ENat.coe_toNat hne
  have hσle : σ ≤ τ := WithTop.coe_le_coe.mp (hσeq.trans_le hhit)
  have hfirst : firstHitSite B (m - 1) X = X σ :=
    firstHitSite_eq_of_hitLevel_eq B (m - 1) X σ hσeq.symm
  have hver : (firstHitSite B (m - 1) X).2 = m - 1 := firstHitSite_ver B (m - 1) X hne
  have hσnot : σ ≠ τ := by
    intro h
    have hXσ : (X σ).2 = m - 1 := by rw [← hfirst]; exact hver
    have : (X τ).2 = m - 1 := h ▸ hXσ
    rw [hXτ] at this
    omega
  have hexit : exitTime' B S X = ((τ : ℕ) : ℕ∞) := by
    rw [hτ]; exact (ENat.coe_toNat hfin).symm
  have hmem : X σ ∈ S :=
    (exitTime'_eq_coe_iff B S X τ).mp hexit |>.2 σ (lt_of_le_of_ne hσle hσnot)
  rw [hfirst]; exact hmem

/-- **The exit level is bounded by the first hit of the boundary layer.**  For
the cluster at time `t`, the event that the walk exits at level `m` is contained
in the event that its first hit of level `m - 1` lands in the cluster. -/
theorem measure_exitSite_level_le_firstHit (B : Base) (ω : TrajSeq B) (t : ℕ) (m : ℤ)
    (hm : 2 ≤ m) :
    walkLawUniform B {X : ℕ → Site B | (exitSite' B (clusterTraj B ω t) X).2 = m}
      ≤ walkLawUniform B
          {X : ℕ → Site B | firstHitSite B (m - 1) X ∈ clusterTraj B ω t} := by
  refine measure_mono_ae ?_
  filter_upwards [walkLawUniform_ae_ver_zero B, walkLawUniformAt_ae_admissible B 0,
    exitTraj_ae_finite_hits_all_levels B] with X hX0 hXadm hall
  intro hmem
  refine firstHitSite_pred_mem_of_exitSite_eq B (clusterTraj B ω t) m hXadm ?_
    (exitTraj_ae_finite_of_hits_all B ω t hall) hmem
  rw [hX0]; omega

/-- **The layer law of the cluster is `Z_m(t)/N`.**  The uniform layer measure is
a weighted sum of Dirac masses, and the cluster meets layer `m` (`m ≥ 1`) in the
finitely many settling sites, so the sum is finite. -/
theorem layerLawAt_clusterTraj (B : Base) (ω : TrajSeq B) (t : ℕ) (m : ℤ) :
    (layerLawAt B m) (clusterTraj B ω t)
      = (layerCount B ω t m : ℝ≥0∞) * ((B.card : ℝ≥0∞))⁻¹ := by
  classical
  have hmeas : MeasurableSet (clusterTraj B ω t) := (Set.to_countable _).measurableSet
  have hdir : ∀ x : B.V,
      (Measure.dirac ((x, m) : Site B)) (clusterTraj B ω t)
        = if ((x, m) : Site B) ∈ clusterTraj B ω t then (1 : ℝ≥0∞) else 0 := by
    intro x
    rw [Measure.dirac_apply' _ hmeas, Set.indicator_apply]
    by_cases hx : ((x, m) : Site B) ∈ clusterTraj B ω t <;> simp [hx]
  unfold layerLawAt
  rw [Measure.sum_apply _ hmeas]
  simp only [Measure.smul_apply, smul_eq_mul, hdir]
  set F : Finset B.V := Finset.univ.filter fun x => ((x, m) : Site B) ∈ clusterTraj B ω t with hF
  have hsupp : ∀ x ∉ F,
      ((B.card : ℝ≥0∞))⁻¹ * (if ((x, m) : Site B) ∈ clusterTraj B ω t then (1 : ℝ≥0∞) else 0)
        = 0 := by
    intro x hx
    rw [hF, Finset.mem_filter] at hx
    rw [if_neg (fun hc => hx ⟨Finset.mem_univ x, hc⟩), mul_zero]
  rw [tsum_eq_sum (s := F) hsupp]
  have hinner : ∀ x ∈ F,
      ((B.card : ℝ≥0∞))⁻¹ * (if ((x, m) : Site B) ∈ clusterTraj B ω t then (1 : ℝ≥0∞) else 0)
        = ((B.card : ℝ≥0∞))⁻¹ := by
    intro x hx
    rw [hF, Finset.mem_filter] at hx
    rw [if_pos hx.2, mul_one]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul, layerCount, ← hF]

/-- **The uniform first hit lands in the cluster with probability `Z_{m-1}/N`.** -/
theorem measure_firstHit_mem_clusterTraj (B : Base) (ω : TrajSeq B) (t : ℕ) (m : ℤ)
    (hrec : External.LazyRwRecurrent) :
    walkLawUniform B {X : ℕ → Site B | firstHitSite B (m - 1) X ∈ clusterTraj B ω t}
      = (layerCount B ω t (m - 1) : ℝ≥0∞) * ((B.card : ℝ≥0∞))⁻¹ := by
  have hmeas : MeasurableSet (clusterTraj B ω t) := (Set.to_countable _).measurableSet
  have hmap : (walkLawUniform B).map (firstHitSite B (m - 1)) = layerLawAt B (m - 1) := by
    rw [walkLawUniform]
    exact unif_first_hit B 0 (m - 1) hrec
  rw [show {X : ℕ → Site B | firstHitSite B (m - 1) X ∈ clusterTraj B ω t}
      = (firstHitSite B (m - 1)) ⁻¹' (clusterTraj B ω t) from rfl,
    ← Measure.map_apply (measurable_firstHitSite B (m - 1)) hmeas, hmap]
  exact layerLawAt_clusterTraj B ω t (m - 1)

/-- **The per-level one-step occupation bound** (`eq:mu-recurrence`, `tex:590`).
Conditionally on `𝓕_t`, the probability that the walk settles exactly at level `m`
is at most `Z_{m-1}(t)/N`, the fraction of layer `m - 1` already occupied.  This
is the conditional-probability form of the recurrence; taking expectations and
telescoping gives `μ_m(t+1) - μ_m(t) ≤ μ_{m-1}(t)/N`. -/
theorem condExp_settleSite_level_le_layerCount (B : Base) (m : ℤ) (hm : 2 ≤ m) (t : ℕ)
    (hrec : External.LazyRwRecurrent) :
    (idlaMeasure B)[fun ω : TrajSeq B =>
        (if (settleSite B ω t).2 = m then (1 : ℝ) else 0) | idlaFiltration B t]
      ≤ᵐ[idlaMeasure B]
      fun ω : TrajSeq B => (layerCount B ω t (m - 1) : ℝ) / (B.card : ℝ) := by
  have hf : StronglyMeasurable (fun p : Site B => if p.2 = m then (1 : ℝ) else 0) :=
    (measurable_of_countable _).stronglyMeasurable
  have hsetS : MeasurableSet {ω : TrajSeq B | (settleSite B ω t).2 = m} :=
    (measurableSet_singleton m).preimage
      ((measurable_of_countable (fun p : Site B => p.2)).comp (measurable_settleSite B t))
  have hint : Integrable (fun ω : TrajSeq B =>
      (if (settleSite B ω t).2 = m then (1 : ℝ) else 0)) (idlaMeasure B) := by
    refine Integrable.of_bound ?_ 1 ?_
    · change AEStronglyMeasurable (fun ω : TrajSeq B =>
        if ω ∈ {ω : TrajSeq B | (settleSite B ω t).2 = m} then (1 : ℝ) else 0) (idlaMeasure B)
      exact (Measurable.ite hsetS measurable_const measurable_const).aestronglyMeasurable
    · filter_upwards with ω
      by_cases h : (settleSite B ω t).2 = m <;> simp [h]
  refine (condExp_settleSite_eq_integral B t
    (fun p : Site B => if p.2 = m then (1 : ℝ) else 0) hf hint).trans_le ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  change (∫ w, (if (exitSite' B (clusterTraj B ω t) w).2 = m then (1 : ℝ) else 0)
      ∂(walkLawUniform B)) ≤ (layerCount B ω t (m - 1) : ℝ) / (B.card : ℝ)
  have hAmeas : MeasurableSet {w : ℕ → Site B | (exitSite' B (clusterTraj B ω t) w).2 = m} :=
    (measurableSet_singleton m).preimage
      ((measurable_of_countable (fun p : Site B => p.2)).comp
        (measurable_exitSite' B (clusterTraj B ω t)))
  have hInt : ∫ w, (if (exitSite' B (clusterTraj B ω t) w).2 = m then (1 : ℝ) else 0)
        ∂(walkLawUniform B)
      = ((walkLawUniform B)
          {w : ℕ → Site B | (exitSite' B (clusterTraj B ω t) w).2 = m}).toReal := by
    rw [show (fun w : ℕ → Site B =>
          if (exitSite' B (clusterTraj B ω t) w).2 = m then (1 : ℝ) else 0)
        = ({w : ℕ → Site B | (exitSite' B (clusterTraj B ω t) w).2 = m} : Set (ℕ → Site B)).indicator
            (fun _ => (1 : ℝ)) from by
      funext w
      rw [Set.indicator_apply]
      by_cases h : (exitSite' B (clusterTraj B ω t) w).2 = m <;> simp [h]]
    rw [integral_indicator_const _ hAmeas]
    simp only [smul_eq_mul, mul_one, Measure.real]
  rw [hInt]
  have hBval : (walkLawUniform B) {w : ℕ → Site B | firstHitSite B (m - 1) w ∈ clusterTraj B ω t}
      = (layerCount B ω t (m - 1) : ℝ≥0∞) * ((B.card : ℝ≥0∞))⁻¹ :=
    measure_firstHit_mem_clusterTraj B ω t m hrec
  have hle := measure_exitSite_level_le_firstHit B ω t m hm
  calc ((walkLawUniform B)
          {w : ℕ → Site B | (exitSite' B (clusterTraj B ω t) w).2 = m}).toReal
      ≤ ((walkLawUniform B)
          {w : ℕ → Site B | firstHitSite B (m - 1) w ∈ clusterTraj B ω t}).toReal :=
        ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top (prob_le_one)) hle
    _ = ((layerCount B ω t (m - 1) : ℝ≥0∞) * ((B.card : ℝ≥0∞))⁻¹).toReal := by rw [hBval]
    _ = (layerCount B ω t (m - 1) : ℝ) / (B.card : ℝ) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
          ENNReal.toReal_natCast]
        ring

end IdlaCyl
