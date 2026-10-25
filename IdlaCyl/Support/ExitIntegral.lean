module

/-
The harmonic exit integral of one cylinder walk (`tex:696-700`).

`FirstHit.hitProb_exit_mean` proves the optional-stopping identity for the
particular bounded harmonic function `H_ζ`.  This file proves it for an
arbitrary discrete harmonic `ψ` that is bounded on half-cylinders (the
admissibility condition `tex:696` reads off an exponentially decaying `ψ`),
and then averages over the uniform start on layer `0` to get the display at
`tex:698`:

  `∫ X, ψ (exitSite' B S X) ∂(walkLawUniform B) = (1/N) ∑_x ψ (x,0) = 0`.

The route avoids the conditional-expectation machinery entirely and follows
`hitProbE_exitIdx`: the truncated exit index `exitIdx B S m` turns optional
stopping into an induction on the truncation level `m`.  The inductive step is
one application of the one-step Markov property `walkPathLaw_map_pathShift`
together with `discreteHarmonic_iff_integral` (`tex:681-684`); the truncation is
removed by dominated convergence.

`S` is required to be contained in a half-cylinder `R_h` (with `R_0 ⊆ S`).
That is not a technicality: it is exactly what bounds `ψ` at the exit site
(`tex:696`, "its finite values at each site of the finite set
`V_N × {1,…,h+1}`"), so that the stopped process is genuinely bounded and the
limit `m → ∞` is honest.  Without it the exit site is unbounded above, `ψ` at
the exit is not integrable in general, and the Bochner integral would silently
take the junk value `0` (`integral_undef`).
-/
public import IdlaCyl.Support.Admissible
public import IdlaCyl.Support.Discrepancy
public import IdlaCyl.Support.HarmonicIntegral

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open IdlaCyl
open scoped ENNReal Topology BigOperators

namespace IdlaCyl

/-! ### Boundedness on half-cylinders -/

/-- `ψ` is bounded on every half-cylinder.  This is the admissibility condition
`tex:696` consumes: the finite set of values below the exit layer plus the
exponential decay as `y → -∞`. -/
def BddOnHalfCylinders (B : Base) (ψ : Site B → ℝ) : Prop :=
  ∀ h : ℤ, ∃ M : ℝ, ∀ p : Site B, p.2 ≤ h → |ψ p| ≤ M

/-- Exponential decay below implies boundedness on every half-cylinder: below
level `0` use the decay, and above it there are only finitely many sites per
layer up to the cut-off. -/
theorem bddOnHalfCylinders_of_expDecayBelow (B : Base) (ψ : Site B → ℝ)
    (hd : ExpDecayBelow B ψ) : BddOnHalfCylinders B ψ := by
  obtain ⟨C, c, hc, hdec⟩ := hd
  have hC : 0 ≤ C := by
    have h := hdec (B.pt, (0 : ℤ)) (by simp)
    have h0 : c * (((0 : ℤ) : ℝ)) = 0 := by simp
    rw [h0, Real.exp_zero, mul_one] at h
    linarith [abs_nonneg (ψ (B.pt, (0 : ℤ)))]
  intro h
  refine ⟨C * Real.exp (c * (max h 0 : ℤ)) + ∑ x : B.V, ∑ j ∈ Finset.Icc 1 h, |ψ (x, j)|, ?_⟩
  intro p hp
  by_cases hp0 : p.2 ≤ 0
  · have h1 : |ψ p| ≤ C * Real.exp (c * (p.2 : ℝ)) := hdec p hp0
    have h2 : Real.exp (c * (p.2 : ℝ)) ≤ Real.exp (c * (max h 0 : ℤ)) := by
      refine Real.exp_le_exp.mpr ?_
      have : (p.2 : ℝ) ≤ (max h 0 : ℤ) := by
        have : p.2 ≤ max h 0 := le_trans hp0 (le_max_right _ _)
        exact_mod_cast this
      exact mul_le_mul_of_nonneg_left this (le_of_lt hc)
    have h3 : C * Real.exp (c * (p.2 : ℝ)) ≤ C * Real.exp (c * (max h 0 : ℤ)) :=
      mul_le_mul_of_nonneg_left h2 hC
    have h4 : 0 ≤ ∑ x : B.V, ∑ j ∈ Finset.Icc 1 h, |ψ (x, j)| := by positivity
    linarith [h1, h3, h4]
  · have hp1 : 1 ≤ p.2 := by omega
    have hle : p ∈ (Finset.univ ×ˢ Finset.Icc 1 h : Finset (Site B)) := by
      rw [Finset.mem_product]
      exact ⟨Finset.mem_univ _, Finset.mem_Icc.mpr ⟨hp1, hp⟩⟩
    have hmem : |ψ p| ≤ ∑ q ∈ (Finset.univ ×ˢ Finset.Icc 1 h : Finset (Site B)), |ψ q| :=
      Finset.single_le_sum (fun q _ => abs_nonneg (ψ q)) hle
    have hsplit : (∑ q ∈ (Finset.univ ×ˢ Finset.Icc 1 h : Finset (Site B)), |ψ q|)
        = ∑ x : B.V, ∑ j ∈ Finset.Icc 1 h, |ψ (x, j)| := Finset.sum_product _ _ _
    have h4 : 0 ≤ C * Real.exp (c * (max h 0 : ℤ)) := mul_nonneg hC (le_of_lt (Real.exp_pos _))
    rw [hsplit] at hmem
    linarith [hmem, h4]

/-! ### The truncated exit position stays in `R_{h+1}` -/

/-- `exitIdx B S m X = 0` when the trajectory does not start in `S`. -/
theorem exitIdx_eq_zero_of_notMem (B : Base) (S : Set (Site B)) :
    ∀ (m : ℕ) (X : ℕ → Site B), X 0 ∉ S → exitIdx B S m X = 0 := by
  intro m
  cases m with
  | zero => intro X _; rfl
  | succ m => intro X hX; rw [exitIdx_succ, if_neg hX]

/-- **The pathwise height bound.**  For an admissible path whose start is at
height at most `h + 1`, the truncated exit position never rises above
`h + 1`, because `S ⊆ R_h` keeps the pre-exit part of the path in `R_h` and each
step moves the height by at most one (`tex:696`). -/
theorem ver_exitIdx_le (B : Base) (S : Set (Site B)) (h : ℤ)
    (hSh : S ⊆ R B (h : ℝ)) :
    ∀ (m : ℕ) (X : ℕ → Site B), CylAdmissible B X → (X 0).2 ≤ h + 1 →
      (X (exitIdx B S m X)).2 ≤ h + 1 := by
  intro m
  induction m with
  | zero => intro X _ hX0; simpa using hX0
  | succ m ih =>
      intro X hXadm hX0
      rw [exitIdx_succ]
      by_cases h0 : X 0 ∈ S
      · rw [if_pos h0]
        have hS0 : (X 0).2 ≤ h := by
          have := hSh h0
          rw [mem_R] at this
          exact_mod_cast this
        have hshift0 : ((pathShift B X) 0).2 ≤ h + 1 := by
          have := CylAdmissible.ver_step B hXadm 0
          simp only [pathShift]
          rcases this with h1 | h1 | h1 <;> omega
        have := ih (pathShift B X) (fun n => hXadm (n + 1)) hshift0
        simpa [pathShift] using this
      · rw [if_neg h0]; exact hX0

/-- The a.s. version of `ver_exitIdx_le` under `walkPathLaw`. -/
theorem ae_ver_exitIdx_le (B : Base) (S : Set (Site B)) (h : ℤ)
    (hSh : S ⊆ R B (h : ℝ)) (p : Site B) (hp : p.2 ≤ h + 1) (m : ℕ) :
    ∀ᵐ X ∂(walkPathLaw B p), (X (exitIdx B S m X)).2 ≤ h + 1 := by
  filter_upwards [walkPathLaw_ae_admissible B p, walkPathLaw_ae_start B p] with X hXadm hX0
  have hstart : (X 0).2 ≤ h + 1 := by rw [hX0]; exact hp
  exact ver_exitIdx_le B S h hSh m X hXadm hstart

/-! ### The cylinder walk as a kernel -/

/-- The path law as a kernel in its starting site. -/
noncomputable def walkPathKernel (B : Base) : Kernel (Site B) (ℕ → Site B) :=
  Kernel.ofFunOfCountable (walkPathLaw B)

@[simp] theorem walkPathKernel_apply (B : Base) (x : Site B) :
    walkPathKernel B x = walkPathLaw B x := rfl

instance walkPathKernel_isMarkov (B : Base) : IsMarkovKernel (walkPathKernel B) :=
  ⟨fun x => walkPathLaw_isProbability B x⟩

/-- The uniform law on layer `0`, as a (constant) kernel. -/
noncomputable def layerKernel (B : Base) : Kernel Unit (Site B) :=
  Kernel.ofFunOfCountable (fun _ : Unit => layerLawAt B 0)

@[simp] theorem layerKernel_apply (B : Base) (u : Unit) : layerKernel B u = layerLawAt B 0 := rfl

instance layerKernel_isMarkov (B : Base) : IsMarkovKernel (layerKernel B) :=
  ⟨fun _ => layerLawAt_isProbability B 0⟩

/-- The kernel composition is the one-step Markov disintegration. -/
theorem walkPathKernel_comp_cylTransitionKernel (B : Base) (q : Site B) :
    (walkPathKernel B).comp (cylTransitionKernel B) q = (walkPathLaw B q).map (pathShift B) := by
  rw [Kernel.comp_apply, walkPathLaw_map_pathShift]
  rfl

/-- The kernel composition `walkPathKernel ∘ layerKernel` is `walkLawUniform`. -/
theorem walkPathKernel_comp_layerKernel (B : Base) :
    (walkPathKernel B).comp (layerKernel B) () = walkLawUniform B := by
  rw [Kernel.comp_apply, layerKernel_apply,
    show walkLawUniform B = walkLawUniformAt B 0 from rfl, walkLawUniformAt_eq_bind]
  rfl

/-! ### The start of the uniform law lies on layer `0` -/

/-- The uniform law on a layer is supported on that layer. -/
theorem layerLawAt_ae_ver (B : Base) (k : ℤ) :
    ∀ᵐ p ∂(layerLawAt B k), p.2 = k := by
  rw [MeasureTheory.ae_iff]
  have hs : MeasurableSet {p : Site B | p.2 ≠ k} := (Set.to_countable _).measurableSet
  rw [layerLawAt, Measure.sum_apply _ hs]
  refine ENNReal.tsum_eq_zero.mpr fun x => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  have : Measure.dirac ((x, k) : Site B) {p : Site B | p.2 ≠ k} = 0 := by
    rw [Measure.dirac_apply' _ hs, Set.indicator_of_notMem (by simp)]
  rw [this, mul_zero]

/-- The start of `walkLawUniform` is on layer `0` almost surely. -/
theorem walkLawUniform_ae_ver_zero (B : Base) :
    ∀ᵐ X ∂(walkLawUniform B), (X 0).2 = 0 := by
  rw [show walkLawUniform B = walkLawUniformAt B 0 from rfl, walkLawUniformAt_eq_bind,
    MeasureTheory.ae_iff]
  have hs : MeasurableSet {X : ℕ → Site B | (X 0).2 ≠ 0} := by
    have hmeas : Measurable (fun X : ℕ → Site B => (X 0).2) :=
      measurable_snd.comp (measurable_pi_apply 0)
    exact hmeas (measurableSet_singleton (0 : ℤ)).compl
  rw [Measure.bind_apply hs (measurable_of_countable (walkPathLaw B)).aemeasurable]
  have hzero_ae : (fun p : Site B => walkPathLaw B p {X : ℕ → Site B | (X 0).2 ≠ 0})
      =ᵐ[layerLawAt B 0] fun _ => 0 := by
    filter_upwards [layerLawAt_ae_ver B 0] with p hp
    refine measure_mono_null ?_ (walkPathLaw_ae_zero B p)
    intro X hX hXp
    simp only [Set.mem_setOf_eq] at hX
    rw [hXp] at hX
    exact hX hp
  rw [lintegral_congr_ae hzero_ae, lintegral_zero]

/-! ### The truncated exit identity -/

/-- Integrability of the truncated test function under `walkPathLaw`.  For a
start at height at most `h + 1` the pathwise height bound applies; for a start
above `h + 1` the walk is already above `S ⊆ R_h`, so the truncated exit index
is `0`. -/
theorem integrable_psi_exitIdx (B : Base) (ψ : Site B → ℝ) (hbdd : BddOnHalfCylinders B ψ)
    (S : Set (Site B)) (h : ℤ) (hSh : S ⊆ R B (h : ℝ)) (m : ℕ) (p : Site B)
    (hp : p.2 ≤ h + 1) :
    Integrable (fun X : ℕ → Site B => ψ (X (exitIdx B S m X))) (walkPathLaw B p) := by
  obtain ⟨K, hK⟩ := hbdd (h + 1)
  refine Integrable.of_bound
    ((measurable_of_countable ψ).comp (measurable_exitIdxSite B S m)).aestronglyMeasurable K ?_
  filter_upwards [ae_ver_exitIdx_le B S h hSh p hp m] with X hX
  rw [Real.norm_eq_abs]
  exact hK _ hX

/-- The truncated test function is integrable under the one-step composition of
`walkPathLaw`, whenever the outer site lies in `S`. -/
theorem integrable_psi_exitIdx_comp (B : Base) (ψ : Site B → ℝ) (hbdd : BddOnHalfCylinders B ψ)
    (S : Set (Site B)) (h : ℤ) (hSh : S ⊆ R B (h : ℝ)) (m : ℕ) (q : Site B) (hq : q ∈ S) :
    Integrable (fun Y : ℕ → Site B => ψ (Y (exitIdx B S m Y)))
      ((walkPathKernel B).comp (cylTransitionKernel B) q) := by
  obtain ⟨K, hK⟩ := hbdd (h + 1)
  have hq_le : q.2 ≤ h := by
    have := hSh hq
    rw [mem_R] at this
    exact_mod_cast this
  have hset : MeasurableSet {Y : ℕ → Site B | ‖ψ (Y (exitIdx B S m Y))‖ ≤ K} :=
    measurableSet_le ((measurable_of_countable ψ).comp (measurable_exitIdxSite B S m)).norm
      measurable_const
  rw [walkPathKernel_comp_cylTransitionKernel]
  refine Integrable.of_bound
    ((measurable_of_countable ψ).comp (measurable_exitIdxSite B S m)).aestronglyMeasurable K ?_
  rw [ae_map_iff (measurable_pathShift B).aemeasurable hset]
  filter_upwards [walkPathLaw_ae_admissible B q, walkPathLaw_ae_start B q] with X hXadm hX0
  have hshift0 : ((pathShift B X) 0).2 ≤ h + 1 := by
    have h0le : (X 0).2 ≤ h := by rw [hX0]; exact hq_le
    have := CylAdmissible.ver_step B hXadm 0
    simp only [pathShift]
    rcases this with h1 | h1 | h1 <;> omega
  rw [Real.norm_eq_abs]
  exact hK _ (ver_exitIdx_le B S h hSh m (pathShift B X) (fun n => hXadm (n + 1)) hshift0)

/-- **The truncated optional-stopping identity.**  For every truncation level
`m` and every starting site `q`, the expectation of the truncated test function
is `ψ q`.  The induction is on `m`; the inductive step is one application of
`walkPathLaw_map_pathShift` (the one-step Markov property) and harmonicity. -/
theorem integral_psi_exitIdx (B : Base) (ψ : Site B → ℝ)
    (hharm : DiscreteHarmonic B ψ) (hbdd : BddOnHalfCylinders B ψ)
    (S : Set (Site B)) (h : ℤ) (hSh : S ⊆ R B (h : ℝ)) :
    ∀ (m : ℕ) (q : Site B),
      ∫ X, ψ (X (exitIdx B S m X)) ∂(walkPathLaw B q) = ψ q := by
  intro m
  induction m with
  | zero =>
      intro q
      have hcongr : (fun X : ℕ → Site B => ψ (X (exitIdx B S 0 X)))
          =ᵐ[walkPathLaw B q] fun _ => ψ q := by
        filter_upwards [walkPathLaw_ae_start B q] with X hX
        simp only [exitIdx_zero]
        rw [hX]
      rw [integral_congr_ae hcongr]
      simp
  | succ m ih =>
      intro q
      by_cases hq : q ∈ S
      · have hint := integrable_psi_exitIdx_comp B ψ hbdd S h hSh m q hq
        have hcongr : (fun X : ℕ → Site B => ψ (X (exitIdx B S (m + 1) X)))
            =ᵐ[walkPathLaw B q]
              fun X => ψ ((pathShift B X) (exitIdx B S m (pathShift B X))) := by
          filter_upwards [walkPathLaw_ae_start B q] with X hX
          rw [exitIdx_succ, if_pos (by rw [hX]; exact hq)]
          rfl
        rw [integral_congr_ae hcongr]
        have hmap : ∫ X, ψ ((pathShift B X) (exitIdx B S m (pathShift B X)))
              ∂(walkPathLaw B q)
            = ∫ Y, ψ (Y (exitIdx B S m Y)) ∂((walkPathLaw B q).map (pathShift B)) := by
          have hgm : AEStronglyMeasurable (fun Y : ℕ → Site B => ψ (Y (exitIdx B S m Y)))
              ((walkPathLaw B q).map (pathShift B)) :=
            ((measurable_of_countable ψ).comp (measurable_exitIdxSite B S m)).aestronglyMeasurable
          rw [← integral_map (measurable_pathShift B).aemeasurable hgm]
        rw [hmap, ← walkPathKernel_comp_cylTransitionKernel]
        rw [Kernel.integral_comp hint]
        have hinner : ∀ x : Site B,
            ∫ y, ψ (y (exitIdx B S m y)) ∂(walkPathKernel B x) = ψ x := by
          intro x
          rw [walkPathKernel_apply]
          exact ih x
        simp_rw [hinner]
        rw [show cylTransitionKernel B q = cylMeasure B q from rfl]
        exact (discreteHarmonic_iff_integral B ψ).mp hharm q
      · have hcongr : (fun X : ℕ → Site B => ψ (X (exitIdx B S (m + 1) X)))
            =ᵐ[walkPathLaw B q] fun _ => ψ q := by
          filter_upwards [walkPathLaw_ae_start B q] with X hX
          rw [exitIdx_eq_zero_of_notMem B S (m + 1) X (by rw [hX]; exact hq), hX]
        rw [integral_congr_ae hcongr]
        simp

/-! ### Removing the truncation -/

/-- **The fixed-start exit identity** (`tex:696-700`), generalising
`FirstHit.hitProb_exit_mean`. -/
theorem integral_exitSite_eq (B : Base) (ψ : Site B → ℝ)
    (hharm : DiscreteHarmonic B ψ) (hbdd : BddOnHalfCylinders B ψ)
    (S : Set (Site B)) (h : ℤ) (hSh : S ⊆ R B (h : ℝ)) (hS0 : R B 0 ⊆ S)
    (x : Site B) (hx : x.2 = 0)
    (hae : ∀ᵐ X ∂(walkPathLaw B x), exitTime' B S X ≠ ⊤) :
    ∫ X, ψ (exitSite' B S X) ∂(walkPathLaw B x) = ψ x := by
  have h0h : (0 : ℤ) ≤ h := by
    have hmem0 : ((B.pt, (0 : ℤ)) : Site B) ∈ R B 0 := by rw [mem_R]; simp
    have := hSh (hS0 hmem0)
    rw [mem_R] at this
    exact_mod_cast this
  obtain ⟨K, hK⟩ := hbdd (h + 1)
  have hmain := integral_psi_exitIdx B ψ hharm hbdd S h hSh
  have hbound : ∀ᵐ X ∂(walkPathLaw B x), ∀ m,
      ‖ψ (X (exitIdx B S m X))‖ ≤ K := by
    filter_upwards [walkPathLaw_ae_admissible B x, walkPathLaw_ae_start B x] with X hXadm hX0
    intro m
    have hstart : (X 0).2 ≤ h + 1 := by rw [hX0, hx]; linarith [h0h]
    rw [Real.norm_eq_abs]
    exact hK _ (ver_exitIdx_le B S h hSh m X hXadm hstart)
  have hconv : ∀ᵐ X ∂(walkPathLaw B x),
      Tendsto (fun m : ℕ => ψ (X (exitIdx B S m X))) atTop (𝓝 (ψ (exitSite' B S X))) := by
    filter_upwards [hae, walkPathLaw_ae_admissible B x, walkPathLaw_ae_start B x]
      with X hfin hXadm hX0
    refine tendsto_atTop_of_eventually_const (i₀ := (exitTime' B S X).toNat) (fun m hm => ?_)
    have hout : X (exitTime' B S X).toNat ∉ S :=
      ((exitTime'_eq_coe_iff B S X (exitTime' B S X).toNat).mp
        (ENat.coe_toNat hfin).symm).1
    have hmem : ∃ j ≤ m, X j ∉ S := ⟨(exitTime' B S X).toNat, hm, hout⟩
    have hspec := exitIdx_spec B S m X hmem
    congr 1
    rw [exitSite'_eq_apply_toNat B S hfin, hspec, ENat.toNat_coe]
  have hDCT := tendsto_integral_of_dominated_convergence (μ := walkPathLaw B x)
    (F := fun (m : ℕ) (X : ℕ → Site B) => ψ (X (exitIdx B S m X)))
    (f := fun X : ℕ → Site B => ψ (exitSite' B S X))
    (bound := fun _ => K)
    (fun m => ((measurable_of_countable ψ).comp (measurable_exitIdxSite B S m)).aestronglyMeasurable)
    (integrable_const K)
    (fun m => hbound.mono (fun X hX => hX m))
    hconv
  have hconst : (fun m : ℕ => ∫ X, ψ (X (exitIdx B S m X)) ∂(walkPathLaw B x))
      = fun _ => ψ x := funext (fun m => hmain m x)
  rw [hconst] at hDCT
  exact tendsto_nhds_unique hDCT tendsto_const_nhds

/-- The uniform start on layer `0` gives the zero-horizontal-average display
`(1/N) ∑_x ψ (x,0) = 0` (`tex:698`). -/
theorem integral_psi_layerLawAt_zero (B : Base) (ψ : Site B → ℝ)
    (hzero : ZeroHorizontalAverage B ψ) :
    ∫ p, ψ p ∂(layerLawAt B 0) = 0 := by
  have hcard_pos : 0 < B.card := lt_of_lt_of_le (by norm_num) B.nontrivial
  have hcard_ne : (B.card : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hcard_pos.ne'
  unfold layerLawAt
  rw [Measure.sum_fintype]
  have hInt : ∀ x ∈ (Finset.univ : Finset B.V),
      Integrable ψ ((B.card : ℝ≥0∞)⁻¹ • Measure.dirac ((x, 0) : Site B)) := by
    intro x _
    refine (integrable_dirac ?_).smul_measure (ENNReal.inv_ne_top.mpr hcard_ne)
    rw [← ofReal_norm]
    exact ENNReal.ofReal_lt_top
  rw [integral_finsetSum_measure hInt]
  simp_rw [integral_smul_measure, integral_dirac, smul_eq_mul]
  rw [← Finset.mul_sum, hzero 0, mul_zero]

/-- **The uniform exit identity** (`tex:698`).  Averaging the fixed-start
identity over the uniform start on layer `0` and using the zero horizontal
average gives `0`. -/
theorem integral_exitSite_uniform_eq_zero (B : Base) (ψ : Site B → ℝ)
    (hharm : DiscreteHarmonic B ψ) (hbdd : BddOnHalfCylinders B ψ)
    (hzero : ZeroHorizontalAverage B ψ)
    (S : Set (Site B)) (h : ℤ) (hSh : S ⊆ R B (h : ℝ)) (hS0 : R B 0 ⊆ S)
    (hae : ∀ᵐ X ∂(walkLawUniform B), exitTime' B S X ≠ ⊤) :
    ∫ X, ψ (exitSite' B S X) ∂(walkLawUniform B) = 0 := by
  have h0h : (0 : ℤ) ≤ h := by
    have hmem0 : ((B.pt, (0 : ℤ)) : Site B) ∈ R B 0 := by
      rw [mem_R]; simp
    have := hSh (hS0 hmem0)
    rw [mem_R] at this
    exact_mod_cast this
  obtain ⟨K, hK⟩ := hbdd (h + 1)
  have hmain := integral_psi_exitIdx B ψ hharm hbdd S h hSh
  -- the truncated identity, averaged over the uniform layer
  have hmain_u : ∀ m, ∫ X, ψ (X (exitIdx B S m X)) ∂(walkLawUniform B) = 0 := by
    intro m
    have hint : Integrable (fun Y : ℕ → Site B => ψ (Y (exitIdx B S m Y)))
        ((walkPathKernel B).comp (layerKernel B) ()) := by
      rw [walkPathKernel_comp_layerKernel]
      refine Integrable.of_bound
        ((measurable_of_countable ψ).comp (measurable_exitIdxSite B S m)).aestronglyMeasurable K ?_
      filter_upwards [walkLawUniformAt_ae_admissible B 0, walkLawUniform_ae_ver_zero B] with X hXadm hX0
      rw [Real.norm_eq_abs]
      exact hK _ (ver_exitIdx_le B S h hSh m X hXadm (by rw [hX0]; linarith [h0h]))
    have hcomp : ∫ X, ψ (X (exitIdx B S m X)) ∂(walkLawUniform B)
        = ∫ p, (∫ X, ψ (X (exitIdx B S m X)) ∂(walkPathLaw B p)) ∂(layerLawAt B 0) := by
      rw [← walkPathKernel_comp_layerKernel]
      rw [Kernel.integral_comp hint]
      simp only [walkPathKernel_apply, layerKernel_apply]
    rw [hcomp]
    simp_rw [hmain m]
    exact integral_psi_layerLawAt_zero B ψ hzero
  -- remove the truncation
  have hbound : ∀ᵐ X ∂(walkLawUniform B), ∀ m,
      ‖ψ (X (exitIdx B S m X))‖ ≤ K := by
    filter_upwards [walkLawUniformAt_ae_admissible B 0, walkLawUniform_ae_ver_zero B]
      with X hXadm hX0
    intro m
    rw [Real.norm_eq_abs]
    exact hK _ (ver_exitIdx_le B S h hSh m X hXadm (by rw [hX0]; linarith [h0h]))
  have hconv : ∀ᵐ X ∂(walkLawUniform B),
      Tendsto (fun m : ℕ => ψ (X (exitIdx B S m X))) atTop (𝓝 (ψ (exitSite' B S X))) := by
    filter_upwards [hae, walkLawUniformAt_ae_admissible B 0, walkLawUniform_ae_ver_zero B]
      with X hfin hXadm hX0
    refine tendsto_atTop_of_eventually_const (i₀ := (exitTime' B S X).toNat) (fun m hm => ?_)
    have hout : X (exitTime' B S X).toNat ∉ S :=
      ((exitTime'_eq_coe_iff B S X (exitTime' B S X).toNat).mp
        (ENat.coe_toNat hfin).symm).1
    have hmem : ∃ j ≤ m, X j ∉ S := ⟨(exitTime' B S X).toNat, hm, hout⟩
    have hspec := exitIdx_spec B S m X hmem
    congr 1
    rw [exitSite'_eq_apply_toNat B S hfin, hspec, ENat.toNat_coe]
  have hDCT := tendsto_integral_of_dominated_convergence (μ := walkLawUniform B)
    (F := fun (m : ℕ) (X : ℕ → Site B) => ψ (X (exitIdx B S m X)))
    (f := fun X : ℕ → Site B => ψ (exitSite' B S X))
    (bound := fun _ => K)
    (fun m => ((measurable_of_countable ψ).comp (measurable_exitIdxSite B S m)).aestronglyMeasurable)
    (integrable_const K)
    (fun m => hbound.mono (fun X hX => hX m))
    hconv
  have hconst : (fun m : ℕ => ∫ X, ψ (X (exitIdx B S m X)) ∂(walkLawUniform B))
      = fun _ => (0 : ℝ) := funext hmain_u
  rw [hconst] at hDCT
  exact tendsto_nhds_unique hDCT tendsto_const_nhds

/-- **The display at `tex:698`**, with the
admissibility condition `ExpDecayBelow` in place of its half-cylinder
consequence `BddOnHalfCylinders`.  `S ⊆ R_h` is the height cap that bounds `ψ`
at the exit site. -/
theorem integral_exitSite_uniform_eq_zero_of_expDecayBelow (B : Base) (ψ : Site B → ℝ)
    (hharm : DiscreteHarmonic B ψ) (hzero : ZeroHorizontalAverage B ψ)
    (hd : ExpDecayBelow B ψ)
    (S : Set (Site B)) (h : ℤ) (hSh : S ⊆ R B (h : ℝ)) (hS0 : R B 0 ⊆ S)
    (hae : ∀ᵐ X ∂(walkLawUniform B), exitTime' B S X ≠ ⊤) :
    ∫ X, ψ (exitSite' B S X) ∂(walkLawUniform B) = 0 :=
  integral_exitSite_uniform_eq_zero B ψ hharm
    (bddOnHalfCylinders_of_expDecayBelow B ψ hd) hzero S h hSh hS0 hae

end IdlaCyl
