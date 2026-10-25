module

/-
The independent entrance-coupon bound.
Source: paper/idla-cylinder-gff.tex, tex:595-610,1440-1453.
No coupon-collector citation is used. First-hit uniformity and recurrence
are discharged in LayerEntrance; all products are finite probability masses.
-/
public import IdlaCyl.Support.Reduction.LayerEntrance

@[expose] public section

namespace IdlaCyl.Reduction

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- The cardinality denominators in the coupon estimates are strictly positive. -/
theorem card_real_pos (B : Base) : (0 : ℝ) < B.card := by
  exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) B.nontrivial)

/-- The single-coupon miss probability is a genuine number in [0,1]. -/
theorem coupon_miss_nonneg (B : Base) : 0 ≤ 1 - 1 / (B.card : ℝ) := by
  have hcard : 2 ≤ B.card := B.nontrivial
  have hN : (1 : ℝ) ≤ B.card := by exact_mod_cast (by omega : 1 ≤ B.card)
  exact sub_nonneg.mpr ((div_le_one (card_real_pos B)).mpr hN)

/-- Exact mass of one stationary first-entrance coupon. -/
theorem entrance_singleton (B : Base) (h L : ℤ) (x : B.V) :
    walkLawUniformAt B h {X | firstHitSite B L X = (x, L)} =
      (B.card : ℝ≥0∞)⁻¹ := by
  have hm := congrArg (fun μ : Measure (Site B) => μ {(x, L)})
    (stationary_entrance B h L)
  rw [Measure.map_apply (measurable_firstHitSite B L) (measurableSet_singleton _),
    layerLawAt_singleton, if_pos rfl] at hm
  exact hm

/-- Exact mass of avoiding one coupon in one walk. -/
theorem entrance_not_singleton (B : Base) (h L : ℤ) (x : B.V) :
    walkLawUniformAt B h {X | firstHitSite B L X ≠ (x, L)} =
      1 - (B.card : ℝ≥0∞)⁻¹ := by
  change walkLawUniformAt B h {X | firstHitSite B L X = (x, L)}ᶜ = _
  rw [measure_compl (measurableSet_firstHit B (x, L)) (measure_ne_top _ _),
    measure_univ, entrance_singleton]

/-- Exactly M independent walks avoid a specified coupon with the product probability. -/
theorem missing_one_coupon (B : Base) (h L : ℤ) (M : ℕ) (x : B.V) :
    layerDrivingLaw B h {ω | ∀ i < M, firstHitSite B L (ω i) ≠ (x, L)} =
      (1 - (B.card : ℝ≥0∞)⁻¹) ^ M := by
  have hi : iIndepFun (fun i (ω : TrajSeq B) => ω i) (layerDrivingLaw B h) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => walkLawUniformAt B h)
      (X := fun _ => id) (fun _ => measurable_id)
  have heq : {ω : TrajSeq B | ∀ i < M, firstHitSite B L (ω i) ≠ (x, L)} =
      ⋂ i ∈ Finset.range M, {ω : TrajSeq B | firstHitSite B L (ω i) ≠ (x, L)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range]
  rw [heq]
  calc
    _ = ∏ i ∈ Finset.range M, layerDrivingLaw B h
        {ω | firstHitSite B L (ω i) ≠ (x, L)} :=
      hi.meas_biInter (S := Finset.range M)
        (s := fun i => {ω | firstHitSite B L (ω i) ≠ (x, L)}) (fun _ _ =>
          ⟨{X | firstHitSite B L X ≠ (x, L)},
            (measurableSet_firstHit B (x, L)).compl, rfl⟩)
    _ = _ := by
      have hcoord (i : ℕ) :
          layerDrivingLaw B h {ω | firstHitSite B L (ω i) ≠ (x, L)} =
            1 - (B.card : ℝ≥0∞)⁻¹ := by
        rw [show {ω : TrajSeq B | firstHitSite B L (ω i) ≠ (x, L)} =
          (fun ω : TrajSeq B => ω i) ⁻¹' {X | firstHitSite B L X ≠ (x, L)} from rfl,
          ← Measure.map_apply (measurable_pi_apply i) (measurableSet_firstHit B (x, L)).compl]
        change (Measure.infinitePi (fun _ : ℕ => walkLawUniformAt B h)).map
          (fun ω => ω i) _ = _
        rw [Measure.infinitePi_map_eval, entrance_not_singleton]
      simp_rw [hcoord]
      rw [Finset.prod_const, Finset.card_range]

/-- The union event is measurable; no outer-measure interpretation is needed. -/
theorem measurableSet_missingCoupons (B : Base) (L : ℤ) (M : ℕ) :
    MeasurableSet (missingCoupons B L M) := by
  have heq : missingCoupons B L M =
      ⋃ x : B.V, ⋂ i : Fin M, {ω : TrajSeq B | firstHitSite B L (ω i) ≠ (x, L)} := by
    ext ω
    simp only [missingCoupons, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_iInter]
    exact exists_congr (fun _ => ⟨fun h i => h i i.2, fun h i hi => h ⟨i, hi⟩⟩)
  rw [heq]
  exact MeasurableSet.iUnion (fun x => MeasurableSet.iInter (fun i =>
    ((measurableSet_firstHit B (x, L)).compl.preimage (measurable_pi_apply (i : ℕ)))))

/-- Union bound for the M independent entrance coupons, including M=0. -/
theorem missing_coupons_le (B : Base) (h L : ℤ) (M : ℕ) :
    layerDrivingLaw B h (missingCoupons B L M) ≤
      ENNReal.ofReal ((B.card : ℝ) * (1 - 1 / (B.card : ℝ)) ^ M) := by
  have hreal : ENNReal.ofReal (1 - 1 / (B.card : ℝ)) =
      1 - (B.card : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_sub 1 (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_div_of_pos (card_real_pos B), ENNReal.ofReal_one,
      ENNReal.ofReal_natCast, one_div]
  have heq : missingCoupons B L M =
      ⋃ x : B.V, {ω : TrajSeq B | ∀ i < M, firstHitSite B L (ω i) ≠ (x, L)} := by
    ext ω
    simp only [missingCoupons, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [heq]
  calc
    _ ≤ ∑ x : B.V, layerDrivingLaw B h
        {ω | ∀ i < M, firstHitSite B L (ω i) ≠ (x, L)} :=
      measure_iUnion_fintype_le _ _
    _ = (B.card : ℝ≥0∞) * (1 - (B.card : ℝ≥0∞)⁻¹) ^ M := by
      simp only [missing_one_coupon, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Base.card]
    _ = ENNReal.ofReal ((B.card : ℝ) * (1 - 1 / (B.card : ℝ)) ^ M) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg B.card), ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow (coupon_miss_nonneg B), hreal]

/-- Elementary exponential upper bound on the coupon miss factor. -/
theorem coupon_factor_exp (B : Base) (M : ℕ) :
    (1 - 1 / (B.card : ℝ)) ^ M ≤ Real.exp (-(M : ℝ) / (B.card : ℝ)) := by
  have hbase : 1 - 1 / (B.card : ℝ) ≤ Real.exp (-(1 / (B.card : ℝ))) := by
    linarith [Real.add_one_le_exp (-(1 / (B.card : ℝ)))]
  calc
    _ ≤ Real.exp (-(1 / (B.card : ℝ))) ^ M :=
      pow_le_pow_left₀ (coupon_miss_nonneg B) hbase M
    _ = Real.exp (-(M : ℝ) / (B.card : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- Exponential form of the coupon bound. -/
theorem missing_coupons_exp (B : Base) (h L : ℤ) (M : ℕ) :
    layerDrivingLaw B h (missingCoupons B L M) ≤
      ENNReal.ofReal ((B.card : ℝ) * Real.exp (-(M : ℝ) / (B.card : ℝ))) :=
  (missing_coupons_le B h L M).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (coupon_factor_exp B M) (Nat.cast_nonneg _)))

/-- The logarithmic batch threshold implies the desired polynomial error. -/
theorem coupon_exp_le_poly (B : Base) (M : ℕ) (q : ℝ)
    (hM : (q + 1) * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (M : ℝ)) :
    (B.card : ℝ) * Real.exp (-(M : ℝ) / (B.card : ℝ)) ≤ (B.card : ℝ) ^ (-q) := by
  have hN := card_real_pos B
  have hdiv : (q + 1) * Real.log (B.card : ℝ) ≤ (M : ℝ) / (B.card : ℝ) := by
    apply (le_div_iff₀ hN).mpr
    calc
      _ = (q + 1) * (B.card : ℝ) * Real.log (B.card : ℝ) := by ring
      _ ≤ _ := hM
  rw [neg_div]
  calc
    _ ≤ (B.card : ℝ) * Real.exp (-((q + 1) * Real.log (B.card : ℝ))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hdiv)) hN.le
    _ = (B.card : ℝ) ^ (-q) := by
      rw [show -q = (1 : ℝ) + -(q + 1) by ring, Real.rpow_add hN, Real.rpow_one,
        Real.rpow_def_of_pos hN]
      congr 2
      ring

/-- Polynomial form of the coupon bound, for an arbitrary real exponent. -/
theorem missing_coupons_poly (B : Base) (h L : ℤ) (M : ℕ) (q : ℝ)
    (hM : (q + 1) * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (M : ℝ)) :
    layerDrivingLaw B h (missingCoupons B L M) ≤
      ENNReal.ofReal ((B.card : ℝ) ^ (-q)) :=
  (missing_coupons_exp B h L M).trans
    (ENNReal.ofReal_le_ofReal (coupon_exp_le_poly B M q hM))

end IdlaCyl.Reduction
