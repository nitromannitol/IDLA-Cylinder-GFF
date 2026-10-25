module

/-
Marginal tails for the well-spread estimate `le:wellspread`.
Source: paper/idla-cylinder-gff.tex, tex:1287-1328.

The alive count `M_x` is a sum of independent first-hit indicators under the driving
law `idlaMeasure`, each with mean `1/N` (tex:1291). The ghost count `L̃_x` is a sum of
independent first-hit indicators under `ghostLaw`, with mean `h - 1` (tex:1294-1295).
Each count gets its own Bernstein tail, so no joint law of the two is used (tex:1314).
The measurability lemmas let the coupling measure of `outer_ghost_coupling` be pulled
back to the driving law. The pathwise split is the arithmetic of tex:1307-1312.
-/
public import IdlaCyl.External.Discharge.Bernstein
public import IdlaCyl.Support.FirstHit
public import IdlaCyl.Support.PrInnerStopped.Boundary
public import IdlaCyl.Support.PrInnerStopped.Filtration
public import IdlaCyl.Support.PrInnerTail.Threshold
public import IdlaCyl.Support.Outer.GhostSplice

@[expose] public section

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- Two-sided Bernstein tail for a sum of independent zero-one variables indexed by a
finite type, obtained from the measurable adapter by reindexing to `Fin`. -/
theorem wellspread_indicator_tail {Ω : Type} [MeasurableSpace Ω] {ι : Type} [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ι → Ω → ℝ) (p : ι → ℝ) (ε : ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (hε : 0 ≤ ε)
    (hind : iIndepFun Y P) (hmeas : ∀ i, Measurable (Y i))
    (hY01 : ∀ i ω, Y i ω = 0 ∨ Y i ω = 1) (hmean : ∀ i, ∫ ω, Y i ω ∂P = p i) :
    P {ω | ε ≤ |(∑ i, Y i ω) - ∑ i, p i|} ≤
      ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 / 2) / (∑ i, p i + ε / 3))) := by
  let e := Fintype.equivFin ι
  have h := External.bernstein_of_latticeProb_of_measurable P (Fintype.card ι)
    (fun k => p (e.symm k)) (fun k => Y (e.symm k)) ε (fun k => hp0 _) (fun k => hp1 _) hε
    (hind.precomp e.symm.injective) (fun k => hmeas _) (fun k ω => hY01 _ ω)
    (fun k => hmean _)
  have hY : ∀ ω, ∑ k, Y (e.symm k) ω = ∑ i, Y i ω :=
    fun ω => Equiv.sum_comp e.symm (fun i => Y i ω)
  have hP : ∑ k, p (e.symm k) = ∑ i, p i := Equiv.sum_comp e.symm p
  simp only [hY, hP] at h
  exact h

/-- Alive count under the driving law: each walk first hits level `h` uniformly on that
layer (`unif_first_hit`), so the mean is `T/N` (tex:1291). -/
theorem wellspread_alive_tail (B : Base) (h : ℤ) (T : ℕ) (x : B.V) (ε : ℝ) (hε : 0 ≤ ε) :
    idlaMeasure B {ω | ε ≤ |((aliveCount B h T ω x : ℕ) : ℝ) - (T : ℝ) / (B.card : ℝ)|} ≤
      ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 / 2) / ((T : ℝ) / (B.card : ℝ) + ε / 3))) := by
  have hrec := External.lazyRwRecurrent_holds
  have hprob : IsProbabilityMeasure (walkLawUniform B) := walkLawUniformAt_isProbability B 0
  haveI : ∀ _ : ℕ, IsProbabilityMeasure (walkLawUniform B) := fun _ => hprob
  set S : Set (ℕ → Site B) := {X | firstHitSite B h X = (x, h)} with hSdef
  have hS : MeasurableSet S := measurableSet_firstHit B (x, h)
  have hm : Measurable (S.indicator (1 : (ℕ → Site B) → ℝ)) := measurable_one.indicator hS
  have hmarg : walkLawUniform B S = ((B.card : ℝ≥0∞))⁻¹ := by
    have h1 := congrArg (fun m : Measure (Site B) => m {(x, h)})
      (unif_first_hit B 0 h hrec)
    rw [Measure.map_apply (measurable_firstHitSite B h) (measurableSet_singleton _),
      layerLawAt_singleton, if_pos rfl] at h1
    exact h1
  have hreal : (walkLawUniform B).real S = (B.card : ℝ)⁻¹ := by
    rw [measureReal_def, hmarg, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hind : iIndepFun (fun (j : ℕ) (ω : TrajSeq B) =>
      S.indicator (1 : (ℕ → Site B) → ℝ) (ω j)) (idlaMeasure B) := by
    unfold idlaMeasure
    exact iIndepFun_infinitePi (X := fun _ => S.indicator (1 : (ℕ → Site B) → ℝ))
      (fun _ => hm)
  have hmeanj : ∀ j : ℕ, ∫ ω, S.indicator (1 : (ℕ → Site B) → ℝ) (ω j) ∂(idlaMeasure B) =
      (B.card : ℝ)⁻¹ := by
    intro j
    have hmap : (idlaMeasure B).map (fun ω : TrajSeq B => ω j) = walkLawUniform B := by
      unfold idlaMeasure
      exact Measure.infinitePi_map_eval (fun _ : ℕ => walkLawUniform B) j
    calc ∫ ω, S.indicator (1 : (ℕ → Site B) → ℝ) (ω j) ∂(idlaMeasure B)
        = ∫ y, S.indicator (1 : (ℕ → Site B) → ℝ) y
            ∂((idlaMeasure B).map (fun ω : TrajSeq B => ω j)) :=
          (integral_map (measurable_pi_apply j).aemeasurable hm.aestronglyMeasurable).symm
      _ = (B.card : ℝ)⁻¹ := by rw [hmap, integral_indicator_one hS, hreal]
  have hp1 : (B.card : ℝ)⁻¹ ≤ 1 := by
    have : (2 : ℝ) ≤ B.card := by exact_mod_cast B.nontrivial
    exact inv_le_one_of_one_le₀ (by linarith)
  have hT := wellspread_indicator_tail (idlaMeasure B)
    (fun k : Fin T => fun ω : TrajSeq B => S.indicator (1 : (ℕ → Site B) → ℝ) (ω (k : ℕ)))
    (fun _ => (B.card : ℝ)⁻¹) ε (fun _ => by positivity) (fun _ => hp1) hε
    (hind.precomp Fin.val_injective)
    (fun k => hm.comp (measurable_pi_apply _))
    (fun k ω => by
      simp only [Set.indicator_apply, Pi.one_apply]
      split_ifs <;> simp)
    (fun k => hmeanj k)
  have hsum : ∀ ω : TrajSeq B, ∑ k : Fin T, S.indicator (1 : (ℕ → Site B) → ℝ) (ω (k : ℕ)) =
      ((aliveCount B h T ω x : ℕ) : ℝ) := by
    intro ω
    rw [Fin.sum_univ_eq_sum_range (fun j => S.indicator (1 : (ℕ → Site B) → ℝ) (ω j)) T,
      aliveCount, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : firstHitSite B h (ω j) = (x, h) <;> simp [hSdef, hj]
  have hsumT : ∑ _k : Fin T, (B.card : ℝ)⁻¹ = (T : ℝ) / (B.card : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, div_eq_mul_inv]
  simp only [hsum, hsumT] at hT
  exact hT

/-- Ghost count under the ghost law: the ghost walks are independent and started at the
interior sites, whose hitting probabilities of `(x, h)` sum to `h - 1` (tex:1294-1295). -/
theorem wellspread_ghost_tail (B : Base) (h : ℤ) (hh : 1 ≤ h) (x : B.V) (ε : ℝ)
    (hε : 0 ≤ ε) :
    ghostLaw B h {U | ε ≤ |((ghostCount B h U x : ℕ) : ℝ) - ((h : ℝ) - 1)|} ≤
      ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 / 2) / (((h : ℝ) - 1) + ε / 3))) := by
  set S : Set (ℕ → Site B) := {X | firstHitSite B h X = (x, h)} with hSdef
  have hS : MeasurableSet S := measurableSet_firstHit B (x, h)
  have hm : Measurable (S.indicator (1 : (ℕ → Site B) → ℝ)) := measurable_one.indicator hS
  have hind : iIndepFun (fun (z : ↥(outerInterior B h)) (U : GhostDriver B h) =>
      S.indicator (1 : (ℕ → Site B) → ℝ) (U z)) (ghostLaw B h) := by
    unfold ghostLaw
    exact iIndepFun_pi (X := fun _ => S.indicator (1 : (ℕ → Site B) → ℝ))
      (fun _ => hm.aemeasurable)
  have hint : ∀ z : ↥(outerInterior B h), z.val.2 < h := by
    intro z
    have hz := z.property
    simp only [outerInterior, Finset.mem_product, Finset.mem_Icc] at hz
    omega
  have hmean : ∀ z : ↥(outerInterior B h),
      ∫ U, S.indicator (1 : (ℕ → Site B) → ℝ) (U z) ∂(ghostLaw B h) = hitProb B (x, h) z.val := by
    intro z
    have hcond : ¬ (x, h).2 < z.val.2 := not_lt.mpr (le_of_lt (hint z))
    have hpush : (ghostLaw B h).map (fun U : GhostDriver B h => U z) = walkPathLaw B z.val := by
      unfold ghostLaw
      exact (measurePreserving_eval (fun z : ↥(outerInterior B h) => walkPathLaw B z.val) z).map_eq
    calc ∫ U, S.indicator (1 : (ℕ → Site B) → ℝ) (U z) ∂(ghostLaw B h)
        = ∫ y, S.indicator (1 : (ℕ → Site B) → ℝ) y ∂((ghostLaw B h).map
            (fun U : GhostDriver B h => U z)) :=
          (integral_map (measurable_pi_apply z).aemeasurable hm.aestronglyMeasurable).symm
      _ = hitProb B (x, h) z.val := by
          rw [hpush, integral_indicator_one hS, hitProb, if_neg hcond, measureReal_def]
  have hp0 : ∀ z : ↥(outerInterior B h), 0 ≤ hitProb B (x, h) z.val := by
    intro z
    unfold hitProb
    split_ifs <;> simp
  have hp1 : ∀ z : ↥(outerInterior B h), hitProb B (x, h) z.val ≤ 1 := by
    intro z
    unfold hitProb
    split_ifs
    · norm_num
    · exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hsumh : ∑ z : ↥(outerInterior B h), hitProb B (x, h) z.val = (h : ℝ) - 1 := by
    rw [Finset.sum_coe_sort (outerInterior B h) (fun p => hitProb B (x, h) p)]
    exact sum_hitProb_layers_below B h hh (x, h) rfl
  have hT := wellspread_indicator_tail (ghostLaw B h)
    (fun z : ↥(outerInterior B h) => fun U : GhostDriver B h =>
      S.indicator (1 : (ℕ → Site B) → ℝ) (U z))
    (fun z => hitProb B (x, h) z.val) ε (fun z => hp0 z) (fun z => hp1 z) hε hind
    (fun z => hm.comp (measurable_pi_apply z))
    (fun z U => by
      simp only [Set.indicator_apply, Pi.one_apply]
      split_ifs <;> simp)
    (fun z => hmean z)
  have hsumG : ∀ U : GhostDriver B h,
      ∑ z : ↥(outerInterior B h), S.indicator (1 : (ℕ → Site B) → ℝ) (U z) =
        ((ghostCount B h U x : ℕ) : ℝ) := by
    intro U
    rw [ghostCount, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun z _ => ?_
    by_cases hz : firstHitSite B h (U z) = (x, h) <;> simp [hSdef, hz]
  simp only [hsumG, hsumh] at hT
  exact hT

/-- Measurability of the fill event `R_{h-1} ⊆ Ā_h(T)`, a countable intersection of
memberships in the stopped cluster. -/
theorem wellspread_measurableSet_outerFill (B : Base) (h : ℤ) (T : ℕ) :
    MeasurableSet (outerFill B h T) := by
  have hmem : ∀ p : Site B, MeasurableSet {ω : TrajSeq B | p ∈ stoppedCluster B h ω T} := by
    intro p
    have hset : {ω : TrajSeq B | p ∈ stoppedCluster B h ω T} =
        {ω : TrajSeq B | p ∈ R B 0} ∪
          ⋃ j ∈ Finset.range T, {ω : TrajSeq B | stoppedSettleSite B h ω j = p} := by
      ext ω
      simp [stoppedCluster_eq_union]
    rw [hset]
    refine MeasurableSet.union (MeasurableSet.const _) ?_
    exact Finset.measurableSet_biUnion _ fun j _ =>
      measurable_stoppedSettleSite B h j (measurableSet_singleton p)
  have hF : outerFill B h T = ⋂ p : Site B,
      {ω : TrajSeq B | p ∈ R B ((h - 1 : ℤ) : ℝ) → p ∈ stoppedCluster B h ω T} := by
    ext ω
    simp [outerFill, Set.subset_def]
  rw [hF]
  refine MeasurableSet.iInter fun p => ?_
  by_cases hp : p ∈ R B ((h - 1 : ℤ) : ℝ)
  · have hset : {ω : TrajSeq B | p ∈ R B ((h - 1 : ℤ) : ℝ) → p ∈ stoppedCluster B h ω T} =
        {ω : TrajSeq B | p ∈ stoppedCluster B h ω T} := by
      ext ω
      simp only [Set.mem_setOf_eq, hp, true_implies]
    rw [hset]
    exact hmem p
  · have hset : {ω : TrajSeq B | p ∈ R B ((h - 1 : ℤ) : ℝ) → p ∈ stoppedCluster B h ω T} =
        Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, hp, false_implies]
    rw [hset]
    exact MeasurableSet.univ

/-- The frozen count at `x` is a finite sum of indicators, hence measurable. -/
theorem wellspread_measurable_frozenCount (B : Base) (h : ℤ) (T : ℕ) (x : B.V) :
    Measurable (fun ω : TrajSeq B => (frozenCount B h T ω x : ℝ)) := by
  have hnat : Measurable (fun ω : TrajSeq B => frozenCount B h T ω x) := by
    unfold frozenCount
    simp_rw [Finset.card_filter]
    refine Finset.measurable_sum _ fun j _ => ?_
    exact Measurable.ite (measurable_stoppedSettleSite B h j (measurableSet_singleton _))
      measurable_const measurable_const
  exact (measurable_from_nat (f := fun n : ℕ => (n : ℝ))).comp hnat

/-- The event of the printed statement is measurable, so its driving-law mass equals the
mass of its preimage under the coupling. -/
theorem wellspread_measurableSet_event (B : Base) (h : ℤ) (T : ℕ) (C : ℝ) :
    MeasurableSet {ω : TrajSeq B | ω ∈ outerFill B h T ∧
      ∃ x : B.V, C < (frozenCount B h T ω x : ℝ)} := by
  have hset : {ω : TrajSeq B | ω ∈ outerFill B h T ∧ ∃ x : B.V, C < (frozenCount B h T ω x : ℝ)}
      = outerFill B h T ∩ ⋃ x : B.V, {ω : TrajSeq B | C < (frozenCount B h T ω x : ℝ)} := by
    ext ω
    simp
  rw [hset]
  exact (wellspread_measurableSet_outerFill B h T).inter
    (MeasurableSet.iUnion fun x => measurableSet_lt measurable_const
      (wellspread_measurable_frozenCount B h T x))

/-- The floor defining `h` loses less than one unit beyond the `h - 1` shift. -/
theorem wellspread_floor_gap (u ℓ : ℝ) : u - ((⌊u - ℓ⌋ : ℤ) : ℝ) + 1 ≤ ℓ + 2 := by
  have hfloor := Int.lt_floor_add_one (u - ℓ)
  linarith

/-- The pathwise split of tex:1307-1312: a frozen count above `C ℓ` forces one of the two
marginal tails. -/
theorem wellspread_large_count_split (M L Nc m ℓ C : ℝ) (hℓ : 2 ≤ ℓ) (hC : 6 ≤ C)
    (hcount : Nc = M - L) (hlarge : C * ℓ < Nc) :
    m + C / 3 * ℓ ≤ M ∨ L ≤ ((⌊m - ℓ⌋ : ℤ) : ℝ) - 1 - C / 3 * ℓ := by
  by_contra hnot
  obtain ⟨hM, hL⟩ := not_or.mp hnot
  have hM' : M < m + C / 3 * ℓ := lt_of_not_ge hM
  have hL' : ((⌊m - ℓ⌋ : ℤ) : ℝ) - 1 - C / 3 * ℓ < L := lt_of_not_ge hL
  have hgap := wellspread_floor_gap m ℓ
  have hprod : 0 ≤ (C - 6) * ℓ := mul_nonneg (by linarith) (by linarith)
  rw [hcount] at hlarge
  nlinarith

/-- The Bernstein exponent at deviation `(18/3) ℓ` dominates `K log N` when the variance
proxy is at most `2t` with `t = T/N`, and the width satisfies `ℓ² ≥ K L t / 18 · 2`. -/
theorem wellspread_exponent_ge (ℓ D t L K : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hDt : D ≤ t) (hℓ : 0 < ℓ) (h2 : 2 * ℓ ≤ t) (hsq : K * L * (2 * t) ≤ 18 * ℓ ^ 2) :
    -((18 / 3 * ℓ) ^ 2 / 2) / (D + 18 / 3 * ℓ / 3) ≤ -(K * L) := by
  have hden : 0 < D + 18 / 3 * ℓ / 3 := by linarith
  have hdenle : D + 18 / 3 * ℓ / 3 ≤ 2 * t := by linarith
  have hKL : 0 ≤ K * L := mul_nonneg hK hL
  have key : K * L * (D + 18 / 3 * ℓ / 3) ≤ (18 / 3 * ℓ) ^ 2 / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hdenle hKL
    nlinarith [hsq]
  rw [neg_div, neg_le_neg_iff, le_div_iff₀ hden]
  exact key

/-- Final polynomial comparison: `N` vertices, each with a `4 N^{-K}` budget, fit inside
`N^{-(ν+1)}` once `K ≥ ν + 3` and `N ≥ 4`. -/
theorem wellspread_final_power (N ν K : ℝ) (hN : 4 ≤ N) (hK : ν + 3 ≤ K) :
    N * (4 * N ^ (-K)) ≤ N ^ (-(ν + 1)) := by
  have hNpos : 0 < N := by linarith
  have h1 : N ^ (-K) = N ^ (-(ν + 2)) * N ^ (-(K - (ν + 2))) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have h2 : N ^ (-(K - (ν + 2))) ≤ N⁻¹ := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h3 : N ^ (-(ν + 1)) = N * N ^ (-(ν + 2)) := by
    rw [show -(ν + 1) = 1 + -(ν + 2) by ring, Real.rpow_add hNpos, Real.rpow_one]
  have h4 : N⁻¹ ≤ 4⁻¹ := inv_anti₀ (by norm_num) hN
  have hp : 0 ≤ N ^ (-(ν + 2)) := Real.rpow_nonneg hNpos.le _
  have h5 : 4 * N ^ (-(K - (ν + 2))) ≤ 1 := by
    linarith
  rw [h3, h1]
  have h6 := mul_le_mul_of_nonneg_left h5 (mul_nonneg hNpos.le hp)
  nlinarith [h6]

end

end IdlaCyl
