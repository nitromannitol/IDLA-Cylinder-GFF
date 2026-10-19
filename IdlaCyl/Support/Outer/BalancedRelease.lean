/-
Literal balanced release: m particles from each vertex, with a fixed order.
Source: paper/idla-cylinder-gff.tex, tex:1331-1351.

The finite product law has N*m coordinates, one for every (vertex,copy).
No order invariance is asserted here. The enumeration is a bijection, and
unused extension trajectories do not affect the cluster at time N*m.
-/
import IdlaCyl.External.Discharge.Chernoff
import IdlaCyl.Support.CanonicalGrowth
import IdlaCyl.Support.PrInnerTail.Nonvacuity

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

/-- One independent trajectory for each of m copies at each vertex. -/
abbrev BalancedDriver (B : Base) (m : ℕ) := (B.V × Fin m) → (ℕ → Site B)

/-- A fixed enumeration of all N*m labelled releases. -/
def balancedIndex (B : Base) (m : ℕ) : Fin (B.card * m) ≃ B.V × Fin m :=
  (Fintype.equivFinOfCardEq (by simp only [Fintype.card_prod, Fintype.card_fin, Base.card])).symm

/-- The actual finite product of prescribed cylinder-walk laws. -/
def balancedLaw (B : Base) (m : ℕ) : Measure (BalancedDriver B m) :=
  Measure.pi (fun i : B.V × Fin m => walkPathLaw B (i.1, 0))

instance balancedLaw_isProbability (B : Base) (m : ℕ) :
    IsProbabilityMeasure (balancedLaw B m) := by
  unfold balancedLaw
  infer_instance

/-- Read the prescribed enumeration; the extension after N*m is ignored. -/
def balancedTrajSeq (B : Base) (m : ℕ) (ω : BalancedDriver B m) : TrajSeq B :=
  fun j => if hj : j < B.card * m then
    ω (balancedIndex B m ⟨j, hj⟩) else fun _ => (B.pt, 0)

/-- The balanced cluster starts from R₀ and settles all N*m releases. -/
def balancedCluster (B : Base) (m : ℕ) (ω : BalancedDriver B m) : Set (Site B) :=
  clusterTraj B (balancedTrajSeq B m ω) (B.card * m)

/-- The total number of independent releases is N*m. -/
theorem balanced_driver_card (B : Base) (m : ℕ) :
    Fintype.card (B.V × Fin m) = B.card * m := by
  rw [Fintype.card_prod, Fintype.card_fin, Base.card]

/-- Exactly m of the enumerated releases start at any given vertex. -/
theorem balanced_start_count (B : Base) (m : ℕ) (x : B.V) :
    (Finset.univ.filter (fun i : Fin (B.card * m) =>
      (balancedIndex B m i).1 = x)).card = m := by
  classical
  let e : {i : Fin (B.card * m) // (balancedIndex B m i).1 = x} ≃ Fin m :=
    { toFun := fun i => (balancedIndex B m i.val).2
      invFun := fun j => ⟨(balancedIndex B m).symm (x, j), by simp only [Equiv.apply_symm_apply]⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply (balancedIndex B m).injective
        simp only [Equiv.apply_symm_apply]
        exact Prod.ext i.property.symm rfl
      right_inv := by intro j; simp only [Equiv.apply_symm_apply] }
  have hc := Fintype.card_congr e
  simpa only [Fintype.card_subtype, Fintype.card_fin] using hc

/-- Every finite release coordinate has precisely its prescribed walk marginal. -/
theorem balancedLaw_map_eval (B : Base) (m : ℕ) (i : B.V × Fin m) :
    (balancedLaw B m).map (fun ω => ω i) = walkPathLaw B (i.1, 0) := by
  exact (measurePreserving_eval (fun j : B.V × Fin m => walkPathLaw B (j.1, 0)) i).map_eq

/-- The prescribed trajectories are jointly independent, not only pairwise. -/
theorem balancedLaw_iIndepFun (B : Base) (m : ℕ) :
    iIndepFun (fun i (ω : BalancedDriver B m) => ω i) (balancedLaw B m) := by
  exact iIndepFun_pi (μ := fun i : B.V × Fin m => walkPathLaw B (i.1, 0))
    (X := fun _ => (id : (ℕ → Site B) → (ℕ → Site B)))
    (fun _ => measurable_id.aemeasurable)

/-- Actual prescribed starting positions, on a single full-measure event. -/
theorem balancedLaw_ae_start (B : Base) (m : ℕ) :
    ∀ᵐ ω ∂balancedLaw B m, ∀ i : B.V × Fin m, ω i 0 = (i.1, 0) := by
  apply ae_all_iff.mpr
  intro i
  have h := walkPathLaw_ae_zero B (i.1, 0)
  rw [← balancedLaw_map_eval B m i] at h
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable h

/-- A comparison of extension streams needs only the first N*m walks. -/
theorem balancedCluster_eq_of_prefix (B : Base) (m : ℕ) (ω : BalancedDriver B m)
    (η : TrajSeq B)
    (hη : ∀ j < B.card * m, η j = balancedTrajSeq B m ω j) :
    clusterTraj B η (B.card * m) = balancedCluster B m ω := by
  exact clusterFrom_congr B (R B 0) η (balancedTrajSeq B m ω) hη

/-- Before the cutoff, the extended stream reads the actual finite coordinate. -/
theorem balancedTrajSeq_apply (B : Base) (m : ℕ) (ω : BalancedDriver B m)
    (j : ℕ) (hj : j < B.card * m) :
    balancedTrajSeq B m ω j = ω (balancedIndex B m ⟨j, hj⟩) := by
  simp only [balancedTrajSeq, dif_pos hj]

/-- No release at m=0: the actual cluster is exactly its seed. -/
theorem balancedCluster_zero (B : Base) (ω : BalancedDriver B 0) :
    balancedCluster B 0 ω = R B 0 := by
  simp only [balancedCluster, Nat.mul_zero, clusterTraj, clusterFrom_zero]

/-- Measurability of the extension into the canonical trajectory space. -/
theorem measurable_balancedTrajSeq (B : Base) (m : ℕ) :
    Measurable (balancedTrajSeq B m) := by
  apply measurable_pi_iff.mpr
  intro j
  unfold balancedTrajSeq
  split_ifs with hj
  · exact measurable_pi_apply (balancedIndex B m ⟨j, hj⟩)
  · exact measurable_const

/-- Each finite release visits every vertical level almost surely. -/
theorem balancedLaw_ae_hits_all (B : Base) (m : ℕ) :
    ∀ᵐ ω ∂balancedLaw B m, ∀ i : B.V × Fin m, ∀ h : ℤ,
      ∃ n, (ω i n).2 = h := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro h
  have hhit := ae_exists_ver_eq External.lazyRwRecurrent_holds B (i.1, 0) h
  rw [← balancedLaw_map_eval B m i] at hhit
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hhit

/-- Every walk actually used by the balanced release exits its current cluster. -/
theorem balancedLaw_ae_exit_ne_top (B : Base) (m : ℕ) :
    ∀ᵐ ω ∂balancedLaw B m, ∀ j < B.card * m,
      exitTime' B (clusterTraj B (balancedTrajSeq B m ω) j)
        (balancedTrajSeq B m ω j) ≠ ⊤ := by
  filter_upwards [balancedLaw_ae_hits_all B m] with ω hω
  intro j hj
  apply exitTraj_ae_finite_of_hits_all B
  rw [balancedTrajSeq_apply B m ω j hj]
  exact hω (balancedIndex B m ⟨j, hj⟩)

/-- The occupied set above R₀ is finite; its ncard therefore cannot hide infinity. -/
theorem balancedCluster_positive_finite (B : Base) (m : ℕ) (ω : BalancedDriver B m) :
    (balancedCluster B m ω ∩ {p : Site B | 1 ≤ p.2}).Finite :=
  clusterTraj_plus_ncard_of_finite B (balancedTrajSeq B m ω) (B.card * m)

/-- All N*m particles settle at distinct new positive sites almost surely. -/
theorem balancedCluster_positive_ncard (B : Base) (m : ℕ) :
    ∀ᵐ ω ∂balancedLaw B m,
      (balancedCluster B m ω ∩ {p : Site B | 1 ≤ p.2}).ncard = B.card * m := by
  filter_upwards [balancedLaw_ae_exit_ne_top B m] with ω hω
  exact clusterTraj_plus_ncard_of B (balancedTrajSeq B m ω) (B.card * m) hω

/-- The actual balanced height-failure event is measurable. -/
theorem measurableSet_balancedCluster_not_subset (B : Base) (m : ℕ) (r : ℝ) :
    MeasurableSet {ω : BalancedDriver B m | ¬ balancedCluster B m ω ⊆ R B r} := by
  have hset : {ω : BalancedDriver B m | ¬ balancedCluster B m ω ⊆ R B r} =
      ⋃ p : Site B, {ω : BalancedDriver B m |
        p ∈ balancedCluster B m ω ∧ p ∉ R B r} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.not_subset]
  rw [hset]
  apply MeasurableSet.iUnion
  intro p
  exact (((measurableSet_mem_clusterTraj B (B.card * m) p).preimage
    (measurable_balancedTrajSeq B m)).inter (MeasurableSet.const _))

/-- The actual independent uniform starts used in the canonical disintegration. -/
def outerStartLaw (B : Base) : Measure (ℕ → Site B) :=
  Measure.infinitePi (fun _ : ℕ => layerLaw B)

instance outerStartLaw_isProbability (B : Base) : IsProbabilityMeasure (outerStartLaw B) := by
  unfold outerStartLaw
  infer_instance

/-- Number of releases from (x,0) in the first t prescribed starts. -/
def outerStartCount (B : Base) (t : ℕ) (s : ℕ → Site B) (x : B.V) : ℕ :=
  ((Finset.range t).filter (fun j => s j = (x, 0))).card

/-- The real indicator of one uniform release at (x,0). -/
def outerStartIndicator (B : Base) (x : B.V) (p : Site B) : ℝ :=
  if p = (x, 0) then 1 else 0

/-- The uniform-start indicator is measurable. -/
theorem measurable_outerStartIndicator (B : Base) (x : B.V) :
    Measurable (outerStartIndicator B x) :=
  measurable_of_countable _

/-- The indicator has mean 1/N under the actual uniform layer measure. -/
theorem integral_outerStartIndicator (B : Base) (x : B.V) :
    ∫ p, outerStartIndicator B x p ∂layerLaw B = 1 / (B.card : ℝ) := by
  have hfun : outerStartIndicator B x = ({(x, 0)} : Set (Site B)).indicator
      (fun _ => (1 : ℝ)) := by
    funext p
    by_cases hp : p = (x, 0) <;> simp [outerStartIndicator, hp]
  rw [hfun, integral_indicator_const 1 (measurableSet_singleton (x, 0))]
  have hprob : layerLaw B {(x, 0)} = (B.card : ℝ≥0∞)⁻¹ := by
    rw [layerLaw, layerLawAt_singleton, if_pos rfl]
  simp only [smul_eq_mul, mul_one, Measure.real, hprob, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, one_div]

/-- A finite release count is the sum of its actual uniform-start indicators. -/
theorem outerStartCount_cast_eq_sum (B : Base) (t : ℕ) (s : ℕ → Site B) (x : B.V) :
    (outerStartCount B t s x : ℝ) = ∑ j ∈ Finset.range t, outerStartIndicator B x (s j) := by
  unfold outerStartCount
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold outerStartIndicator
  split_ifs <;> norm_num

/-- The adapter's certified start shortage tail at τ=4mN: exponent −9m/16. -/
theorem outerStartCount_lower_tail (B : Base) (m : ℕ) (x : B.V) :
    outerStartLaw B {s : ℕ → Site B | outerStartCount B (4 * m * B.card) s x < m} ≤
      ENNReal.ofReal (Real.exp (-(9 / 16 * (m : ℝ)))) := by
  have hcard : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
  have hNne : (B.card : ℝ) ≠ 0 := by linarith
  let t : ℕ := 4 * m * B.card
  have hmean (j : Fin t) :
      ∫ s : ℕ → Site B, outerStartIndicator B x (s j) ∂outerStartLaw B = 1 / (B.card : ℝ) := by
    have hi := integral_outerStartIndicator B x
    have hmarg : (outerStartLaw B).map (fun s : ℕ → Site B => s j) = layerLaw B :=
      Measure.infinitePi_map_eval (fun _ : ℕ => layerLaw B) j
    rw [← hmarg, integral_map (measurable_pi_apply (j : ℕ)).aemeasurable
      (measurable_outerStartIndicator B x).aestronglyMeasurable] at hi
    exact hi
  have hind : iIndepFun (fun j : ℕ => fun s : ℕ → Site B => outerStartIndicator B x (s j))
      (outerStartLaw B) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => layerLaw B)
      (X := fun _ => outerStartIndicator B x) (fun _ => measurable_outerStartIndicator B x)
  have h01 (j : Fin t) (s : ℕ → Site B) :
      outerStartIndicator B x (s j) = 0 ∨ outerStartIndicator B x (s j) = 1 := by
    unfold outerStartIndicator
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have H := External.chernoff_of_latticeProb (outerStartLaw B) t (1 / (B.card : ℝ))
    (3 / 4) (fun j : Fin t => fun s : ℕ → Site B => outerStartIndicator B x (s j))
    (by positivity) ((div_le_one (by linarith)).mpr (by linarith)) (by norm_num) (by norm_num)
    (iIndepFun.precomp Fin.val_injective hind) h01 hmean
  have htp : (t : ℝ) * (1 / (B.card : ℝ)) = 4 * (m : ℝ) := by
    dsimp only [t]
    push_cast
    field_simp
  have hthreshold : (1 - (3 / 4 : ℝ)) * ((t : ℝ) * (1 / (B.card : ℝ))) = (m : ℝ) := by
    rw [htp]
    ring
  have hexp : -((3 / 4 : ℝ) ^ 2 * (t : ℝ) * (1 / (B.card : ℝ)) / 4) =
      -(9 / 16 * (m : ℝ)) := by
    rw [mul_assoc ((3 / 4 : ℝ) ^ 2), htp]
    ring
  have hsum (s : ℕ → Site B) : (∑ j : Fin t, outerStartIndicator B x (s j)) =
      (outerStartCount B t s x : ℝ) := by
    exact (Fin.sum_univ_eq_sum_range (fun j => outerStartIndicator B x (s j)) t).trans
      (outerStartCount_cast_eq_sum B t s x).symm
  simp_rw [hsum, hthreshold, hexp, Nat.cast_lt] at H
  exact H

/-- The probability of any deficient vertex in the longer uniform release. -/
theorem outerStartCount_exists_lower_tail (B : Base) (m : ℕ) :
    outerStartLaw B {s : ℕ → Site B | ∃ x : B.V, outerStartCount B (4 * m * B.card) s x < m} ≤
      ENNReal.ofReal ((B.card : ℝ) * Real.exp (-(9 / 16 * (m : ℝ)))) := by
  have hset : {s : ℕ → Site B | ∃ x : B.V, outerStartCount B (4 * m * B.card) s x < m} =
      ⋃ x : B.V, {s : ℕ → Site B | outerStartCount B (4 * m * B.card) s x < m} := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [hset]
  calc
    outerStartLaw B (⋃ x : B.V, {s : ℕ → Site B | outerStartCount B (4 * m * B.card) s x < m}) ≤
        ∑ x : B.V, outerStartLaw B {s : ℕ → Site B | outerStartCount B (4 * m * B.card) s x < m} :=
      measure_iUnion_fintype_le (outerStartLaw B) _
    _ ≤ ∑ _x : B.V, ENNReal.ofReal (Real.exp (-(9 / 16 * (m : ℝ)))) :=
      Finset.sum_le_sum (fun x _ => outerStartCount_lower_tail B m x)
    _ = ENNReal.ofReal ((B.card : ℝ) * Real.exp (-(9 / 16 * (m : ℝ)))) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg B.card), ENNReal.ofReal_natCast]
      rfl

/- Nonvacuity: N=2,m=1 has TWO independent release coordinates, one per vertex.
The actual driver measure has mass one, including at the empty release. -/
example : Fintype.card (PrInnerTail.K2.V × Fin 1) = 2 := by
  rw [balanced_driver_card]
  rfl

example (x : PrInnerTail.K2.V) :
    (Finset.univ.filter (fun i : Fin (PrInnerTail.K2.card * 1) =>
      (balancedIndex PrInnerTail.K2 1 i).1 = x)).card = 1 :=
  balanced_start_count PrInnerTail.K2 1 x

example : balancedLaw PrInnerTail.K2 1 Set.univ = 1 := measure_univ

example : ∀ᵐ ω ∂balancedLaw PrInnerTail.K2 1,
    (balancedCluster PrInnerTail.K2 1 ω ∩ {p : Site PrInnerTail.K2 | 1 ≤ p.2}).ncard = 2 :=
  balancedCluster_positive_ncard PrInnerTail.K2 1
example : balancedLaw PrInnerTail.K2 0 Set.univ = 1 := measure_univ

example : outerStartLaw PrInnerTail.K2 Set.univ = 1 := measure_univ

example (x : PrInnerTail.K2.V) :
    outerStartLaw PrInnerTail.K2 {s : ℕ → Site PrInnerTail.K2 |
      outerStartCount PrInnerTail.K2 (4 * 1 * PrInnerTail.K2.card) s x < 1} ≤
        ENNReal.ofReal (Real.exp (-(9 / 16 * ((1 : ℕ) : ℝ)))) :=
  outerStartCount_lower_tail PrInnerTail.K2 1 x

end
end IdlaCyl
