module

public import IdlaCyl.Support.Silvestri.Dyadic
public import IdlaCyl.Support.Silvestri.Bridge
public import IdlaCyl.Support.FiniteCoupling
public import Mathlib

@[expose] public section

/-!
# Window coupling of two horizontal chains

Fix a base `B` with lazy kernel `B.P`. After `s` steps from `x`, the endpoint of the
base chain has law `endLaw B s x`, with weights `basePow B s x ·`. The path of `s`
steps has law `pathLaw B s x`, with weights `pathWeight B x s`. Given an endpoint `e`,
the path can be drawn from the bridge law `bridgeLaw B s x e`, and mixing the bridges
with the endpoint weights gives back the path law.

`windowCouple B s s' x x'` is a joint law of a path of `s` steps and a path of `s'`
steps. It couples the two endpoint laws maximally, and then draws each path from the
bridge law of its coupled endpoint, independently given the endpoints.

The file proves:

* the first marginal of `windowCouple` is `pathLaw B s x`, and its second marginal is
  `pathLaw B s' x'`, stated as identities of expectations of functions of one path;
* the half `ℓ¹` distance `endTV` between `endLaw B s x` and `endLaw B s' x'` equals the
  deficit of the maximal coupling, and is at most `2 * (1/2) ^ (min s s' / τ)`, where
  `τ = silvestriMixingTime B`.

Every sum is a finite sum over a finite type. The bridge laws fall back to the uniform
law on paths when `basePow B s x e = 0`. That fallback has total mass one, and it is
multiplied by `basePow B s x e = 0` in every mixture identity, so no statement depends on it.
-/

namespace IdlaCyl.Silvestri

open IdlaCyl.External
open scoped BigOperators

/-- The number of paths of `s` steps is positive. -/
theorem card_paths_pos (B : Base) (s : ℕ) : 0 < Fintype.card (Fin s → B.V) :=
  Fintype.card_pos

/-- The weight of the bridge from `x` to `e` in `s` steps: the bridge weight, or the uniform
weight on paths when `basePow B s x e = 0`. -/
noncomputable def bridgeLawWeight (B : Base) (s : ℕ) (x e : B.V) (w : Fin s → B.V) : ℝ :=
  if basePow B s x e = 0 then 1 / (Fintype.card (Fin s → B.V) : ℝ) else bridgeWeight B s x e w

/-- The bridge weights are nonnegative. -/
theorem bridgeLawWeight_nonneg (B : Base) (s : ℕ) (x e : B.V) (w : Fin s → B.V) :
    0 ≤ bridgeLawWeight B s x e w := by
  unfold bridgeLawWeight
  split_ifs
  · exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  · exact bridgeWeight_nonneg B x e s w

/-- The bridge weights sum to `1` for every endpoint `e`. -/
theorem sum_bridgeLawWeight (B : Base) (s : ℕ) (x e : B.V) :
    ∑ w, bridgeLawWeight B s x e w = 1 := by
  unfold bridgeLawWeight
  split_ifs with h
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hN : (Fintype.card (Fin s → B.V) : ℝ) ≠ 0 := by
      exact_mod_cast (card_paths_pos B s).ne'
    exact mul_one_div_cancel hN
  · exact sum_bridgeWeight B x e s h

/-- The bridge law from `x` to `e` in `s` steps, as a law on paths. -/
noncomputable def bridgeLaw (B : Base) (s : ℕ) (x e : B.V) : FiniteLaw (Fin s → B.V) where
  weight := bridgeLawWeight B s x e
  nonneg := bridgeLawWeight_nonneg B s x e
  total := sum_bridgeLawWeight B s x e

/-- The law of the path of `s` steps from `x`. -/
noncomputable def pathLaw (B : Base) (s : ℕ) (x : B.V) : FiniteLaw (Fin s → B.V) where
  weight := pathWeight B x s
  nonneg := pathWeight_nonneg B x s
  total := sum_pathWeight B x s

/-- The rows of `basePow` sum to `1`. -/
theorem sum_basePow_row (B : Base) (s : ℕ) (x : B.V) : ∑ e, basePow B s x e = 1 := by
  simp only [← sum_paths_end_eq_basePow B x s]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact sum_pathWeight B x s

/-- The law of the endpoint of the base chain after `s` steps from `x`. -/
noncomputable def endLaw (B : Base) (s : ℕ) (x : B.V) : FiniteLaw B.V where
  weight := basePow B s x
  nonneg := basePow_nonneg B x s
  total := sum_basePow_row B s x

/-- The maximal coupling of the two endpoint laws `endLaw B s x` and `endLaw B s' x'`. -/
noncomputable def windowEnd (B : Base) (s s' : ℕ) (x x' : B.V) : FiniteLaw (B.V × B.V) :=
  FiniteLaw.maximalCoupling (endLaw B s x) (endLaw B s' x')

/-- The weight of the pair of paths `ww` in the window coupling: the maximal coupling of the
endpoints, with each endpoint pair expanded by independent bridges. -/
noncomputable def windowWeight (B : Base) (s s' : ℕ) (x x' : B.V)
    (ww : (Fin s → B.V) × (Fin s' → B.V)) : ℝ :=
  ∑ z : B.V × B.V, (windowEnd B s s' x x').weight z *
    ((bridgeLaw B s x z.1).weight ww.1 * (bridgeLaw B s' x' z.2).weight ww.2)

/-- For a product of two functions on the two factors, summed over the product type. -/
theorem sum_mul_pair {A C : Type*} [Fintype A] [Fintype C] (f : A → ℝ) (g : C → ℝ) :
    ∑ ac : A × C, f ac.1 * g ac.2 = (∑ a, f a) * ∑ c, g c := by
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by simp only [Finset.mul_sum]

/-- The window coupling: a joint law of a path of `s` steps from `x` and a path of `s'` steps
from `x'`. -/
noncomputable def windowCouple (B : Base) (s s' : ℕ) (x x' : B.V) :
    FiniteLaw ((Fin s → B.V) × (Fin s' → B.V)) where
  weight := windowWeight B s s' x x'
  nonneg ww := by
    unfold windowWeight
    exact Finset.sum_nonneg fun z _ => mul_nonneg ((windowEnd B s s' x x').nonneg z)
      (mul_nonneg ((bridgeLaw B s x z.1).nonneg ww.1) ((bridgeLaw B s' x' z.2).nonneg ww.2))
  total := by
    unfold windowWeight
    rw [Finset.sum_comm]
    calc ∑ z : B.V × B.V, ∑ ww : (Fin s → B.V) × (Fin s' → B.V),
            (windowEnd B s s' x x').weight z *
              ((bridgeLaw B s x z.1).weight ww.1 * (bridgeLaw B s' x' z.2).weight ww.2)
        = ∑ z : B.V × B.V, (windowEnd B s s' x x').weight z := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [← Finset.mul_sum, sum_mul_pair (bridgeLaw B s x z.1).weight
            (bridgeLaw B s' x' z.2).weight, (bridgeLaw B s x z.1).total,
            (bridgeLaw B s' x' z.2).total, mul_one, mul_one]
      _ = 1 := (windowEnd B s s' x x').total

/-- The row sums of the maximal coupling are the first endpoint weights. -/
theorem windowEnd_row (B : Base) (s s' : ℕ) (x x' e : B.V) :
    ∑ e', (windowEnd B s s' x x').weight (e, e') = (endLaw B s x).weight e :=
  FiniteLaw.couplingWeight_row (endLaw B s x) (endLaw B s' x') e

/-- The column sums of the maximal coupling are the second endpoint weights. -/
theorem windowEnd_col (B : Base) (s s' : ℕ) (x x' e' : B.V) :
    ∑ e, (windowEnd B s s' x x').weight (e, e') = (endLaw B s' x').weight e' :=
  FiniteLaw.couplingWeight_column (endLaw B s x) (endLaw B s' x') e'

/-- Mixing the bridges from `x` with the endpoint weights gives the path weight. -/
theorem sum_endLaw_bridgeLaw (B : Base) (s : ℕ) (x : B.V) (a : Fin s → B.V) :
    ∑ e, (endLaw B s x).weight e * (bridgeLaw B s x e).weight a = pathWeight B x s a := by
  rw [← bridge_mixture B x s a]
  refine Finset.sum_congr rfl fun e _ => ?_
  change basePow B s x e * bridgeLawWeight B s x e a = basePow B s x e * bridgeWeight B s x e a
  unfold bridgeLawWeight
  split_ifs with h
  · rw [h, zero_mul, zero_mul]
  · rfl

/-- The first marginal of the window coupling: the weights of the first path sum to the
path weight of `pathLaw B s x`. -/
theorem windowCouple_fst_weight (B : Base) (s s' : ℕ) (x x' : B.V) (a : Fin s → B.V) :
    ∑ b, (windowCouple B s s' x x').weight (a, b) = (pathLaw B s x).weight a := by
  change ∑ b, windowWeight B s s' x x' (a, b) = pathWeight B x s a
  unfold windowWeight
  rw [Finset.sum_comm]
  have hz : ∀ z : B.V × B.V, ∑ b, (windowEnd B s s' x x').weight z *
      ((bridgeLaw B s x z.1).weight a * (bridgeLaw B s' x' z.2).weight b)
      = (windowEnd B s s' x x').weight z * (bridgeLaw B s x z.1).weight a := by
    intro z
    calc ∑ b, (windowEnd B s s' x x').weight z *
          ((bridgeLaw B s x z.1).weight a * (bridgeLaw B s' x' z.2).weight b)
        = ∑ b, ((windowEnd B s s' x x').weight z * (bridgeLaw B s x z.1).weight a) *
            (bridgeLaw B s' x' z.2).weight b :=
          Finset.sum_congr rfl fun b _ => by ring
      _ = ((windowEnd B s s' x x').weight z * (bridgeLaw B s x z.1).weight a) *
            ∑ b, (bridgeLaw B s' x' z.2).weight b := by rw [Finset.mul_sum]
      _ = (windowEnd B s s' x x').weight z * (bridgeLaw B s x z.1).weight a := by
          rw [(bridgeLaw B s' x' z.2).total, mul_one]
  simp only [hz]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.sum_mul, windowEnd_row]
  exact sum_endLaw_bridgeLaw B s x a

/-- The second marginal of the window coupling: the weights of the second path sum to the
path weight of `pathLaw B s' x'`. -/
theorem windowCouple_snd_weight (B : Base) (s s' : ℕ) (x x' : B.V) (b : Fin s' → B.V) :
    ∑ a, (windowCouple B s s' x x').weight (a, b) = (pathLaw B s' x').weight b := by
  change ∑ a, windowWeight B s s' x x' (a, b) = pathWeight B x' s' b
  unfold windowWeight
  rw [Finset.sum_comm]
  have hz : ∀ z : B.V × B.V, ∑ a, (windowEnd B s s' x x').weight z *
      ((bridgeLaw B s x z.1).weight a * (bridgeLaw B s' x' z.2).weight b)
      = (windowEnd B s s' x x').weight z * (bridgeLaw B s' x' z.2).weight b := by
    intro z
    calc ∑ a, (windowEnd B s s' x x').weight z *
          ((bridgeLaw B s x z.1).weight a * (bridgeLaw B s' x' z.2).weight b)
        = ∑ a, ((windowEnd B s s' x x').weight z * (bridgeLaw B s' x' z.2).weight b) *
            (bridgeLaw B s x z.1).weight a :=
          Finset.sum_congr rfl fun a _ => by ring
      _ = ((windowEnd B s s' x x').weight z * (bridgeLaw B s' x' z.2).weight b) *
            ∑ a, (bridgeLaw B s x z.1).weight a := by rw [Finset.mul_sum]
      _ = (windowEnd B s s' x x').weight z * (bridgeLaw B s' x' z.2).weight b := by
          rw [(bridgeLaw B s x z.1).total, mul_one]
  simp only [hz]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [← Finset.sum_mul, windowEnd_col]
  exact sum_endLaw_bridgeLaw B s' x' b

/-- The first marginal of the window coupling is the path law from `x`: for every function
`f` of the first path, the expectation under the window coupling equals `pathLaw` expectation. -/
theorem windowCouple_fst_expect (B : Base) (s s' : ℕ) (x x' : B.V) (f : (Fin s → B.V) → ℝ) :
    (windowCouple B s s' x x').expect (fun ww => f ww.1) = (pathLaw B s x).expect f := by
  unfold FiniteLaw.expect
  rw [Fintype.sum_prod_type]
  simp only [← Finset.sum_mul, windowCouple_fst_weight]

/-- The second marginal of the window coupling is the path law from `x'`: for every function
`g` of the second path, the expectation under the window coupling equals `pathLaw` expectation. -/
theorem windowCouple_snd_expect (B : Base) (s s' : ℕ) (x x' : B.V) (g : (Fin s' → B.V) → ℝ) :
    (windowCouple B s s' x x').expect (fun ww => g ww.2) = (pathLaw B s' x').expect g := by
  unfold FiniteLaw.expect
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [← Finset.sum_mul, windowCouple_snd_weight]

/-- The half `ℓ¹` distance between the endpoint laws `endLaw B s x` and `endLaw B s' x'`. -/
noncomputable def endTV (B : Base) (s s' : ℕ) (x x' : B.V) : ℝ :=
  (1 / 2) * ∑ e, |basePow B s x e - basePow B s' x' e|

/-- The endpoint distance is the deficit of the maximal coupling of the endpoint laws. -/
theorem endTV_eq_deficit (B : Base) (s s' : ℕ) (x x' : B.V) :
    endTV B s s' x x' = (endLaw B s x).deficit (endLaw B s' x') := by
  rw [FiniteLaw.deficit_half_l1]
  unfold endTV
  show (1 / 2 : ℝ) * ∑ e, |basePow B s x e - basePow B s' x' e|
    = (∑ e, |basePow B s x e - basePow B s' x' e|) / 2
  ring

/-- The endpoint distance is at most the sum of the two distances to the uniform law. -/
theorem endTV_le_tvToUniform (B : Base) (s s' : ℕ) (x x' : B.V) :
    endTV B s s' x x' ≤ tvToUniform B s x + tvToUniform B s' x' := by
  unfold endTV tvToUniform
  have hsum : (∑ e, |basePow B s x e - basePow B s' x' e|) ≤
      ∑ e, (|basePow B s x e - 1 / (B.card : ℝ)| + |basePow B s' x' e - 1 / (B.card : ℝ)|) := by
    apply Finset.sum_le_sum
    intro e _
    have h := abs_sub_le (basePow B s x e) (1 / (B.card : ℝ)) (basePow B s' x' e)
    rwa [abs_sub_comm (1 / (B.card : ℝ)) (basePow B s' x' e)] at h
  rw [Finset.sum_add_distrib] at hsum
  linarith

/-- The endpoint distance is at most `2 * (1/2) ^ (min s s' / τ)`, for any two lengths. -/
theorem endTV_le_dyadic (B : Base) (s s' : ℕ) (x x' : B.V) :
    endTV B s s' x x' ≤ 2 * (1 / 2 : ℝ) ^ (min s s' / silvestriMixingTime B) := by
  have h1 := endTV_le_tvToUniform B s s' x x'
  have hs : tvToUniform B s x ≤ (1 / 2 : ℝ) ^ (min s s' / silvestriMixingTime B) :=
    (tvToUniform_le_dyadic B s x).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (Nat.div_le_div_right (min_le_left s s')))
  have hs' : tvToUniform B s' x' ≤ (1 / 2 : ℝ) ^ (min s s' / silvestriMixingTime B) :=
    (tvToUniform_le_dyadic B s' x').trans (pow_le_pow_of_le_one (by norm_num) (by norm_num)
      (Nat.div_le_div_right (min_le_right s s')))
  linarith

/-- The expectation of an indicator is the weighted sum of the indicator values. -/
theorem event_eq_sum' {S : Type*} [Fintype S] (μ : FiniteLaw S) (P : S → Prop)
    [DecidablePred P] : μ.event P = ∑ z, μ.weight z * (if P z then 1 else 0) := by
  simp only [FiniteLaw.event, FiniteLaw.expect]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases h : P z <;> simp [h]

/-- A bridge weight is nonzero only on the paths that end at the bridge endpoint. -/
theorem pathEnd_eq_of_bridgeLaw_ne (B : Base) (s : ℕ) (x e : B.V) (w : Fin s → B.V)
    (hb : basePow B s x e ≠ 0) (h : (bridgeLaw B s x e).weight w ≠ 0) :
    pathEnd B x s w = e := by
  by_contra hne
  apply h
  change bridgeLawWeight B s x e w = 0
  unfold bridgeLawWeight
  rw [if_neg hb]
  simp [bridgeWeight, hne]

/-- The agreement mass of the bridges from the endpoint pair `z`: the total weight of the pairs
of paths whose endpoints agree. -/
noncomputable def agreeMass (B : Base) (s s' : ℕ) (x x' : B.V) (z : B.V × B.V) : ℝ :=
  ∑ ww : (Fin s → B.V) × (Fin s' → B.V),
    (bridgeLaw B s x z.1).weight ww.1 * (bridgeLaw B s' x' z.2).weight ww.2 *
      (if pathEnd B x s ww.1 = pathEnd B x' s' ww.2 then (1 : ℝ) else 0)

/-- The agreement mass is nonnegative. -/
theorem agreeMass_nonneg (B : Base) (s s' : ℕ) (x x' : B.V) (z : B.V × B.V) :
    0 ≤ agreeMass B s s' x x' z := by
  unfold agreeMass
  refine Finset.sum_nonneg fun ww _ => mul_nonneg
    (mul_nonneg ((bridgeLaw B s x z.1).nonneg ww.1) ((bridgeLaw B s' x' z.2).nonneg ww.2)) ?_
  split_ifs <;> norm_num

/-- When both endpoint masses at `e` are positive, the agreement mass of `(e, e)` is one. -/
theorem agreeMass_diag_eq_one (B : Base) (s s' : ℕ) (x x' e : B.V)
    (hs : basePow B s x e ≠ 0) (hs' : basePow B s' x' e ≠ 0) :
    agreeMass B s s' x x' (e, e) = 1 := by
  show ∑ ww : (Fin s → B.V) × (Fin s' → B.V),
      (bridgeLaw B s x e).weight ww.1 * (bridgeLaw B s' x' e).weight ww.2 *
        (if pathEnd B x s ww.1 = pathEnd B x' s' ww.2 then (1 : ℝ) else 0) = 1
  have hpt : ∀ ww : (Fin s → B.V) × (Fin s' → B.V),
      (bridgeLaw B s x e).weight ww.1 * (bridgeLaw B s' x' e).weight ww.2 *
        (if pathEnd B x s ww.1 = pathEnd B x' s' ww.2 then (1 : ℝ) else 0)
      = (bridgeLaw B s x e).weight ww.1 * (bridgeLaw B s' x' e).weight ww.2 := by
    intro ww
    by_cases h : (bridgeLaw B s x e).weight ww.1 * (bridgeLaw B s' x' e).weight ww.2 = 0
    · rw [h, zero_mul]
    · have h1 : (bridgeLaw B s x e).weight ww.1 ≠ 0 := left_ne_zero_of_mul h
      have h2 : (bridgeLaw B s' x' e).weight ww.2 ≠ 0 := right_ne_zero_of_mul h
      have e1 := pathEnd_eq_of_bridgeLaw_ne B s x e ww.1 hs h1
      have e2 := pathEnd_eq_of_bridgeLaw_ne B s' x' e ww.2 hs' h2
      rw [if_pos (e1.trans e2.symm), mul_one]
  rw [Finset.sum_congr rfl fun ww _ => hpt ww,
    sum_mul_pair (bridgeLaw B s x e).weight (bridgeLaw B s' x' e).weight,
    (bridgeLaw B s x e).total, (bridgeLaw B s' x' e).total, mul_one]

/-- The diagonal weight of the endpoint coupling is the minimum of the two endpoint masses. -/
theorem windowEnd_diag (B : Base) (s s' : ℕ) (x x' e : B.V) :
    (windowEnd B s s' x x').weight (e, e) = min (basePow B s x e) (basePow B s' x' e) :=
  FiniteLaw.coupling_diagonal (endLaw B s x) (endLaw B s' x') e

/-- The window endpoints agree with probability at least `1 - endTV`, the deficit of the
maximal coupling of the endpoint laws. -/
theorem windowCouple_agree_endTV (B : Base) (s s' : ℕ) (x x' : B.V) :
    1 - endTV B s s' x x' ≤
      (windowCouple B s s' x x').event (fun ww => pathEnd B x s ww.1 = pathEnd B x' s' ww.2) := by
  have hev : (windowCouple B s s' x x').event (fun ww => pathEnd B x s ww.1 = pathEnd B x' s' ww.2)
      = ∑ z : B.V × B.V, (windowEnd B s s' x x').weight z * agreeMass B s s' x x' z := by
    rw [event_eq_sum']
    unfold agreeMass
    simp only [Finset.mul_sum]
    show ∑ ww, windowWeight B s s' x x' ww * _ = _
    unfold windowWeight
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun ww _ => by ring
  have hlow : ∑ e : B.V, (windowEnd B s s' x x').weight (e, e) * agreeMass B s s' x x' (e, e)
      ≤ ∑ z : B.V × B.V, (windowEnd B s s' x x').weight z * agreeMass B s s' x x' z := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun e _ => ?_
    exact Finset.single_le_sum
      (f := fun e' => (windowEnd B s s' x x').weight (e, e') * agreeMass B s s' x x' (e, e'))
      (fun e' _ => mul_nonneg ((windowEnd B s s' x x').nonneg _)
        (agreeMass_nonneg B s s' x x' _)) (Finset.mem_univ e)
  have hdiag : ∑ e : B.V, (windowEnd B s s' x x').weight (e, e) * agreeMass B s s' x x' (e, e)
      = ∑ e : B.V, (windowEnd B s s' x x').weight (e, e) := by
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases hs : basePow B s x e = 0
    · rw [windowEnd_diag, hs, min_eq_left (basePow_nonneg B x' s' e), zero_mul]
    · by_cases ht : basePow B s' x' e = 0
      · rw [windowEnd_diag, ht, min_eq_right (basePow_nonneg B x s e), zero_mul]
      · rw [agreeMass_diag_eq_one B s s' x x' e hs ht, mul_one]
  have hsum_diag : ∑ e : B.V, (windowEnd B s s' x x').weight (e, e)
      = ∑ e : B.V, (endLaw B s x).common (endLaw B s' x') e :=
    Finset.sum_congr rfl fun e _ => FiniteLaw.coupling_diagonal (endLaw B s x) (endLaw B s' x') e
  have hdef := FiniteLaw.deficit_eq (endLaw B s x) (endLaw B s' x')
  have hD := endTV_eq_deficit B s s' x x'
  linarith

/-- The window endpoints agree with probability at least `1 - 2 * (1/2) ^ (min s s' / τ)`,
where `τ = silvestriMixingTime B`. The two lengths need not be equal. -/
theorem windowCouple_agreement (B : Base) (s s' : ℕ) (x x' : B.V) :
    1 - 2 * (1 / 2 : ℝ) ^ (min s s' / silvestriMixingTime B) ≤
      (windowCouple B s s' x x').event (fun ww => pathEnd B x s ww.1 = pathEnd B x' s' ww.2) := by
  have h := windowCouple_agree_endTV B s s' x x'
  have hE := endTV_le_dyadic B s s' x x'
  linarith

/-- For two paths of the same length `s`, the endpoints agree with probability at least
`1 - silvestriTV B s x x'`. -/
theorem windowCouple_agreement_same (B : Base) (s : ℕ) (x x' : B.V) :
    1 - silvestriTV B s x x' ≤
      (windowCouple B s s x x').event (fun ww => pathEnd B x s ww.1 = pathEnd B x' s ww.2) :=
  windowCouple_agree_endTV B s s x x'

end IdlaCyl.Silvestri
