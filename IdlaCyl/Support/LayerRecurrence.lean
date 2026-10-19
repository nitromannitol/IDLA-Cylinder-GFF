/-
The canonical one-step occupation recurrence of `pr:apriori`
(`tex:583-619`, `eq:mu-recurrence`), and the resulting binomial bound.

`layerMean B t m` (defined in `Support/PrAprioriTail.lean`) is the paper's
`μ_m(t) = 𝔼 Z_m(t)`, the expected number of occupied sites of `clusterTraj B · t`
at vertical coordinate `m` under `idlaMeasure B`.  This file proves

  `μ_M(t+1) − μ_M(t) ≤ (1/N) μ_{M-1}(t)`   (`M ≥ 2`, `tex:590`)

by the conditional first-hit bound
`IdlaCyl.condExp_settleSite_level_le_layerCount`, and instantiates
`IdlaCyl.layerMean_le_binom_of_recurrence` to obtain
`μ_{m+1}(t) ≤ N^{-m} C(t, m+1)`.

Entirely on the canonical carrier (`TrajSeq`/`idlaMeasure`/`clusterTraj`); no
`Driver`/`driverLaw`/`cluster`.
-/
import IdlaCyl.Support.PrAprioriTail
import IdlaCyl.Support.PrAprioriSupport
import IdlaCyl.Support.CanonicalGrowth
import IdlaCyl.Support.CanonicalMeas

namespace IdlaCyl

open MeasureTheory Filter
open scoped BigOperators ENNReal

/-- `Z_m(t)` as a sum of indicators, the form in which it is an expectation. -/
theorem layerCount_eq_sum (B : Base) (ω : TrajSeq B) (t : ℕ) (m : ℤ) :
    (layerCount B ω t m : ℝ)
      = ∑ x : B.V, Set.indicator {x : B.V | (x, m) ∈ clusterTraj B ω t} (fun _ => (1 : ℝ)) x := by
  classical
  unfold layerCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Set.indicator_apply]
  by_cases h : (x, m) ∈ clusterTraj B ω t <;> simp [h]

theorem layerCount_le_card (B : Base) (ω : TrajSeq B) (t : ℕ) (m : ℤ) :
    layerCount B ω t m ≤ B.card := by
  rw [layerCount, Base.card]
  exact Finset.card_le_univ _

/-- Measurability of `Z_m(t)` in the trajectory, through its indicator form. -/
theorem measurable_layerCount (B : Base) (t : ℕ) (m : ℤ) :
    Measurable (fun ω : TrajSeq B => (layerCount B ω t m : ℝ)) := by
  classical
  rw [show (fun ω : TrajSeq B => (layerCount B ω t m : ℝ))
      = fun ω => ∑ x : B.V,
          Set.indicator {x : B.V | (x, m) ∈ clusterTraj B ω t} (fun _ => (1 : ℝ)) x from
    funext fun ω => layerCount_eq_sum B ω t m]
  exact Finset.measurable_sum _ fun x _ =>
    Measurable.indicator measurable_const (measurableSet_mem_clusterTraj B t (x, m))

theorem integrable_layerCount (B : Base) (t : ℕ) (m : ℤ) :
    Integrable (fun ω : TrajSeq B => (layerCount B ω t m : ℝ)) (idlaMeasure B) := by
  refine Integrable.of_bound (measurable_layerCount B t m).aestronglyMeasurable (B.card : ℝ) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast layerCount_le_card B ω t m

/-- **`μ_m(t)` as an integral of `Z_m(t)`.**  The two ways of writing the
expected occupation agree; this bridges the `Finset.sum`/probability definition
to the Bochner integral used in the recurrence. -/
theorem layerMean_eq_integral (B : Base) (t : ℕ) (m : ℤ) :
    layerMean B t m = ∫ ω : TrajSeq B, (layerCount B ω t m : ℝ) ∂idlaMeasure B := by
  classical
  unfold layerMean
  rw [show (∫ ω : TrajSeq B, (layerCount B ω t m : ℝ) ∂idlaMeasure B)
      = ∫ ω : TrajSeq B, ∑ x : B.V,
          Set.indicator {x : B.V | (x, m) ∈ clusterTraj B ω t} (fun _ => (1 : ℝ)) x
          ∂idlaMeasure B from by
    congr 1 with ω; exact layerCount_eq_sum B ω t m]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    exact ((integral_indicator_const (1 : ℝ) (μ := idlaMeasure B)
      (s := {ω : TrajSeq B | (x, m) ∈ clusterTraj B ω t})
      (measurableSet_mem_clusterTraj B t (x, m))).trans (by simp [Measure.real])).symm
  · intro x _
    exact (integrable_const (1 : ℝ)).indicator (measurableSet_mem_clusterTraj B t (x, m))

/-- `∑_x 1{(x,m) = s}` is `1` exactly when `s` lies on layer `m`. -/
theorem sum_indicator_eq_single (B : Base) (m : ℤ) (s : Site B) :
    (∑ x : B.V, (if ((x, m) : Site B) = s then (1 : ℝ) else 0))
      = if s.2 = m then (1 : ℝ) else 0 := by
  classical
  have key : (∑ x : B.V, (if ((x, m) : Site B) = s then (1 : ℝ) else 0))
      = (if ((s.1, m) : Site B) = s then (1 : ℝ) else 0) :=
    Finset.sum_eq_single s.1
      (fun x _ hx => by rw [if_neg]; intro hc; exact hx (congrArg Prod.fst hc))
      (fun hnot => absurd (Finset.mem_univ s.1) hnot)
  rw [key]
  by_cases hm : m = s.2
  · have hcond : ((s.1, m) : Site B) = s := by rw [hm]
    simp only [if_pos hcond, if_pos hm.symm]
  · have hcond : ¬ (((s.1, m) : Site B) = s) := fun hc => hm (congrArg Prod.snd hc)
    have hcond2 : ¬ (s.2 = m) := fun hc => hm hc.symm
    simp only [if_neg hcond, if_neg hcond2]

/-- **The one-step layer increment.**  On the a.s. event that the walk exits the
cluster, `Z_M(t+1) − Z_M(t)` is the indicator that the new settling site lies on
layer `M`. -/
theorem layerCount_succ_sub (B : Base) (ω : TrajSeq B) (t : ℕ) (M : ℤ)
    (h : settleSite B ω t ∉ clusterTraj B ω t) :
    (layerCount B ω (t + 1) M : ℝ) - (layerCount B ω t M : ℝ)
      = if (settleSite B ω t).2 = M then (1 : ℝ) else 0 := by
  classical
  rw [layerCount_eq_sum, layerCount_eq_sum, ← Finset.sum_sub_distrib]
  rw [clusterTraj_plus_ncard_of_succ]
  rw [show (∑ x : B.V,
        (Set.indicator {x : B.V | (x, M) ∈ clusterTraj B ω t ∪ {settleSite B ω t}}
            (fun _ => (1 : ℝ)) x
          - Set.indicator {x : B.V | (x, M) ∈ clusterTraj B ω t} (fun _ => (1 : ℝ)) x))
      = ∑ x : B.V, (if ((x, M) : Site B) = settleSite B ω t then (1 : ℝ) else 0) from by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Set.indicator_apply, Set.indicator_apply]
    simp only [Set.mem_setOf_eq]
    by_cases hs : ((x, M) : Site B) = settleSite B ω t
    · have hmem : ((x, M) : Site B) ∈ clusterTraj B ω t ∪ {settleSite B ω t} :=
        Set.mem_union_right _ hs
      have hnot : ((x, M) : Site B) ∉ clusterTraj B ω t := by rw [hs]; exact h
      rw [if_pos hmem, if_neg hnot, if_pos hs]; ring
    · by_cases hmem : ((x, M) : Site B) ∈ clusterTraj B ω t
      · rw [if_pos (Set.mem_union_left _ hmem), if_pos hmem, if_neg hs]; ring
      · have hnot : ((x, M) : Site B) ∉ clusterTraj B ω t ∪ {settleSite B ω t} := by
          rw [Set.mem_union, Set.mem_singleton_iff]
          rintro (h1 | h2)
          · exact hmem h1
          · exact hs h2
        rw [if_neg hnot, if_neg hmem, if_neg hs]; ring]
  exact sum_indicator_eq_single B M (settleSite B ω t)

/-- **`eq:mu-recurrence`** (`tex:590`): `μ_M(t+1) − μ_M(t) ≤ (1/N) μ_{M-1}(t)`
for `M ≥ 2`, where `N = |V_N|`.  The increment is the conditional probability
that the next settling site lands on layer `M`, bounded through the first-hit
uniformity `IdlaCyl.condExp_settleSite_level_le_layerCount`. -/
theorem layerMean_recurrence (B : Base) (M : ℤ) (hM : 2 ≤ M) (t : ℕ)
    (hrec : External.LazyRwRecurrent) :
    layerMean B (t + 1) M ≤ layerMean B t M + (1 / (B.card : ℝ)) * layerMean B t (M - 1) := by
  classical
  have h1 := integrable_layerCount B (t + 1) M
  have h2 := integrable_layerCount B t M
  have h3 := integrable_layerCount B t (M - 1)
  have hsub : layerMean B (t + 1) M - layerMean B t M
      = ∫ ω : TrajSeq B,
          ((layerCount B ω (t + 1) M : ℝ) - (layerCount B ω t M : ℝ)) ∂idlaMeasure B := by
    rw [layerMean_eq_integral, layerMean_eq_integral, integral_sub h1 h2]
  have hae : (fun ω : TrajSeq B =>
        ((layerCount B ω (t + 1) M : ℝ) - (layerCount B ω t M : ℝ)))
      =ᵐ[idlaMeasure B]
        (fun ω : TrajSeq B => if (settleSite B ω t).2 = M then (1 : ℝ) else 0) := by
    filter_upwards [exitTraj_ae_finite B t] with ω hω
    exact layerCount_succ_sub B ω t M (clusterTraj_plus_ncard_of_settle B ω t hω).1
  have hkey : layerMean B (t + 1) M - layerMean B t M
      ≤ (1 / (B.card : ℝ)) * layerMean B t (M - 1) := by
    rw [hsub, integral_congr_ae hae]
    rw [← integral_condExp ((idlaFiltration B).le t)
      (f := fun ω : TrajSeq B => if (settleSite B ω t).2 = M then (1 : ℝ) else 0)]
    have hbound := condExp_settleSite_level_le_layerCount B M hM t hrec
    have hmono : ∫ ω : TrajSeq B,
          (idlaMeasure B)[(fun ω : TrajSeq B => if (settleSite B ω t).2 = M then (1 : ℝ) else 0)
            | idlaFiltration B t] ω ∂idlaMeasure B
        ≤ ∫ ω : TrajSeq B, (1 / (B.card : ℝ)) * (layerCount B ω t (M - 1) : ℝ) ∂idlaMeasure B := by
      refine integral_mono_ae integrable_condExp (h3.const_mul _) ?_
      filter_upwards [hbound] with ω hω
      calc (idlaMeasure B)[(fun ω : TrajSeq B => if (settleSite B ω t).2 = M then (1 : ℝ) else 0)
            | idlaFiltration B t] ω
          ≤ (layerCount B ω t (M - 1) : ℝ) / (B.card : ℝ) := hω
        _ = (1 / (B.card : ℝ)) * (layerCount B ω t (M - 1) : ℝ) := by ring
    refine hmono.trans (le_of_eq ?_)
    rw [integral_const_mul, layerMean_eq_integral]
  linarith [hkey]

/-- One step adds at most one site to any layer. -/
theorem layerCount_succ_le (B : Base) (ω : TrajSeq B) (t : ℕ) (m : ℤ) :
    layerCount B ω (t + 1) m ≤ layerCount B ω t m + 1 := by
  classical
  have hreal : (layerCount B ω (t + 1) m : ℝ) ≤ (layerCount B ω t m : ℝ) + 1 := by
    have hdiff : (layerCount B ω (t + 1) m : ℝ) - (layerCount B ω t m : ℝ) ≤ (1 : ℝ) := by
      rw [layerCount_eq_sum, layerCount_eq_sum, ← Finset.sum_sub_distrib]
      rw [clusterTraj_plus_ncard_of_succ]
      calc (∑ x : B.V, (Set.indicator
            {x : B.V | (x, m) ∈ clusterTraj B ω t ∪ {settleSite B ω t}} (fun _ => (1 : ℝ)) x
            - Set.indicator {x : B.V | (x, m) ∈ clusterTraj B ω t} (fun _ => (1 : ℝ)) x))
          ≤ ∑ x : B.V, (if ((x, m) : Site B) = settleSite B ω t then (1 : ℝ) else 0) := by
            refine Finset.sum_le_sum fun x _ => ?_
            by_cases hs : x ∈ {x : B.V | (x, m) = settleSite B ω t}
            · have hsm : ((x, m) : Site B) = settleSite B ω t := hs
              by_cases hc : x ∈ {x : B.V | (x, m) ∈ clusterTraj B ω t}
              · have h1 : x ∈ {x : B.V | (x, m) ∈ clusterTraj B ω t ∪ {settleSite B ω t}} := Or.inl hc
                rw [Set.indicator_of_mem h1, Set.indicator_of_mem hc, if_pos hsm]
                norm_num
              · have h1 : x ∈ {x : B.V | (x, m) ∈ clusterTraj B ω t ∪ {settleSite B ω t}} := Or.inr hsm
                rw [Set.indicator_of_mem h1, Set.indicator_of_notMem hc, if_pos hsm]
                norm_num
            · have hsm : ((x, m) : Site B) ≠ settleSite B ω t := hs
              by_cases hc : x ∈ {x : B.V | (x, m) ∈ clusterTraj B ω t}
              · have h1 : x ∈ {x : B.V | (x, m) ∈ clusterTraj B ω t ∪ {settleSite B ω t}} := Or.inl hc
                rw [Set.indicator_of_mem h1, Set.indicator_of_mem hc, if_neg hsm]
                norm_num
              · have hnot : x ∉ {x : B.V | (x, m) ∈ clusterTraj B ω t ∪ {settleSite B ω t}} := by
                  rintro (h | h)
                  · exact hc h
                  · exact hsm h
                rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hc, if_neg hsm]
                norm_num
        _ = if (settleSite B ω t).2 = m then (1 : ℝ) else 0 :=
            sum_indicator_eq_single B m (settleSite B ω t)
        _ ≤ 1 := by split_ifs <;> norm_num
    linarith [hdiff]
  exact_mod_cast hreal

/-- At time `t` layer `1` carries at most `t` sites (`clusterTraj B · 0 = R_0` has
none, and each step adds at most one). -/
theorem layerCount_one_le (B : Base) (ω : TrajSeq B) (t : ℕ) :
    layerCount B ω t 1 ≤ t := by
  classical
  induction t with
  | zero =>
    rw [layerCount]
    refine le_of_eq (Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_))
    rw [Finset.mem_filter] at hx
    rw [show clusterTraj B ω 0 = R B 0 from rfl, mem_R] at hx
    norm_num at hx
  | succ n ih => exact (layerCount_succ_le B ω n 1).trans (by omega)

/-- `μ_1(t) ≤ t` (`tex:625`). -/
theorem layerMean_one_le (B : Base) (t : ℕ) : layerMean B t 1 ≤ (t : ℝ) := by
  rw [layerMean_eq_integral]
  calc ∫ ω : TrajSeq B, (layerCount B ω t 1 : ℝ) ∂idlaMeasure B
      ≤ ∫ _ω : TrajSeq B, (t : ℝ) ∂idlaMeasure B := by
        refine integral_mono_ae (integrable_layerCount B t 1) (integrable_const _) ?_
        filter_upwards with ω
        exact_mod_cast layerCount_one_le B ω t
    _ = (t : ℝ) := by simp

/-- **`LBG_up`** (`tex:585-619`): `μ_{m+1}(t) ≤ N^{-m} C(t, m+1)`, obtained from the
one-step recurrence by the deterministic binomial induction. -/
theorem layerMean_le_binom (B : Base) (hrec : External.LazyRwRecurrent) (m t : ℕ) :
    layerMean B t ((m : ℤ) + 1)
      ≤ (1 / (B.card : ℝ)) ^ m * (Nat.choose t (m + 1) : ℝ) := by
  have hN : 0 < B.card := by have h := B.nontrivial; simp only [Base.card]; omega
  have h := cylinder_binomial_recurrence (fun m t => layerMean B t ((m : ℤ) + 1)) B.card hN
    (fun m => le_of_eq (layerMean_zero B ((m : ℤ) + 1)
      (by exact (add_le_add_iff_right (1 : ℤ)).mpr (Int.natCast_nonneg m))))
    (fun t => layerMean_one_le B t) ?_
  · exact h m t
  · intro m t
    have hh := layerMean_recurrence B ((m : ℤ) + 2)
      (by exact (add_le_add_iff_right (2 : ℤ)).mpr (Int.natCast_nonneg m)) t hrec
    have hidx : ((m : ℤ) + 2) = ((((m + 1 : ℕ) : ℤ) + 1)) := by push_cast; ring
    have hidx2 : ((m : ℤ) + 2 - 1) = ((m : ℤ) + 1) := by ring
    rw [hidx2] at hh
    rw [← hidx]
    exact hh

end IdlaCyl
