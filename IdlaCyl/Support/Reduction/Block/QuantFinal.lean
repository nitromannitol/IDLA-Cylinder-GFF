import IdlaCyl.Support.Reduction.Block.QuantRound
import IdlaCyl.Support.Reduction.Block.QuantAssemble
import IdlaCyl.Support.Reduction.Block.FutureLiftAssemble

/-!
# The quantitative reduction

The three strengthenings of `pr:reduction` registered in `Frozen/PrReductionQuant.lean`,
`Frozen/PrReductionStrong.lean` and `Frozen/PrReductionAlphaStrong.lean`: the endpoint couplings of
`Block/QuantAssemble.lean`, with the round `quant_round`, lifted to couplings of the driving
sequences that agree at every later addition (`lift_cluster_coupling_future`).
-/

namespace IdlaCyl.Reduction

open MeasureTheory
open scoped ENNReal

/-- A failure bound `μ Eᶜ ≤ ε` gives `μ E ≥ 1 - ε` for a probability measure, for any set `E`. -/
theorem ofReal_one_sub_le_of_compl {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Set Ω) (ε : ℝ) (hε : 0 ≤ ε)
    (h : μ Eᶜ ≤ ENNReal.ofReal ε) : ENNReal.ofReal (1 - ε) ≤ μ E := by
  have h1 : (1 : ℝ≥0∞) ≤ μ E + ENNReal.ofReal ε := by
    calc (1 : ℝ≥0∞) = μ (E ∪ Eᶜ) := by rw [Set.union_compl_self, measure_univ]
      _ ≤ μ E + μ Eᶜ := measure_union_le _ _
      _ ≤ μ E + ENNReal.ofReal ε := add_le_add le_rfl h
  rcases le_or_gt 1 ε with h1ε | hε1
  · rw [ENNReal.ofReal_of_nonpos (by linarith)]
    exact zero_le
  · have hsum : ENNReal.ofReal (1 - ε) + ENNReal.ofReal ε = 1 := by
      rw [← ENNReal.ofReal_add (by linarith) hε, sub_add_cancel, ENNReal.ofReal_one]
    rw [← hsum] at h1
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h1

/-- The lift used by the three statements: an endpoint coupling with failure allowance `ε` gives a
coupling of the driving sequences that agree at every later addition with probability `≥ 1 - ε`. -/
theorem future_coupling_of_cluster (B : Base) (T T' k : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (hc : ClusterCoupling B (flatClusterLaw B T) (flatClusterLaw B T') k ε) :
    ∃ μ : Measure (TrajSeq B × TrajSeq B),
      μ.map (Prod.fst : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
      μ.map (Prod.snd : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
      ENNReal.ofReal (1 - ε) ≤
        μ {p | ∀ s : ℕ, clusterTraj B p.1 (T + s) =
          shiftCluster B k (clusterTraj B p.2 (T' + s))} := by
  obtain ⟨μ, hf, hs, he⟩ := lift_cluster_coupling_future B T T' k ε hc
  haveI : IsProbabilityMeasure μ := coupling_isProbability B μ hf
  exact ⟨μ, hf, hs, ofReal_one_sub_le_of_compl μ _ ε hε he⟩

/-- The round of the quantitative reduction, in the form taken by `Block/QuantAssemble.lean`. -/
theorem quant_round_all : ∀ (B : Base) (S : SpectralData B) (H t : ℕ), 1 ≤ H →
    3 * (2 * (B.card * H)) ≤ t →
    ClusterCoupling B (flatClusterLaw B t)
      (flatClusterLaw B (t - B.card * H * (t / (2 * (B.card * H)))))
      (H * (t / (2 * (B.card * H))))
      ((((t / (2 * (B.card * H)) : ℕ) : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4))
        + 2 * ((t : ℝ) * explicitEta B S H)) :=
  fun B S H t hH h3 => quant_round B S H t hH h3

/-- **The quantitative reduction**; the statement of
`Frozen.pr_reduction_quant`. -/
theorem pr_reduction_quant_proof (B : Base) (S : SpectralData B) (T : ℕ) (hT : 1 ≤ T)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ T' k : ℕ, 1 ≤ T' ∧ T' ≤ T ∧
      T' < 6 * (B.card * ⌈4 * Real.sqrt S.relaxTime *
        Real.log (2 * ((max B.card T : ℕ) : ℝ) ^ 2 / ε)⌉₊) ∧
      T' + B.card * k = T ∧
      ∃ μ : Measure (TrajSeq B × TrajSeq B),
        μ.map (Prod.fst : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
        μ.map (Prod.snd : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
        ENNReal.ofReal (1 - ε) ≤
          μ {p | ∀ s : ℕ, clusterTraj B p.1 (T + s) =
            shiftCluster B k (clusterTraj B p.2 (T' + s))} := by
  obtain ⟨T', k, h1, h2, h3, h4, hc⟩ :=
    quant_cluster_coupling_of_round quant_round_all B S T hT ε hε hε1
  exact ⟨T', k, h1, h2, h3, h4, future_coupling_of_cluster B T T' k ε hε.le hc⟩

/-- **The reduction in the polynomial range**; the statement of
`Frozen.pr_reduction_strong`. -/
theorem pr_reduction_strong_proof (ν : ℝ) (hν : 0 < ν) (m : ℝ) (hm : 1 ≤ m) (B : Base)
    (hN : 3 ≤ B.card) (S : SpectralData B) (T : ℕ) (hT : 1 ≤ T)
    (hTm : (T : ℝ) ≤ (B.card : ℝ) ^ m) :
    ∃ T' k : ℕ, 1 ≤ T' ∧ T' ≤ T ∧
      (T' : ℝ) ≤ 6 * (4 * (ν + 2 * m + 2) + 1) * B.card * Real.sqrt S.relaxTime *
        Real.log B.card ∧
      (T' : ℝ) ≤ Real.sqrt 2 * (6 * (4 * (ν + 2 * m + 2) + 1)) * B.card *
        Real.sqrt (mixingTime B) * Real.log B.card ∧
      T' + B.card * k = T ∧
      ∃ μ : Measure (TrajSeq B × TrajSeq B),
        μ.map (Prod.fst : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
        μ.map (Prod.snd : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
        ENNReal.ofReal (1 - (B.card : ℝ) ^ (-(ν + 1))) ≤
          μ {p | ∀ s : ℕ, clusterTraj B p.1 (T + s) =
            shiftCluster B k (clusterTraj B p.2 (T' + s))} := by
  obtain ⟨T', k, h1, h2, h3, h4, h5, hc⟩ :=
    strong_cluster_coupling_of_round quant_round_all ν hν m hm B hN S T hT hTm
  exact ⟨T', k, h1, h2, h3, h4, h5,
    future_coupling_of_cluster B T T' k _ (Real.rpow_nonneg (Nat.cast_nonneg _) _) hc⟩

/-- **The reduction with an arbitrary coefficient and an explicit cutoff**;
the statement of `Frozen.pr_reduction_alpha_strong`. -/
theorem pr_reduction_alpha_strong_proof (ν : ℝ) (hν : 0 < ν) (m : ℝ) (hm : 1 ≤ m) (α : ℝ)
    (hα : 0 < α) (B : Base)
    (hN : max 3 ⌈Real.exp (Real.sqrt 2 * (6 * (4 * (ν + 2 * m + 2) + 1)) / α)⌉₊ ≤ B.card)
    (T : ℕ) (hT : 1 ≤ T) (hTm : (T : ℝ) ≤ (B.card : ℝ) ^ m) :
    ∃ T' k : ℕ, 1 ≤ T' ∧ (T' : ℝ) ≤ α * Defs.sharp B ∧ T' + B.card * k = T ∧
      ∃ μ : Measure (TrajSeq B × TrajSeq B),
        μ.map (Prod.fst : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
        μ.map (Prod.snd : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
        ENNReal.ofReal (1 - (B.card : ℝ) ^ (-(ν + 1))) ≤
          μ {p | ∀ s : ℕ, clusterTraj B p.1 (T + s) =
            shiftCluster B k (clusterTraj B p.2 (T' + s))} := by
  obtain ⟨T', k, h1, h2, h3, hc⟩ :=
    alpha_cluster_coupling_of_round quant_round_all ν hν m hm α hα B hN T hT hTm
  exact ⟨T', k, h1, h2, h3,
    future_coupling_of_cluster B T T' k _ (Real.rpow_nonneg (Nat.cast_nonneg _) _) hc⟩

end IdlaCyl.Reduction
