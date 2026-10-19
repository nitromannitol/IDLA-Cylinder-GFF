/-
Nonvacuity of the stopped conditional mean at the complete graph on two vertices
(`paper/idla-cylinder-gff.tex:229`, `tex:1198-1202`).

`K2` (`IdlaCyl.PrInnerTail.K2`) is a legitimate paper base: two vertices, connected, vertex
transitive.  At stopping height `h = 1` and stopping site `ζ = (1, 1)` the hypotheses of the
stopped conditional mean hold, and the canonical driver `idlaMeasure K2` gives a positive
probability to the event where the stopped hitting probability is positive.

The two-vertex base does not satisfy the threshold `256 C_1⁴ + 1 ≤ N` of
`pr_inner_probability_bound`, so the `K2` facts are sub-lemma checks only.  The large-`N`
instance of that theorem is `pr_inner_probability_bound_completeBase_102401` below.
-/
import IdlaCyl.Support.PrInnerStopped.Composition
import IdlaCyl.Support.PrInnerStopped.Martingale
import IdlaCyl.Support.PrInnerTail.Nonvacuity

namespace IdlaCyl.PrInnerStopped

open MeasureTheory ProbabilityTheory
open IdlaCyl.PrInnerTail

/-- The stopping site `(1, 1)` of the base `K2`: the vertex `1` on the stopping layer `1`. -/
def K2Stop : Site K2 := ((1 : Fin 2), (1 : ℤ))

theorem K2_card_eq : K2.card = 2 := rfl

/-- At `K2`, the conditional mean of the stopped hitting probability at `ζ = (1, 1)` is `1/2`
given the stopped settle-site filtration of height `1`. -/
theorem K2_condExp_hitProb_stoppedSettleSite (k : ℕ) :
    (idlaMeasure K2)[fun ω : TrajSeq K2 => hitProb K2 K2Stop (stoppedSettleSite K2 1 ω k)
        | stoppedFiltration K2 1 k]
      =ᵐ[idlaMeasure K2] fun _ => (1 : ℝ) / 2 := by
  have h := condExp_hitProb_stoppedSettleSite K2 1 le_rfl K2Stop rfl k
  filter_upwards [h] with ω hω
  rw [hω, K2_card_eq]
  norm_num

/-- **A positive-probability event at `K2`.**  The stopped hitting probability `H_ζ` at the
settle site of the stopped process is positive on a set of positive `idlaMeasure K2` probability:
it is nonnegative and has conditional mean `1/2`, so it cannot vanish almost surely. -/
theorem K2_measure_hitProb_pos (k : ℕ) :
    0 < idlaMeasure K2 {ω : TrajSeq K2 | 0 < hitProb K2 K2Stop (stoppedSettleSite K2 1 ω k)} := by
  by_contra hcon
  have hzero : idlaMeasure K2 {ω : TrajSeq K2 | 0 < hitProb K2 K2Stop (stoppedSettleSite K2 1 ω k)}
      = 0 := le_antisymm (not_lt.mp hcon) zero_le
  have hae : ∀ᵐ ω ∂(idlaMeasure K2), hitProb K2 K2Stop (stoppedSettleSite K2 1 ω k) = 0 := by
    rw [ae_iff]
    refine measure_mono_null ?_ hzero
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact lt_of_le_of_ne (hitProb_nonneg _ _ _) (Ne.symm hω)
  have hint0 : ∫ ω, hitProb K2 K2Stop (stoppedSettleSite K2 1 ω k) ∂(idlaMeasure K2) = 0 :=
    integral_eq_zero_of_ae hae
  have htower : ∫ ω, (idlaMeasure K2)[fun ω : TrajSeq K2 =>
        hitProb K2 K2Stop (stoppedSettleSite K2 1 ω k) | stoppedFiltration K2 1 k] ω
        ∂(idlaMeasure K2)
      = ∫ ω, hitProb K2 K2Stop (stoppedSettleSite K2 1 ω k) ∂(idlaMeasure K2) :=
    integral_condExp ((stoppedFiltration K2 1).le k)
  have hcm : ∫ ω, (idlaMeasure K2)[fun ω : TrajSeq K2 =>
        hitProb K2 K2Stop (stoppedSettleSite K2 1 ω k) | stoppedFiltration K2 1 k] ω
        ∂(idlaMeasure K2)
      = ∫ _ : TrajSeq K2, (1 : ℝ) / 2 ∂(idlaMeasure K2) :=
    integral_congr_ae (K2_condExp_hitProb_stoppedSettleSite k)
  rw [hint0] at htower
  rw [htower] at hcm
  norm_num at hcm

/-- The complete graph on `N ≥ 2` vertices has `N` vertices. -/
theorem completeBase_card_eq (N : ℕ) (hN : 2 ≤ N) : (completeBase N hN).card = N :=
  Fintype.card_fin N

/-- **Large-`N` nonvacuity of `pr_inner_probability_bound` (`ν = 1`), for a base `B` with
`102401` vertices.**  The threshold `256 C_1⁴ + 1 = 102401` holds with equality for
`C_1 = 2√(ν+4) = 2√5` (`tex:1222-1225`), and `T = 4 · 10¹²` satisfies `16 C_1² N log N ≤ T`,
because `log N ≤ N - 1` and `320 N (N - 1) < 4 · 10¹²`.  The base is a variable here, so no tactic
evaluates its cardinality. -/
theorem pr_inner_probability_bound_card_102401 (B : Base) (hcard : B.card = 102401) (h : ℤ)
    (hh : h = ⌊((4000000000000 : ℕ) : ℝ) / (B.card : ℝ)
      - 2 * Real.sqrt (1 + 4)
        * Real.sqrt (((4000000000000 : ℕ) : ℝ) / (B.card : ℝ)
          * logTerm (B.card : ℝ) ((4000000000000 : ℕ) : ℝ))⌋) :
    1 ≤ h ∧
      idlaMeasure B {ω : TrajSeq B | ¬ R B (h : ℝ) ⊆ clusterTraj B ω 4000000000000}
        ≤ idlaMeasure B {ω : TrajSeq B | ¬ R B (h : ℝ) ⊆ stoppedCluster B h ω 4000000000000} ∧
      idlaMeasure B {ω : TrajSeq B | ¬ R B (h : ℝ) ⊆ stoppedCluster B h ω 4000000000000}
        ≤ ENNReal.ofReal ((B.card : ℝ) ^ (-((1 : ℝ) + 1))) := by
  have hcardR : (B.card : ℝ) = 102401 := by simp [hcard]
  have hsq : Real.sqrt ((1 : ℝ) + 4) ^ 2 = 5 := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + 4)]
    norm_num
  have hC2 : (2 * Real.sqrt ((1 : ℝ) + 4)) ^ 2 = 20 := by
    rw [mul_pow, hsq]
    norm_num
  have hC4 : (2 * Real.sqrt ((1 : ℝ) + 4)) ^ 4 = 400 := by
    rw [show (2 * Real.sqrt ((1 : ℝ) + 4)) ^ 4 = ((2 * Real.sqrt ((1 : ℝ) + 4)) ^ 2) ^ 2 by ring,
      hC2]
    norm_num
  have hN : 256 * (2 * Real.sqrt ((1 : ℝ) + 4)) ^ 4 + 1 ≤ (B.card : ℝ) := by
    rw [hC4, hcardR]
    norm_num
  have hTR : ((4000000000000 : ℕ) : ℝ) = 4000000000000 := by norm_num
  have hlog : Real.log (B.card : ℝ) ≤ 102400 := by
    have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 102401)
    rw [hcardR]
    linarith
  have hT : 16 * (2 * Real.sqrt ((1 : ℝ) + 4)) ^ 2 * (B.card : ℝ) * Real.log (B.card : ℝ)
      ≤ ((4000000000000 : ℕ) : ℝ) := by
    rw [hC2, hTR]
    have h2 : 16 * 20 * (B.card : ℝ) * Real.log (B.card : ℝ)
        ≤ 16 * 20 * (B.card : ℝ) * 102400 :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    have h3 : 16 * 20 * (B.card : ℝ) * 102400 ≤ 4000000000000 := by
      rw [hcardR]
      norm_num
    linarith
  exact pr_inner_probability_bound B 1 one_pos hN 4000000000000 hT h hh

/-- **Large-`N` nonvacuity of `pr_inner_probability_bound` at `ν = 1`.**  The complete graph on
`102401` vertices is a legitimate base (`tex:229`) with cardinality `102401`, so the instance of
`pr_inner_probability_bound_card_102401` at that base is a closed statement, with no hypothesis. -/
theorem pr_inner_probability_bound_completeBase_102401 :
    let B : Base := completeBase 102401 (by norm_num)
    let T : ℕ := 4000000000000
    let h : ℤ := ⌊(T : ℝ) / (B.card : ℝ)
      - 2 * Real.sqrt (1 + 4) * Real.sqrt ((T : ℝ) / (B.card : ℝ) * logTerm (B.card : ℝ) (T : ℝ))⌋
    1 ≤ h ∧
      idlaMeasure B {ω : TrajSeq B | ¬ R B (h : ℝ) ⊆ clusterTraj B ω T}
        ≤ idlaMeasure B {ω : TrajSeq B | ¬ R B (h : ℝ) ⊆ stoppedCluster B h ω T} ∧
      idlaMeasure B {ω : TrajSeq B | ¬ R B (h : ℝ) ⊆ stoppedCluster B h ω T}
        ≤ ENNReal.ofReal ((B.card : ℝ) ^ (-((1 : ℝ) + 1))) := by
  intro B _ h
  exact pr_inner_probability_bound_card_102401 B (completeBase_card_eq 102401 (by norm_num)) h rfl

end IdlaCyl.PrInnerStopped
