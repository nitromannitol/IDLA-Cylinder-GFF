/-
The lower tail of the stopped score (`paper/idla-cylinder-gff.tex:1194-1215`, `lem:M lower tail`).

The paper applies Freedman's inequality to the stopped martingale `M_ζ`, with increments in
`[-1/N, 1]` (`tex:1203-1204`) and predictable quadratic variation at most `T/N` (`tex:1208`).  The
library theorem `LatticeProb.freedman` gives `exp(-r²/(2(v + b r/3)))`; for `r ≤ 3v` with
`v = T/N` this is at most `exp(-r² N/(4T))`, which is the paper's bound on `0 ≤ ℓ ≤ T/(2N)`.
-/
import IdlaCyl.Support.PrInnerStopped.Martingale
import LatticeProb.Prob.Freedman

namespace IdlaCyl

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

variable (B : Base)

/-- **Lower tail of the stopped score** (`tex:1194-1197`).  For `1 ≤ T` and `0 ≤ ℓ ≤ T/(2N)`,
`P(M_ζ(T) ≤ -ℓ) ≤ exp(-ℓ² N/(4T))`, where `M_ζ(T)` is the stopped score on `stoppedFiltration`. -/
theorem stoppedScoreOf_lower_tail_stopped (h : ℤ) (hh : 1 ≤ h) (ζ : Site B) (hζ : ζ.2 = h)
    (T : ℕ) (hT : 1 ≤ T) (ℓ : ℝ) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ (T : ℝ) / (2 * (B.card : ℝ))) :
    idlaMeasure B {ω : TrajSeq B |
        stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T ω ≤ -ℓ}
      ≤ ENNReal.ofReal (Real.exp (-(ℓ ^ 2 * (B.card : ℝ) / (4 * T)))) := by
  have hmart := stoppedScoreOf_isMartingale_stopped B h hh ζ hζ
  have hM0 : (fun ω : TrajSeq B =>
      stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) 0 ω) = 0 := by
    funext ω
    simp [stoppedScoreOf]
  have hN : (0 : ℝ) < (B.card : ℝ) := by
    have h2 : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
    linarith
  have hNne : (B.card : ℝ) ≠ 0 := hN.ne'
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hv0 : (0 : ℝ) ≤ (T : ℝ) / (B.card : ℝ) := by positivity
  have hvpos : (0 : ℝ) < (T : ℝ) / (B.card : ℝ) := div_pos hTpos hN
  have hinc : ∀ i < T, ∀ ω : TrajSeq B,
      |stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) (i + 1) ω
        - stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) i ω| ≤ 1 :=
    fun i _ ω => abs_stoppedScore_increment B h ζ i ω
  -- the conditional variance of each increment is at most `1/N` (`tex:1203-1208`)
  have hterm : ∀ i ∈ Finset.range T, ∀ᵐ ω ∂(idlaMeasure B),
      ((idlaMeasure B)[fun ω' : TrajSeq B =>
          (stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) (i + 1) ω'
            - stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) i ω') ^ 2
          | stoppedFiltration B h i]) ω ≤ 1 / (B.card : ℝ) := by
    intro i _
    have hfun : (fun ω' : TrajSeq B =>
          (stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) (i + 1) ω'
            - stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) i ω') ^ 2)
        = fun ω' : TrajSeq B =>
          (hitProb B ζ (stoppedSettleSite B h ω' i) - 1 / (B.card : ℝ)) ^ 2 := by
      funext ω'
      congr 1
      simp only [stoppedScoreOf]
      rw [Finset.sum_range_succ]
      ring
    rw [hfun]
    filter_upwards [condExp_sq_stoppedSettleSite_le B h hh ζ hζ i] with ω hω
    have hle : (1 / (B.card : ℝ)) - (1 / (B.card : ℝ)) ^ 2 ≤ 1 / (B.card : ℝ) := by
      have : (0 : ℝ) ≤ (1 / (B.card : ℝ)) ^ 2 := sq_nonneg _
      linarith
    exact le_trans hω hle
  have hqv : ∀ᵐ ω ∂(idlaMeasure B), ∑ i ∈ Finset.range T,
      ((idlaMeasure B)[fun ω' : TrajSeq B =>
          (stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) (i + 1) ω'
            - stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) i ω') ^ 2
          | stoppedFiltration B h i]) ω ≤ (T : ℝ) / (B.card : ℝ) := by
    filter_upwards [(Filter.eventually_all_finset (Finset.range T)).mpr hterm] with ω hω
    calc ∑ i ∈ Finset.range T,
          ((idlaMeasure B)[fun ω' : TrajSeq B =>
            (stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) (i + 1) ω'
              - stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) i ω') ^ 2
            | stoppedFiltration B h i]) ω
        ≤ ∑ _i ∈ Finset.range T, 1 / (B.card : ℝ) :=
          Finset.sum_le_sum fun i hi => hω i hi
      _ = (T : ℝ) / (B.card : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hF := LatticeProb.freedman (P := idlaMeasure B) (ℱ := stoppedFiltration B h) hmart hM0
    one_pos hv0 hinc hqv ℓ hℓ0
  -- `ℓ ≤ T/(2N)` gives `ℓ N ≤ T/2` and `ℓ ≤ 3 T/N`
  have h2N : (0 : ℝ) < 2 * (B.card : ℝ) := by linarith
  have hT' : (T : ℝ) / (B.card : ℝ) * (B.card : ℝ) = (T : ℝ) := div_mul_cancel₀ _ hNne
  have hv_def : (T : ℝ) / (2 * (B.card : ℝ)) = ((T : ℝ) / (B.card : ℝ)) / 2 := by
    field_simp
  have hℓv : ℓ ≤ 3 * ((T : ℝ) / (B.card : ℝ)) := by
    rw [hv_def] at hℓ
    linarith
  have hexp : -(ℓ ^ 2 / (2 * ((T : ℝ) / (B.card : ℝ) + 1 * ℓ / 3)))
      ≤ -(ℓ ^ 2 * (B.card : ℝ) / (4 * (T : ℝ))) := by
    rw [neg_le_neg_iff, div_le_div_iff₀ (by linarith) (by linarith)]
    have h5 : ℓ ^ 2 * ((T : ℝ) / (B.card : ℝ) * (B.card : ℝ)) = ℓ ^ 2 * (T : ℝ) := by
      rw [hT']
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg ℓ) hN.le) (sub_nonneg.2 hℓv), h5]
  have hfin : idlaMeasure B {ω : TrajSeq B |
        stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T ω ≤ -ℓ}
      = ENNReal.ofReal ((idlaMeasure B {ω : TrajSeq B |
        stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T ω ≤ -ℓ}).toReal) :=
    (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  rw [hfin]
  refine ENNReal.ofReal_le_ofReal (le_trans hF ?_)
  exact Real.exp_le_exp.mpr hexp

end IdlaCyl
