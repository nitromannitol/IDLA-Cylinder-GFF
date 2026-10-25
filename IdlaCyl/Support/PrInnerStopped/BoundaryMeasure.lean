module

/-
The boundary inclusion and the per-site estimate, almost surely (`paper/idla-cylinder-gff.tex:1227-1251`).

The pathwise inclusion `{ζ ∉ Ā_h(T)} ⊆ {M_ζ(T) < -ℓ}` of `Boundary.lean` holds under the almost sure
pathwise hypotheses of the stopped process (`idlaMeasure_ae_stopped_hyp`).  Together with the lower
tail of `LowerTail.lean` it gives the per-site estimate `P(ζ ∉ Ā_h(T)) ≤ exp(-ℓ² N/(4T))`.
-/
public import IdlaCyl.Support.PrInnerStopped.Boundary
public import IdlaCyl.Support.PrInnerStopped.LowerTail
public import IdlaCyl.Support.StoppedAe

@[expose] public section

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable (B : Base)

/-- **Boundary inclusion, in measure** (`tex:1249-1251`): for `h + ℓ ≤ T/N`,
`P(ζ ∉ Ā_h(T)) ≤ P(M_ζ(T) ≤ -ℓ)`. -/
theorem measure_not_mem_stoppedCluster_le_score (h : ℤ) (hh : 1 ≤ h) (ζ : Site B) (hζ : ζ.2 = h)
    (T : ℕ) (ℓ : ℝ) (hℓ : (h : ℝ) + ℓ ≤ (T : ℝ) / (B.card : ℝ)) :
    idlaMeasure B {ω : TrajSeq B | ζ ∉ stoppedCluster B h ω T}
      ≤ idlaMeasure B {ω : TrajSeq B |
          stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T ω ≤ -ℓ} := by
  refine measure_mono_ae ?_
  filter_upwards [idlaMeasure_ae_stopped_hyp B] with ω hω
  intro hnot
  exact (stoppedScoreOf_lt_neg_of_not_mem B h hh ζ hζ T ℓ ω hω.1 hω.2.1
    (fun t => hω.2.2.1 t h hh) hnot hℓ).le

/-- **Per-site estimate** (`tex:1233-1235`, `goal_inner`).  For `1 ≤ T`, `0 ≤ ℓ ≤ T/(2N)` and
`h + ℓ ≤ T/N`, the probability that the site `ζ` on the stopping layer is not in `Ā_h(T)` is at
most `exp(-ℓ² N/(4T))`. -/
theorem measure_not_mem_stoppedCluster_le_exp (h : ℤ) (hh : 1 ≤ h) (ζ : Site B) (hζ : ζ.2 = h)
    (T : ℕ) (hT : 1 ≤ T) (ℓ : ℝ) (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ (T : ℝ) / (2 * (B.card : ℝ)))
    (hℓh : (h : ℝ) + ℓ ≤ (T : ℝ) / (B.card : ℝ)) :
    idlaMeasure B {ω : TrajSeq B | ζ ∉ stoppedCluster B h ω T}
      ≤ ENNReal.ofReal (Real.exp (-(ℓ ^ 2 * (B.card : ℝ) / (4 * T)))) :=
  (measure_not_mem_stoppedCluster_le_score B h hh ζ hζ T ℓ hℓh).trans
    (stoppedScoreOf_lower_tail_stopped B h hh ζ hζ T hT ℓ hℓ0 hℓ)

end IdlaCyl
