module

/-
Source: paper/idla-cylinder-gff.tex, tex:1066-1072.
The zero-variance case follows from the second-moment identity and Markov's
inequality. Combining it with McLeish handles every nonnegative variance.
-/
public import IdlaCyl.Support.Gff.Positive
public import IdlaCyl.Support.Gff.SecondMoment

@[expose] public section

namespace IdlaCyl.Gff

open IdlaCyl.Defs Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- The second moments of the row sums converge to the printed variance. -/
theorem integral_product_sum_sq_tendsto (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    Tendsto (fun N => ∫ ω : Space U,
      (∑ k ∈ Finset.range (time U y₀ N), increment U K α y₀ N k ω) ^ 2 ∂law U)
      atTop (𝓝 (variance K α γ y₀)) := by
  apply (integral_qmass_tendsto U y₀ hy₀ K hK α hα γ hspec hgrowth).congr'
  filter_upwards [eventually_rows U y₀ hy₀ K] with N hN
  symm
  change (∫ ω : Space U,
    (∑ k ∈ Finset.range (time U y₀ N), gffIncrement U K α y₀ N k (ω N)) ^ 2 ∂law U) = _
  rw [integral_eval U N _ ((Finset.measurable_sum _
    (fun k _ => measurable_increment U K α y₀ N k)).pow_const 2)]
  exact integral_sum_sq_eq_qmass U K α y₀ N hN.1 hN.2.1

/-- When the variance is zero the row sums converge in probability to zero. -/
theorem sums_tendstoInMeasure_zero (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition)
    (hσ : variance K α γ y₀ = 0) :
    TendstoInMeasure (law U)
      (fun N ω => ∑ k ∈ Finset.range (time U y₀ N), increment U K α y₀ N k ω)
      atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hlim := (integral_product_sum_sq_tendsto U y₀ hy₀ K hK α hα γ hspec hgrowth).div_const (ε ^ 2)
  rw [hσ, zero_div] at hlim
  refine squeeze_zero' (.of_forall fun _ => measureReal_nonneg) ?_ hlim
  filter_upwards with N
  have hint := (eval_preserving U N).integrable_comp_of_integrable
    (memLp_sum U K α y₀ N (time U y₀ N)).integrable_sq
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := law U)
    (.of_forall fun ω : Space U => sq_nonneg
      (∑ k ∈ Finset.range (time U y₀ N), increment U K α y₀ N k ω)) hint (ε ^ 2)
  have hsubset : {ω : Space U | ε ≤
      ‖(∑ k ∈ Finset.range (time U y₀ N), increment U K α y₀ N k ω) - 0‖} ⊆
      {ω : Space U | ε ^ 2 ≤
        (∑ k ∈ Finset.range (time U y₀ N), increment U K α y₀ N k ω) ^ 2} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs] at hω ⊢
    nlinarith [sq_abs (∑ k ∈ Finset.range (time U y₀ N), increment U K α y₀ N k ω)]
  exact (measureReal_mono hsubset).trans ((le_div_iff₀ (sq_pos_of_pos hε)).mpr (by
    simpa only [mul_comm] using hmark))

/-- The canonical row sums converge to the claimed Gaussian for every
variance, including zero (`tex:1066-1112`). -/
theorem sums_tendstoInDistribution (hclt : IdlaCyl.External.martingale_clt_v2)
    (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    TendstoInDistribution
      (fun N ω => ∑ k ∈ Finset.range (time U y₀ N), increment U K α y₀ N k ω)
      atTop (id : ℝ → ℝ) (fun _ => law U)
      (gaussianReal 0 (Real.toNNReal (variance K α γ y₀))) := by
  rcases (variance_nonneg U y₀ hy₀ K α γ hspec).eq_or_lt with hσ | hσ
  · have hz := sums_tendstoInMeasure_zero U y₀ hy₀ K hK α hα γ hspec hgrowth hσ.symm
    have hdist := hz.tendstoInDistribution (fun N =>
      (Finset.measurable_sum _ (fun k _ =>
        (measurable_increment U K α y₀ N k).comp (eval_preserving U N).measurable)).aemeasurable)
    refine ⟨hdist.forall_aemeasurable, measurable_id.aemeasurable, ?_⟩
    convert hdist.tendsto using 1
    congr 1
    apply Subtype.ext
    simp only [hσ.symm, Real.toNNReal_zero, gaussianReal_zero_var, Measure.map_id,
      Measure.map_const, measure_univ, one_smul]
  · exact sums_tendstoInDistribution_pos hclt U y₀ hy₀ K hK α hα γ hspec hgrowth hσ

end IdlaCyl.Gff
