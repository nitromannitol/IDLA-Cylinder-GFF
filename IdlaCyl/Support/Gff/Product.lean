/-
Source: paper/idla-cylinder-gff.tex, tex:882-912,1074-1112.
All rows of the martingale array on the product of the canonical IDLA spaces.
Coordinate evaluation preserves the row laws, martingales, and expectations.
-/
import IdlaCyl.Support.Gff.Maximum
import IdlaCyl.Support.MartingaleTransport
import IdlaCyl.External.MartingaleCltV2

namespace IdlaCyl.Gff

open IdlaCyl.Defs Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- A common sample space for all rows of the array. -/
abbrev Space (U : Setup) := (N : ℕ) → TrajSeq (U.B N)

/-- Independent canonical IDLA coordinates, one for each size. -/
noncomputable def law (U : Setup) : Measure (Space U) :=
  Measure.infinitePi (fun N => idlaMeasure (U.B N))

instance law_isProbabilityMeasure (U : Setup) : IsProbabilityMeasure (law U) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.infinitePi (fun N => idlaMeasure (U.B N))))

theorem eval_preserving (U : Setup) (N : ℕ) :
    MeasurePreserving (fun ω : Space U => ω N) (law U) (idlaMeasure (U.B N)) :=
  measurePreserving_eval_infinitePi (fun N => idlaMeasure (U.B N)) N

/-- Integrals on a coordinate agree with the original row integrals. -/
theorem integral_eval (U : Setup) (N : ℕ) (f : TrajSeq (U.B N) → ℝ)
    (hf : Measurable f) :
    (∫ ω : Space U, f (ω N) ∂law U) = ∫ ω, f ω ∂idlaMeasure (U.B N) := by
  have h := integral_map (eval_preserving U N).measurable.aemeasurable
    (μ := law U) (φ := fun ω : Space U => ω N)
    (by rw [(eval_preserving U N).map_eq]; exact hf.aestronglyMeasurable)
  rw [(eval_preserving U N).map_eq] at h
  exact h.symm

/-- The row filtration pulled back to the common sample space. -/
noncomputable def rowFiltration (U : Setup) (N : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace (Space U)) :=
  filtrationComap (eval_preserving U N).measurable (idlaFiltration (U.B N))

/-- The literal paper increment evaluated on the corresponding coordinate. -/
noncomputable def increment (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ)
    (N k : ℕ) (ω : Space U) : ℝ := gffIncrement U K α y₀ N k (ω N)

theorem increment_martingale (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ)
    (N : ℕ) (hK : K ≤ (U.B N).card) :
    Martingale (fun t ω => ∑ k ∈ Finset.range t, increment U K α y₀ N k ω)
      (rowFiltration U N) (law U) :=
  martingale_comp_measurePreserving (eval_preserving U N)
    (gffIncrement_martingale U K α y₀ N hK)

theorem qmass_product_L1 (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    Tendsto (fun N => ∫ ω : Space U, |qmass U K α y₀ N (ω N) - variance K α γ y₀|
      ∂law U) atTop (𝓝 0) := by
  have heq : ∀ N, (∫ ω : Space U, |qmass U K α y₀ N (ω N) - variance K α γ y₀| ∂law U) =
      ∫ ω, |qmass U K α y₀ N ω - variance K α γ y₀| ∂idlaMeasure (U.B N) := by
    intro N
    exact integral_eval U N _ (((QOnEc.measurable_QN (U.B N) U.a (time U y₀ N)
      (psi U K α y₀ N)).sub measurable_const).abs)
  simp_rw [heq]
  exact qmass_L1 U y₀ hy₀ K hK α hα γ hspec hgrowth

/-- Condition (c), before replacing the quadratic mass by the sum of squares. -/
theorem qmass_tendstoInMeasure (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    TendstoInMeasure (law U) (fun N ω => qmass U K α y₀ N (ω N)) atTop
      (fun _ => variance K α γ y₀) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hlim := (qmass_product_L1 U y₀ hy₀ K hK α hα γ hspec hgrowth).div_const ε
  simp only [zero_div] at hlim
  refine squeeze_zero' (.of_forall fun _ => measureReal_nonneg) ?_ hlim
  filter_upwards with N
  have hint := (eval_preserving U N).integrable_comp_of_integrable
    ((QOnEc.integrable_qmass U K α y₀ N).sub (integrable_const (variance K α γ y₀))).abs
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (μ := law U) (.of_forall fun ω : Space U => abs_nonneg
      (qmass U K α y₀ N (ω N) - variance K α γ y₀)) hint ε
  rw [le_div_iff₀ hε]
  simpa only [Real.norm_eq_abs, mul_comm] using hmark

/-- The maximal squared increment tends to zero in mean on the common space. -/
theorem integral_product_maxSq_tendsto_zero (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    Tendsto (fun N => ∫ ω : Space U, maxSq U K α y₀ N (time U y₀ N) (ω N) ∂law U)
      atTop (𝓝 0) := by
  simp_rw [integral_eval U _ _ (measurable_maxSq U K α y₀ _ _)]
  exact integral_maxSq_tendsto_zero U y₀ hy₀ K hK α hα γ hspec hgrowth

end IdlaCyl.Gff
