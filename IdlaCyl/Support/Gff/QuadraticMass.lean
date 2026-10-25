module

/-
Source: paper/idla-cylinder-gff.tex, tex:1066-1087.
The quadratic mass converges in L¹ and in mean, with the bad-event and
shape-probability premises discharged from the printed hypotheses of th:GFF.
-/
public import IdlaCyl.Support.QmassL1
public import IdlaCyl.Frozen.ClmQOnEcV2

@[expose] public section

namespace IdlaCyl.Gff

open IdlaCyl.Defs Filter MeasureTheory
open scoped Topology

/-- One width constant supplies both the shape estimate and the vanishing
bad-event contribution used in the proof of `th:GFF` (`tex:1074-1085`). -/
theorem exists_width (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ N in atTop, idlaMeasure (U.B N) (shape U C y₀ N)ᶜ ≤
        ENNReal.ofReal ((N : ℝ) ^ (-(1 : ℝ)))) ∧
      Tendsto (fun N => ∫ ω, qmass U K α y₀ N ω *
        ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω
          ∂idlaMeasure (U.B N)) atTop (𝓝 0) := by
  obtain ⟨C₁, hC₁, hbad⟩ := Frozen.clm_q_on_ec_v2 U y₀ hy₀ K hK α hα γ hspec hgrowth
  obtain ⟨C₂, hC₂, hshape⟩ := QOnEc.shape_compl_le_eventually U y₀ hy₀ γ
    ((hspec 2 le_rfl hK).1) hgrowth 1 one_pos
  exact ⟨max C₁ C₂, hC₁.trans_le (le_max_left _ _),
    hshape _ (le_max_right _ _), hbad _ (le_max_left _ _)⟩

/-- The variance in Theorem 1.3 is nonnegative (`tex:407`). -/
theorem variance_nonneg (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (α : ℕ → ℝ → ℝ) (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) :
    0 ≤ variance K α γ y₀ := by
  apply Finset.sum_nonneg
  intro k hk
  obtain ⟨hk₂, hkK⟩ := Finset.mem_Icc.mp hk
  have hγ : 0 < γ k := (hspec k hk₂ hkK).2
  exact div_nonneg (mul_nonneg (sq_nonneg _)
    (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith)))) (by positivity)

/-- The `L¹` convergence asserted in the assembly proof, with no extra
probabilistic premises (`tex:1074-1085`). -/
theorem qmass_L1 (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    Tendsto (fun N => ∫ ω, |qmass U K α y₀ N ω - variance K α γ y₀|
      ∂idlaMeasure (U.B N)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hshape, hbad⟩ := exists_width U y₀ hy₀ K hK α hα γ hspec hgrowth
  have hprob : Tendsto (fun N => (idlaMeasure (U.B N) (shape U C y₀ N)ᶜ).toReal)
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop one_pos).comp tendsto_natCast_atTop_atTop
    refine squeeze_zero' (.of_forall fun _ => ENNReal.toReal_nonneg) ?_ hlim
    filter_upwards [hshape] with N hN
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hN).trans_eq
      (ENNReal.toReal_ofReal (Real.rpow_nonneg (Nat.cast_nonneg N) _))
  exact qmass_tendsto_variance_L1 U y₀ hy₀ K hK α hα γ hspec hgrowth C hC
    (QOnEc.integrable_qmass U K α y₀) hbad hprob

/-- The means of the quadratic masses converge to the printed variance
(`tex:1084-1087`). -/
theorem integral_qmass_tendsto (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    Tendsto (fun N => ∫ ω, qmass U K α y₀ N ω ∂idlaMeasure (U.B N))
      atTop (𝓝 (variance K α γ y₀)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (.of_forall fun _ => norm_nonneg _) ?_
    (qmass_L1 U y₀ hy₀ K hK α hα γ hspec hgrowth)
  filter_upwards with N
  have hint := QOnEc.integrable_qmass U K α y₀ N
  have heq : (∫ ω, qmass U K α y₀ N ω ∂idlaMeasure (U.B N)) - variance K α γ y₀ =
      ∫ ω, qmass U K α y₀ N ω - variance K α γ y₀ ∂idlaMeasure (U.B N) := by
    rw [integral_sub hint (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul]
  rw [heq]
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
    (fun ω : TrajSeq (U.B N) => qmass U K α y₀ N ω - variance K α γ y₀)

end IdlaCyl.Gff
