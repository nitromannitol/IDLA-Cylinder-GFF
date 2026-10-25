module

/-
Source: paper/idla-cylinder-gff.tex, tex:882-912,1074-1112.
McLeish's three conditions for the canonical array and the positive-variance
conclusion on the common probability space. A finite shift removes empty rows.
-/
public import IdlaCyl.Support.Gff.Product

@[expose] public section

namespace IdlaCyl.Gff

open IdlaCyl.Defs Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- Eventually the rows are nonempty and contain all the prescribed modes. -/
theorem eventually_rows (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀) (K : ℕ) :
    ∀ᶠ N in atTop, 2 ≤ N ∧ K ≤ (U.B N).card ∧ 0 < time U y₀ N := by
  have hh : Tendsto (height U y₀) atTop atTop :=
    tendsto_nat_floor_atTop.comp (U.a_tendsto.const_mul_atTop hy₀)
  filter_upwards [eventually_ge_atTop (max K 2), hh.eventually_ge_atTop 1] with N hN hhN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  refine ⟨hN2, ?_, ?_⟩
  · rw [U.card_eq N hN2]
    exact (le_max_left _ _).trans hN
  · exact Nat.mul_pos (lt_of_lt_of_le (by norm_num) (U.B N).nontrivial) hhN

/-- The sums of squares converge to the variance on the common space, (c). -/
theorem squares_tendstoInMeasure (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    TendstoInMeasure (law U)
      (fun N ω => ∑ k ∈ Finset.range (time U y₀ N), increment U K α y₀ N k ω ^ 2)
      atTop (fun _ => variance K α γ y₀) := by
  apply (qmass_tendstoInMeasure U y₀ hy₀ K hK α hα γ hspec hgrowth).congr'
    (h_right := EventuallyEq.rfl)
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hae := (eval_preserving U N).quasiMeasurePreserving.ae
    (gffIncrement_sq_sum_eq_qmass U K α y₀ N hN)
  filter_upwards [hae] with ω hω using hω.symm

/-- The shifted nonempty maximal absolute increment tends to zero, (b). -/
theorem maximum_tendstoInMeasure (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition)
    (N₀ : ℕ) (ht : ∀ n, 0 < time U y₀ (n + N₀)) :
    TendstoInMeasure (law U) (fun n ω =>
      (Finset.range (time U y₀ (n + N₀))).sup'
        (Finset.nonempty_range_iff.mpr (ht n).ne')
        (fun k => |increment U K α y₀ (n + N₀) k ω|)) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hlim := ((integral_product_maxSq_tendsto_zero U y₀ hy₀ K hK α hα γ hspec hgrowth).comp
    (tendsto_add_atTop_nat N₀)).div_const (ε ^ 2)
  simp only [zero_div, Function.comp_def] at hlim
  refine squeeze_zero' (.of_forall fun _ => measureReal_nonneg) ?_ hlim
  filter_upwards with n
  have hint := (eval_preserving U (n + N₀)).integrable_comp_of_integrable
    (integrable_maxSq U K α y₀ (n + N₀) (time U y₀ (n + N₀)))
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := law U)
    (.of_forall fun ω => maxSq_nonneg U K α y₀ (n + N₀) (time U y₀ (n + N₀)) (ω (n + N₀)))
    hint (ε ^ 2)
  have hsubset : {ω : Space U | ε ≤ ‖(Finset.range (time U y₀ (n + N₀))).sup'
      (Finset.nonempty_range_iff.mpr (ht n).ne')
      (fun k => |increment U K α y₀ (n + N₀) k ω|) - 0‖} ⊆
      {ω : Space U | ε ^ 2 ≤ maxSq U K α y₀ (n + N₀) (time U y₀ (n + N₀)) (ω (n + N₀))} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hn : 0 ≤ (Finset.range (time U y₀ (n + N₀))).sup'
        (Finset.nonempty_range_iff.mpr (ht n).ne')
        (fun k => |increment U K α y₀ (n + N₀) k ω|) :=
      (abs_nonneg _).trans (Finset.le_sup'
        (fun k => |increment U K α y₀ (n + N₀) k ω|) (Finset.mem_range.mpr (ht n)))
    rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hn] at hω
    obtain ⟨k, hk, hεk⟩ := (Finset.le_sup'_iff (Finset.nonempty_range_iff.mpr (ht n).ne')).mp hω
    have hsq : ε ^ 2 ≤ increment U K α y₀ (n + N₀) k ω ^ 2 := by
      nlinarith [sq_abs (increment U K α y₀ (n + N₀) k ω)]
    exact hsq.trans (sq_le_maxSq U K α y₀ (n + N₀) _ k (Finset.mem_range.mp hk) _)
  exact (measureReal_mono hsubset).trans ((le_div_iff₀ (sq_pos_of_pos hε)).mpr (by
    simpa only [mul_comm] using hmark))

/-- McLeish's conclusion for positive printed variance, after undoing the
finite shift of rows (`tex:1072-1112`). -/
theorem sums_tendstoInDistribution_pos (hclt : IdlaCyl.External.martingale_clt_v2)
    (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition)
    (hσ : 0 < variance K α γ y₀) :
    TendstoInDistribution
      (fun N ω => ∑ k ∈ Finset.range (time U y₀ N), increment U K α y₀ N k ω)
      atTop (id : ℝ → ℝ) (fun _ => law U)
      (gaussianReal 0 (Real.toNNReal (variance K α γ y₀))) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (eventually_rows U y₀ hy₀ K)
  have hrows (n : ℕ) := hN₀ (n + N₀) (Nat.le_add_left N₀ n)
  have ht (n : ℕ) : 0 < time U y₀ (n + N₀) := (hrows n).2.2
  have hi (n : ℕ) : Integrable (fun ω : Space U =>
      (Finset.range (time U y₀ (n + N₀))).sup'
        (Finset.nonempty_range_iff.mpr (ht n).ne')
        (fun k => increment U K α y₀ (n + N₀) k ω ^ 2)) (law U) := by
    have h := (eval_preserving U (n + N₀)).integrable_comp_of_integrable
      (integrable_maxSq U K α y₀ (n + N₀) (time U y₀ (n + N₀)))
    simpa only [Function.comp_def, maxSq_eq_sup U K α y₀ _ _ (ht n), increment] using h
  obtain ⟨C, hC⟩ :=
    (integral_product_maxSq_tendsto_zero U y₀ hy₀ K hK α hα γ hspec hgrowth).bddAbove_range
  have hbound : ∃ C : ℝ, ∀ n, ∫ ω : Space U,
      (Finset.range (time U y₀ (n + N₀))).sup'
        (Finset.nonempty_range_iff.mpr (ht n).ne')
        (fun k => increment U K α y₀ (n + N₀) k ω ^ 2) ∂law U ≤ C := by
    refine ⟨C, fun n => ?_⟩
    simpa only [Function.comp_def, maxSq_eq_sup U K α y₀ _ _ (ht n), increment] using
      hC (Set.mem_range.mpr ⟨n + N₀, rfl⟩)
  have hsq := (squares_tendstoInMeasure U y₀ hy₀ K hK α hα γ hspec hgrowth).comp
    (tendsto_add_atTop_nat N₀)
  have hres := hclt (law U) (fun n => rowFiltration U (n + N₀))
    (fun n => increment U K α y₀ (n + N₀)) (fun n => time U y₀ (n + N₀)) ht
    (Real.toNNReal (variance K α γ y₀)) (Real.toNNReal_pos.mpr hσ)
    (fun n => increment_martingale U K α y₀ (n + N₀) (hrows n).2.1) hi hbound
    (maximum_tendstoInMeasure U y₀ hy₀ K hK α hα γ hspec hgrowth N₀ ht)
    (by simpa only [Function.comp_def, Real.coe_toNNReal _ hσ.le] using hsq)
  refine ⟨?_, measurable_id.aemeasurable, ?_⟩
  · intro N
    exact (Finset.measurable_sum _ (fun k _ =>
      (measurable_increment U K α y₀ N k).comp (eval_preserving U N).measurable)).aemeasurable
  · exact (tendsto_add_atTop_iff_nat N₀).mp hres.tendsto

end IdlaCyl.Gff
