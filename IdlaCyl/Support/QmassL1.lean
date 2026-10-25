module

public import IdlaCyl.Frozen.ClmQWV2
public import IdlaCyl.Frozen.ClmWToSigmaV2
public import IdlaCyl.Support.CanonicalShape

@[expose] public section

/-!
The `L¹` convergence of the quadratic mass `Q_N` to the limiting variance `σ²(φ)`
(`paper/idla-cylinder-gff.tex:1074-1085`, the proof of `th:GFF`).

The bound `E|Q_N - σ²(φ)| ≤ E(|Q_N - W_N| 1_E) + E(Q_N 1_{E^c}) + W_N P(E^c)
+ |W_N - σ²(φ)|` is obtained pointwise and integrated; each term is then shown to
tend to zero.
-/

namespace IdlaCyl

open IdlaCyl.Defs Filter MeasureTheory

/-- Multiplying an integrable function by the indicator of a measurable set gives the
restriction of that function to the set. -/
private theorem qmassL1_integrable_mul_indicator {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} {s : Set Ω} (hf : Integrable f μ) (hs : MeasurableSet s) :
    Integrable (fun ω => f ω * s.indicator (fun _ => (1 : ℝ)) ω) μ := by
  have hfun : (fun ω => f ω * s.indicator (fun _ => (1 : ℝ)) ω) = s.indicator f := by
    funext ω
    by_cases h : ω ∈ s <;> simp [h]
  rw [hfun]
  exact hf.indicator hs

/-- The quadratic mass `Q_N` is nonnegative. -/
private theorem qmassL1_qmass_nonneg (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ)
    (N : ℕ) (ω : TrajSeq (U.B N)) : 0 ≤ qmass U K α y₀ N ω := by
  unfold qmass QN
  exact mul_nonneg (div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (U.a_pos _).le))
    (Finset.sum_nonneg fun p _ => sq_nonneg _)

/-- The rectangular mass `W_N` is nonnegative. -/
private theorem qmassL1_wmass_nonneg (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ)
    (N : ℕ) : 0 ≤ wmass U K α y₀ N := by
  unfold wmass
  exact mul_nonneg (div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (U.a_pos _).le))
    (Finset.sum_nonneg fun p _ => sq_nonneg _)

/-- The good event `E` of `clm:Q-W` is measurable. -/
private theorem qmassL1_shape_measurable (U : Setup) (C y₀ : ℝ) (N : ℕ) :
    MeasurableSet (shape U C y₀ N) := by
  unfold shape eventAt
  exact measurableSet_shapeTraj (U.B N) (time U y₀ N) _ _

/-- The `L¹` convergence of `Q_N` to `σ²(φ)` under the premises of `th:GFF`. -/
theorem qmass_tendsto_variance_L1 (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀) (K : ℕ) (hK : 2 ≤ K)
    (α : ℕ → ℝ → ℝ) (hα : regular α K y₀) (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K)
    (hgrowth : U.GrowthCondition) (C : ℝ) (hC : 0 < C)
    (hint : ∀ N, Integrable (qmass U K α y₀ N) (idlaMeasure (U.B N)))
    (hEc : Tendsto (fun N => ∫ ω, qmass U K α y₀ N ω *
        ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω ∂idlaMeasure (U.B N)) atTop (nhds 0))
    (hprob : Tendsto (fun N => (idlaMeasure (U.B N) (shape U C y₀ N)ᶜ).toReal) atTop (nhds 0)) :
    Tendsto (fun N => ∫ ω, |qmass U K α y₀ N ω - variance K α γ y₀| ∂idlaMeasure (U.B N))
      atTop (nhds 0) := by
  obtain ⟨A, -, hev, hAlim⟩ := Frozen.clm_q_w_v2 U y₀ hy₀ K hK α hα γ hspec hgrowth C hC
  have hW := Frozen.clm_w_to_sigma_v2 U y₀ hy₀ K hK α hα γ hspec
  have hWσ : Tendsto (fun N => |wmass U K α y₀ N - variance K α γ y₀|) atTop (nhds 0) := by
    have := tendsto_iff_norm_sub_tendsto_zero.mp hW
    simpa [Real.norm_eq_abs] using this
  have hWP : Tendsto (fun N => wmass U K α y₀ N *
      (idlaMeasure (U.B N) (shape U C y₀ N)ᶜ).toReal) atTop (nhds 0) := by
    have := hW.mul hprob
    simpa using this
  have hbound := ((hAlim.add hEc).add hWP).add hWσ
  simp only [add_zero] at hbound
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound ?_ ?_
  · exact Eventually.of_forall fun N => integral_nonneg fun ω => abs_nonneg _
  · filter_upwards [hev] with N hN
    have hQ := hint N
    have hE := qmassL1_shape_measurable U C y₀ N
    have hEc' := hE.compl
    have hI1 : Integrable (fun ω => |qmass U K α y₀ N ω - wmass U K α y₀ N| *
        (shape U C y₀ N).indicator (fun _ => (1 : ℝ)) ω) (idlaMeasure (U.B N)) :=
      qmassL1_integrable_mul_indicator ((hQ.sub (integrable_const _)).abs) hE
    have hI2 : Integrable (fun ω => qmass U K α y₀ N ω *
        ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω) (idlaMeasure (U.B N)) :=
      qmassL1_integrable_mul_indicator hQ hEc'
    have hI3 : Integrable (fun ω => wmass U K α y₀ N *
        ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω) (idlaMeasure (U.B N)) :=
      qmassL1_integrable_mul_indicator (integrable_const _) hEc'
    have hI4 : Integrable (fun _ : TrajSeq (U.B N) =>
        |wmass U K α y₀ N - variance K α γ y₀|) (idlaMeasure (U.B N)) := integrable_const _
    have hLHS : Integrable (fun ω => |qmass U K α y₀ N ω - variance K α γ y₀|)
        (idlaMeasure (U.B N)) := (hQ.sub (integrable_const _)).abs
    have hpt : ∀ ω : TrajSeq (U.B N),
        |qmass U K α y₀ N ω - variance K α γ y₀| ≤
          |qmass U K α y₀ N ω - wmass U K α y₀ N| *
              (shape U C y₀ N).indicator (fun _ => (1 : ℝ)) ω +
            qmass U K α y₀ N ω * ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω +
            wmass U K α y₀ N * ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω +
            |wmass U K α y₀ N - variance K α γ y₀| := by
      intro ω
      have h1 := abs_sub_le (qmass U K α y₀ N ω) (wmass U K α y₀ N) (variance K α γ y₀)
      have hQω := qmassL1_qmass_nonneg U K α y₀ N ω
      have hWN := qmassL1_wmass_nonneg U K α y₀ N
      by_cases hω : ω ∈ shape U C y₀ N
      · rw [Set.indicator_of_mem hω,
          Set.indicator_of_notMem (show ω ∉ (shape U C y₀ N)ᶜ from fun h => h hω)]
        simp only [mul_one, mul_zero, add_zero]
        linarith
      · rw [Set.indicator_of_notMem hω, Set.indicator_of_mem (Set.mem_compl hω)]
        have h2 : |qmass U K α y₀ N ω - wmass U K α y₀ N| ≤
            qmass U K α y₀ N ω + wmass U K α y₀ N :=
          abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
        simp only [mul_one, mul_zero, zero_add]
        linarith
    have s1 : Integrable (fun ω => |qmass U K α y₀ N ω - wmass U K α y₀ N| *
        (shape U C y₀ N).indicator (fun _ => (1 : ℝ)) ω +
        qmass U K α y₀ N ω * ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω)
        (idlaMeasure (U.B N)) := hI1.add hI2
    have s2 : Integrable (fun ω => |qmass U K α y₀ N ω - wmass U K α y₀ N| *
        (shape U C y₀ N).indicator (fun _ => (1 : ℝ)) ω +
        qmass U K α y₀ N ω * ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω +
        wmass U K α y₀ N * ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω)
        (idlaMeasure (U.B N)) := s1.add hI3
    have hR : Integrable (fun ω => |qmass U K α y₀ N ω - wmass U K α y₀ N| *
        (shape U C y₀ N).indicator (fun _ => (1 : ℝ)) ω +
        qmass U K α y₀ N ω * ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω +
        wmass U K α y₀ N * ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω +
        |wmass U K α y₀ N - variance K α γ y₀|) (idlaMeasure (U.B N)) := s2.add hI4
    have hmono := integral_mono hLHS hR hpt
    rw [integral_add s2 hI4, integral_add s1 hI3, integral_add hI1 hI2] at hmono
    have hT1 : ∫ ω, |qmass U K α y₀ N ω - wmass U K α y₀ N| *
        (shape U C y₀ N).indicator (fun _ => (1 : ℝ)) ω ∂idlaMeasure (U.B N)
        ≤ A * width U C y₀ N / U.a N := by
      calc _ ≤ ∫ _ : TrajSeq (U.B N), A * width U C y₀ N / U.a N ∂idlaMeasure (U.B N) :=
            integral_mono hI1 (integrable_const _) (fun ω => hN ω)
        _ = A * width U C y₀ N / U.a N := by simp
    have hT3 : ∫ ω, wmass U K α y₀ N *
        ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω ∂idlaMeasure (U.B N)
        = wmass U K α y₀ N * (idlaMeasure (U.B N) (shape U C y₀ N)ᶜ).toReal := by
      rw [integral_const_mul, integral_indicator_const _ hEc']
      simp [measureReal_def]
    have hT4 : ∫ _ : TrajSeq (U.B N), |wmass U K α y₀ N - variance K α γ y₀|
        ∂idlaMeasure (U.B N) = |wmass U K α y₀ N - variance K α γ y₀| := by
      simp
    linarith [hmono, hT1, hT3, hT4]

end IdlaCyl
