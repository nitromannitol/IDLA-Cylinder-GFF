/-
Source: paper/idla-cylinder-gff.tex, tex:915-918; proof tex:919-998.
-/
import IdlaCyl.Support.QOnEc.Estimate
import IdlaCyl.Support.GffSeq.BadMassEstimate
import IdlaCyl.Support.Torus.Sequence

namespace IdlaCyl.GffSeq

open IdlaCyl IdlaCyl.Defs Filter MeasureTheory
open scoped Topology

/-- “We have $\mathbb E(Q_N \mathbf1_{E^c}) \to 0$ as $N \to \infty$.” (`tex:915-918`)
The bad-event contribution to the quadratic mass tends to zero for every
sufficiently large fixed width constant. -/
theorem clm_q_on_ec_v2 (U : SequenceSetup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K)
    (hgrowth : U.GrowthCondition) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      Tendsto (fun N => ∫ ω : TrajSeq (U.B N),
        SequenceSetup.qmass U K α y₀ N ω *
          ((SequenceSetup.shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω
            ∂idlaMeasure (U.B N)) atTop (nhds 0)
:= by
  obtain ⟨C₀, M, D, L, hC₀, -, -, hL, hbound⟩ :=
    QOnEc.bad_integral_bound_eventually U y₀ hy₀ K hK α hα γ hspec hgrowth
  refine ⟨C₀, hC₀, ?_⟩
  intro C hC
  have hpoly : Tendsto (fun N : ℕ => M / ((U.B N).card : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp U.card_tendsto)
  have hheight : Tendsto (fun N => (QOnEc.cutHeight U L N : ℝ) / 2) atTop atTop := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (QOnEc.cutHeight_tendsto U L hL).const_mul_atTop (show (0 : ℝ) < (2 : ℝ)⁻¹ by norm_num)
  have he : Tendsto (fun N => Real.exp (-(QOnEc.cutHeight U L N : ℝ) / 2))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, neg_div] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hheight
  have hmajor : Tendsto (fun N : ℕ => M / ((U.B N).card : ℝ) +
      D * Real.exp (-(QOnEc.cutHeight U L N : ℝ) / 2)) atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using hpoly.add (he.const_mul D)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor ?_ (hbound C hC)
  filter_upwards with N
  exact integral_nonneg fun ω => mul_nonneg (QOnEc.qmass_nonneg U K α y₀ N ω)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)

end IdlaCyl.GffSeq
