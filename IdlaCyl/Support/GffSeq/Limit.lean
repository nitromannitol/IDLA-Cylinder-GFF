/-
Source: paper/idla-cylinder-gff.tex, tex:877-881,1066-1112.
Slutsky's theorem transfers the canonical harmonic-array limit to the printed
test-function pairing, including zero variance.
-/
import IdlaCyl.Support.Gff.Degenerate
import IdlaCyl.Support.Gff.Replacement
import IdlaCyl.Support.GffSeq.Degenerate
import IdlaCyl.Support.GffSeq.Replacement
import IdlaCyl.Support.Torus.Sequence

namespace IdlaCyl.GffSeq.Gff

open IdlaCyl.Defs Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- The normalized discrepancy pairing converges in distribution to the
Gaussian in Theorem 1.3, on the common probability space. -/
theorem statistic_tendstoInDistribution (hclt : IdlaCyl.External.martingale_clt_v2)
    (U : SequenceSetup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    TendstoInDistribution (statistic U K α y₀) atTop (id : ℝ → ℝ) (fun _ => law U)
      (gaussianReal 0 (Real.toNNReal (variance K α γ y₀))) := by
  exact tendstoInDistribution_of_tendstoInMeasure_sub (statistic U K α y₀) id
    (sums_tendstoInDistribution hclt U y₀ hy₀ K hK α hα γ hspec hgrowth)
    (statistic_sub_sums_tendstoInMeasure U y₀ hy₀ K hK α hα γ hspec hgrowth)
    (fun N => (measurable_statistic U K α y₀ N).aemeasurable)

end IdlaCyl.GffSeq.Gff
