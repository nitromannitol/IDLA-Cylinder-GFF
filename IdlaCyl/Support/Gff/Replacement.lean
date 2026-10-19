/-
Source: paper/idla-cylinder-gff.tex, tex:784-789,877-881,1069-1070.
The printed width supplies every hypothesis of the replacement lemma. On the
common probability space the difference between the test-function pairing and
the harmonic array sum therefore converges in probability to zero.
-/
import IdlaCyl.Support.Gff.Positive
import IdlaCyl.Frozen.LeReplaceV2

namespace IdlaCyl.Gff

open IdlaCyl.Defs Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- The finite discrepancy pairing is linear under subtraction of tests. -/
theorem pairing_sub (B : Base) (ω : TrajSeq B) (t : ℕ) (f g : Site B → ℝ) :
    pairingTraj B ω t (fun p => f p - g p) = pairingTraj B ω t f - pairingTraj B ω t g := by
  simp only [pairingTraj_eq_sum, Finset.sum_sub_distrib]
  ring

/-- The normalized test-function pairing, on the common probability space. -/
noncomputable def statistic (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ)
    (N : ℕ) (ω : Space U) : ℝ :=
  (Real.sqrt ((N : ℝ) * U.a N))⁻¹ * pairingTraj (U.B N) (ω N) (time U y₀ N)
    (testAt (U.B N) (U.S N) (U.a N) K α)

theorem measurable_statistic (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ)
    (N : ℕ) : Measurable (statistic U K α y₀ N) := by
  exact measurable_const.mul ((measurable_pairingTraj (U.B N) (time U y₀ N) _).comp
    (eval_preserving U N).measurable)

/-- The replacement error converges in probability with the shape and width
requirements discharged (`tex:877-881`). -/
theorem replacement_tendstoInMeasure (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    TendstoInMeasure (law U) (fun (N : ℕ) (ω : Space U) =>
      (Real.sqrt ((N : ℝ) * U.a N))⁻¹ * pairingTraj (U.B N) (ω N) (time U y₀ N)
        (fun p => testAt (U.B N) (U.S N) (U.a N) K α p - psi U K α y₀ N p))
      atTop (fun _ => 0) := by
  obtain ⟨C, hC, hshape, -⟩ := exists_width U y₀ hy₀ K hK α hα γ hspec hgrowth
  have hreplace := Frozen.le_replace_v2 U y₀ 1 hy₀ one_pos K hK α hα γ hspec hgrowth
    (width U C y₀) (width_pos U y₀ C hC) (width_le_order U y₀ hy₀ hgrowth C hC) hshape
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have h := hreplace ε hε
  have heq : ∀ N : ℕ, (law U).real {ω : Space U | ε ≤
      ‖(Real.sqrt ((N : ℝ) * U.a N))⁻¹ * pairingTraj (U.B N) (ω N) (time U y₀ N)
        (fun p => testAt (U.B N) (U.S N) (U.a N) K α p - psi U K α y₀ N p) - 0‖} =
      (idlaMeasure (U.B N) {ω : TrajSeq (U.B N) | ε ≤
        |(Real.sqrt ((N : ℝ) * U.a N))⁻¹ * pairingTraj (U.B N) ω (time U y₀ N)
          (fun p => testAt (U.B N) (U.S N) (U.a N) K α p - psi U K α y₀ N p)|}).toReal := by
    intro N
    simp only [sub_zero, Real.norm_eq_abs]
    have hm : MeasurableSet {ω : TrajSeq (U.B N) | ε ≤
        |(Real.sqrt ((N : ℝ) * U.a N))⁻¹ * pairingTraj (U.B N) ω (time U y₀ N)
          (fun p => testAt (U.B N) (U.S N) (U.a N) K α p - psi U K α y₀ N p)|} :=
      measurableSet_le measurable_const ((measurable_const.mul
        (measurable_pairingTraj (U.B N) (time U y₀ N) _)).abs)
    exact congrArg ENNReal.toReal ((eval_preserving U N).measure_preimage hm.nullMeasurableSet)
  simpa only [heq] using h

/-- The difference needed by Slutsky is the replacement error, almost surely
for every sufficiently large row. -/
theorem statistic_sub_sums_tendstoInMeasure (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    TendstoInMeasure (law U)
      (statistic U K α y₀ - fun N ω =>
        ∑ k ∈ Finset.range (time U y₀ N), increment U K α y₀ N k ω)
      atTop 0 := by
  apply (replacement_tendstoInMeasure U y₀ hy₀ K hK α hα γ hspec hgrowth).congr'
    (h_right := EventuallyEq.rfl)
  filter_upwards [eventually_rows U y₀ hy₀ K] with N hN
  have hae := (eval_preserving U N).quasiMeasurePreserving.ae
    (gffIncrement_sum_eq_pairing U K α y₀ N hN.1 hN.2.1 (time U y₀ N))
  filter_upwards [hae] with ω hω
  change _ = statistic U K α y₀ N ω -
    ∑ k ∈ Finset.range (time U y₀ N), increment U K α y₀ N k ω
  change _ = (Real.sqrt ((N : ℝ) * U.a N))⁻¹ * pairingTraj (U.B N) (ω N) (time U y₀ N)
    (testAt (U.B N) (U.S N) (U.a N) K α) -
      ∑ k ∈ Finset.range (time U y₀ N), gffIncrement U K α y₀ N k (ω N)
  rw [hω, pairing_sub, mul_sub]

end IdlaCyl.Gff
