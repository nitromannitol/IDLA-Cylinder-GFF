/-
The lawful torus family as a cardinality-independent GFF sequence.
Source: tex:398-416,502-520, `paper/idla-cylinder-gff.tex`.
-/
import IdlaCyl.Support.Torus.Sequence
import IdlaCyl.Support.Torus.Limit

namespace IdlaCyl
open Filter
open scoped Topology

/-- The torus sequence with the finite inadmissible prefix removed. -/
abbrev torusSeq (d : ℕ) (hd : 1 ≤ d) (n : ℕ) : Base :=
  torusBase d (n + 3) hd (by omega)

/-- The torus GFF setup with the supplied lawful eigenfunctions on every row. -/
noncomputable def torusSetupOf (d : ℕ) (hd : 1 ≤ d)
    (S : (n : ℕ) → SpectralData (torusSeq d hd n)) : SequenceSetup where
  B := torusSeq d hd
  S := S
  a n := ((n + 3 : ℕ) : ℝ)
  a_pos n := Nat.cast_pos.mpr (by omega)
  a_tendsto := tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  card_tendsto := by
    apply tendsto_atTop_mono _ (tendsto_add_atTop_nat 3)
    intro n
    rw [torusBase_card]
    exact Nat.le_self_pow (by omega : d ≠ 0) (n + 3)

/-- The explicit continuum spectral parameters, in one-based order. -/
noncomputable def torusGamma (d : ℕ) (hd : 1 ≤ d) (k : ℕ) : ℝ :=
  Real.pi * Real.sqrt (2 / (d : ℝ)) * Real.sqrt (TorusSpectrum.shell d hd k)

lemma torusSetupOf_spectralAssumption (d : ℕ) (hd : 1 ≤ d)
    (S : (n : ℕ) → SpectralData (torusSeq d hd n)) (K : ℕ) :
    (torusSetupOf d hd S).SpectralAssumption (torusGamma d hd) K := by
  intro k hk _
  exact TorusSpectrum.gamma_limit d hd S k hk

lemma torusSetupOf_growthCondition (d : ℕ) (hd : 1 ≤ d)
    (S : (n : ℕ) → SpectralData (torusSeq d hd n)) :
    (torusSetupOf d hd S).GrowthCondition := by
  have hN : Tendsto (fun n : ℕ => ((n + 3 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hlog : Tendsto (fun n : ℕ => Real.log (((n + 3 : ℕ) : ℝ)) / ((n + 3 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hN
  have hlim := hlog.const_mul ((d : ℝ) + 1)
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards with n
  have hnr : (1 : ℝ) ≤ ((n + 3 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 3 by omega)
  change ((d : ℝ) + 1) * (Real.log (((n + 3 : ℕ) : ℝ)) / ((n + 3 : ℕ) : ℝ)) =
    (Real.log ((torusSeq d hd n).card : ℝ) + logPlus (((n + 3 : ℕ) : ℝ))) / ((n + 3 : ℕ) : ℝ)
  rw [torusBase_card, Nat.cast_pow, Real.log_pow, logPlus, max_eq_left (Real.log_nonneg hnr)]
  ring

end IdlaCyl
