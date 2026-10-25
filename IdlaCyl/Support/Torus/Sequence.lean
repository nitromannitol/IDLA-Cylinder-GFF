module

/-
A cardinality-independent row index for the GFF theorem. Source: tex:398-416,
tex:502-520, `paper/idla-cylinder-gff.tex`. This is the sequence-facing model;
no general GFF theorem is asserted here.
-/
public import IdlaCyl.Definitions.ShapeEvent

@[expose] public section

namespace IdlaCyl
open Filter
open scoped BigOperators Topology

/-- Bases with cofinal cardinalities, indexed independently of their sizes. -/
structure SequenceSetup where
  B : ℕ → Base
  S : ∀ n, SpectralData (B n)
  a : ℕ → ℝ
  a_pos : ∀ n, 0 < a n
  a_tendsto : Tendsto a atTop atTop
  card_tendsto : Tendsto (fun n => (B n).card) atTop atTop

namespace SequenceSetup

/-- The finite-mode spectral limit along rows. -/
def GammaLimit (U : SequenceSetup) (γ : ℕ → ℝ) (k : ℕ) : Prop :=
  Tendsto (fun n => U.a n * Real.sqrt (2 * (1 - (U.S n).lam k))) atTop (𝓝 (γ k))

/-- The positive spectral assumptions required by a fixed finite test. -/
def SpectralAssumption (U : SequenceSetup) (γ : ℕ → ℝ) (K : ℕ) : Prop :=
  ∀ k, 2 ≤ k → k ≤ K → U.GammaLimit γ k ∧ 0 < γ k

/-- The growth condition uses actual cardinalities, independently of the row index. -/
def GrowthCondition (U : SequenceSetup) : Prop :=
  Tendsto (fun n => (Real.log ((U.B n).card : ℝ) + logPlus (U.a n)) / U.a n) atTop (𝓝 0)

lemma card_pos (U : SequenceSetup) (n : ℕ) : 0 < (U.B n).card :=
  lt_of_lt_of_le (by norm_num) (U.B n).nontrivial

lemma eventually_modes (U : SequenceSetup) (K : ℕ) : ∀ᶠ n in atTop, K ≤ (U.B n).card :=
  U.card_tendsto.eventually_ge_atTop K

/-- The floor reference height. -/
noncomputable def height (U : SequenceSetup) (y₀ : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (y₀ * U.a n)

/-- The observation time uses the actual base cardinality. -/
noncomputable def time (U : SequenceSetup) (y₀ : ℝ) (n : ℕ) : ℕ :=
  (U.B n).card * U.height y₀ n

/-- The harmonic extension at the reference height. -/
noncomputable def psi (U : SequenceSetup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (n : ℕ) :
    Site (U.B n) → ℝ :=
  Defs.harmAt (U.B n) (U.S n) (U.a n) (U.height y₀ n : ℤ) K α

/-- The rectangular mass with the row's scale. -/
noncomputable def wmass (U : SequenceSetup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (n : ℕ) : ℝ :=
  1 / (((U.B n).card : ℝ) * U.a n) *
    ∑ p ∈ rectangleFinset (U.B n) (U.time y₀ n), (U.psi K α y₀ n p) ^ 2

/-- The quadratic mass uses `a n`, through a constant-scale invocation of `QN`. -/
noncomputable def qmass (U : SequenceSetup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (n : ℕ)
    (ω : TrajSeq (U.B n)) : ℝ :=
  QN (U.B n) (fun _ => U.a n) (U.time y₀ n) (U.psi K α y₀ n) ω

/-- The printed shape width at the observation time. -/
noncomputable def width (U : SequenceSetup) (C y₀ : ℝ) (n : ℕ) : ℝ :=
  Defs.delta (U.B n) C (U.time y₀ n)

/-- The printed good event at the observation time. -/
noncomputable def shape (U : SequenceSetup) (C y₀ : ℝ) (n : ℕ) : Set (TrajSeq (U.B n)) :=
  Defs.eventAt (U.B n) (U.time y₀ n) (U.width C y₀ n)

lemma qmass_nonneg (U : SequenceSetup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (n : ℕ)
    (ω : TrajSeq (U.B n)) : 0 ≤ U.qmass K α y₀ n ω := by
  apply mul_nonneg
  · exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (U.a_pos n).le)
  · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma time_div_card (U : SequenceSetup) (y₀ : ℝ) (n : ℕ) :
    (U.time y₀ n : ℝ) / ((U.B n).card : ℝ) = (U.height y₀ n : ℝ) := by
  have hc : ((U.B n).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (U.card_pos n).ne'
  simp only [time, Nat.cast_mul]
  field_simp

lemma height_ratio_tendsto (U : SequenceSetup) (y₀ : ℝ) (hy₀ : 0 ≤ y₀) :
    Tendsto (fun n => (U.height y₀ n : ℝ) / U.a n) atTop (𝓝 y₀) :=
  (tendsto_nat_floor_mul_div_atTop hy₀).comp U.a_tendsto

end SequenceSetup
end IdlaCyl
