module

/-
Source: paper/idla-cylinder-gff.tex, tex:915-918,931-938,970-998.
The bad-event expectation is bounded by a vanishing polynomial term and a
geometric height-tail term. All probability and mass estimates are produced
from the source assumptions inside the proof.
-/
public import IdlaCyl.Support.QOnEc.Tail
public import IdlaCyl.Support.QOnEc.Weights
public import IdlaCyl.Support.QOnEc.Layers
public import IdlaCyl.Support.GffSeq.Tail
public import IdlaCyl.Support.GffSeq.Weights
public import IdlaCyl.Support.GffSeq.Layers
public import IdlaCyl.Support.Torus.Sequence

@[expose] public section

namespace IdlaCyl.GffSeq.QOnEc

open IdlaCyl.Defs IdlaCyl.QOnEc Filter MeasureTheory
open scoped Topology BigOperators

/-- A deterministic bound for the bad-event expectation, uniform in all
sufficiently large width constants. -/
theorem bad_integral_bound_eventually (U : SequenceSetup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    ∃ C₀ M D L : ℝ, 0 < C₀ ∧ 0 < M ∧ 0 < D ∧ 0 < L ∧
      ∀ C : ℝ, C₀ ≤ C → ∀ᶠ N in atTop,
        (∫ ω : TrajSeq (U.B N), SequenceSetup.qmass U K α y₀ N ω *
          (SequenceSetup.shape U C y₀ N)ᶜ.indicator (fun _ => (1 : ℝ)) ω ∂idlaMeasure (U.B N)) ≤
          M / ((U.B N).card : ℝ) + D * Real.exp (-(cutHeight U L N : ℝ) / 2) := by
  obtain ⟨C₀, hC₀, hshape⟩ := shape_compl_le_eventually U y₀ hy₀ γ
    (hspec 2 le_rfl hK).1 hgrowth 1 one_pos
  obtain ⟨A, b, hA, hb, hmass⟩ := qmass_height_bound_eventually U y₀ hy₀ K α hα γ hspec
  let L := Real.exp 3 * y₀ + 1
  let M := A * (L + 1) * Real.exp (b * (L + 1))
  let D := (4 * A * Real.exp (1 / 2)) / (1 - Real.exp (-(1 : ℝ) / 2))
  have hL : 0 < L := by dsimp [L]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hr : 0 < 1 - Real.exp (-(1 : ℝ) / 2) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hD : 0 < D := div_pos (by positivity) hr
  refine ⟨C₀, M, D, L, hC₀, hM, hD, hL, ?_⟩
  intro C hC
  filter_upwards [hshape C hC, hmass, height_tail_eventually U y₀ hy₀ hgrowth,
    U.a_tendsto.eventually_ge_atTop (max 1 (4 * b))] with N hshapeN hmassN htailN haN
  have ha1 : 1 ≤ U.a N := (le_max_left _ _).trans haN
  have hab : 4 * b ≤ U.a N := (le_max_right _ _).trans haN
  let H := cutHeight U L N
  let T := SequenceSetup.time U y₀ N
  let w : ℕ → ℝ := fun j => A * (((H + j + 1 : ℕ) : ℝ) / U.a N) *
    Real.exp (b * (((H + j + 1 : ℕ) : ℝ) / U.a N))
  have hH : 1 ≤ H := cutHeight_pos U L hL N
  have hw : ∀ j, 0 ≤ w j := fun j =>
    mul_nonneg (mul_nonneg hA.le (div_nonneg (Nat.cast_nonneg _) (U.a_pos N).le))
      (Real.exp_nonneg _)
  have hfirst : ∀ ω : TrajSeq (U.B N),
      clusterTraj (U.B N) ω T ⊆ R (U.B N) (H : ℝ) → SequenceSetup.qmass U K α y₀ N ω ≤ M := by
    intro ω hω
    exact (hmassN H hH ω hω).trans (first_weight_le U L hL A b hA.le hb.le N ha1)
  have hweights : ∀ j ω, clusterTraj (U.B N) ω T ⊆
      R (U.B N) ((H + j + 1 : ℕ) : ℝ) → SequenceSetup.qmass U K α y₀ N ω ≤ w j := by
    intro j ω hω
    exact hmassN (H + j + 1) (by omega) ω hω
  have hfinite := integral_le_height_layers (U.B N) T H (SequenceSetup.qmass U K α y₀ N)
    (integrable_qmass U K α y₀ N) (SequenceSetup.shape U C y₀ N) (measurableSet_shape U C y₀ N)
    M hM.le w hw hfirst hweights
  have hshapeReal : (idlaMeasure (U.B N) (SequenceSetup.shape U C y₀ N)ᶜ).toReal ≤ 1 / ((U.B N).card : ℝ) := by
    apply ENNReal.toReal_le_of_le_ofReal (by positivity)
    simpa only [Real.rpow_neg_one, one_div] using hshapeN
  have hterm : ∀ j : ℕ,
      w j * (idlaMeasure (U.B N) (aboveHeight (U.B N) T (H + j))).toReal ≤
        (4 * A * Real.exp (1 / 2)) * Real.exp (-((H + j : ℕ) : ℝ) / 2) := by
    intro j
    have hh : Real.exp 3 * y₀ * U.a N ≤ ((H + j : ℕ) : ℝ) := by
      have hcut := le_cutHeight U L N
      have hLa : Real.exp 3 * y₀ * U.a N ≤ L * U.a N := by
        dsimp [L]
        nlinarith [U.a_pos N]
      exact (hLa.trans hcut).trans (by exact_mod_cast Nat.le_add_right H j)
    have hprob : (idlaMeasure (U.B N) (aboveHeight (U.B N) T (H + j))).toReal ≤
        Real.exp (-((H + j : ℕ) : ℝ)) :=
      ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _) (htailN (H + j) hh)
    calc _ ≤ w j * Real.exp (-((H + j : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hprob (hw j)
      _ ≤ _ := by
        dsimp [w]
        rw [Nat.cast_add, Nat.cast_one]
        exact weight_tail_le A b (U.a N) ((H + j : ℕ) : ℝ) hA.le ha1 hab
          (Nat.cast_nonneg _)
  have hsum : (∑ j ∈ Finset.range T,
      w j * (idlaMeasure (U.B N) (aboveHeight (U.B N) T (H + j))).toReal) ≤
      D * Real.exp (-(H : ℝ) / 2) := by
    calc _ ≤ ∑ j ∈ Finset.range T,
          (4 * A * Real.exp (1 / 2)) * Real.exp (-((H + j : ℕ) : ℝ) / 2) :=
        Finset.sum_le_sum fun j _ => hterm j
      _ = (4 * A * Real.exp (1 / 2)) *
          ∑ j ∈ Finset.range T, Real.exp (-((H + j : ℕ) : ℝ) / 2) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (4 * A * Real.exp (1 / 2)) *
          (Real.exp (-(H : ℝ) / 2) / (1 - Real.exp (-(1 : ℝ) / 2))) :=
        mul_le_mul_of_nonneg_left (sum_exp_layers_le H T) (by positivity)
      _ = D * Real.exp (-(H : ℝ) / 2) := by dsimp [D]; ring
  have hfirstprob : M * (idlaMeasure (U.B N) (SequenceSetup.shape U C y₀ N)ᶜ).toReal ≤ M / ((U.B N).card : ℝ) := by
    calc _ ≤ M * (1 / ((U.B N).card : ℝ)) := mul_le_mul_of_nonneg_left hshapeReal hM.le
      _ = M / ((U.B N).card : ℝ) := by ring
  exact hfinite.trans (add_le_add hfirstprob hsum)

end IdlaCyl.GffSeq.QOnEc
