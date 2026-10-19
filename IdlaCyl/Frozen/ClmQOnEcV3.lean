/-
Source: paper/idla-cylinder-gff.tex, tex:915-918; proof tex:919-998.
`clm:Q on Ec` says `𝔼(Q_N 1_{E^c}) → 0`, where `E` is the event of Theorem 1.1
at its constant `C(ν,m)` (tex:271-280, tex:908-910). The statement therefore
takes any width constant `C` as an argument, together with the Theorem 1.1
probability bound `ℙ(E^c) ≤ N^{-ν}` for that `C`, eventually, as the hypothesis
`hP`. The constant enters the proof only through `hP`: tex:933 and tex:977 are
the only places the paper's proof uses it.
-/
import IdlaCyl.Support.QOnEc.Estimate

namespace IdlaCyl.Frozen

open IdlaCyl IdlaCyl.Defs IdlaCyl.QOnEc Filter MeasureTheory
open scoped Topology

/-- Helper: `QOnEc.bad_integral_bound_eventually` with the probability bound at
a fixed width `C` supplied as `hP`, for every `ν`, instead of
`shape_compl_le_eventually` at `ν = 1`. The height constants `M D L` do not
depend on `C` or `ν`. -/
theorem clm_q_on_ec_v3_bad_integral_le (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition)
    (ν : ℝ) (C : ℝ)
    (hP : ∀ᶠ N in atTop, idlaMeasure (U.B N) (shape U C y₀ N)ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ (-ν))) :
    ∃ M D L : ℝ, 0 < M ∧ 0 < D ∧ 0 < L ∧ ∀ᶠ N in atTop,
      (∫ ω : TrajSeq (U.B N), qmass U K α y₀ N ω *
        (shape U C y₀ N)ᶜ.indicator (fun _ => (1 : ℝ)) ω ∂idlaMeasure (U.B N)) ≤
        M * (N : ℝ) ^ (-ν) + D * Real.exp (-(cutHeight U L N : ℝ) / 2) := by
  obtain ⟨A, b, hA, hb, hmass⟩ := qmass_height_bound_eventually U y₀ hy₀ K α hα γ hspec
  let L := Real.exp 3 * y₀ + 1
  let M := A * (L + 1) * Real.exp (b * (L + 1))
  let D := (4 * A * Real.exp (1 / 2)) / (1 - Real.exp (-(1 : ℝ) / 2))
  have hL : 0 < L := by dsimp [L]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hr : 0 < 1 - Real.exp (-(1 : ℝ) / 2) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hD : 0 < D := div_pos (by positivity) hr
  refine ⟨M, D, L, hM, hD, hL, ?_⟩
  filter_upwards [hP, hmass, height_tail_eventually U y₀ hy₀ hgrowth,
    U.a_tendsto.eventually_ge_atTop (max 1 (4 * b))] with N hshapeN hmassN htailN haN
  have ha1 : 1 ≤ U.a N := (le_max_left _ _).trans haN
  have hab : 4 * b ≤ U.a N := (le_max_right _ _).trans haN
  let H := cutHeight U L N
  let T := time U y₀ N
  let w : ℕ → ℝ := fun j => A * (((H + j + 1 : ℕ) : ℝ) / U.a N) *
    Real.exp (b * (((H + j + 1 : ℕ) : ℝ) / U.a N))
  have hH : 1 ≤ H := cutHeight_pos U L hL N
  have hw : ∀ j, 0 ≤ w j := fun j =>
    mul_nonneg (mul_nonneg hA.le (div_nonneg (Nat.cast_nonneg _) (U.a_pos N).le))
      (Real.exp_nonneg _)
  have hfirst : ∀ ω : TrajSeq (U.B N),
      clusterTraj (U.B N) ω T ⊆ R (U.B N) (H : ℝ) → qmass U K α y₀ N ω ≤ M := by
    intro ω hω
    exact (hmassN H hH ω hω).trans (first_weight_le U L hL A b hA.le hb.le N ha1)
  have hweights : ∀ j ω, clusterTraj (U.B N) ω T ⊆
      R (U.B N) ((H + j + 1 : ℕ) : ℝ) → qmass U K α y₀ N ω ≤ w j := by
    intro j ω hω
    exact hmassN (H + j + 1) (by omega) ω hω
  have hfinite := integral_le_height_layers (U.B N) T H (qmass U K α y₀ N)
    (integrable_qmass U K α y₀ N) (shape U C y₀ N) (QOnEc.measurableSet_shape U C y₀ N)
    M hM.le w hw hfirst hweights
  have hshapeReal : (idlaMeasure (U.B N) (shape U C y₀ N)ᶜ).toReal ≤ (N : ℝ) ^ (-ν) :=
    ENNReal.toReal_le_of_le_ofReal (Real.rpow_nonneg (Nat.cast_nonneg _) _) hshapeN
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
  have hfirstprob : M * (idlaMeasure (U.B N) (shape U C y₀ N)ᶜ).toReal ≤
      M * (N : ℝ) ^ (-ν) :=
    mul_le_mul_of_nonneg_left hshapeReal hM.le
  exact hfinite.trans (add_le_add hfirstprob hsum)

/-- “We have $\mathbb E(Q_N \mathbf1_{E^c}) \to 0$ as $N \to \infty$.” (`tex:915-918`)
The bad-event contribution to the quadratic mass tends to zero for every width
constant `C` whose Theorem 1.1 bound `ℙ(E^c) ≤ N^{-ν}` holds eventually. -/
-- FROZEN-STATEMENT-BEGIN
theorem clm_q_on_ec_v3 (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition)
    (ν : ℝ) (hν : 0 < ν) (C : ℝ)
    (hP : ∀ᶠ N in atTop, idlaMeasure (U.B N) (shape U C y₀ N)ᶜ ≤
      ENNReal.ofReal ((N : ℝ) ^ (-ν))) :
    Tendsto (fun N => ∫ ω : TrajSeq (U.B N), qmass U K α y₀ N ω *
      ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω
        ∂idlaMeasure (U.B N)) atTop (nhds 0)
-- FROZEN-STATEMENT-END
:= by
  obtain ⟨M, D, L, hM, hD, hL, hbound⟩ :=
    clm_q_on_ec_v3_bad_integral_le U y₀ hy₀ K α hα γ hspec hgrowth ν C hP
  have hpoly : Tendsto (fun N : ℕ => M * (N : ℝ) ^ (-ν)) atTop (nhds 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_rpow_neg_atTop hν).comp tendsto_natCast_atTop_atTop).const_mul M
  have hheight : Tendsto (fun N => (cutHeight U L N : ℝ) / 2) atTop atTop := by
    simpa only [div_eq_mul_inv, mul_comm] using
      (cutHeight_tendsto U L hL).const_mul_atTop (show (0 : ℝ) < (2 : ℝ)⁻¹ by norm_num)
  have he : Tendsto (fun N => Real.exp (-(cutHeight U L N : ℝ) / 2))
      atTop (nhds 0) := by
    simpa only [Function.comp_def, neg_div] using Real.tendsto_exp_neg_atTop_nhds_zero.comp hheight
  have hmajor : Tendsto (fun N : ℕ => M * (N : ℝ) ^ (-ν) +
      D * Real.exp (-(cutHeight U L N : ℝ) / 2)) atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using hpoly.add (he.const_mul D)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor ?_ hbound
  filter_upwards with N
  exact integral_nonneg fun ω => mul_nonneg (qmass_nonneg U K α y₀ N ω)
    (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)

/-- Sanity check: the conclusion of `clm_q_on_ec_v2` follows from
`clm_q_on_ec_v3`, with `hP` instantiated by `shape_compl_le_eventually` at `ν = 1`. -/
theorem clm_q_on_ec_v3_of_large (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C →
      Tendsto (fun N => ∫ ω : TrajSeq (U.B N),
        qmass U K α y₀ N ω *
          ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω
            ∂idlaMeasure (U.B N)) atTop (nhds 0) := by
  obtain ⟨C₀, hC₀, hshape⟩ := shape_compl_le_eventually U y₀ hy₀ γ
    (hspec 2 le_rfl hK).1 hgrowth 1 one_pos
  exact ⟨C₀, hC₀, fun C hC =>
    clm_q_on_ec_v3 U y₀ hy₀ K α hα γ hspec hgrowth 1 one_pos C (hshape C hC)⟩

end IdlaCyl.Frozen
