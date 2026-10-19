/-
Source: paper/idla-cylinder-gff.tex, tex:1084-1110.
Maximal squared increments are dominated by the quadratic mass, and their
expectations vanish by the shape estimate and the height-restricted mode bound.
-/
import IdlaCyl.Support.Gff.QuadraticMass
import IdlaCyl.Support.GffArray
import IdlaCyl.Support.GffMaxIncrement
import IdlaCyl.Support.WidthOrder

namespace IdlaCyl.Gff

open IdlaCyl.Defs Filter MeasureTheory
open scoped Topology

/-- The maximum of zero and the squared increments before time `t`.
The zero convention also covers an empty row. -/
noncomputable def maxSq (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (N : ℕ) :
    ℕ → TrajSeq (U.B N) → ℝ
  | 0, _ => 0
  | t + 1, ω => max (maxSq U K α y₀ N t ω) (gffIncrement U K α y₀ N t ω ^ 2)

theorem maxSq_nonneg (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (N t : ℕ)
    (ω : TrajSeq (U.B N)) : 0 ≤ maxSq U K α y₀ N t ω := by
  cases t with
  | zero => exact le_rfl
  | succ t => exact (sq_nonneg _).trans (le_max_right _ _)

theorem sq_le_maxSq (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (N t k : ℕ)
    (hk : k < t) (ω : TrajSeq (U.B N)) :
    gffIncrement U K α y₀ N k ω ^ 2 ≤ maxSq U K α y₀ N t ω := by
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
    · exact (ih h).trans (le_max_left _ _)
    · exact le_max_right _ _

theorem maxSq_le (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (N t : ℕ)
    (ω : TrajSeq (U.B N)) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ k < t, gffIncrement U K α y₀ N k ω ^ 2 ≤ b) :
    maxSq U K α y₀ N t ω ≤ b := by
  induction t with
  | zero => exact hb
  | succ t ih => exact max_le (ih (fun k hk => h k (by omega))) (h t (by omega))

theorem maxSq_le_sum (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (N t : ℕ)
    (ω : TrajSeq (U.B N)) : maxSq U K α y₀ N t ω ≤
      ∑ k ∈ Finset.range t, gffIncrement U K α y₀ N k ω ^ 2 := by
  apply maxSq_le U K α y₀ N t ω _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  intro k hk
  exact Finset.single_le_sum (f := fun j => gffIncrement U K α y₀ N j ω ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_range.mpr hk)

/-- This is exactly the nonempty maximum used in McLeish's condition (a). -/
theorem maxSq_eq_sup (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (N t : ℕ)
    (ht : 0 < t) (ω : TrajSeq (U.B N)) : maxSq U K α y₀ N t ω =
      (Finset.range t).sup' (Finset.nonempty_range_iff.mpr ht.ne')
        (fun k => gffIncrement U K α y₀ N k ω ^ 2) := by
  apply le_antisymm
  · apply maxSq_le
    · exact (sq_nonneg (gffIncrement U K α y₀ N 0 ω)).trans
        (Finset.le_sup' (fun k => gffIncrement U K α y₀ N k ω ^ 2) (Finset.mem_range.mpr ht))
    · intro k hk
      exact Finset.le_sup' (fun k => gffIncrement U K α y₀ N k ω ^ 2) (Finset.mem_range.mpr hk)
  · exact Finset.sup'_le _ _ (fun k hk =>
      sq_le_maxSq U K α y₀ N t k (Finset.mem_range.mp hk) ω)

theorem measurable_increment (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ)
    (N k : ℕ) : Measurable (gffIncrement U K α y₀ N k) := by
  exact measurable_const.mul ((measurable_of_countable _).comp (measurable_settleSite (U.B N) k))

theorem measurable_maxSq (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ)
    (N t : ℕ) : Measurable (maxSq U K α y₀ N t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih => exact ih.max ((measurable_increment U K α y₀ N t).pow_const 2)

/-- The maximum is integrable even before the asymptotic regime: every
individual increment has an almost-sure finite height cap. -/
theorem integrable_maxSq (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ)
    (N t : ℕ) : Integrable (maxSq U K α y₀ N t) (idlaMeasure (U.B N)) := by
  have hi : ∀ k, Integrable (fun ω => gffIncrement U K α y₀ N k ω ^ 2)
      (idlaMeasure (U.B N)) := by
    intro k
    simpa only [gffIncrement, mul_pow] using
      (integrable_psi_settleSite (U.B N) (fun p => psi U K α y₀ N p ^ 2) k).const_mul
        ((Real.sqrt ((N : ℝ) * U.a N))⁻¹ ^ 2)
  apply Integrable.mono' (integrable_finsetSum (Finset.range t) (fun k _ => hi k))
    (measurable_maxSq U K α y₀ N t).aestronglyMeasurable
  exact .of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (maxSq_nonneg U K α y₀ N t ω)]
    exact maxSq_le_sum U K α y₀ N t ω

/-- The pathwise bound used in (a) (`tex:1084-1087`). -/
theorem maxSq_ae_le_qmass (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ)
    (N : ℕ) (hN : 2 ≤ N) :
    ∀ᵐ ω ∂idlaMeasure (U.B N), maxSq U K α y₀ N (time U y₀ N) ω ≤ qmass U K α y₀ N ω := by
  filter_upwards [gffIncrement_sq_sum_eq_qmass U K α y₀ N hN] with ω hω
  exact (maxSq_le_sum U K α y₀ N (time U y₀ N) ω).trans_eq hω

/-- The expectation of the maximal squared increment tends to zero
(`tex:1088-1110`), which is stronger than McLeish's condition (b). -/
theorem integral_maxSq_tendsto_zero (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) (hgrowth : U.GrowthCondition) :
    Tendsto (fun N => ∫ ω, maxSq U K α y₀ N (time U y₀ N) ω
      ∂idlaMeasure (U.B N)) atTop (𝓝 0) := by
  obtain ⟨C, hC, -, hbad⟩ := exists_width U y₀ hy₀ K hK α hα γ hspec hgrowth
  have hd := Replace.width_ratio_tendsto_zero U hgrowth (width U C y₀)
    (width_pos U y₀ C hC) (width_le_order U y₀ hy₀ hgrowth C hC)
  obtain ⟨b, hb, hbound⟩ := psi_sq_div_le_of_height_le U y₀ hy₀ K hK α hα γ hspec
    (width U C y₀) hd
  have hlim : Tendsto (fun N => max (b N) 0 + ∫ ω, qmass U K α y₀ N ω *
      ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω
        ∂idlaMeasure (U.B N)) atTop (𝓝 0) := by
    simpa only [max_self, add_zero] using (hb.max (tendsto_const_nhds (x := (0 : ℝ)))).add hbad
  refine squeeze_zero' (.of_forall fun N => integral_nonneg
    (maxSq_nonneg U K α y₀ N (time U y₀ N))) ?_ hlim
  filter_upwards [hbound, eventually_ge_atTop (2 : ℕ)] with N hboundN hN
  have hshape : MeasurableSet (shape U C y₀ N) := by
    exact measurableSet_shapeTraj (U.B N) (time U y₀ N) _ _
  have hbadint : Integrable (fun ω => qmass U K α y₀ N ω *
      ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω) (idlaMeasure (U.B N)) := by
    have heq : (fun ω => qmass U K α y₀ N ω *
        ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω) =
        (shape U C y₀ N)ᶜ.indicator (qmass U K α y₀ N) := by
      funext ω
      by_cases h : ω ∈ (shape U C y₀ N)ᶜ <;> simp [h]
    rw [heq]
    exact (QOnEc.integrable_qmass U K α y₀ N).indicator hshape.compl
  have hmajor : ∀ᵐ ω ∂idlaMeasure (U.B N), maxSq U K α y₀ N (time U y₀ N) ω ≤
      max (b N) 0 + qmass U K α y₀ N ω *
        ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [maxSq_ae_le_qmass U K α y₀ N hN] with ω hω
    by_cases hE : ω ∈ shape U C y₀ N
    · rw [Set.indicator_of_notMem (show ω ∉ (shape U C y₀ N)ᶜ from fun h => h hE),
        mul_zero, add_zero]
      apply maxSq_le U K α y₀ N _ ω _ (le_max_right _ _)
      intro k hk
      have hsettle : settleSite (U.B N) ω k ∈ clusterTraj (U.B N) ω (time U y₀ N) := by
        rw [clusterTraj_eq_union]
        exact Or.inr (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩)
      have hh := hE.2 hsettle
      change ((settleSite (U.B N) ω k).2 : ℝ) ≤
        (time U y₀ N : ℝ) / ((U.B N).card : ℝ) + width U C y₀ N at hh
      rw [Replace.time_div_card] at hh
      have hpos : 0 ≤ (N : ℝ) * U.a N := mul_nonneg (Nat.cast_nonneg _) (U.a_pos N).le
      have heq : gffIncrement U K α y₀ N k ω ^ 2 =
          psi U K α y₀ N (settleSite (U.B N) ω k) ^ 2 / ((N : ℝ) * U.a N) := by
        rw [gffIncrement, mul_pow, inv_pow, Real.sq_sqrt hpos]
        ring
      rw [heq]
      exact (hboundN _ hh).trans (le_max_left _ _)
    · rw [Set.indicator_of_mem (Set.mem_compl hE), mul_one]
      exact hω.trans (le_add_of_nonneg_left (le_max_right _ _))
  have hmono := integral_mono_ae (integrable_maxSq U K α y₀ N (time U y₀ N))
    ((integrable_const (max (b N) 0)).add hbadint) hmajor
  change (∫ ω, maxSq U K α y₀ N (time U y₀ N) ω ∂idlaMeasure (U.B N)) ≤
    ∫ ω, max (b N) 0 + qmass U K α y₀ N ω *
      ((shape U C y₀ N)ᶜ).indicator (fun _ => (1 : ℝ)) ω ∂idlaMeasure (U.B N) at hmono
  simpa only [integral_add (integrable_const _) hbadint, integral_const, probReal_univ,
    one_smul] using hmono

end IdlaCyl.Gff
