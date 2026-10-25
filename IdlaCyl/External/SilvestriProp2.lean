module

/-
Cited input for the reduction used by Theorem 1.1 (the weaker variant `pr_reduction_alpha`).
Source: paper/idla-cylinder-gff.tex, tex:1440-1453 (citation and consumer).
Literal external source: Silvestri, ECP 25 (2020), paper 61, Proposition 2,
silvestri2020.txt:334-344; definitions at lines 89-106 and 148-157.

Encoding choices:
* Specialize the quasi-regular bases to the manuscript's `Base`; stationary
  measure is uniform and the suppressed regularity constants are δ = δ' = 1.
* `m : ℕ`, `0 < T`, and `T ≤ B.card ^ m` are literal integer bounds. No
  small-base uniformity is claimed: the confidence clause has an existential
  cutoff N₀, following b.
* Starts are `Fin T → Site B`, indexed 0,...,T-1 instead of 1,...,T. Both
  vectors have height ≤ 0. Their arbitrary extension after T cannot affect
  the history through T.
* A common `ResumeFinite B` encodes A(0)=A'(0)=R₀∪F with finite F above 0,
  the state space Ω printed in the source, and A(0) is required to be
  connected in the cylinder graph (`SeedConnected`, Support/CylGraph.lean),
  as in Silvestri's Definition 2 of IDLA (source line 90), for which the
  proposition is stated. No rectangularity, flatness, or height cap is
  required of F. (Until 2026-10-19 the encoding omitted connectedness and
  so stated slightly more than the source; ledger/ERRATA.md, E21.)
* The law is the pushforward of independent canonical `walkPathLaw`s under
  the literal `resumeGrow` history map; `resumeSeed_grow` identifies it with
  `clusterFrom`. Equality of these injective finite codes is set equality.
* The coupling family is selected BEFORE γ, then b is selected AFTER γ,
  uniformly over B,T,F and both starting vectors. The family formulation
  makes the source's phrase "depending only on γ and m" explicit without
  moving the coupling behind γ. For ineligible inputs the family is unused.
* b is a finite real with b>0 (enlarge any printed constant to a positive
  one). The hypothesis is the literal real-height rectangle R_{b√τ log N}.
* Silvestri equation (3.1) is false for some small γ (e.g. N=2,
  γ=0.1); this declaration does not cite it.
* The walk is the manuscript canonical walk: vertical ±1 each with mass
  1/4 and a lazy base step otherwise, Silvestri Definition 1.
* τ is Silvestri's PAIRWISE total-variation mixing time at threshold 1/2,
  not the manuscript's distance-to-uniform threshold 1/4. Nonemptiness of
  its defining set is proved before taking the natural infimum. There is
  no empty-infimum or ENat.toNat branch. Definition 4 is read as the
  LAZY base chain, forced by Definition 1; the non-lazy K₂ defining set
  would be empty.
* All t≤T, including 0, are retained. The success event is the diagonal in
  the finite history space, with both marginal laws specified separately.
* This is only a `def ... : Prop`; no theorem asserts this citation, and
  consumers must bind `(hsil : External.silvestri_prop2)` explicitly.
-/
public import IdlaCyl.Support.Outer.ResumeGrowth
public import IdlaCyl.Support.CylGraph
public import IdlaCyl.Support.Obligation.MixingContraction
public import IdlaCyl.Support.Obligation.BasePowPos

@[expose] public section

namespace IdlaCyl.External

open MeasureTheory
open scoped ENNReal BigOperators

-- FROZEN-STATEMENT-BEGIN
/-- Pairwise TV of the lazy base chain, in Silvestri's convention. -/
noncomputable def silvestriTV (B : Base) (t : ℕ) (x y : B.V) : ℝ :=
  (1 / 2) * ∑ z : B.V, |basePow B t x z - basePow B t y z|

/-- Triangle inequality comparing the two printed mixing conventions. -/
theorem silvestriTV_le (B : Base) (t : ℕ) (x y : B.V) :
    silvestriTV B t x y ≤ tvToUniform B t x + tvToUniform B t y := by
  unfold silvestriTV tvToUniform
  have hsum : (∑ z : B.V, |basePow B t x z - basePow B t y z|) ≤
      ∑ z : B.V, (|basePow B t x z - 1 / (B.card : ℝ)| +
        |basePow B t y z - 1 / (B.card : ℝ)|) := by
    apply Finset.sum_le_sum
    intro z _
    have h := abs_sub_le (basePow B t x z) (1 / (B.card : ℝ)) (basePow B t y z)
    rwa [abs_sub_comm (1 / (B.card : ℝ)) (basePow B t y z)] at h
  rw [Finset.sum_add_distrib] at hsum
  linarith

/-- The set defining τ_N(1/2) is nonempty for every legitimate base. -/
theorem silvestriMixing_nonempty (B : Base) :
    {t : ℕ | ∀ x y : B.V, silvestriTV B t x y ≤ 1 / 2}.Nonempty := by
  obtain ⟨t, ht⟩ := Obligation.mixingTime_spec_of_pos B (Obligation.basePow_pos_uniform B)
  refine ⟨t, fun x y => (silvestriTV_le B t x y).trans ?_⟩
  linarith [ht x, ht y]

/-- Silvestri's pairwise threshold-1/2 mixing time; the infimum is nonempty. -/
noncomputable def silvestriMixingTime (B : Base) : ℕ :=
  sInf {t : ℕ | ∀ x y : B.V, silvestriTV B t x y ≤ 1 / 2}

/-- The defining inequality really holds at the selected mixing time. -/
theorem silvestriMixingTime_spec (B : Base) (x y : B.V) :
    silvestriTV B (silvestriMixingTime B) x y ≤ 1 / 2 :=
  Nat.sInf_mem (silvestriMixing_nonempty B) x y

/-- Comparison with the manuscript's convention without importing Obligations. -/
theorem silvestriMixingTime_le (B : Base) : silvestriMixingTime B ≤ mixingTime B := by
  apply Nat.sInf_le
  have hmix := Nat.sInf_mem
    (Obligation.mixingTime_spec_of_pos B (Obligation.basePow_pos_uniform B))
  change ∀ x : B.V, tvToUniform B (mixingTime B) x ≤ 1 / 4 at hmix
  intro x y
  exact (silvestriTV_le B (mixingTime B) x y).trans (by linarith [hmix x, hmix y])

/-- All finite cluster histories through the literal positive time T. -/
abbrev SilvestriHistory (B : Base) (T : ℕ) := Fin (T + 1) → ResumeFinite B

/-- Extend a finite start vector; the extension is never read before time T. -/
noncomputable def silvestriStarts (B : Base) (T : ℕ) (s : Fin T → Site B) : ℕ → Site B :=
  fun i => if hi : i < T then s ⟨i, hi⟩ else (B.pt, 0)

/-- The history map is the canonical growth map, with its entire initial seed. -/
noncomputable def silvestriHistory (B : Base) (T : ℕ) (F : ResumeFinite B)
    (ω : TrajSeq B) : SilvestriHistory B T := fun t => resumeGrow B F ω t

/-- Measurability of the literal finite history. -/
theorem measurable_silvestriHistory (B : Base) (T : ℕ) (F : ResumeFinite B) :
    Measurable (silvestriHistory B T F) :=
  measurable_pi_iff.mpr (fun t => measurable_resumeGrow B F t)

/-- Fixed-start IDLA history law, using the canonical independent walk law. -/
noncomputable def silvestriProcessLaw (B : Base) (T : ℕ) (F : ResumeFinite B)
    (s : Fin T → Site B) : Measure (SilvestriHistory B T) :=
  (prescribedMeasure B (silvestriStarts B T s)).map (silvestriHistory B T F)

instance silvestriProcessLaw_isProbability (B : Base) (T : ℕ) (F : ResumeFinite B)
    (s : Fin T → Site B) : IsProbabilityMeasure (silvestriProcessLaw B T F s) :=
  Measure.isProbabilityMeasure_map (measurable_silvestriHistory B T F).aemeasurable

/-- A family chosen before the confidence parameter, as in the printed proposition. -/
abbrev SilvestriCouplings := ∀ (B : Base) (T : ℕ), ResumeFinite B →
  (Fin T → Site B) → (Fin T → Site B) →
    Measure (SilvestriHistory B T × SilvestriHistory B T)

/-- Cited Proposition 2. This declaration asserts no theorem. -/
def silvestri_prop2 : Prop :=
  ∀ m : ℕ, ∃ J : SilvestriCouplings,
    (∀ (B : Base) (T : ℕ), 0 < T → T ≤ B.card ^ m →
      ∀ (F : ResumeFinite B) (s s' : Fin T → Site B),
        SeedConnected B (resumeSeed B F) →
        (∀ i, (s i).2 ≤ 0) → (∀ i, (s' i).2 ≤ 0) →
        (J B T F s s').map Prod.fst = silvestriProcessLaw B T F s ∧
        (J B T F s s').map Prod.snd = silvestriProcessLaw B T F s') ∧
    ∀ γ : ℝ, 0 < γ → ∃ b : ℝ, 0 < b ∧ ∃ N₀ : ℕ,
      ∀ (B : Base), N₀ ≤ B.card → ∀ (T : ℕ), 0 < T → T ≤ B.card ^ m →
        ∀ (F : ResumeFinite B) (s s' : Fin T → Site B),
          SeedConnected B (resumeSeed B F) →
          (∀ i, (s i).2 ≤ 0) → (∀ i, (s' i).2 ≤ 0) →
          R B (b * Real.sqrt (silvestriMixingTime B) * Real.log (B.card : ℝ)) ⊆
            resumeSeed B F →
          ENNReal.ofReal (1 - (B.card : ℝ) ^ (-γ)) ≤
            J B T F s s' {p | p.1 = p.2}

-- FROZEN-STATEMENT-END

end IdlaCyl.External
