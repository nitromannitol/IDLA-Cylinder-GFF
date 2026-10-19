import IdlaCyl.External.SilvestriProp2
import IdlaCyl.Support.CanonicalIdla

/-!
# The coupling family of Silvestri's Proposition 2 and its marginals

This file builds the coupling family `silvestriJ` of Silvestri's Proposition 2 from
an arbitrary family `Q` of pair laws on path space, and proves that its two marginals
are the fixed-start process laws `silvestriProcessLaw`.

The pair law `pairLawTot B Q x x'` is `Q x x'` when both heights are at most `0`, and
the independent product of the two walk laws otherwise. The family `silvestriJ` is the
law of the coordinate paths of an infinite product of pair laws, mapped to histories
by the canonical growth map.

It proves the following.

1. `silvestriStarts_height_le`: the extended starts keep height at most `0`.
2. `pairLawTot_isProbability`, `pairLawTot_map_fst` and `pairLawTot_map_snd`: the pair
   law is a probability measure whose marginals are the walk laws, given the
   corresponding properties of `Q` on the pairs of height at most `0`.
3. `silvestriJ_map_fst` and `silvestriJ_map_snd`: the first and second marginals of
   `silvestriJ` are `silvestriProcessLaw B T F s` and `silvestriProcessLaw B T F s'`.
   No height hypothesis on the starts is needed.
-/

namespace IdlaCyl.Silvestri

open MeasureTheory IdlaCyl.External
open scoped ENNReal

/-- The extended starts of `silvestriStarts` never exceed height `0` when the given
starts do. -/
theorem silvestriStarts_height_le (B : Base) (T : ℕ) (s : Fin T → Site B)
    (hs : ∀ i, (s i).2 ≤ 0) (j : ℕ) : (silvestriStarts B T s j).2 ≤ 0 := by
  unfold silvestriStarts
  split_ifs with hi
  · exact hs _
  · simp

/-- The pair law of two starts. It is the pair law `Q x x'` when both heights are at
most `0`, and the independent product of the two walk laws otherwise. -/
noncomputable def pairLawTot (B : Base)
    (Q : Site B → Site B → Measure ((ℕ → Site B) × (ℕ → Site B)))
    (x x' : Site B) : Measure ((ℕ → Site B) × (ℕ → Site B)) :=
  if x.2 ≤ 0 ∧ x'.2 ≤ 0 then Q x x' else (walkPathLaw B x).prod (walkPathLaw B x')

/-- The pair law is a probability measure for all starts, once `Q` is one on the pairs
of height at most `0`. -/
theorem pairLawTot_isProbability (B : Base)
    (Q : Site B → Site B → Measure ((ℕ → Site B) × (ℕ → Site B)))
    (hQ : ∀ x x' : Site B, x.2 ≤ 0 → x'.2 ≤ 0 → IsProbabilityMeasure (Q x x'))
    (x x' : Site B) : IsProbabilityMeasure (pairLawTot B Q x x') := by
  unfold pairLawTot
  split_ifs with h
  · exact hQ x x' h.1 h.2
  · infer_instance

/-- The first marginal of the pair law is the walk law of the first start. -/
theorem pairLawTot_map_fst (B : Base)
    (Q : Site B → Site B → Measure ((ℕ → Site B) × (ℕ → Site B)))
    (hQ1 : ∀ x x' : Site B, x.2 ≤ 0 → x'.2 ≤ 0 →
      (Q x x').map Prod.fst = walkPathLaw B x)
    (x x' : Site B) : (pairLawTot B Q x x').map Prod.fst = walkPathLaw B x := by
  unfold pairLawTot
  split_ifs with h
  · exact hQ1 x x' h.1 h.2
  · rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- The second marginal of the pair law is the walk law of the second start. -/
theorem pairLawTot_map_snd (B : Base)
    (Q : Site B → Site B → Measure ((ℕ → Site B) × (ℕ → Site B)))
    (hQ2 : ∀ x x' : Site B, x.2 ≤ 0 → x'.2 ≤ 0 →
      (Q x x').map Prod.snd = walkPathLaw B x')
    (x x' : Site B) : (pairLawTot B Q x x').map Prod.snd = walkPathLaw B x' := by
  unfold pairLawTot
  split_ifs with h
  · exact hQ2 x x' h.1 h.2
  · rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- Pair `j` of the family, with the starts of `silvestriStarts`. -/
noncomputable def silvestriPairLaw (B : Base)
    (Q : Site B → Site B → Measure ((ℕ → Site B) × (ℕ → Site B)))
    (T : ℕ) (s s' : Fin T → Site B) (j : ℕ) :
    Measure ((ℕ → Site B) × (ℕ → Site B)) :=
  pairLawTot B Q (silvestriStarts B T s j) (silvestriStarts B T s' j)

/-- Each pair of the family is a probability measure, once `Q` is one on the pairs of
height at most `0`. -/
theorem silvestriPairLaw_isProbability (B : Base)
    (Q : Site B → Site B → Measure ((ℕ → Site B) × (ℕ → Site B)))
    (hQ : ∀ x x' : Site B, x.2 ≤ 0 → x'.2 ≤ 0 → IsProbabilityMeasure (Q x x'))
    (T : ℕ) (s s' : Fin T → Site B) (j : ℕ) :
    IsProbabilityMeasure (silvestriPairLaw B Q T s s' j) :=
  pairLawTot_isProbability B Q hQ _ _

/-- The coupling family. It depends on `(B, Q, T, F, s, s')` only, not on `m` and not on
`γ`, so one family serves every `m` in `silvestri_prop2`. The probability hypothesis
`hQ` is used only to make each pair law a probability measure. -/
noncomputable def silvestriJ (B : Base)
    (Q : Site B → Site B → Measure ((ℕ → Site B) × (ℕ → Site B)))
    (hQ : ∀ x x' : Site B, x.2 ≤ 0 → x'.2 ≤ 0 → IsProbabilityMeasure (Q x x'))
    (T : ℕ) (F : ResumeFinite B) (s s' : Fin T → Site B) :
    Measure (SilvestriHistory B T × SilvestriHistory B T) :=
  haveI : ∀ j, IsProbabilityMeasure (silvestriPairLaw B Q T s s' j) :=
    fun j => silvestriPairLaw_isProbability B Q hQ T s s' j
  ((Measure.infinitePi fun j => silvestriPairLaw B Q T s s' j).map
      (fun ω : ℕ → (ℕ → Site B) × (ℕ → Site B) =>
        ((fun j => (ω j).1 : TrajSeq B), (fun j => (ω j).2 : TrajSeq B)))).map
    (Prod.map (silvestriHistory B T F) (silvestriHistory B T F))

/-- Measurability of the map that splits a sequence of pairs into two coordinate paths. -/
theorem measurable_silvestriCoords (B : Base) :
    Measurable (fun ω : ℕ → (ℕ → Site B) × (ℕ → Site B) =>
      ((fun j => (ω j).1 : TrajSeq B), (fun j => (ω j).2 : TrajSeq B))) := by
  refine Measurable.prodMk ?_ ?_
  · exact measurable_pi_lambda _ fun j => measurable_fst.comp (measurable_pi_apply j)
  · exact measurable_pi_lambda _ fun j => measurable_snd.comp (measurable_pi_apply j)

/-- The first marginal of `silvestriJ` is the fixed-start process law of the first
starts. -/
theorem silvestriJ_map_fst (B : Base)
    (Q : Site B → Site B → Measure ((ℕ → Site B) × (ℕ → Site B)))
    (hQ : ∀ x x' : Site B, x.2 ≤ 0 → x'.2 ≤ 0 → IsProbabilityMeasure (Q x x'))
    (hQ1 : ∀ x x' : Site B, x.2 ≤ 0 → x'.2 ≤ 0 →
      (Q x x').map Prod.fst = walkPathLaw B x)
    (T : ℕ) (F : ResumeFinite B) (s s' : Fin T → Site B) :
    (silvestriJ B Q hQ T F s s').map Prod.fst = silvestriProcessLaw B T F s := by
  haveI : ∀ j, IsProbabilityMeasure (silvestriPairLaw B Q T s s' j) :=
    fun j => silvestriPairLaw_isProbability B Q hQ T s s' j
  have hfam : (fun j => (silvestriPairLaw B Q T s s' j).map Prod.fst) =
      fun j => walkPathLaw B (silvestriStarts B T s j) :=
    funext fun j => pairLawTot_map_fst B Q hQ1 _ _
  have hfst : Measurable (fun ω : ℕ → (ℕ → Site B) × (ℕ → Site B) =>
      (fun j => (ω j).1 : TrajSeq B)) :=
    measurable_pi_lambda _ fun j => measurable_fst.comp (measurable_pi_apply j)
  have hcoord : (Measure.infinitePi fun j => silvestriPairLaw B Q T s s' j).map
      (fun ω : ℕ → (ℕ → Site B) × (ℕ → Site B) => (fun j => (ω j).1 : TrajSeq B)) =
      Measure.infinitePi fun j => (silvestriPairLaw B Q T s s' j).map Prod.fst :=
    Measure.infinitePi_map_pi (μ := fun j => silvestriPairLaw B Q T s s' j)
      (f := fun _ => Prod.fst) (fun _ => measurable_fst)
  unfold silvestriJ
  rw [Measure.map_map measurable_fst
      ((measurable_silvestriHistory B T F).prodMap (measurable_silvestriHistory B T F)),
    show (Prod.fst ∘ Prod.map (silvestriHistory B T F) (silvestriHistory B T F)) =
      silvestriHistory B T F ∘ Prod.fst from rfl,
    Measure.map_map ((measurable_silvestriHistory B T F).comp measurable_fst)
      (measurable_silvestriCoords B),
    show (silvestriHistory B T F ∘ Prod.fst) ∘
        (fun ω : ℕ → (ℕ → Site B) × (ℕ → Site B) =>
          ((fun j => (ω j).1 : TrajSeq B), (fun j => (ω j).2 : TrajSeq B))) =
      silvestriHistory B T F ∘ (fun ω : ℕ → (ℕ → Site B) × (ℕ → Site B) =>
        (fun j => (ω j).1 : TrajSeq B)) from rfl,
    ← Measure.map_map (measurable_silvestriHistory B T F) hfst, hcoord, hfam]
  rfl

/-- The second marginal of `silvestriJ` is the fixed-start process law of the second
starts. -/
theorem silvestriJ_map_snd (B : Base)
    (Q : Site B → Site B → Measure ((ℕ → Site B) × (ℕ → Site B)))
    (hQ : ∀ x x' : Site B, x.2 ≤ 0 → x'.2 ≤ 0 → IsProbabilityMeasure (Q x x'))
    (hQ2 : ∀ x x' : Site B, x.2 ≤ 0 → x'.2 ≤ 0 →
      (Q x x').map Prod.snd = walkPathLaw B x')
    (T : ℕ) (F : ResumeFinite B) (s s' : Fin T → Site B) :
    (silvestriJ B Q hQ T F s s').map Prod.snd = silvestriProcessLaw B T F s' := by
  haveI : ∀ j, IsProbabilityMeasure (silvestriPairLaw B Q T s s' j) :=
    fun j => silvestriPairLaw_isProbability B Q hQ T s s' j
  have hfam : (fun j => (silvestriPairLaw B Q T s s' j).map Prod.snd) =
      fun j => walkPathLaw B (silvestriStarts B T s' j) :=
    funext fun j => pairLawTot_map_snd B Q hQ2 _ _
  have hsnd : Measurable (fun ω : ℕ → (ℕ → Site B) × (ℕ → Site B) =>
      (fun j => (ω j).2 : TrajSeq B)) :=
    measurable_pi_lambda _ fun j => measurable_snd.comp (measurable_pi_apply j)
  have hcoord : (Measure.infinitePi fun j => silvestriPairLaw B Q T s s' j).map
      (fun ω : ℕ → (ℕ → Site B) × (ℕ → Site B) => (fun j => (ω j).2 : TrajSeq B)) =
      Measure.infinitePi fun j => (silvestriPairLaw B Q T s s' j).map Prod.snd :=
    Measure.infinitePi_map_pi (μ := fun j => silvestriPairLaw B Q T s s' j)
      (f := fun _ => Prod.snd) (fun _ => measurable_snd)
  unfold silvestriJ
  rw [Measure.map_map measurable_snd
      ((measurable_silvestriHistory B T F).prodMap (measurable_silvestriHistory B T F)),
    show (Prod.snd ∘ Prod.map (silvestriHistory B T F) (silvestriHistory B T F)) =
      silvestriHistory B T F ∘ Prod.snd from rfl,
    Measure.map_map ((measurable_silvestriHistory B T F).comp measurable_snd)
      (measurable_silvestriCoords B),
    show (silvestriHistory B T F ∘ Prod.snd) ∘
        (fun ω : ℕ → (ℕ → Site B) × (ℕ → Site B) =>
          ((fun j => (ω j).1 : TrajSeq B), (fun j => (ω j).2 : TrajSeq B))) =
      silvestriHistory B T F ∘ (fun ω : ℕ → (ℕ → Site B) × (ℕ → Site B) =>
        (fun j => (ω j).2 : TrajSeq B)) from rfl,
    ← Measure.map_map (measurable_silvestriHistory B T F) hsnd, hcoord, hfam]
  rfl

end IdlaCyl.Silvestri
