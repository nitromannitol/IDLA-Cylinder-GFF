import IdlaCyl.Support.Silvestri.AssembleDet
import IdlaCyl.Support.Silvestri.AssembleFamily

/-!
# The diagonal of the coupling family of Silvestri's Proposition 2

The coupling family `silvestriJ` pairs two IDLA histories, one from each of its two
marginals. This file bounds the probability that the two histories agree.

Each pair of the family is a law on pairs of paths. If, for every walker `t < T`, the pair
`silvestriPairLaw B Q T s s' t` fails the pathwise success event `pairGood B H` with
probability at most `ε`, then the diagonal `{p | p.1 = p.2}` has `silvestriJ`-measure at
least `1 - T * ε`.

The file proves the following.

1. `silvestriJ_diag_ge`: the diagonal bound above, for any seed `F` containing the
   half-cylinder `R B H`.

The proof uses no measurability of the diagonal or of the good event. It uses only the
outer inequalities `MeasureTheory.Measure.le_map_apply` and `measure_biUnion_finset_le`,
together with the deterministic induction `resumeGrow_eq_of_success`, which turns success
on every walker into equal histories.
-/

namespace IdlaCyl.Silvestri

open MeasureTheory IdlaCyl.External
open scoped ENNReal

/-- The coupling family puts the two histories on the diagonal with probability at least
`1 - T * ε`, when every pair of the family fails the pathwise success event below the height
`H` with probability at most `ε`, and the seed `F` contains the half-cylinder `R B H`. -/
theorem silvestriJ_diag_ge (B : Base)
    (Q : Site B → Site B → Measure ((ℕ → Site B) × (ℕ → Site B)))
    (hQ : ∀ x x' : Site B, x.2 ≤ 0 → x'.2 ≤ 0 → IsProbabilityMeasure (Q x x'))
    (T : ℕ) (F : ResumeFinite B) (s s' : Fin T → Site B) (H : ℝ)
    (hF : R B H ⊆ resumeSeed B F) (ε : ℝ≥0∞)
    (hε : ∀ t < T, silvestriPairLaw B Q T s s' t {x | ¬ pairGood B H x.1 x.2} ≤ ε) :
    1 - (T : ℝ≥0∞) * ε ≤ silvestriJ B Q hQ T F s s' {p | p.1 = p.2} := by
  haveI : ∀ j, IsProbabilityMeasure (silvestriPairLaw B Q T s s' j) :=
    fun j => silvestriPairLaw_isProbability B Q hQ T s s' j
  unfold silvestriJ
  generalize hP : Measure.infinitePi (fun j => silvestriPairLaw B Q T s s' j) = P
  have hPprob : IsProbabilityMeasure P := by
    rw [← hP]
    infer_instance
  -- the coordinate map, the history map, and the event that the histories agree
  set G : (ℕ → (ℕ → Site B) × (ℕ → Site B)) → TrajSeq B × TrajSeq B :=
    fun ω => ((fun j => (ω j).1 : TrajSeq B), (fun j => (ω j).2 : TrajSeq B))
  set Φ := Prod.map (silvestriHistory B T F) (silvestriHistory B T F)
  have hGm : Measurable G := measurable_silvestriCoords B
  have hΦm : Measurable Φ :=
    (measurable_silvestriHistory B T F).prodMap (measurable_silvestriHistory B T F)
  set A : Set (ℕ → (ℕ → Site B) × (ℕ → Site B)) := G ⁻¹' (Φ ⁻¹' {p | p.1 = p.2})
  -- Step 1: the probability of `A` is at most the probability of the diagonal.
  have h1 : P A ≤ Measure.map Φ (Measure.map G P) {p | p.1 = p.2} :=
    (Measure.le_map_apply hGm.aemeasurable _).trans
      (Measure.le_map_apply hΦm.aemeasurable _)
  -- Step 2: `A` and its complement cover the whole space.
  have h2 : (1 : ℝ≥0∞) ≤ P A + P Aᶜ := by
    calc (1 : ℝ≥0∞) = P Set.univ := measure_univ.symm
      _ = P (A ∪ Aᶜ) := by rw [Set.union_compl_self]
      _ ≤ P A + P Aᶜ := measure_union_le _ _
  -- Step 3: if every walker below `T` is good, the two histories agree.
  have h3 : Aᶜ ⊆ ⋃ t ∈ Finset.range T, (fun ω => ω t) ⁻¹' {x | ¬ pairGood B H x.1 x.2} := by
    intro ω hω
    have hne : ¬ silvestriHistory B T F (fun j => (ω j).1) =
        silvestriHistory B T F (fun j => (ω j).2) := hω
    by_contra hcon
    have hgood : ∀ t < T, pairGood B H ((fun j => (ω j).1 : TrajSeq B) t)
        ((fun j => (ω j).2 : TrajSeq B) t) := by
      intro t ht
      by_contra hbad
      exact hcon (Set.mem_iUnion₂.mpr ⟨t, Finset.mem_range.mpr ht, hbad⟩)
    apply hne
    funext t
    exact resumeGrow_eq_of_success B T F H hF (fun j => (ω j).1 : TrajSeq B)
      (fun j => (ω j).2 : TrajSeq B) hgood t (Nat.le_of_lt_succ t.2)
  -- Step 4: each walker fails with probability at most `ε`, so the union bound gives `T * ε`.
  have hmarg : ∀ t, P.map (fun ω => ω t) = silvestriPairLaw B Q T s s' t := by
    intro t
    rw [← hP]
    exact Measure.infinitePi_map_eval (fun j => silvestriPairLaw B Q T s s' j) t
  have h4 : P (⋃ t ∈ Finset.range T, (fun ω => ω t) ⁻¹' {x | ¬ pairGood B H x.1 x.2}) ≤
      (T : ℝ≥0∞) * ε := by
    refine (measure_biUnion_finset_le (μ := P) _ _).trans ?_
    calc ∑ t ∈ Finset.range T, P ((fun ω => ω t) ⁻¹' {x | ¬ pairGood B H x.1 x.2})
        ≤ ∑ _t ∈ Finset.range T, ε := by
          refine Finset.sum_le_sum fun t ht => ?_
          calc P ((fun ω => ω t) ⁻¹' {x | ¬ pairGood B H x.1 x.2})
              ≤ P.map (fun ω => ω t) {x | ¬ pairGood B H x.1 x.2} :=
                Measure.le_map_apply (measurable_pi_apply t).aemeasurable _
            _ = silvestriPairLaw B Q T s s' t {x | ¬ pairGood B H x.1 x.2} := by
                rw [hmarg t]
            _ ≤ ε := hε t (Finset.mem_range.mp ht)
      _ = (T : ℝ≥0∞) * ε := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Step 5: combine the bounds.
  have h5 : P Aᶜ ≤ (T : ℝ≥0∞) * ε := (measure_mono h3).trans h4
  exact (tsub_le_tsub_left h5 1).trans ((tsub_le_iff_right.mpr h2).trans h1)

end IdlaCyl.Silvestri
