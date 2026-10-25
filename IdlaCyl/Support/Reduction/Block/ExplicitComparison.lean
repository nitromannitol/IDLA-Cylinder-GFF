module

public import IdlaCyl.Support.Admissible
public import IdlaCyl.Support.Recurrence.Discharge
public import IdlaCyl.Support.Reduction.Block.EndCoupledBlocks
public import IdlaCyl.Support.Reduction.Block.FirstHitSpectral
public import IdlaCyl.Support.Reduction.Block.SpectralCompare
public import IdlaCyl.Support.Reduction.CitationEndpoint
public import IdlaCyl.Support.Reduction.EntranceTail
public import IdlaCyl.Support.Silvestri.AssembleUnion
public import IdlaCyl.Support.Silvestri.LadderFail

@[expose] public section

/-!
# The explicit comparison of two release lists

For a spectral datum `S` of the base and a height `H ≥ 1`, the first-hit laws on a layer
`ℓ` of two walks started at heights at most `ℓ - H` are within total variation
`η = √N e^{-H/√τ_rel}` of each other (`blockEnd_tv_le`). The end vertices of the first
blocks to layer `ℓ` are the first-hit sites (`blockEndLaw_eq_hitProb`), so one end-coupled
block round at layer `H` gives a pair law `explicitPair` whose failure probability is at most
`η` (`explicitPair_fail_le`). Feeding these pair laws into the coupling family `silvestriJ`
gives a coupling of two release lists of length `T` with failure allowance `T η`
(`explicit_endpoint`). The proof uses no connectedness hypothesis.

The recurrence input of the first-hit identities is the proved theorem
`External.lazyRwRecurrent_holds`.
-/

namespace IdlaCyl.Reduction

open MeasureTheory IdlaCyl.Silvestri
open scoped ENNReal

/-- The explicit uniform end distance `η_H = √N e^{-H/√τ_rel}`. -/
noncomputable def explicitEta (B : Base) (S : SpectralData B) (H : ℕ) : ℝ :=
  Real.sqrt (B.card : ℝ) * Real.exp (-(H : ℝ) / Real.sqrt S.relaxTime)

/-- The explicit distance is nonnegative. -/
theorem explicitEta_nonneg (B : Base) (S : SpectralData B) (H : ℕ) :
    0 ≤ explicitEta B S H := by
  unfold explicitEta
  positivity

/-- Almost every path from `p` below layer `ℓ` has its first block ending at the first hitting
site of layer `ℓ`. -/
theorem blockEnd_firstBlock_ae (B : Base) (ℓ : ℤ) (p : Site B) (hp : p.2 < ℓ) :
    ∀ᵐ X ∂(walkPathLaw B p), blockEnd B p (firstBlock B ℓ X) = firstHitSite B ℓ X := by
  filter_upwards [walkPathLaw_ae_admissible B p, walkPathLaw_ae_start B p,
    ae_hitLevel_ne_top External.lazyRwRecurrent_holds B p ℓ] with X ha h0 hf
  have hset : below B ℓ = R B ((ℓ : ℝ) - 1) := by
    ext q
    simp only [below, R, Set.mem_setOf_eq]
    constructor
    · intro h
      have h' : q.2 + 1 ≤ ℓ := h
      have h'' : ((q.2 : ℤ) : ℝ) + 1 ≤ (ℓ : ℝ) := by exact_mod_cast h'
      linarith
    · intro h
      have h' : ((q.2 : ℤ) : ℝ) < (ℓ : ℝ) := by linarith
      exact_mod_cast h'
  have hexit : exitTime' B (below B ℓ) X = hitLevel B ℓ X := by
    rw [hset]
    exact exit_lower_eq_hit B ℓ X ha (by rw [h0]; exact_mod_cast hp.le) hf
  have hn : WithTop.untopA (exitTime' B (below B ℓ) X) = WithTop.untopA (hitLevel B ℓ X) := by
    rw [hexit]
  rw [blockEnd_firstBlock B ℓ p X _ h0 hn]
  rfl

/-- Almost every path has its layer-`ℓ` first hit at height `ℓ`. -/
theorem firstHitSite_snd_ae (B : Base) (ℓ : ℤ) (p : Site B) :
    ∀ᵐ X ∂(walkPathLaw B p), (firstHitSite B ℓ X).2 = ℓ := by
  filter_upwards [ae_hitLevel_ne_top External.lazyRwRecurrent_holds B p ℓ] with X hf
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hf
  have hhit : hitLevel B ℓ X = (k : ℕ∞) := hk.symm
  have hu : WithTop.untopA (hitLevel B ℓ X) = k := by
    rw [hhit]
    rfl
  show (X (WithTop.untopA (hitLevel B ℓ X))).2 = ℓ
  rw [hu]
  exact ((hitLevel_eq_coe_iff B ℓ X k).mp hhit).1

/-- The end law of the first block from `p` to layer `ℓ` is the first-hit law of that layer:
its mass at `z` is `H_{(z,ℓ)}(p)`. -/
theorem blockEndLaw_eq_hitProb (B : Base) (ℓ : ℤ) (p : Site B) (hp : p.2 < ℓ) (z : B.V) :
    (blockEndLaw B ℓ p {z}).toReal = hitProb B (z, ℓ) p := by
  rw [hitProb_eq_toReal B (z, ℓ) p (not_lt.mpr hp.le), hitProbE, ← blockLaw_end_preimage B ℓ p z]
  unfold blockLaw
  rw [Measure.map_apply (measurable_firstBlock B ℓ)
    (Set.to_countable {c : Block B | (blockEnd B p c).1 = z}).measurableSet]
  refine congrArg ENNReal.toReal (measure_congr ?_)
  filter_upwards [blockEnd_firstBlock_ae B ℓ p hp, firstHitSite_snd_ae B ℓ p] with X h1 h2
  show ((blockEnd B p (firstBlock B ℓ X)).1 = z) = (firstHitSite B ℓ X = (z, ℓ))
  rw [h1]
  exact propext ⟨fun h => Prod.ext h h2, fun h => by rw [h]⟩

/-- The first-hit laws of two starts at heights at most `ℓ - H` are within `η_H` in total
variation, through the uniform law on the layer. The bound is the triangle inequality through
the uniform law, with the spectral total-variation bound at each start. -/
theorem blockEnd_tv_le (B : Base) (S : SpectralData B) (hN : 2 ≤ B.card) (H : ℕ) (hH : 1 ≤ H)
    (ℓ : ℤ) (p p' : Site B) (hp : (p.2 : ℝ) + H ≤ ℓ) (hp' : (p'.2 : ℝ) + H ≤ ℓ) :
    (1 / 2 : ℝ) * ∑ z : B.V, |(blockEndLaw B ℓ p {z}).toReal - (blockEndLaw B ℓ p' {z}).toReal|
      ≤ explicitEta B S H := by
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hH0 : (0 : ℝ) ≤ H := by positivity
  have hlt : p.2 < ℓ := by
    have : (p.2 : ℝ) < ℓ := by linarith
    exact_mod_cast this
  have hlt' : p'.2 < ℓ := by
    have : (p'.2 : ℝ) < ℓ := by linarith
    exact_mod_cast this
  have hsum : ∑ z : B.V, |(blockEndLaw B ℓ p {z}).toReal - (blockEndLaw B ℓ p' {z}).toReal| ≤
      ∑ z : B.V, |hitProb B (z, ℓ) p - 1 / (B.card : ℝ)| +
        ∑ z : B.V, |hitProb B (z, ℓ) p' - 1 / (B.card : ℝ)| := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun z _ => ?_
    rw [blockEndLaw_eq_hitProb B ℓ p hlt z, blockEndLaw_eq_hitProb B ℓ p' hlt' z]
    have h := abs_sub_le (hitProb B (z, ℓ) p) (1 / (B.card : ℝ)) (hitProb B (z, ℓ) p')
    rwa [abs_sub_comm (1 / (B.card : ℝ)) (hitProb B (z, ℓ) p')] at h
  have hq2 := inv_sqrt_relaxTime_le_qk_two S hN
  have hpos : (0 : ℝ) ≤ 1 / Real.sqrt S.relaxTime := by positivity
  have hqn : 0 ≤ S.qk 2 := hpos.trans hq2
  have hTV : ∀ q : Site B, (q.2 : ℝ) + H ≤ ℓ →
      (1 / 2 : ℝ) * ∑ z : B.V, |hitProb B (z, ℓ) q - 1 / (B.card : ℝ)| ≤
        (1 / 2 : ℝ) * Real.sqrt ((B.card : ℝ) - 1) * Real.exp (-(H : ℝ) / Real.sqrt S.relaxTime) := by
    intro q hq
    have hqle : q.2 ≤ ℓ := by
      have : (q.2 : ℝ) ≤ ℓ := by linarith
      exact_mod_cast this
    refine (hitProb_tv B S ℓ q hqle External.lazyRwRecurrent_holds).trans ?_
    have hd : (H : ℝ) ≤ (ℓ : ℝ) - (q.2 : ℝ) := by linarith
    have e1 : -(S.qk 2) * ((ℓ : ℝ) - (q.2 : ℝ)) ≤ -(S.qk 2) * (H : ℝ) := by
      have := mul_le_mul_of_nonneg_left hd hqn
      linarith
    have e2 : -(S.qk 2) * (H : ℝ) ≤ -(H : ℝ) / Real.sqrt S.relaxTime := by
      have := mul_le_mul_of_nonneg_right hq2 hH0
      have e3 : -(H : ℝ) / Real.sqrt S.relaxTime = -((1 / Real.sqrt S.relaxTime) * H) := by
        ring
      linarith
    have he := Real.exp_le_exp.mpr (e1.trans e2)
    exact mul_le_mul_of_nonneg_left he (by positivity)
  have hA := hTV p hp
  have hA' := hTV p' hp'
  have hsq : Real.sqrt ((B.card : ℝ) - 1) ≤ Real.sqrt (B.card : ℝ) :=
    Real.sqrt_le_sqrt (by linarith)
  have hE := Real.exp_nonneg (-(H : ℝ) / Real.sqrt S.relaxTime)
  have hmain := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
  unfold explicitEta
  nlinarith [hmain, hA, hA', mul_le_mul_of_nonneg_right hsq hE]

/-- The explicit pair law of two walks: one end-coupled block round at layer `H`. -/
noncomputable def explicitPair (B : Base) (H : ℕ) (x x' : Site B) :
    Measure ((ℕ → Site B) × (ℕ → Site B)) :=
  ladderLaw B (endCoupledPair B) H 1 (H : ℤ) x x'

/-- The first marginal of the explicit pair law is the walk law from its first start. -/
theorem explicitPair_map_fst (B : Base) (H : ℕ) (hH : 1 ≤ H) (x x' : Site B)
    (hx : x.2 ≤ 0) (hx' : x'.2 ≤ 0) :
    (explicitPair B H x x').map Prod.fst = walkPathLaw B x := by
  have hlt : x.2 < (H : ℤ) := by omega
  have hlt' : x'.2 < (H : ℤ) := by omega
  unfold explicitPair
  exact ladderLaw_map_fst B (Q := endCoupledPair B)
    (fun ℓ p p' _ _ => endCoupledPair_map_fst B ℓ p p')
    (fun ℓ p p' _ _ => endCoupledPair_map_snd B ℓ p p') (by omega) 1 (H : ℤ) x x' hlt hlt'

/-- The second marginal of the explicit pair law is the walk law from its second start. -/
theorem explicitPair_map_snd (B : Base) (H : ℕ) (hH : 1 ≤ H) (x x' : Site B)
    (hx : x.2 ≤ 0) (hx' : x'.2 ≤ 0) :
    (explicitPair B H x x').map Prod.snd = walkPathLaw B x' := by
  have hlt : x.2 < (H : ℤ) := by omega
  have hlt' : x'.2 < (H : ℤ) := by omega
  unfold explicitPair
  exact ladderLaw_map_snd B (Q := endCoupledPair B)
    (fun ℓ p p' _ _ => endCoupledPair_map_fst B ℓ p p')
    (fun ℓ p p' _ _ => endCoupledPair_map_snd B ℓ p p') (by omega) 1 (H : ℤ) x x' hlt hlt'

/-- The explicit pair law is a probability measure on the starts of height at most `0`. -/
theorem explicitPair_isProbability (B : Base) (H : ℕ) (hH : 1 ≤ H) (x x' : Site B)
    (hx : x.2 ≤ 0) (hx' : x'.2 ≤ 0) :
    IsProbabilityMeasure (explicitPair B H x x') := by
  have hlt : x.2 < (H : ℤ) := by omega
  have hlt' : x'.2 < (H : ℤ) := by omega
  unfold explicitPair
  exact ⟨ladderLaw_univ B (Q := endCoupledPair B)
    (fun ℓ p p' _ _ => endCoupledPair_map_fst B ℓ p p')
    (fun ℓ p p' _ _ => endCoupledPair_map_snd B ℓ p p') (by omega) 1 (H : ℤ) x x' hlt hlt'⟩

/-- The end vertices of one end-coupled block round at layer `ℓ` differ with probability at
most `η_H`, when both starts lie `H` below the layer. -/
theorem endCoupled_end_le (B : Base) (S : SpectralData B) (hN : 2 ≤ B.card) (H : ℕ) (hH : 1 ≤ H)
    (ℓ : ℤ) (p p' : Site B) (hp : (p.2 : ℝ) + H ≤ ℓ) (hp' : (p'.2 : ℝ) + H ≤ ℓ) :
    endCoupledPair B ℓ p p' {cc | blockEnd B p cc.1 ≠ blockEnd B p' cc.2} ≤
      ENNReal.ofReal (explicitEta B S H) := by
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hlt : p.2 < ℓ := by
    have : (p.2 : ℝ) < ℓ := by linarith
    exact_mod_cast this
  have hlt' : p'.2 < ℓ := by
    have : (p'.2 : ℝ) < ℓ := by linarith
    exact_mod_cast this
  exact (endCoupledPair_end_ne B ℓ p p' hlt hlt').trans
    (ENNReal.ofReal_le_ofReal (blockEnd_tv_le B S hN H hH ℓ p p' hp hp'))

/-- The explicit pair law fails the pathwise success event below height `H` with probability
at most `η_H`, for starts at heights at most `0`: one end-coupled round, no iteration. -/
theorem explicitPair_fail_le (B : Base) (S : SpectralData B) (hN : 2 ≤ B.card) (H : ℕ)
    (hH : 1 ≤ H) (x x' : Site B) (hx : x.2 ≤ 0) (hx' : x'.2 ≤ 0) :
    explicitPair B H x x' {pp | ¬ pairGood B (H : ℝ) pp.1 pp.2} ≤
      ENNReal.ofReal (explicitEta B S H) := by
  have hH0 : 0 < H := by omega
  have hlt : x.2 < (H : ℤ) := by omega
  have hlt' : x'.2 < (H : ℤ) := by omega
  have hp : (x.2 : ℝ) + (H : ℝ) ≤ ((H : ℤ) : ℝ) := by
    have : (x.2 : ℝ) ≤ 0 := by exact_mod_cast hx
    push_cast
    linarith
  have hp' : (x'.2 : ℝ) + (H : ℝ) ≤ ((H : ℤ) : ℝ) := by
    have : (x'.2 : ℝ) ≤ 0 := by exact_mod_cast hx'
    push_cast
    linarith
  have hQf : ∀ (ℓ : ℤ) (p p' : Site B), (p.2 : ℝ) + (H : ℝ) ≤ ℓ → (p'.2 : ℝ) + (H : ℝ) ≤ ℓ →
      endCoupledPair B ℓ p p' {cc | blockEnd B p cc.1 ≠ blockEnd B p' cc.2} ≤
        ENNReal.ofReal (explicitEta B S H) :=
    fun ℓ p p' hq hq' => endCoupled_end_le B S hN H hH ℓ p p' hq hq'
  have h := ladderLaw_notPairGood_le B (Q := endCoupledPair B)
    (fun ℓ p p' _ _ => endCoupledPair_map_fst B ℓ p p')
    (fun ℓ p p' _ _ => endCoupledPair_map_snd B ℓ p p') hH0 (explicitEta_nonneg B S H) hQf
    1 1 le_rfl (H : ℤ) x x' hp hp'
  have hval : ((H : ℤ) : ℝ) + (((1 : ℕ) : ℝ) - 1) * (H : ℝ) = (H : ℝ) := by
    push_cast
    ring
  rw [hval, pow_one] at h
  unfold explicitPair
  exact h

/-- Two release lists of length `T` at heights at most `0`, with seed containing `R_H`, are
coupled with failure allowance `T η_H` in the sense of `ClusterCoupling`. No connectedness is
needed. -/
theorem explicit_endpoint (B : Base) (S : SpectralData B) (hN : 2 ≤ B.card) (H : ℕ) (hH : 1 ≤ H)
    (T : ℕ) (F : ResumeFinite B) (hF : R B (H : ℝ) ⊆ resumeSeed B F)
    (s s' : Fin T → Site B) (hs : ∀ i, (s i).2 ≤ 0) (hs' : ∀ i, (s' i).2 ≤ 0) :
    ClusterCoupling B (resumeRun B F (List.ofFn s)) (resumeRun B F (List.ofFn s')) 0
      ((T : ℝ) * explicitEta B S H) := by
  have hstart : ∀ (s0 : Fin T → Site B), (∀ i, (s0 i).2 ≤ 0) →
      ∀ j, (External.silvestriStarts B T s0 j).2 ≤ 0 := by
    intro s0 hs0 j
    by_cases hj : j < T
    · simp only [External.silvestriStarts, dif_pos hj]
      exact hs0 _
    · simp only [External.silvestriStarts, dif_neg hj]
      exact le_refl _
  have hQ : ∀ x x' : Site B, x.2 ≤ 0 → x'.2 ≤ 0 → IsProbabilityMeasure (explicitPair B H x x') :=
    fun x x' hx hx' => explicitPair_isProbability B H hH x x' hx hx'
  have hQ1 : ∀ x x' : Site B, x.2 ≤ 0 → x'.2 ≤ 0 →
      (explicitPair B H x x').map Prod.fst = walkPathLaw B x :=
    fun x x' hx hx' => explicitPair_map_fst B H hH x x' hx hx'
  have hQ2 : ∀ x x' : Site B, x.2 ≤ 0 → x'.2 ≤ 0 →
      (explicitPair B H x x').map Prod.snd = walkPathLaw B x' :=
    fun x x' hx hx' => explicitPair_map_snd B H hH x x' hx hx'
  have hε : ∀ t < T, silvestriPairLaw B (explicitPair B H) T s s' t
      {x | ¬ pairGood B (H : ℝ) x.1 x.2} ≤ ENNReal.ofReal (explicitEta B S H) := by
    intro t _
    unfold silvestriPairLaw pairLawTot
    rw [if_pos ⟨hstart s hs t, hstart s' hs' t⟩]
    exact explicitPair_fail_le B S hN H hH _ _ (hstart s hs t) (hstart s' hs' t)
  have hdiag := silvestriJ_diag_ge B (explicitPair B H) hQ T F s s' (H : ℝ) hF
    (ENNReal.ofReal (explicitEta B S H)) hε
  haveI : IsProbabilityMeasure (silvestriJ B (explicitPair B H) hQ T F s s') :=
    probability_of_first_marginal _ _ (silvestriJ_map_fst B (explicitPair B H) hQ hQ1 T F s s')
  let e : External.SilvestriHistory B T × External.SilvestriHistory B T →
      ResumeFinite B × ResumeFinite B := fun p => (p.1 (Fin.last T), p.2 (Fin.last T))
  have he : Measurable e := (measurable_pi_apply (Fin.last T) |>.comp measurable_fst).prodMk
    ((measurable_pi_apply (Fin.last T)).comp measurable_snd)
  refine ⟨(silvestriJ B (explicitPair B H) hQ T F s s').map e, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst he]
    have hm := Measure.map_map (measurable_pi_apply (Fin.last T)) measurable_fst
      (μ := silvestriJ B (explicitPair B H) hQ T F s s')
    rw [silvestriJ_map_fst B (explicitPair B H) hQ hQ1 T F s s', silvestri_endpoint_law]
      at hm
    exact hm.symm
  · rw [Measure.map_map measurable_snd he]
    have hm := Measure.map_map (measurable_pi_apply (Fin.last T)) measurable_snd
      (μ := silvestriJ B (explicitPair B H) hQ T F s s')
    rw [silvestriJ_map_snd B (explicitPair B H) hQ hQ2 T F s s', silvestri_endpoint_law]
      at hm
    exact hm.symm
  · rw [Measure.map_apply he (Set.to_countable _).measurableSet]
    have hsub : e ⁻¹' (matchShift B 0)ᶜ ⊆
        {p : External.SilvestriHistory B T × External.SilvestriHistory B T | p.1 = p.2}ᶜ := by
      intro p hp heq
      apply hp
      rw [mem_matchShift_zero]
      exact congrFun heq (Fin.last T)
    apply (measure_mono hsub).trans
    have hD : MeasurableSet
        {p : External.SilvestriHistory B T × External.SilvestriHistory B T | p.1 = p.2} :=
      (Set.to_countable _).measurableSet
    have hT : ENNReal.ofReal ((T : ℝ) * explicitEta B S H) =
        (T : ℝ≥0∞) * ENNReal.ofReal (explicitEta B S H) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg T), ENNReal.ofReal_natCast]
    rw [prob_compl_eq_one_sub hD, hT, tsub_le_iff_right, add_comm]
    exact tsub_le_iff_right.mp hdiag

end IdlaCyl.Reduction
