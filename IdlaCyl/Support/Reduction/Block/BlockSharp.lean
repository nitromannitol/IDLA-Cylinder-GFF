module

public import IdlaCyl.Support.Reduction.Block.StoppedTailSharp
public import IdlaCyl.Support.Reduction.Block.BlockStopped
public import IdlaCyl.Support.Reduction.Block.BlockLedger
public import IdlaCyl.Support.Reduction.Block.BlockBuffer

@[expose] public section

/-!
# Block filling and the block ledger with the sharp tail

Source: paper/idla-cylinder-gff.tex, tex:1194-1251 (the sharp lower tail of the stopped score and
the block filling of the stopped cluster).

The block-filling bound `N H e^{-H/8}` of `BlockFill.lean` is replaced by the sharper bound
`N H e^{-H/4}` of `StoppedTailSharp.lean`. This file gives the four consumers of the block filling
their sharp versions: the stopped cluster at every time `M ≥ 2 N H`, the stopped growth from the
rectangle `R_a`, the block batch and its ledger, and the canonical growth from a shifted empty seed.
Each proof is the proof of its `e^{-H/8}` counterpart with the sharp input.
-/

attribute [local instance] Classical.propDecidable

namespace IdlaCyl.Reduction

open MeasureTheory
open scoped ENNReal

variable (B : Base)

/-- **Block filling at every later time, with the sharper exponent** (`tex:1194-1251`). For
`M ≥ 2 N H` the stopped cluster contains `R_H` except on an event of probability at most
`N H e^{-H/4}`, since the stopped cluster is nondecreasing in time. -/
theorem stopped_block_fill_sharp_ge (H : ℕ) (hH : 1 ≤ H) (M : ℕ) (hM : 2 * B.card * H ≤ M) :
    idlaMeasure B {ω : TrajSeq B | ¬ R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) ω M}
      ≤ ENNReal.ofReal ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4)) :=
  (measure_mono fun ω (hω : ¬ R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) ω M)
      (hsub : R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) ω (2 * B.card * H)) =>
    hω (Set.Subset.trans hsub (stoppedCluster_monotone B (H : ℤ) ω hM))).trans
    (stopped_block_fill_sharp B H hH)

/-- **Block filling from the rectangle `R_a`, with the sharper exponent** (`tex:1194-1251`).
With `2 N H` releases the stopped cluster from `R_a` at height `a + H` fills `R_{a+H}` except on an
event of probability at most `N H e^{-H/4}`. -/
theorem stoppedFrom_block_fill_sharp (B : Base) (a H M : ℕ) (hH : 1 ≤ H)
    (hM : 2 * B.card * H ≤ M) :
    idlaMeasure B {ω : TrajSeq B | ¬ R B ((a + H : ℕ) : ℝ) ⊆
      stoppedFrom B ((a + H : ℕ) : ℤ) (R B a) ω M} ≤
      ENNReal.ofReal ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4)) := by
  have hcast : ((a + H : ℕ) : ℤ) = (a : ℤ) + (H : ℤ) := by push_cast; ring
  have hRcast : ((a + H : ℕ) : ℝ) = (H : ℝ) + ((a : ℤ) : ℝ) := by push_cast; ring
  have hae : ∀ᵐ ω ∂(idlaMeasure B), ∀ i, CylAdmissible B (ω i) ∧ (ω i 0).2 = 0 ∧
      ∀ j : ℤ, ∃ n, (ω i n).2 = j :=
    layerDriving_ae_good B 0
  have hcongr : {ω : TrajSeq B | ¬ R B ((a + H : ℕ) : ℝ) ⊆
        stoppedFrom B ((a + H : ℕ) : ℤ) (R B a) ω M} =ᵐ[idlaMeasure B]
      blockTail B a ⁻¹' {X : TrajSeq B | ¬ R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) X M} := by
    filter_upwards [hae] with ω hω
    have hsh := stoppedFrom_rect_eq_shift B a H hH ω (fun i => (hω i).1)
      (fun i => (hω i).2.1) (fun i j => (hω i).2.2 j) M
    show (¬ R B ((a + H : ℕ) : ℝ) ⊆ stoppedFrom B ((a + H : ℕ) : ℤ) (R B a) ω M) =
      (¬ R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) (blockTail B a ω) M)
    rw [hcast, hsh, hRcast, ← outerShift_image_R B (a : ℤ) (H : ℝ),
      Set.image_subset_image_iff (outerShift B (a : ℤ)).injective]
  have hmeasG : MeasurableSet {X : TrajSeq B | ¬ R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) X M} :=
    measurableSet_not_subset_stoppedCluster B (H : ℤ) (H : ℝ) M
  calc idlaMeasure B {ω : TrajSeq B | ¬ R B ((a + H : ℕ) : ℝ) ⊆
        stoppedFrom B ((a + H : ℕ) : ℤ) (R B a) ω M}
      = idlaMeasure B (blockTail B a ⁻¹' {X : TrajSeq B | ¬ R B (H : ℝ) ⊆
          stoppedCluster B (H : ℤ) X M}) := measure_congr hcongr
    _ = (idlaMeasure B).map (blockTail B a) {X : TrajSeq B | ¬ R B (H : ℝ) ⊆
          stoppedCluster B (H : ℤ) X M} :=
        (Measure.map_apply (measurable_blockTail B a) hmeasG).symm
    _ = idlaMeasure B {X : TrajSeq B | ¬ R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) X M} := by
        rw [idlaMeasure_map_blockTail]
    _ ≤ ENNReal.ofReal ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4)) :=
        stopped_block_fill_sharp_ge B H hH M hM

/-- A block batch from the rectangle `R_a` misses its hit set with probability at most
`N H e^{-H/4}`, for any batch size `M ≥ 2 N H`. -/
theorem blockBatch_hit_fail_le_sharp (B : Base) (a H c : ℕ) (hH : 1 ≤ H) (hc : c = a + H)
    (s : ResumeState B) (hs : resumeSeed B s.1 = R B (a : ℝ)) (M : ℕ) (hM : 2 * B.card * H ≤ M) :
    blockBatch B (c : ℤ) M s (blockStageHit B M H c s)ᶜ ≤
      ENNReal.ofReal ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4)) := by
  subst hc
  have hG := blockGrow_count_ae B a H hH ((a + H : ℕ) : ℤ) (Nat.cast_add a H) s hs M
  have hG' : ∀ᵐ ω ∂idlaMeasure B, R B ((a + H : ℕ) : ℝ) ⊆
      resumeSeed B (blockGrow B ((a + H : ℕ) : ℤ) s ω M).1 →
      resumeSeed B (blockGrow B ((a + H : ℕ) : ℤ) s ω M).1 = R B ((a + H : ℕ) : ℝ) ∧
        ∀ k : ℤ, mobileOnLayer B (blockGrow B ((a + H : ℕ) : ℤ) s ω M).2 k =
          mobileOnLayer B s.2 k + if k = ((a + H : ℕ) : ℤ) then M - B.card * H else 0 := by
    simpa only [Int.cast_natCast] using hG
  rw [← blockBatch_law, Measure.map_apply (measurable_blockGrow B _ _ _)
    (Set.to_countable _).measurableSet]
  have hfill := stoppedFrom_block_fill_sharp B a H M hH hM
  have hsplit : (fun ω => blockGrow B ((a + H : ℕ) : ℤ) s ω M) ⁻¹'
      (blockStageHit B M H (a + H) s)ᶜ ⊆
      {ω | ¬ R B ((a + H : ℕ) : ℝ) ⊆
          stoppedFrom B ((a + H : ℕ) : ℤ) (R B (a : ℝ)) ω M} ∪
        {ω | ¬ (R B ((a + H : ℕ) : ℝ) ⊆ resumeSeed B (blockGrow B ((a + H : ℕ) : ℤ) s ω M).1 →
          resumeSeed B (blockGrow B ((a + H : ℕ) : ℤ) s ω M).1 = R B ((a + H : ℕ) : ℝ) ∧
          ∀ k : ℤ, mobileOnLayer B (blockGrow B ((a + H : ℕ) : ℤ) s ω M).2 k =
            mobileOnLayer B s.2 k + if k = ((a + H : ℕ) : ℤ) then M - B.card * H else 0)} := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_compl_iff, blockStageHit, Set.mem_setOf_eq] at hω
    by_cases hR : R B ((a + H : ℕ) : ℝ) ⊆ resumeSeed B (blockGrow B ((a + H : ℕ) : ℤ) s ω M).1
    · exact Or.inr (fun hP => hω (hP hR))
    · left
      show ¬ R B ((a + H : ℕ) : ℝ) ⊆ stoppedFrom B ((a + H : ℕ) : ℤ) (R B (a : ℝ)) ω M
      rw [← hs, ← resumeSeed_blockGrow_eq_stoppedFrom]
      exact hR
  refine le_trans (measure_mono hsplit) ?_
  refine le_trans (measure_union_le _ _) ?_
  rw [ae_iff.mp hG', add_zero]
  exact hfill

/-- A block batch from the rectangle `R_a` fails to fill `R_{a+H}` with probability at most
`N H e^{-H/4}`, for any batch size `M ≥ 2 N H`. -/
theorem blockBatch_fail_le_sharp (B : Base) (a H : ℕ) (hH : 1 ≤ H) (F : ResumeFinite B)
    (L : List (Site B)) (hF : resumeSeed B F = R B (a : ℝ)) (M : ℕ) (hM : 2 * B.card * H ≤ M) :
    blockBatch B ((a + H : ℕ) : ℤ) M (F, L) {s | ¬ R B ((a + H : ℕ) : ℝ) ⊆ resumeSeed B s.1} ≤
      ENNReal.ofReal ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4)) :=
  by
    refine le_trans (measure_mono ?_) (blockBatch_hit_fail_le_sharp B a H (a + H) hH rfl (F, L) hF M hM)
    intro t ht hit
    obtain ⟨hit1, -⟩ := hit
    simp only [Set.mem_setOf_eq] at ht
    exact ht (le_of_eq hit1.symm)

/-- **One block stage with its exact ledger, with the sharper exponent.** From a state whose seed
is the rectangle `R_{jH}`, the `n` block stages reach the ledger `blockStageGood`, except with
probability at most `n N H e^{-H/4}`. -/
theorem blockPause_stage_good_sharp (B : Base) (M H : ℕ) (hH : 1 ≤ H) (hM : 2 * B.card * H ≤ M)
    (n : ℕ) : ∀ (j : ℕ) (s : ResumeState B) (ρ : ℕ),
      resumeSeed B s.1 = R B ((j * H : ℕ) : ℝ) →
      blockPause B M H n j s (M * n + ρ) (blockStageGood B M H n j s ρ)ᶜ ≤
        ENNReal.ofReal ((n : ℝ) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4))) := by
  induction n with
  | zero =>
      intro j s ρ hs
      have hnot : (s, M * 0 + ρ) ∉ (blockStageGood B M H 0 j s ρ)ᶜ := by
        intro h
        apply h
        refine ⟨?_, ?_, fun k => ?_⟩
        · simpa using hs
        · simp
        · have hnone : ¬ ∃ i : ℕ, 1 ≤ i ∧ i ≤ 0 ∧ k = (((j + i) * H : ℕ) : ℤ) := by
            rintro ⟨i, h1, h2, -⟩
            omega
          rw [if_neg hnone, add_zero]
      show Measure.dirac (s, M * 0 + ρ) (blockStageGood B M H 0 j s ρ)ᶜ ≤ _
      rw [Measure.dirac_apply' _ (Set.to_countable _).measurableSet,
        Set.indicator_of_notMem hnot]
      exact zero_le
  | succ n ih =>
      intro j s ρ hs
      have hremain : M * (n + 1) + ρ - M = M * n + ρ := by
        rw [Nat.mul_succ]
        omega
      have hcond : R B ((j * H : ℕ) : ℝ) ⊆ resumeSeed B s.1 := by rw [hs]
      rw [blockPause, if_pos hcond, hremain]
      have hc : (j + 1) * H = j * H + H := by ring
      have hbatch := blockBatch_hit_fail_le_sharp B (j * H) H ((j + 1) * H) hH hc s hs M hM
      have hgood : ∀ t ∈ blockStageHit B M H ((j + 1) * H) s,
          blockPause B M H n (j + 1) t (M * n + ρ) (blockStageGood B M H (n + 1) j s ρ)ᶜ ≤
            ENNReal.ofReal ((n : ℝ) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4))) := by
        intro t ht
        have h := ih (j + 1) t ρ ht.1
        refine le_trans (measure_mono (Set.compl_subset_compl.mpr ?_)) h
        rintro u ⟨hu1, hu2, hu3⟩
        refine ⟨?_, hu2, fun k => ?_⟩
        · rw [show j + (n + 1) = j + 1 + n by omega]
          exact hu1
        · rw [stage_indicator_split B M H j n hH k, hu3 k, ht.2 k]
          ring
      have hfail := bind_failure_le (blockBatch B (((j + 1) * H : ℕ) : ℤ) M s)
        (fun t => blockPause B M H n (j + 1) t (M * n + ρ))
        (blockStageHit B M H ((j + 1) * H) s) (blockStageGood B M H (n + 1) j s ρ)ᶜ
        (Set.to_countable _).measurableSet (Set.to_countable _).measurableSet _ hgood
      refine le_trans hfail ?_
      refine le_trans (add_le_add hbatch le_rfl) (le_of_eq ?_)
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      push_cast
      ring

/-- **The paused block exploration fails the good ledger with at most `ℓ N H e^{-H/4}`**, with the
sharper exponent. -/
theorem blockPause_good_sharp (B : Base) (M H ℓ ρ : ℕ) (hH : 1 ≤ H) (hM : M = 2 * B.card * H) :
    blockPause B M H ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ) (goodBlockPaused B M H ℓ ρ)ᶜ ≤
      ENNReal.ofReal ((ℓ : ℝ) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4))) := by
  have hstage := blockPause_stage_good_sharp B M H hH (le_of_eq hM.symm) ℓ 0 (resumeEmpty B, []) ρ
    (by simp [resumeSeed_empty])
  have hsub : blockStageGood B M H ℓ 0 (resumeEmpty B, []) ρ ⊆ goodBlockPaused B M H ℓ ρ := by
    rintro t ⟨h1, h2, h3⟩
    refine ⟨by rw [Nat.zero_add] at h1; exact h1, h2, fun k => ?_⟩
    have h := h3 k
    simp only [mobileOnLayer, List.filter_nil, List.length_nil, zero_add] at h ⊢
    exact h
  exact le_trans (measure_mono (Set.compl_subset_compl.mpr hsub)) hstage

/-- **Canonical block filling, with the sharper exponent** (`tex:1194-1251`). Canonical additions
from the shifted empty seed, released on any layer `h ≤ L`, fill the rectangle of height `L + H`
except on an event of probability at most `N H e^{-H/4}`, once `2 N H ≤ n` additions have been
made. -/
theorem canonical_block_fill_sharp (L : ℕ) (h : ℤ) (hh : h ≤ L) (H : ℕ) (hH : 1 ≤ H) (n : ℕ)
    (hn : 2 * B.card * H ≤ n) :
    layerGrowthLaw B (shiftFinite B L (resumeEmpty B)) h n (filled B ((L : ℤ) + H))ᶜ ≤
      ENNReal.ofReal ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4)) := by
  have hF : R B ((L : ℤ) : ℝ) ⊆ resumeSeed B (shiftFinite B L (resumeEmpty B)) := by
    rw [resumeSeed_shiftFinite_empty, Int.cast_natCast]
  rw [below_layer_release_growth B (shiftFinite B L (resumeEmpty B)) h (L : ℤ) hh hF n,
    layerGrowthLaw_shiftFinite_filled_compl B L H n]
  refine (measure_mono_ae ?_).trans (stopped_block_fill_sharp_ge B H hH n hn)
  filter_upwards [idlaMeasure_ae_stopped_hyp B] with ω hω
  intro hnot hmem
  exact hnot (hmem.trans (stoppedCluster_subset_clusterTraj B (H : ℤ) ω hω.2.2.2 n))

end IdlaCyl.Reduction
