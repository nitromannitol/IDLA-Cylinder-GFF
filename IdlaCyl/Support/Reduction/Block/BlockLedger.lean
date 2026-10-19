/-
Ledger of the paused block exploration: the seed identity, the block failure bound, and the
successful state with its deep and shallow queues.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396,1440-1453 (as in PausedLedger.lean).
-/
import IdlaCyl.Support.Reduction.Block.BlockBatchLaw
import IdlaCyl.Support.Reduction.Block.BlockStopped
import IdlaCyl.Support.Reduction.Block.BlockFill
import IdlaCyl.Support.Reduction.Block.BlockPause
import IdlaCyl.Support.Reduction.QueueSplit
import IdlaCyl.Support.Outer.QueueDomination

/-!
The block exploration of `H` layers per stage, each stage a batch of `M = 2 N H` stopped
releases, is tracked by an exact ledger on its successful paths.

The file proves four things. First, the seed of a pathwise block growth is the stopped cluster
from the starting rectangle, so the block batch inherits the flat stopped fill bound. Second,
a batch that starts from the rectangle `R_a` fills `R_{a+H}` and records exactly `M - N H`
copies on that layer, except with probability at most `N H e^{-H/8}`. Third, the successful
state after `ℓ` block stages is the rectangle `R_{ℓH}` with `M - N H` mobile copies on each of
the layers `H, 2H, ..., ℓH`, and nothing else, and the failure probability of the whole paused
exploration is at most `ℓ N H e^{-H/8}`. Fourth, the copies split at the deep cutoff `(ℓ - 1) H`
into exactly `N H (ℓ - 1)` deep copies and `N H` shallow copies, and completing the two groups in
order gives the completion law of the unsplit queue.
-/

attribute [local instance] Classical.propDecidable

namespace IdlaCyl.Reduction

open MeasureTheory

/-- The seed of a pathwise block growth is the stopped growth from the initial seed. -/
theorem resumeSeed_blockGrow_eq_stoppedFrom (B : Base) (h : ℤ) (s : ResumeState B)
    (ω : TrajSeq B) (n : ℕ) :
    resumeSeed B (blockGrow B h s ω n).1 = stoppedFrom B h (resumeSeed B s.1) ω n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [blockGrow_succ_seed, stoppedFrom, ih]

/-- The successful block ledger: the seed is the rectangle `R_{ℓH}`, the phase is `ρ`, and the
queue has `M - N H` copies on each layer `jH` with `1 ≤ j ≤ ℓ`, and no copies elsewhere. -/
def goodBlockPaused (B : Base) (M H ℓ ρ : ℕ) : Set (ResumeState B × ℕ) :=
  {s | resumeSeed B s.1.1 = R B ((ℓ * H : ℕ) : ℝ) ∧ s.2 = ρ ∧
    ∀ k : ℤ, mobileOnLayer B s.1.2 k =
      if ∃ j : ℕ, 1 ≤ j ∧ j ≤ ℓ ∧ k = ((j * H : ℕ) : ℤ) then M - B.card * H else 0}

/-- The ledger after `n` block stages from block `j`, starting at the state `s`: the seed is the
rectangle `R_{(j+n)H}`, the phase is `ρ`, and the queue gained `M - N H` copies on each layer
`(j+i)H` with `1 ≤ i ≤ n`, beyond the queue of `s`. -/
def blockStageGood (B : Base) (M H n j : ℕ) (s : ResumeState B) (ρ : ℕ) :
    Set (ResumeState B × ℕ) :=
  {t | resumeSeed B t.1.1 = R B (((j + n) * H : ℕ) : ℝ) ∧ t.2 = ρ ∧
    ∀ k : ℤ, mobileOnLayer B t.1.2 k = mobileOnLayer B s.2 k +
      if ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ k = (((j + i) * H : ℕ) : ℤ) then M - B.card * H else 0}

/-- The one-batch hit set: the seed is the rectangle `R_c` and the queue gained `M - N H` copies
on layer `c`, relative to the queue of `s`. -/
def blockStageHit (B : Base) (M H c : ℕ) (s : ResumeState B) : Set (ResumeState B) :=
  {t | resumeSeed B t.1 = R B ((c : ℕ) : ℝ) ∧
    ∀ k : ℤ, mobileOnLayer B t.2 k = mobileOnLayer B s.2 k +
      if k = ((c : ℕ) : ℤ) then M - B.card * H else 0}

/-- Almost surely, a pathwise block growth that ends in the rectangle `R_h` has the queue count of
a block batch: it gains `M - N H` copies on layer `h` and none elsewhere. -/
theorem blockGrow_count_ae (B : Base) (a H : ℕ) (hH : 1 ≤ H) (h : ℤ) (hh : h = (a : ℤ) + H)
    (s : ResumeState B) (hs : resumeSeed B s.1 = R B (a : ℝ)) (M : ℕ) :
    ∀ᵐ ω ∂idlaMeasure B, R B (h : ℝ) ⊆ resumeSeed B (blockGrow B h s ω M).1 →
      resumeSeed B (blockGrow B h s ω M).1 = R B (h : ℝ) ∧
        ∀ k : ℤ, mobileOnLayer B (blockGrow B h s ω M).2 k =
          mobileOnLayer B s.2 k + if k = h then M - B.card * H else 0 := by
  have ha : (a : ℤ) < h := by omega
  have hae : ∀ᵐ ω ∂idlaMeasure B, ∀ i, CylAdmissible B (ω i) ∧ ω i 0 ∈ R B 0 ∧
      exitTime' B (resumeSeed B (blockGrow B h s ω i).1 ∩ R B ((h : ℝ) - 1)) (ω i) ≠ ⊤ := by
    filter_upwards [idlaMeasure_ae_admissible B, idlaMeasure_ae_start_mem B,
      idlaMeasure_ae_coord_hits_all B] with ω hadm hst hcoord i
    refine ⟨hadm i, hst i, ?_⟩
    obtain ⟨m, hm⟩ := hcoord i h
    exact exitTime'_ne_top_of_height B Set.inter_subset_right hm.ge
  filter_upwards [hae] with ω hω hsup
  have hend : resumeSeed B (blockGrow B h s ω M).1 = R B (h : ℝ) :=
    Set.Subset.antisymm (blockGrow_queue_at_height B a h ha s hs ω M (fun i _ => (hω i).1)
      (fun i _ => (hω i).2.1) (fun i _ => (hω i).2.2)).1 hsup
  refine ⟨hend, fun k => ?_⟩
  exact blockGrow_queue_layer_count B a H hH h hh s hs ω M (fun i _ => (hω i).1)
    (fun i _ => (hω i).2.1) (fun i _ => (hω i).2.2) hend k

/-- A block batch from the rectangle `R_a` misses its hit set with probability at most
`N H e^{-H/8}`, for any batch size `M ≥ 2 N H`. -/
theorem blockBatch_hit_fail_le (B : Base) (a H c : ℕ) (hH : 1 ≤ H) (hc : c = a + H)
    (s : ResumeState B) (hs : resumeSeed B s.1 = R B (a : ℝ)) (M : ℕ) (hM : 2 * B.card * H ≤ M) :
    blockBatch B (c : ℤ) M s (blockStageHit B M H c s)ᶜ ≤
      ENNReal.ofReal ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8)) := by
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
  have hfill := stoppedFrom_block_fill B a H M hH hM
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
`N H e^{-H/8}`, for any batch size `M ≥ 2 N H`. -/
theorem blockBatch_fail_le (B : Base) (a H : ℕ) (hH : 1 ≤ H) (F : ResumeFinite B)
    (L : List (Site B)) (hF : resumeSeed B F = R B (a : ℝ)) (M : ℕ) (hM : 2 * B.card * H ≤ M) :
    blockBatch B ((a + H : ℕ) : ℤ) M (F, L) {s | ¬ R B ((a + H : ℕ) : ℝ) ⊆ resumeSeed B s.1} ≤
      ENNReal.ofReal ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8)) :=
  by
    refine le_trans (measure_mono ?_) (blockBatch_hit_fail_le B a H (a + H) hH rfl (F, L) hF M hM)
    intro t ht hit
    obtain ⟨hit1, -⟩ := hit
    simp only [Set.mem_setOf_eq] at ht
    exact ht (le_of_eq hit1.symm)

/-- Splitting the stage indicator at its first layer `(j+1)H`: the indicator over `n + 1` stages
is the first-layer indicator plus the indicator over the remaining `n` stages. -/
theorem stage_indicator_split (B : Base) (M H j n : ℕ) (hH : 1 ≤ H) (k : ℤ) :
    (if ∃ i : ℕ, 1 ≤ i ∧ i ≤ n + 1 ∧ k = (((j + i) * H : ℕ) : ℤ) then M - B.card * H else 0) =
      (if k = (((j + 1) * H : ℕ) : ℤ) then M - B.card * H else 0) +
      (if ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ k = (((j + 1 + i) * H : ℕ) : ℤ) then M - B.card * H
        else 0) := by
  by_cases hQ : k = (((j + 1) * H : ℕ) : ℤ)
  · have hR : ¬ ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ k = (((j + 1 + i) * H : ℕ) : ℤ) := by
      rintro ⟨i, hi1, -, hk⟩
      have hlt : (j + 1) * H < (j + 1 + i) * H := by nlinarith
      have heq : (j + 1) * H = (j + 1 + i) * H := by exact_mod_cast hQ.symm.trans hk
      exact absurd heq (ne_of_lt hlt)
    have hP : ∃ i : ℕ, 1 ≤ i ∧ i ≤ n + 1 ∧ k = (((j + i) * H : ℕ) : ℤ) :=
      ⟨1, le_rfl, by omega, hQ⟩
    rw [if_pos hP, if_pos hQ, if_neg hR, add_zero]
  · by_cases hR : ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ k = (((j + 1 + i) * H : ℕ) : ℤ)
    · obtain ⟨i, hi1, hin, hk⟩ := hR
      have hP : ∃ i : ℕ, 1 ≤ i ∧ i ≤ n + 1 ∧ k = (((j + i) * H : ℕ) : ℤ) :=
        ⟨i + 1, by omega, by omega, by rw [hk, show j + 1 + i = j + (i + 1) by omega]⟩
      rw [if_pos hP, if_neg hQ, if_pos ⟨i, hi1, hin, hk⟩, zero_add]
    · have hP : ¬ ∃ i : ℕ, 1 ≤ i ∧ i ≤ n + 1 ∧ k = (((j + i) * H : ℕ) : ℤ) := by
        rintro ⟨i, hi1, hin, hk⟩
        rcases Nat.lt_or_ge i 2 with h2 | h2
        · obtain rfl : i = 1 := by omega
          exact hQ hk
        · exact hR ⟨i - 1, by omega, by omega,
            by rw [hk, show j + i = j + 1 + (i - 1) by omega]⟩
      rw [if_neg hP, if_neg hQ, if_neg hR]

/-- **One block stage with its exact ledger.** From a state whose seed is the rectangle `R_{jH}`,
the `n` block stages reach the ledger `blockStageGood`, except with probability at most
`n N H e^{-H/8}`. -/
theorem blockPause_stage_good (B : Base) (M H : ℕ) (hH : 1 ≤ H) (hM : 2 * B.card * H ≤ M)
    (n : ℕ) : ∀ (j : ℕ) (s : ResumeState B) (ρ : ℕ),
      resumeSeed B s.1 = R B ((j * H : ℕ) : ℝ) →
      blockPause B M H n j s (M * n + ρ) (blockStageGood B M H n j s ρ)ᶜ ≤
        ENNReal.ofReal ((n : ℝ) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8))) := by
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
      have hbatch := blockBatch_hit_fail_le B (j * H) H ((j + 1) * H) hH hc s hs M hM
      have hgood : ∀ t ∈ blockStageHit B M H ((j + 1) * H) s,
          blockPause B M H n (j + 1) t (M * n + ρ) (blockStageGood B M H (n + 1) j s ρ)ᶜ ≤
            ENNReal.ofReal ((n : ℝ) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8))) := by
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

/-- **The paused block exploration fails the good ledger with at most `ℓ N H e^{-H/8}`.** -/
theorem blockPause_good (B : Base) (M H ℓ ρ : ℕ) (hH : 1 ≤ H) (hM : M = 2 * B.card * H) :
    blockPause B M H ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ) (goodBlockPaused B M H ℓ ρ)ᶜ ≤
      ENNReal.ofReal ((ℓ : ℝ) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8))) := by
  have hstage := blockPause_stage_good B M H hH (le_of_eq hM.symm) ℓ 0 (resumeEmpty B, []) ρ
    (by simp [resumeSeed_empty])
  have hsub : blockStageGood B M H ℓ 0 (resumeEmpty B, []) ρ ⊆ goodBlockPaused B M H ℓ ρ := by
    rintro t ⟨h1, h2, h3⟩
    refine ⟨by rw [Nat.zero_add] at h1; exact h1, h2, fun k => ?_⟩
    have h := h3 k
    simp only [mobileOnLayer, List.filter_nil, List.length_nil, zero_add] at h ⊢
    exact h
  exact le_trans (measure_mono (Set.compl_subset_compl.mpr hsub)) hstage

/-- The deep part of the queue: every copy at height at most `(ℓ - 1) H`, in its original order. -/
noncomputable def blockDeepQueue (B : Base) (H ℓ : ℕ) (s : ResumeState B × ℕ) : List (Site B) :=
  s.1.2.filter (fun z => z.2 ≤ (((ℓ - 1) * H : ℕ) : ℤ))

/-- The shallow part of the queue: every copy above height `(ℓ - 1) H`, in its original order. -/
noncomputable def blockShallowQueue (B : Base) (H ℓ : ℕ) (s : ResumeState B × ℕ) :
    List (Site B) :=
  s.1.2.filter (fun z => (((ℓ - 1) * H : ℕ) : ℤ) < z.2)

/-- Reordering the actual queue into its deep and shallow parts changes no completion law. -/
theorem finishUniform_block_split (B : Base) (H ℓ ρ : ℕ) (s : ResumeState B × ℕ)
    (hs : s.2 = ρ) :
    finishUniform B s.1 s.2 =
      (resumeRun B s.1.1 (blockDeepQueue B H ℓ s)).bind
        (fun C => (resumeRun B C (blockShallowQueue B H ℓ s)).bind
          (fun D => layerGrowthLaw B D 0 ρ)) := by
  have hp := (List.filter_append_perm
    (fun z : Site B => decide (z.2 ≤ (((ℓ - 1) * H : ℕ) : ℤ))) s.1.2).symm
  have hcompl : (fun z : Site B => !decide (z.2 ≤ (((ℓ - 1) * H : ℕ) : ℤ))) =
      (fun z => decide ((((ℓ - 1) * H : ℕ) : ℤ) < z.2)) := by
    funext z
    simp only [← decide_not, not_le]
  rw [hcompl] at hp
  unfold finishUniform
  rw [hs, outerRun_perm B hp s.1.1, resumeRun_append,
    Measure.bind_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
  rfl

/-- Every copy of a successful block ledger sits at height at most `ℓ H`. -/
theorem goodBlockPaused_queue_heights (B : Base) (M H ℓ ρ : ℕ) (s : ResumeState B × ℕ)
    (hs : s ∈ goodBlockPaused B M H ℓ ρ) (z : Site B) (hz : z ∈ s.1.2) :
    z.2 ≤ ((ℓ * H : ℕ) : ℤ) := by
  by_contra hbad
  have hnot : ¬ ∃ j : ℕ, 1 ≤ j ∧ j ≤ ℓ ∧ z.2 = ((j * H : ℕ) : ℤ) := by
    rintro ⟨j, -, hj, hk⟩
    apply hbad
    rw [hk]
    exact_mod_cast Nat.mul_le_mul_right H hj
  have hc := hs.2.2 z.2
  rw [if_neg hnot] at hc
  have hm : z ∈ s.1.2.filter (fun w => w.2 = z.2) := by
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨hz, True.intro⟩
  have hnil : s.1.2.filter (fun w => w.2 = z.2) = [] := List.length_eq_zero_iff.mp hc
  rw [hnil] at hm
  exact List.not_mem_nil hm

/-- Every deep copy sits at height at most `(ℓ - 1) H`. -/
theorem blockDeepQueue_heights (B : Base) (H ℓ : ℕ) (s : ResumeState B × ℕ) (z : Site B)
    (hz : z ∈ blockDeepQueue B H ℓ s) : z.2 ≤ (((ℓ - 1) * H : ℕ) : ℤ) :=
  of_decide_eq_true (List.mem_filter.mp hz).2

/-- Every shallow copy of a successful block ledger sits at height at most `ℓ H`. -/
theorem blockShallowQueue_heights (B : Base) (M H ℓ ρ : ℕ) (s : ResumeState B × ℕ)
    (hs : s ∈ goodBlockPaused B M H ℓ ρ) (z : Site B) (hz : z ∈ blockShallowQueue B H ℓ s) :
    z.2 ≤ ((ℓ * H : ℕ) : ℤ) :=
  goodBlockPaused_queue_heights B M H ℓ ρ s hs z (List.mem_filter.mp hz).1

/-- Every copy of a successful block ledger sits at height at least `1`. -/
theorem goodBlockPaused_queue_pos (B : Base) (M H ℓ ρ : ℕ) (hH : 1 ≤ H)
    (s : ResumeState B × ℕ) (hs : s ∈ goodBlockPaused B M H ℓ ρ) (z : Site B) (hz : z ∈ s.1.2) :
    1 ≤ z.2 := by
  by_contra hbad
  have hnot : ¬ ∃ j : ℕ, 1 ≤ j ∧ j ≤ ℓ ∧ z.2 = ((j * H : ℕ) : ℤ) := by
    rintro ⟨j, hj, -, hk⟩
    have hpos : 0 < j * H := Nat.mul_pos hj hH
    have : (0 : ℤ) < ((j * H : ℕ) : ℤ) := by exact_mod_cast hpos
    rw [← hk] at this
    omega
  have hc := hs.2.2 z.2
  rw [if_neg hnot] at hc
  have hm : z ∈ s.1.2.filter (fun w => w.2 = z.2) := by
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨hz, True.intro⟩
  have hnil : s.1.2.filter (fun w => w.2 = z.2) = [] := List.length_eq_zero_iff.mp hc
  rw [hnil] at hm
  exact List.not_mem_nil hm

/-- The mobile mass on the multiples `H, 2H, ..., mH` of a successful ledger, for `m ≤ ℓ`. -/
theorem goodBlockPaused_multiple_sum (B : Base) (M H ℓ ρ : ℕ) (hH : 1 ≤ H)
    (s : ResumeState B × ℕ) (hs : s ∈ goodBlockPaused B M H ℓ ρ) (m : ℕ) (hm : m ≤ ℓ) :
    ∑ k ∈ Finset.Icc (1 : ℤ) ((m * H : ℕ) : ℤ), mobileOnLayer B s.1.2 k = m * (M - B.card * H) := by
  have hpt : ∀ k ∈ Finset.Icc (1 : ℤ) ((m * H : ℕ) : ℤ), mobileOnLayer B s.1.2 k =
      if ∃ j : ℕ, 1 ≤ j ∧ j ≤ m ∧ k = ((j * H : ℕ) : ℤ) then M - B.card * H else 0 := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
    rw [hs.2.2 k]
    by_cases hP : ∃ j : ℕ, 1 ≤ j ∧ j ≤ m ∧ k = ((j * H : ℕ) : ℤ)
    · have hQ : ∃ j : ℕ, 1 ≤ j ∧ j ≤ ℓ ∧ k = ((j * H : ℕ) : ℤ) := by
        obtain ⟨j, h1, h2, h3⟩ := hP
        exact ⟨j, h1, le_trans h2 hm, h3⟩
      rw [if_pos hQ, if_pos hP]
    · have hQ : ¬ ∃ j : ℕ, 1 ≤ j ∧ j ≤ ℓ ∧ k = ((j * H : ℕ) : ℤ) := by
        rintro ⟨j, h1, h2, h3⟩
        apply hP
        refine ⟨j, h1, ?_, h3⟩
        have hle : ((j * H : ℕ) : ℤ) ≤ ((m * H : ℕ) : ℤ) := by
          rw [← h3]
          exact hk2
        have hle' : j * H ≤ m * H := by exact_mod_cast hle
        exact Nat.le_of_mul_le_mul_right hle' hH
      rw [if_neg hQ, if_neg hP]
  have hfilt : (Finset.Icc (1 : ℤ) ((m * H : ℕ) : ℤ)).filter
      (fun k => ∃ j : ℕ, 1 ≤ j ∧ j ≤ m ∧ k = ((j * H : ℕ) : ℤ)) =
      (Finset.Icc 1 m).image (fun j : ℕ => ((j * H : ℕ) : ℤ)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨-, j, hj1, hjm, rfl⟩
      exact ⟨j, ⟨hj1, hjm⟩, rfl⟩
    · rintro ⟨j, ⟨hj1, hjm⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, j, hj1, hjm, rfl⟩
      · have : 0 < j * H := Nat.mul_pos hj1 hH
        exact_mod_cast this
      · exact_mod_cast Nat.mul_le_mul_right H hjm
  have hinj : Function.Injective (fun j : ℕ => ((j * H : ℕ) : ℤ)) := by
    intro a b hab
    have hab' : ((a * H : ℕ) : ℤ) = ((b * H : ℕ) : ℤ) := hab
    have h1 : a * H = b * H := by exact_mod_cast hab'
    exact Nat.eq_of_mul_eq_mul_right hH h1
  rw [Finset.sum_congr rfl hpt, Finset.sum_ite, Finset.sum_const_zero, add_zero,
    Finset.sum_const, smul_eq_mul, hfilt, Finset.card_image_of_injective _ hinj, Nat.card_Icc]
  simp

/-- The deep copies of a successful ledger number `N H (ℓ - 1)` up to the common mass `M - N H`. -/
theorem goodBlockPaused_deep_length (B : Base) (M H ℓ ρ : ℕ) (hH : 1 ≤ H)
    (s : ResumeState B × ℕ) (hs : s ∈ goodBlockPaused B M H ℓ ρ) :
    (blockDeepQueue B H ℓ s).length = (ℓ - 1) * (M - B.card * H) := by
  have hdeep : blockDeepQueue B H ℓ s =
      s.1.2.filter (fun z => 1 ≤ z.2 ∧ z.2 ≤ (((ℓ - 1) * H : ℕ) : ℤ)) := by
    unfold blockDeepQueue
    apply List.filter_congr
    intro z hz
    simp only [decide_eq_decide]
    exact ⟨fun h => ⟨goodBlockPaused_queue_pos B M H ℓ ρ hH s hs z hz, h⟩, fun h => h.2⟩
  rw [hdeep, queue_interval_count, goodBlockPaused_multiple_sum B M H ℓ ρ hH s hs (ℓ - 1)
    (Nat.sub_le ℓ 1)]

/-- The deep and shallow parts of the queue together contain every copy, once. -/
theorem blockQueue_split_perm (B : Base) (H ℓ : ℕ) (s : ResumeState B × ℕ) :
    s.1.2.Perm (blockDeepQueue B H ℓ s ++ blockShallowQueue B H ℓ s) := by
  have hp := (List.filter_append_perm
    (fun z : Site B => decide (z.2 ≤ (((ℓ - 1) * H : ℕ) : ℤ))) s.1.2).symm
  have hcompl : (fun z : Site B => !decide (z.2 ≤ (((ℓ - 1) * H : ℕ) : ℤ))) =
      (fun z => decide ((((ℓ - 1) * H : ℕ) : ℤ) < z.2)) := by
    funext z
    simp only [← decide_not, not_le]
  rw [hcompl] at hp
  exact hp

/-- The shallow copies of a successful ledger number `M - N H`. -/
theorem goodBlockPaused_shallow_length (B : Base) (M H ℓ ρ : ℕ) (hH : 1 ≤ H) (hℓ : 1 ≤ ℓ)
    (s : ResumeState B × ℕ) (hs : s ∈ goodBlockPaused B M H ℓ ρ) :
    (blockShallowQueue B H ℓ s).length = M - B.card * H := by
  have hfilt : s.1.2.filter (fun z => 1 ≤ z.2 ∧ z.2 ≤ ((ℓ * H : ℕ) : ℤ)) = s.1.2 := by
    apply List.filter_eq_self.mpr
    intro z hz
    exact decide_eq_true ⟨goodBlockPaused_queue_pos B M H ℓ ρ hH s hs z hz,
      goodBlockPaused_queue_heights B M H ℓ ρ s hs z hz⟩
  have htot : s.1.2.length = ℓ * (M - B.card * H) := by
    have h := queue_interval_count B s.1.2 1 ((ℓ * H : ℕ) : ℤ)
    rw [hfilt, goodBlockPaused_multiple_sum B M H ℓ ρ hH s hs ℓ le_rfl] at h
    exact h
  have hlen := (blockQueue_split_perm B H ℓ s).length_eq
  rw [List.length_append, htot, goodBlockPaused_deep_length B M H ℓ ρ hH s hs] at hlen
  obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hlen
  rw [Nat.add_mul, one_mul] at hlen
  omega

/-- **The block queue lengths of a successful ledger**, with `M = 2 N H`. -/
theorem goodBlockPaused_block_lengths (B : Base) (M H ℓ ρ : ℕ) (hH : 1 ≤ H) (hℓ : 1 ≤ ℓ)
    (hM : M = 2 * B.card * H) (s : ResumeState B × ℕ) (hs : s ∈ goodBlockPaused B M H ℓ ρ) :
    (blockDeepQueue B H ℓ s).length = B.card * H * (ℓ - 1) ∧
      (blockShallowQueue B H ℓ s).length = B.card * H := by
  have hc : M - B.card * H = B.card * H := by
    rw [hM, show 2 * B.card * H = B.card * H + B.card * H by ring, Nat.add_sub_cancel]
  refine ⟨?_, ?_⟩
  · rw [goodBlockPaused_deep_length B M H ℓ ρ hH s hs, hc]
    ring
  · rw [goodBlockPaused_shallow_length B M H ℓ ρ hH hℓ s hs, hc]

end IdlaCyl.Reduction
