module

public import IdlaCyl.Support.Reduction.Block.BlockRoundGen
public import IdlaCyl.Support.Reduction.Block.BlockLedger
public import IdlaCyl.Support.Reduction.Block.BlockSharp
public import IdlaCyl.Support.Reduction.Block.ExplicitUniform

@[expose] public section

/-!
# One round of the quantitative block reduction

`quant_round` is one round of the block reduction with explicit constants: from time `t ≥ 3M`, with
`M = 2NH` and `ℓ = t / M`, the flat cluster at time `t` is coupled with the flat cluster at time
`t - NHℓ` shifted up by `Hℓ`, except with probability at most
`(ℓ + 1) N H e^{-H/4} + 2 t √N e^{-H/√τ_rel}`. It applies `block_round_of_ledger_gen` to the
block pause, with the sharp block bounds (`Block/BlockSharp.lean`) and the explicit comparisons
of two release lists (`Block/ExplicitUniform.lean`) in place of Silvestri's Proposition 2. There
is no size cutoff and no lower bound on `H` beyond `H ≥ 1`.
-/

namespace IdlaCyl.Reduction

open MeasureTheory

/-- One round of the quantitative block reduction (`M = 2NH` particles per block, `ℓ = t / M`
blocks): the error is the probability that some block or the buffer fails to fill, plus the two
explicit comparisons, each at most `t η` with `η = √N e^{-H/√τ_rel}`. -/
theorem quant_round (B : Base) (S : SpectralData B) (H t : ℕ) (hH : 1 ≤ H)
    (h3 : 3 * (2 * (B.card * H)) ≤ t) :
    ClusterCoupling B (flatClusterLaw B t)
      (flatClusterLaw B (t - B.card * H * (t / (2 * (B.card * H)))))
      (H * (t / (2 * (B.card * H))))
      ((((t / (2 * (B.card * H)) : ℕ) : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4))
        + 2 * ((t : ℝ) * explicitEta B S H)) := by
  classical
  obtain ⟨M, hMdef⟩ : ∃ M, M = 2 * (B.card * H) := ⟨_, rfl⟩
  rw [← hMdef] at h3 ⊢
  have hM : M = 2 * B.card * H := by rw [hMdef]; ring
  have hNpos : 0 < B.card := lt_of_lt_of_le (by decide) B.nontrivial
  have hHpos : 0 < H := hH
  have hMpos : 0 < M := by rw [hMdef]; positivity
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = t / M := ⟨_, rfl⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = t % M := ⟨_, rfl⟩
  rw [← hℓ]
  have hℓ3 : 3 ≤ ℓ := by
    rw [hℓ]
    exact (Nat.le_div_iff_mul_le hMpos).mpr (by linarith)
  have hℓ1 : 1 ≤ ℓ := le_trans (by decide) hℓ3
  have htime : M * ℓ + ρ = t := by
    rw [hℓ, hρ]
    exact Nat.div_add_mod t M
  have ht : t = 2 * B.card * H * ℓ + ρ := by rw [← htime, hM]
  have hfin : (blockPause B M H ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ)).bind
      (fun s => finishUniform B s.1 s.2) = flatClusterLaw B t := by
    rw [blockPause_finish, htime]
  have hgood := blockPause_good_sharp B M H ℓ ρ hH hM
  have hf0 : 0 ≤ (B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4) := by positivity
  have hη0 : 0 ≤ explicitEta B S H := explicitEta_nonneg B S H
  -- the counts of the two comparisons
  have hP : 2 * B.card * H * ℓ = 2 * (B.card * H * ℓ) := by ring
  have hQ : B.card * H * ℓ = B.card * H * (ℓ - 1) + B.card * H := by
    have hℓ' : ℓ = (ℓ - 1) + 1 := by omega
    calc B.card * H * ℓ = B.card * H * ((ℓ - 1) + 1) := by rw [← hℓ']
      _ = _ := by ring
  have hsub : B.card * H * (ℓ - 1) + (B.card * H + ρ) ≤ t := by omega
  have hcount : ((B.card * H * (ℓ - 1) : ℕ) : ℝ) + ((B.card * H + ρ : ℕ) : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hsub
  -- the buffer
  have hfillset : filled B (((ℓ * H : ℕ) : ℤ) + (H : ℤ)) = filled B (((ℓ + 1) * H : ℕ) : ℤ) := by
    congr 1
    push_cast
    ring
  have hn : 2 * B.card * H ≤ B.card * H * (ℓ - 1) := by
    have h2 : 2 ≤ ℓ - 1 := by omega
    calc 2 * B.card * H = B.card * H * 2 := by ring
      _ ≤ B.card * H * (ℓ - 1) := Nat.mul_le_mul (le_refl _) h2
  have hbuf : layerGrowthLaw B (shiftFinite B (ℓ * H) (resumeEmpty B)) ((ℓ * H : ℕ) : ℤ)
      (B.card * H * (ℓ - 1)) (filled B (((ℓ + 1) * H : ℕ) : ℤ))ᶜ ≤
      ENNReal.ofReal ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4)) := by
    rw [← hfillset]
    exact canonical_block_fill_sharp B (ℓ * H) ((ℓ * H : ℕ) : ℤ) le_rfl H hH
      (B.card * H * (ℓ - 1)) hn
  -- the two explicit comparisons
  have hdeepB : ∀ (F : ResumeFinite B) (L : List (Site B)),
      resumeSeed B F = R B ((ℓ * H : ℕ) : ℝ) →
      (∀ z ∈ L, z.2 ≤ (((ℓ - 1) * H : ℕ) : ℤ)) → L.length = B.card * H * (ℓ - 1) →
      ClusterCoupling B (resumeRun B F L)
        (layerGrowthLaw B (shiftFinite B (ℓ * H) (resumeEmpty B)) ((ℓ * H : ℕ) : ℤ) L.length)
        0 (((B.card * H * (ℓ - 1) : ℕ) : ℝ) * explicitEta B S H) := by
    intro F L hseed hst hlen
    have hc := block_deep_explicit B S H hH ℓ F L hℓ1 hseed hst
    rw [hlen] at hc ⊢
    exact hc
  have hshallowB : ∀ (c : ResumeFinite B) (L : List (Site B)),
      c ∈ filled B (((ℓ + 1) * H : ℕ) : ℤ) → SeedConnected B (resumeSeed B c) →
      (∀ z ∈ L, z.2 ≤ ((ℓ * H : ℕ) : ℤ)) → L.length = B.card * H →
      ClusterCoupling B ((resumeRun B c L).bind (fun C => layerGrowthLaw B C 0 ρ))
        (layerGrowthLaw B c ((ℓ * H : ℕ) : ℤ) (L.length + ρ)) 0
        (((B.card * H + ρ : ℕ) : ℝ) * explicitEta B S H) := by
    intro c L hc _ hst hlen
    have hc' := block_shallow_explicit B S H hH ℓ ρ c L hc hst
    rw [hlen] at hc' ⊢
    exact hc'
  have key := block_round_of_ledger_gen B H ℓ ρ t
    (blockPause B M H ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ))
    (goodBlockPaused B M H ℓ ρ) (blockDeepQueue B H ℓ) (blockShallowQueue B H ℓ)
    ((ℓ : ℝ) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4)))
    (((B.card * H * (ℓ - 1) : ℕ) : ℝ) * explicitEta B S H)
    (((B.card * H + ρ : ℕ) : ℝ) * explicitEta B S H)
    ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4))
    (by positivity) (by positivity) (by positivity) hf0 hdeepB hshallowB hbuf hℓ3 ht hfin hgood
    (fun s hs => ⟨hs.1, hs.2.1,
      (goodBlockPaused_block_lengths B M H ℓ ρ hH hℓ1 hM s hs).1,
      blockDeepQueue_heights B H ℓ s,
      (goodBlockPaused_block_lengths B M H ℓ ρ hH hℓ1 hM s hs).2,
      blockShallowQueue_heights B M H ℓ ρ s hs,
      finishUniform_block_split B H ℓ ρ s hs.2.1⟩)
  refine clusterCoupling_mono B _ _ _ _ _ ?_ key
  have hcomp : ((B.card * H * (ℓ - 1) : ℕ) : ℝ) * explicitEta B S H
      + ((B.card * H + ρ : ℕ) : ℝ) * explicitEta B S H ≤ (t : ℝ) * explicitEta B S H := by
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right hcount hη0
  have ht0 : 0 ≤ (t : ℝ) * explicitEta B S H := by positivity
  nlinarith

end IdlaCyl.Reduction
