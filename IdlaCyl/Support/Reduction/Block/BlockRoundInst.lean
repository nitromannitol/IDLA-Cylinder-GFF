module

public import IdlaCyl.Support.Reduction.Block.BlockRound
public import IdlaCyl.Support.Reduction.Block.BlockLedger
public import IdlaCyl.Support.Reduction.Block.BlockAssemble
public import IdlaCyl.External.Discharge.Silvestri

@[expose] public section

/-!
# One round of the block reduction, from Silvestri's Proposition 2

`block_round` is the round used by the assembly (`Block/BlockAssemble.lean`): from time `t ≥ 3M`, with
`M = 2NH` and `ℓ = t / M`, the flat cluster at time `t` is coupled with the flat cluster at time
`t - NHℓ` shifted up by `Hℓ`. It applies `block_round_of_ledger` to the block pause of
`Block/BlockPause.lean` and its ledger (`Block/BlockLedger.lean`). With it, `block_pr_reduction`
proves the printed `pr:reduction` and `block_pr_reduction_alpha` the finite-coefficient form.
-/

namespace IdlaCyl.Reduction

open MeasureTheory

/-- One round of the block reduction (`M = 2NH` particles per block, `ℓ = t / M` blocks), from
Silvestri's Proposition 2: the error is the probability that some block fails to fill, plus the
buffer failure, plus the two comparisons. -/
theorem block_round (hsil : External.silvestri_prop2) (r : ℕ) (p : ℝ) (hp : 0 < p) :
    ∃ b : ℝ, 1 ≤ b ∧ ∃ N₀ : ℕ, ∀ B : Base,
      N₀ ≤ B.card → ∀ H t : ℕ, 1 ≤ H →
      b * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ) ≤ (H : ℝ) →
      0 < t → t ≤ B.card ^ r → 3 * (2 * (B.card * H)) ≤ t →
      ClusterCoupling B (flatClusterLaw B t)
        (flatClusterLaw B (t - B.card * H * (t / (2 * (B.card * H)))))
        (H * (t / (2 * (B.card * H))))
        ((((t / (2 * (B.card * H)) : ℕ) : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8))
          + 2 * (B.card : ℝ) ^ (-p)) := by
  obtain ⟨b, hb, N₀, hc⟩ := block_round_of_ledger hsil r p hp
  refine ⟨b, hb, N₀, ?_⟩
  intro B hN H t hH hbH _ htr h3
  obtain ⟨M, hMdef⟩ : ∃ M, M = 2 * (B.card * H) := ⟨_, rfl⟩
  rw [← hMdef] at h3 ⊢
  have hM : M = 2 * B.card * H := by rw [hMdef]; ring
  have hMpos : 0 < M := by
    have : 0 < B.card := lt_of_lt_of_le (by decide) B.nontrivial
    rw [hMdef]; positivity
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
  have hgood := blockPause_good B M H ℓ ρ hH hM
  have hεA : 0 ≤ (ℓ : ℝ) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8)) := by positivity
  have hround := hc B hN H ℓ ρ t (blockPause B M H ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ))
    (goodBlockPaused B M H ℓ ρ) (blockDeepQueue B H ℓ) (blockShallowQueue B H ℓ)
    ((ℓ : ℝ) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8))) hεA hH hbH hℓ3 ht htr hfin hgood
    (fun s hs => ⟨hs.1, hs.2.1,
      (goodBlockPaused_block_lengths B M H ℓ ρ hH hℓ1 hM s hs).1,
      blockDeepQueue_heights B H ℓ s,
      (goodBlockPaused_block_lengths B M H ℓ ρ hH hℓ1 hM s hs).2,
      blockShallowQueue_heights B M H ℓ ρ s hs,
      finishUniform_block_split B H ℓ ρ s hs.2.1⟩)
  have herr : (ℓ : ℝ) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8)) +
        (B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8) + 2 * (B.card : ℝ) ^ (-p) =
      ((ℓ : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8)) + 2 * (B.card : ℝ) ^ (-p) := by
    ring
  rw [herr] at hround
  exact hround

/-- **The printed `pr:reduction`** (`tex:1446-1449`), with a cutoff uniform over the bases: from
Silvestri's Proposition 2, proved in `External/Discharge/Silvestri.lean`. -/
theorem block_pr_reduction (ν : ℝ) (hν : 0 < ν) (m : ℝ) (hm : 1 ≤ m) :
    ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card → ∀ T : ℕ,
      Defs.sharp B ≤ (T : ℝ) → (T : ℝ) ≤ (B.card : ℝ) ^ m →
      ∃ T' k : ℕ,
        1 ≤ T' ∧ (T' : ℝ) ≤ Defs.sharp B ∧ T' + B.card * k = T ∧
        ∃ μ : Measure (TrajSeq B × TrajSeq B),
          μ.map (Prod.fst : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
          μ.map (Prod.snd : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
          ENNReal.ofReal (1 - (B.card : ℝ) ^ (-(ν + 1))) ≤
            μ {p | clusterTraj B p.1 T =
              Reduction.shiftCluster B k (clusterTraj B p.2 T')} :=
  pr_reduction_of_round (block_round External.silvestri_prop2_proved) ν hν m hm

/-- The finite-coefficient reduction `pr_reduction_alpha`, here with coefficient `1`. -/
theorem block_pr_reduction_alpha : IdlaCyl.pr_reduction_alpha :=
  pr_reduction_alpha_of_round (block_round External.silvestri_prop2_proved)

end IdlaCyl.Reduction
