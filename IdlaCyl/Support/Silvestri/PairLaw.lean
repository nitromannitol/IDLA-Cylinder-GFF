module

public import IdlaCyl.Support.Silvestri.BlockPair
public import IdlaCyl.Support.Silvestri.BlockResampleLaw
public import IdlaCyl.Support.Silvestri.LadderFail
public import IdlaCyl.Support.Silvestri.FromPairFamily

@[expose] public section

/-!
# The pair law of two walks and Silvestri's Proposition 2

The pair law `pairLaw B x x'` is the ladder law of `Ladder.lean` with the block couplings
`blockPair B`, `B.card` rounds, and the first level `ladderStep B`. The file proves the
following.

* Both marginals of the pair law are the walk laws from `x` and `x'`, when both starts lie at
  height at most `0` and the base has at least two vertices (`pairLaw_map_fst`,
  `pairLaw_map_snd`). The pair law is a probability measure under the same hypotheses
  (`pairLaw_isProbability`).
* For `6 ≤ B.card` and `K ≤ B.card`, the pathwise success event at the level
  `K · ladderStep B` fails with probability at most `holdFail B ^ K` (`pairLaw_fail_le`). This
  uses the one-round bound on the block ends as the hypothesis `hend`.
* Given `hend`, the pair law satisfies the hypotheses of `silvestri_prop2_of_pairFamily`, so
  `External.silvestri_prop2` holds (`silvestri_prop2_of_end_bound`).

The one-round bound `hend` is an input of the file. It is not proved here.
-/

namespace IdlaCyl.Silvestri

open MeasureTheory IdlaCyl.External
open scoped ENNReal

noncomputable section

variable (B : Base)

/-- The pair law of two walks started at `x` and `x'`: the ladder law with the block couplings
`blockPair B`, `B.card` rounds, and the first level `ladderStep B`. -/
def pairLaw (x x' : Site B) : Measure ((ℕ → Site B) × (ℕ → Site B)) :=
  ladderLaw B (blockPair B) (ladderStep B) B.card (ladderStep B) x x'

/-- The first marginal of the block pair is the block law of the first start, at every level
strictly above that start. -/
theorem blockPair_map_fst' (ℓ : ℤ) (p p' : Site B) (hp : p.2 < ℓ) :
    (blockPair B ℓ p p').map Prod.fst = blockLaw B ℓ p :=
  blockPair_map_fst B ℓ p p' (blockLaw_resample B ℓ p hp)

/-- The second marginal of the block pair is the block law of the second start, at every level
strictly above that start. -/
theorem blockPair_map_snd' (ℓ : ℤ) (p p' : Site B) (hp' : p'.2 < ℓ) :
    (blockPair B ℓ p p').map Prod.snd = blockLaw B ℓ p' :=
  blockPair_map_snd B ℓ p p' (blockLaw_resample B ℓ p' hp')

/-- The first-marginal hypothesis of the ladder law, for the block pair. -/
theorem blockPair_marginal_fst :
    ∀ (ℓ : ℤ) (p p' : Site B), p.2 < ℓ → p'.2 < ℓ →
      (blockPair B ℓ p p').map Prod.fst = blockLaw B ℓ p :=
  fun ℓ p p' hp _ => blockPair_map_fst' B ℓ p p' hp

/-- The second-marginal hypothesis of the ladder law, for the block pair. -/
theorem blockPair_marginal_snd :
    ∀ (ℓ : ℤ) (p p' : Site B), p.2 < ℓ → p'.2 < ℓ →
      (blockPair B ℓ p p').map Prod.snd = blockLaw B ℓ p' :=
  fun ℓ p p' _ hp' => blockPair_map_snd' B ℓ p p' hp'

/-- The pair law is a probability measure when both starts lie at height at most `0`. -/
theorem pairLaw_isProbability (hN : 2 ≤ B.card) (x x' : Site B) (hx : x.2 ≤ 0)
    (hx' : x'.2 ≤ 0) :
    IsProbabilityMeasure (pairLaw B x x') := by
  have hh : 0 < ladderStep B := ladderStep_pos B hN
  have hp : x.2 < (ladderStep B : ℤ) := by omega
  have hp' : x'.2 < (ladderStep B : ℤ) := by omega
  unfold pairLaw
  exact ⟨ladderLaw_univ B (Q := blockPair B) (blockPair_marginal_fst B)
    (blockPair_marginal_snd B) hh B.card (ladderStep B) x x' hp hp'⟩

/-- The first marginal of the pair law is the walk law from `x`, when both starts lie at height
at most `0` and the base has at least two vertices. -/
theorem pairLaw_map_fst (hN : 2 ≤ B.card) (x x' : Site B) (hx : x.2 ≤ 0) (hx' : x'.2 ≤ 0) :
    (pairLaw B x x').map Prod.fst = walkPathLaw B x := by
  have hh : 0 < ladderStep B := ladderStep_pos B hN
  have hp : x.2 < (ladderStep B : ℤ) := by omega
  have hp' : x'.2 < (ladderStep B : ℤ) := by omega
  unfold pairLaw
  exact ladderLaw_map_fst B (Q := blockPair B) (blockPair_marginal_fst B)
    (blockPair_marginal_snd B) hh B.card (ladderStep B) x x' hp hp'

/-- The second marginal of the pair law is the walk law from `x'`, when both starts lie at height
at most `0` and the base has at least two vertices. -/
theorem pairLaw_map_snd (hN : 2 ≤ B.card) (x x' : Site B) (hx : x.2 ≤ 0) (hx' : x'.2 ≤ 0) :
    (pairLaw B x x').map Prod.snd = walkPathLaw B x' := by
  have hh : 0 < ladderStep B := ladderStep_pos B hN
  have hp : x.2 < (ladderStep B : ℤ) := by omega
  have hp' : x'.2 < (ladderStep B : ℤ) := by omega
  unfold pairLaw
  exact ladderLaw_map_snd B (Q := blockPair B) (blockPair_marginal_fst B)
    (blockPair_marginal_snd B) hh B.card (ladderStep B) x x' hp hp'

/-- The failure bound of the pair law. Given the one-round bound `hend` on the block ends, for
`6 ≤ B.card` and `K ≤ B.card` the pathwise success event at the level `K · ladderStep B` fails
with probability at most `holdFail B ^ K`, for starts at height at most `0`. -/
theorem pairLaw_fail_le
    (hend : ∀ (B : Base), 2 ≤ B.card → ∀ (ℓ : ℤ) (p p' : Site B),
      (p.2 : ℝ) + ladderStep B ≤ ℓ → (p'.2 : ℝ) + ladderStep B ≤ ℓ →
        blockPair B ℓ p p' {cc | blockEnd B p cc.1 ≠ blockEnd B p' cc.2} ≤
          ENNReal.ofReal (holdFail B))
    (hN : 6 ≤ B.card) (K : ℕ) (hK : K ≤ B.card) (x x' : Site B) (hx : x.2 ≤ 0)
    (hx' : x'.2 ≤ 0) :
    pairLaw B x x' {pp | ¬ pairGood B ((K : ℝ) * ladderStep B) pp.1 pp.2} ≤
      ENNReal.ofReal (holdFail B ^ K) := by
  have hN2 : 2 ≤ B.card := by omega
  have hh : 0 < ladderStep B := ladderStep_pos B hN2
  have hp : (x.2 : ℝ) + (ladderStep B : ℝ) ≤ ((ladderStep B : ℤ) : ℝ) := by
    have hx0 : (x.2 : ℝ) ≤ 0 := by exact_mod_cast hx
    push_cast
    linarith
  have hp' : (x'.2 : ℝ) + (ladderStep B : ℝ) ≤ ((ladderStep B : ℤ) : ℝ) := by
    have hx0 : (x'.2 : ℝ) ≤ 0 := by exact_mod_cast hx'
    push_cast
    linarith
  have hQf : ∀ (ℓ : ℤ) (p p' : Site B), (p.2 : ℝ) + (ladderStep B : ℝ) ≤ ℓ →
      (p'.2 : ℝ) + (ladderStep B : ℝ) ≤ ℓ →
        blockPair B ℓ p p' {cc | blockEnd B p cc.1 ≠ blockEnd B p' cc.2} ≤
          ENNReal.ofReal (holdFail B) :=
    fun ℓ p p' h1 h2 => hend B hN2 ℓ p p' h1 h2
  have key := ladderLaw_notPairGood_le B (Q := blockPair B) (blockPair_marginal_fst B)
    (blockPair_marginal_snd B) hh (holdFail_nonneg B) hQf B.card K hK ((ladderStep B : ℤ))
    x x' hp hp'
  have hH : ((ladderStep B : ℤ) : ℝ) + ((K : ℝ) - 1) * (ladderStep B : ℝ) =
      (K : ℝ) * ladderStep B := by
    push_cast
    ring
  rw [hH] at key
  exact key

/-- Silvestri's Proposition 2 holds once the one-round bound `hend` on the block ends holds for
every base with at least two vertices. The pair family is the pair law `pairLaw`. -/
theorem silvestri_prop2_of_end_bound
    (hend : ∀ (B : Base), 2 ≤ B.card → ∀ (ℓ : ℤ) (p p' : Site B),
      (p.2 : ℝ) + ladderStep B ≤ ℓ → (p'.2 : ℝ) + ladderStep B ≤ ℓ →
        blockPair B ℓ p p' {cc | blockEnd B p cc.1 ≠ blockEnd B p' cc.2} ≤
          ENNReal.ofReal (holdFail B)) :
    External.silvestri_prop2 := by
  refine silvestri_prop2_of_pairFamily pairLaw ?_ ?_ ?_ ?_
  · intro B x x' hx hx'
    exact pairLaw_isProbability B B.nontrivial x x' hx hx'
  · intro B x x' hx hx'
    exact pairLaw_map_fst B B.nontrivial x x' hx hx'
  · intro B x x' hx hx'
    exact pairLaw_map_snd B B.nontrivial x x' hx hx'
  · intro B hN K hK x x' hx hx'
    exact pairLaw_fail_le B hend hN K hK x x' hx hx'

end

end IdlaCyl.Silvestri
