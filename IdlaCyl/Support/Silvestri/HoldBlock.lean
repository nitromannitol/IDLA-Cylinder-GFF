import IdlaCyl.Support.Silvestri.Blocks
import IdlaCyl.Support.Silvestri.BlockResample
import IdlaCyl.Support.Silvestri.HoldTail
import IdlaCyl.Support.Silvestri.Params

/-!
# The holding tail of the first block

The first block of the cylinder walk from `p` to level `ℓ` is the list of sites visited after
`p` up to the first arrival at height `ℓ`. Its number of horizontal steps `hcount` is the
number of steps of the walk before that arrival on which the height does not change, which is
the holding count of the walk (`hcount_firstBlock`).

Hence the probability that the block law of the walk from `p` gives a block with fewer than
`m` horizontal steps is the probability that the walk has holding count below `m`. The file
proves that this probability is at most `exp (-h ^ 2 / (4 m)) + exp (-m / 2)` whenever `p` lies
at distance at least `h ≥ 0` below `ℓ` (`blockLaw_hcount_lt`). At the ladder spacing and the
holding threshold of `Params`, the bound reads in the constants of `Params`
(`blockLaw_hcount_lt_ladder`).
-/

namespace IdlaCyl.Silvestri

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Prepending a site adds one horizontal step when its height is the height of the start. -/
theorem length_hors_cons {B : Base} (p q : Site B) (c : List (Site B)) :
    (hors p (q :: c)).length = (if q.2 = p.2 then 1 else 0) + (hors q c).length := by
  by_cases h : q.2 - p.2 = 0
  · have h' : q.2 = p.2 := by omega
    simp only [hors, if_pos h, if_pos h', List.length_cons]
    omega
  · have h' : ¬ q.2 = p.2 := by omega
    simp only [hors, if_neg h, if_neg h', zero_add]

/-- The horizontal steps of the first `n` entries `X 1, …, X n` of a path, read from a start
`p` at the height of `X 0`, are the indices `i < n` at which the height does not change. -/
theorem length_hors_ofFn {B : Base} (n : ℕ) : ∀ (X : ℕ → Site B) (p : Site B), p.2 = (X 0).2 →
    (hors p (List.ofFn fun i : Fin n => X ((i : ℕ) + 1))).length =
      ∑ i ∈ Finset.range n, if (X (i + 1)).2 = (X i).2 then 1 else 0 := by
  induction n with
  | zero => intro X p _; simp [hors]
  | succ n ih =>
    intro X p hp
    have ih' := ih (fun j => X (j + 1)) (X 1) rfl
    beta_reduce at ih'
    simp only [List.ofFn_succ, Fin.val_zero, Fin.val_succ, zero_add]
    rw [length_hors_cons, ih', Finset.sum_range_succ', hp]
    simp [add_comm]

/-- The holding count of the first block of a path is the holding count of the path: the
number of steps before the first exit from `below B ℓ` on which the height does not change. -/
theorem hcount_firstBlock (B : Base) (ℓ : ℤ) (p : Site B) (X : ℕ → Site B) (hX0 : X 0 = p) :
    hcount B p (firstBlock B ℓ X) = holdCount B ℓ X := by
  unfold hcount holdCount firstBlock below
  rw [length_hors_ofFn _ X p (by rw [hX0]), Finset.card_filter]

/-- The first block of the walk from `p` has fewer than `m` horizontal steps with probability
at most `exp (-h ^ 2 / (4 m)) + exp (-m / 2)`, when `p` lies at distance at least `h ≥ 0`
below level `ℓ` and `m ≥ 1`. -/
theorem blockLaw_hcount_lt (B : Base) (ℓ : ℤ) (p : Site B) (h : ℝ) (hh : 0 ≤ h)
    (hℓ : (p.2 : ℝ) + h ≤ ℓ) (m : ℕ) (hm : 0 < m) :
    blockLaw B ℓ p {c | hcount B p c < m} ≤
      ENNReal.ofReal (Real.exp (-h ^ 2 / (4 * m)) + Real.exp (-(m : ℝ) / 2)) := by
  unfold blockLaw
  rw [Measure.map_apply (measurable_firstBlock B ℓ) MeasurableSpace.measurableSet_top]
  refine le_trans (measure_mono_ae ?_) (walkPathLaw_holdCount_lt B ℓ p h hh hℓ m hm)
  filter_upwards [walkPathLaw_ae_start B p] with X hX0 hX
  have hX' : hcount B p (firstBlock B ℓ X) < m := hX
  rw [hcount_firstBlock B ℓ p X hX0] at hX'
  exact hX'

/-- The first block of the walk from `p` at the ladder spacing `ladderStep B` below level `ℓ`
has fewer than `holdLen B` horizontal steps with probability at most the bound of
`blockLaw_hcount_lt`, at `h = ladderStep B` and `m = holdLen B`. -/
theorem blockLaw_hcount_lt_ladder (B : Base) (ℓ : ℤ) (p : Site B) (hN : 2 ≤ B.card)
    (hℓ : (p.2 : ℝ) + (ladderStep B : ℝ) ≤ ℓ) :
    blockLaw B ℓ p {c | hcount B p c < holdLen B} ≤
      ENNReal.ofReal (Real.exp (-(ladderStep B : ℝ) ^ 2 / (4 * (holdLen B : ℝ))) +
        Real.exp (-(holdLen B : ℝ) / 2)) :=
  blockLaw_hcount_lt B ℓ p (ladderStep B : ℝ) (Nat.cast_nonneg _) hℓ (holdLen B)
    (holdLen_pos B hN)

end

end IdlaCyl.Silvestri
