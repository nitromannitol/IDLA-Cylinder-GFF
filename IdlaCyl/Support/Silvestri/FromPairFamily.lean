module

public import IdlaCyl.Support.Silvestri.AssembleFamily
public import IdlaCyl.Support.Silvestri.AssembleUnion
public import IdlaCyl.Support.Silvestri.AssembleDet
public import IdlaCyl.Support.Silvestri.FinalArith
public import IdlaCyl.External.SilvestriProp2

@[expose] public section

/-!
# Silvestri's Proposition 2 from a family of pair laws

`External.silvestri_prop2` asks, for each `m`, for a coupling of two IDLA histories
started from any two families of starts of height at most `0`. Each marginal is the
fixed-start process law, and the two histories agree with probability at least
`1 - N^{-γ}` once the seed contains the half-cylinder of height `b √τ log N`.

This file reduces the proposition to one family `Q B x x'` of laws on pairs of paths.
It assumes that each `Q B x x'` is a probability measure on pairs of starts of height at
most `0`, that its two marginals are the walk laws of the starts, and that the pathwise
success event `pairGood` at the level `K · ladderStep B` fails with probability at most
`holdFail B ^ K`, for every `K ≤ B.card`. The coupling is `silvestriJ` built from `Q`. It
does not depend on `m` or `γ`.

The main theorem is `silvestri_prop2_of_pairFamily`. The constants are `K = attempts m γ`,
`b = 14 * K` and `N₀ = max 6 K`.
-/

namespace IdlaCyl.Silvestri

open MeasureTheory IdlaCyl.External
open scoped ENNReal

/-- Silvestri's Proposition 2 holds once there is a family `Q` of pair laws with the walk
laws as marginals, and with the failure bound `holdFail B ^ K` for the pathwise success event
at the level `K · ladderStep B`, for every `K ≤ B.card` when `6 ≤ B.card`. The connectedness of the
initial cluster assumed by the proposition is not used. -/
theorem silvestri_prop2_of_pairFamily
    (Q : ∀ B : Base, Site B → Site B → Measure ((ℕ → Site B) × (ℕ → Site B)))
    (hQ : ∀ (B : Base) (x x' : Site B), x.2 ≤ 0 → x'.2 ≤ 0 → IsProbabilityMeasure (Q B x x'))
    (hQ1 : ∀ (B : Base) (x x' : Site B), x.2 ≤ 0 → x'.2 ≤ 0 →
      (Q B x x').map Prod.fst = walkPathLaw B x)
    (hQ2 : ∀ (B : Base) (x x' : Site B), x.2 ≤ 0 → x'.2 ≤ 0 →
      (Q B x x').map Prod.snd = walkPathLaw B x')
    (hfail : ∀ (B : Base), 6 ≤ B.card → ∀ K : ℕ, K ≤ B.card →
      ∀ (x x' : Site B), x.2 ≤ 0 → x'.2 ≤ 0 →
        Q B x x' {pp | ¬ pairGood B ((K : ℝ) * ladderStep B) pp.1 pp.2}
          ≤ ENNReal.ofReal (holdFail B ^ K)) :
    External.silvestri_prop2 := by
  intro m
  refine ⟨fun B T F s s' => silvestriJ B (Q B) (hQ B) T F s s', ?_, ?_⟩
  · intro B T _ _ F s s' _ _ _
    exact ⟨silvestriJ_map_fst B (Q B) (hQ B) (hQ1 B) T F s s',
      silvestriJ_map_snd B (Q B) (hQ B) (hQ2 B) T F s s'⟩
  · intro γ hγ
    have hK1 : 0 < attempts m γ := by
      have := (attempts_spec m γ hγ).1
      omega
    have hb : (0 : ℝ) < 14 * (attempts m γ : ℝ) :=
      mul_pos (by norm_num) (Nat.cast_pos.mpr hK1)
    refine ⟨14 * (attempts m γ : ℝ), hb, max 6 (attempts m γ), ?_⟩
    intro B hN T _ hTm F s s' _ hs hs' hR
    have hN6 : 6 ≤ B.card := le_trans (le_max_left _ _) hN
    have hKN : attempts m γ ≤ B.card := le_trans (le_max_right _ _) hN
    have hF : R B ((attempts m γ : ℝ) * ladderStep B) ⊆ resumeSeed B F :=
      (ladder_rect B hN6 (attempts m γ)).trans hR
    have hε : ∀ t < T, silvestriPairLaw B (Q B) T s s' t
        {x | ¬ pairGood B ((attempts m γ : ℝ) * ladderStep B) x.1 x.2}
          ≤ ENNReal.ofReal (holdFail B ^ attempts m γ) := by
      intro t _
      unfold silvestriPairLaw pairLawTot
      rw [if_pos (And.intro (silvestriStarts_height_le B T s hs t)
        (silvestriStarts_height_le B T s' hs' t))]
      exact hfail B hN6 (attempts m γ) hKN _ _
        (silvestriStarts_height_le B T s hs t) (silvestriStarts_height_le B T s' hs' t)
    have hU := silvestriJ_diag_ge B (Q B) (hQ B) T F s s' _ hF _ hε
    exact (fail_mul_le B m T γ hγ hN6 hTm).trans hU

end IdlaCyl.Silvestri
