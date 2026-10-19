import IdlaCyl.Support.Base
import IdlaCyl.Support.Cylinder
import IdlaCyl.Support.CanonicalIdla
import IdlaCyl.Support.PrInnerSupport
import IdlaCyl.Support.StoppedScoreMartingale
import IdlaCyl.Support.PrInnerStopped.LowerTail
import IdlaCyl.Support.PrInnerTail.Nonvacuity

/-!
# Lower tail of the stopped score, for every `T : ℕ`

The printed lemma (`paper/idla-cylinder-gff.tex:1194-1197`, `lem:M lower tail`, with the score
`M_ζ` defined at `tex:1189`) reads:

  For every $0 \leq \ell \leq T/(2N)$,
  $$ \bbP( M_\zeta(T) \leq -\ell ) \leq \exp\!\Big( -\frac{\ell^2 N}{4T} \Big)\,. $$

The Lean statement reads `M_ζ(T)` as `stoppedScore B h ζ T`, `ℙ` as `idlaMeasure B`, `N` as `B.card`
and `ζ` as a site on the stopping level `h`, and, as the printed lemma does, places no restriction
on `T`.
-/

namespace IdlaCyl.Frozen

-- FROZEN-STATEMENT-BEGIN
theorem lem_m_lower_tail_v2 (B : Base) (h : ℤ) (hh : 1 ≤ h)
    (ζ : Site B) (hζ : ζ.2 = h) (T : ℕ)
    (ℓ : ℝ) (hℓ₀ : 0 ≤ ℓ) (hℓ : ℓ ≤ (T : ℝ) / (2 * (B.card : ℝ))) :
    idlaMeasure B {ω : TrajSeq B | stoppedScore B h ζ T ω ≤ -ℓ} ≤
      ENNReal.ofReal (Real.exp (-(ℓ ^ 2 * (B.card : ℝ) / (4 * (T : ℝ)))))
-- FROZEN-STATEMENT-END
  := by
  rcases Nat.eq_zero_or_pos T with hT0 | hT
  · -- `T = 0` forces `ℓ = 0`; the score is then identically `0` and the bound is `exp 0 = 1`
    subst hT0
    have hℓ0 : ℓ = 0 := by
      have hle : ℓ ≤ 0 := by simpa using hℓ
      exact le_antisymm hle hℓ₀
    subst hℓ0
    have hset : {ω : TrajSeq B | stoppedScore B h ζ 0 ω ≤ -0} = Set.univ := by
      ext ω
      simp
    rw [hset, MeasureTheory.measure_univ]
    simp
  · -- `1 ≤ T`: the producer of `lem:M lower tail` on the stopped filtration, bridged to `stoppedScore`
    have hT1 : 1 ≤ T := hT
    have key := stoppedScoreOf_lower_tail_stopped B h hh ζ hζ T hT1 ℓ hℓ₀ hℓ
    simpa only [← stoppedScore_eq_stoppedScoreOf] using key

-- Nonvacuity at the two-vertex base `K2`: `h = 1`, `ζ = (1, 1)` on level 1, `T = 2`, and
-- `ℓ = 1/2 = T/(2N)`, so every hypothesis holds and the bound is an instance of the theorem.
open IdlaCyl.PrInnerTail in
example : idlaMeasure K2 {ω : TrajSeq K2 | stoppedScore K2 1 ((1 : Fin 2), (1 : ℤ)) 2 ω ≤ -(1 / 2 : ℝ)} ≤
    ENNReal.ofReal (Real.exp (-((1 / 2 : ℝ) ^ 2 * (K2.card : ℝ) / (4 * ((2 : ℕ) : ℝ))))) :=
  lem_m_lower_tail_v2 K2 1 le_rfl ((1 : Fin 2), (1 : ℤ)) rfl 2 (1 / 2) (by norm_num)
    (by norm_num [show K2.card = 2 from rfl])

end IdlaCyl.Frozen
