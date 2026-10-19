import IdlaCyl.Support.Outer.WellspreadTails

/-!
# `le:wellspread` (well-spread frozen particles), Frozen statement V3

Source: paper/idla-cylinder-gff.tex, tex:1280-1284 (Lemma `le:wellspread`), proof at
tex:1286-1329.

> \begin{Lemma}[Well-spread frozen particles]\label{le:wellspread}
> Let $N_x$ denote the number of particles frozen at $(x, h)$ in $\bar A_h(T)$. For every
> $\n > 0$ there exists $C_2 = C_2(\n) < \infty$ such that
> \[ \bbP\big( G \cap \{ \exists\, x \in V_N : N_x > C_2 \ell_* \} \big) \leq N^{-(\n+1)} \]
> for $N$ large enough.
> \end{Lemma}

V3 replaces V2's threshold `T ≥ 16 (2√(ν+4))² N log N` by the hypothesis `1 ≤ ⌊T/N - ℓ⌋`, that
is `h ≥ 1` with `h = ⌊T/N - ℓ_*⌋`. This is the paper's well-definedness condition for `\bar A_h`
(tex:1147, `h ≥ 1` integer), and pr:inner gives `h ≥ 1` for `T ≥ K₀ N log N` (tex:1160-1166). The
standing assumption `T ≥ C N log N` of tex:1259 therefore gives it for `C` large, so V3 is at
least as strong as the printed lemma on its domain.

The width is `ℓ = innerWidth` with `C₁ = 2√(ν+4)`. From `h ≥ 1` one gets `1 ≤ T/N` and
`ℓ ≤ T/N - 1`, which give `ℓ ≥ 2` for every `N ≥ 4`. They do not give `2ℓ ≤ T/N`, so the
Bernstein exponent uses the helper `le_wellspread_v3_exponent_ge` with `ℓ ≤ T/N` and the
constant `K = 24(ν+4)`.

The Lean statement reads: for each `ν > 0` there are `C₂ > 0` and `N₀ = 4` such that, for every
base with at least `N₀` sites and every `T` with `h ≥ 1`, the driving-law probability of the fill
event `G` together with some level-`h` site carrying more than `C₂ ℓ` frozen particles is at most
`N^{-(ν+1)}`, where `ℓ` is the printed width `innerWidth` and `h = ⌊T/N - ℓ⌋`.
-/

namespace IdlaCyl.Frozen

open IdlaCyl MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The Bernstein exponent bound of `wellspread_exponent_ge` with the width condition weakened
from `2ℓ ≤ t` to `ℓ ≤ t`. Under `h ≥ 1` the width only satisfies `ℓ ≤ t - 1`, and at `h = 1` it
is close to `t`, so `2ℓ ≤ t` can fail. The variance hypothesis is strengthened to `K L (3t)`
to cover the denominator `D + 2ℓ ≤ 3t`. -/
theorem le_wellspread_v3_exponent_ge (ℓ D t L K : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hDt : D ≤ t) (hℓ : 0 < ℓ) (h2 : ℓ ≤ t) (hsq : K * L * (3 * t) ≤ 18 * ℓ ^ 2) :
    -((18 / 3 * ℓ) ^ 2 / 2) / (D + 18 / 3 * ℓ / 3) ≤ -(K * L) := by
  have hden : 0 < D + 18 / 3 * ℓ / 3 := by linarith
  have hdenle : D + 18 / 3 * ℓ / 3 ≤ 3 * t := by linarith
  have hKL : 0 ≤ K * L := mul_nonneg hK hL
  have key : K * L * (D + 18 / 3 * ℓ / 3) ≤ (18 / 3 * ℓ) ^ 2 / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hdenle hKL
    nlinarith [hsq]
  rw [neg_div, neg_le_neg_iff, le_div_iff₀ hden]
  exact key

-- FROZEN-STATEMENT-BEGIN
theorem le_wellspread_v3 (ν : ℝ) (hν : 0 < ν) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card →
      ∀ T : ℕ,
        1 ≤ Int.floor ((T : ℝ) / (B.card : ℝ) - innerWidth ν B.card T) →
        (let ℓ := innerWidth ν B.card T;
         let h : ℤ := Int.floor ((T : ℝ) / (B.card : ℝ) - ℓ);
         idlaMeasure B {ω : TrajSeq B |
           ω ∈ outerFill B h T ∧
           ∃ x : B.V, C₂ * ℓ < (frozenCount B h T ω x : ℝ)} ≤
             ENNReal.ofReal ((B.card : ℝ) ^ (-(ν + 1))))
-- FROZEN-STATEMENT-END
  := by
  refine ⟨18, by norm_num, 4, ?_⟩
  intro B hB T hT ℓ h
  set N : ℝ := (B.card : ℝ) with hNdef
  set C : ℝ := 2 * Real.sqrt (ν + 4) with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; positivity
  have hCsq : C ^ 2 = 4 * (ν + 4) := by
    rw [hCdef, mul_pow, Real.sq_sqrt (by linarith)]
    ring
  have hN4 : (4 : ℝ) ≤ N := by
    have h3 : ((4 : ℕ) : ℝ) ≤ (B.card : ℝ) := Nat.cast_le.mpr hB
    push_cast at h3
    exact h3
  have hNpos : 0 < N := by linarith
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this
    linarith
  have hlog4 : Real.log 4 ≤ Real.log N := Real.log_le_log (by norm_num) hN4
  have hlog4' : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hL1 : 1 ≤ Real.log N := by linarith
  have hL0 : 0 ≤ Real.log N := by linarith
  have hlogT : Real.log N ≤ PrInnerTail.logTerm N T := by
    unfold PrInnerTail.logTerm
    linarith [le_max_right (Real.log ((T : ℝ) / N)) 0]
  have hTnn : (0 : ℝ) ≤ (T : ℝ) / N := div_nonneg (Nat.cast_nonneg T) hNpos.le
  have hlogTnn : 0 ≤ PrInnerTail.logTerm N T := by linarith
  have hℓdef : ℓ = C * Real.sqrt ((T : ℝ) / N * PrInnerTail.logTerm N T) := rfl
  have hℓsq : ℓ ^ 2 = 4 * (ν + 4) * ((T : ℝ) / N * PrInnerTail.logTerm N T) := by
    rw [hℓdef, mul_pow, Real.sq_sqrt (mul_nonneg hTnn hlogTnn), hCsq]
  have hℓ0 : 0 ≤ ℓ := by
    rw [hℓdef]
    exact mul_nonneg hC0 (Real.sqrt_nonneg _)
  -- The only hypothesis on `T` is `h ≥ 1`, which gives `1 + ℓ ≤ T/N`.
  have hh1 : 1 ≤ h := hT
  have hh1R : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  have hh_le : (h : ℝ) ≤ (T : ℝ) / N - ℓ := Int.floor_le _
  have ht1 : 1 ≤ (T : ℝ) / N := by linarith
  have hℓt : ℓ ≤ (T : ℝ) / N := by linarith
  have htl : 1 ≤ (T : ℝ) / N * PrInnerTail.logTerm N T := by
    have hL : 1 ≤ PrInnerTail.logTerm N T := by linarith
    have := mul_le_mul ht1 hL (by norm_num) (by linarith)
    linarith
  have hℓ2sq : 4 ≤ ℓ ^ 2 := by
    rw [hℓsq]
    have h16 : (16 : ℝ) ≤ 4 * (ν + 4) := by linarith
    have := mul_le_mul h16 htl zero_le_one (by linarith)
    linarith
  have hℓ2 : 2 ≤ ℓ := by nlinarith
  have hℓpos : 0 < ℓ := by linarith
  -- Constants of the exponent bound; `K = 24(ν+4)` makes `hsq` an equality.
  set K : ℝ := 24 * (ν + 4) with hK
  have hKν : ν + 3 ≤ K := by
    rw [hK]
    linarith
  have hNK : 0 ≤ N ^ (-K) := Real.rpow_nonneg hNpos.le _
  have h72 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogT hTnn)
    (by linarith : (0 : ℝ) ≤ 72 * (ν + 4))
  have hexp : ∀ D : ℝ, 0 ≤ D → D ≤ (T : ℝ) / N →
      Real.exp (-((18 / 3 * ℓ) ^ 2 / 2) / (D + 18 / 3 * ℓ / 3)) ≤ N ^ (-K) := by
    intro D hD hDt
    have hsq : K * Real.log N * (3 * ((T : ℝ) / N)) ≤ 18 * ℓ ^ 2 := by
      rw [hℓsq, hK]
      nlinarith [h72]
    calc Real.exp (-((18 / 3 * ℓ) ^ 2 / 2) / (D + 18 / 3 * ℓ / 3))
        ≤ Real.exp (-(K * Real.log N)) :=
          Real.exp_le_exp.mpr (le_wellspread_v3_exponent_ge ℓ D ((T : ℝ) / N) (Real.log N) K
            (by rw [hK]; linarith) hL0 hD hDt hℓpos hℓt hsq)
      _ = N ^ (-K) := by
          rw [Real.rpow_def_of_pos hNpos]
          congr 1
          ring
  -- The coupling: the driving law is the first marginal, and the count identity holds a.e.
  obtain ⟨μ, -, hfst, hsnd, -, hae⟩ := outer_ghost_coupling B h hh1 T
  have hSm := wellspread_measurableSet_event B h T (18 * ℓ)
  rw [← hfst, Measure.map_apply measurable_fst hSm]
  set F : B.V → Set (TrajSeq B) :=
    fun x => {ω | (T : ℝ) / N + 18 / 3 * ℓ ≤ (aliveCount B h T ω x : ℝ)} with hF
  set G : B.V → Set (GhostDriver B h) :=
    fun x => {U | (ghostCount B h U x : ℝ) ≤ (h : ℝ) - 1 - 18 / 3 * ℓ} with hG
  -- Pathwise: a frozen count above `18 ℓ` forces one of the two marginal tails.
  have hsub : Prod.fst ⁻¹' {ω : TrajSeq B | ω ∈ outerFill B h T ∧
      ∃ x : B.V, 18 * ℓ < (frozenCount B h T ω x : ℝ)}
      ≤ᵐ[μ] ⋃ x, (Prod.fst ⁻¹' F x ∪ Prod.snd ⁻¹' G x) := by
    filter_upwards [hae] with p hp hpS
    obtain ⟨hfill, x, hx⟩ := hpS
    have hid := hp hfill x
    have hcnt : (frozenCount B h T p.1 x : ℝ) =
        (aliveCount B h T p.1 x : ℝ) - (ghostCount B h p.2 x : ℝ) := by
      have : (aliveCount B h T p.1 x : ℝ) =
          (frozenCount B h T p.1 x : ℝ) + (ghostCount B h p.2 x : ℝ) := by
        exact_mod_cast hid
      linarith
    rcases wellspread_large_count_split (aliveCount B h T p.1 x : ℝ)
        (ghostCount B h p.2 x : ℝ) (frozenCount B h T p.1 x : ℝ) ((T : ℝ) / N) ℓ 18
        hℓ2 (by norm_num) hcnt hx with h1 | h1
    · exact Set.mem_iUnion.mpr ⟨x, Or.inl h1⟩
    · exact Set.mem_iUnion.mpr ⟨x, Or.inr h1⟩
  -- Alive tail: `μ(M ≥ T/N + 6ℓ)` is at most `2 N^{-K}`.
  have hAlive : ∀ x : B.V, μ (Prod.fst ⁻¹' F x) ≤ ENNReal.ofReal (2 * N ^ (-K)) := by
    intro x
    have hle : μ (Prod.fst ⁻¹' F x) ≤ idlaMeasure B (F x) := by
      rw [← hfst]
      exact Measure.le_map_apply measurable_fst.aemeasurable _
    have hBern : idlaMeasure B {ω | 18 / 3 * ℓ ≤
        |((aliveCount B h T ω x : ℕ) : ℝ) - (T : ℝ) / N|} ≤
        ENNReal.ofReal (2 * Real.exp (-((18 / 3 * ℓ) ^ 2 / 2) / ((T : ℝ) / N + 18 / 3 * ℓ / 3))) :=
      wellspread_alive_tail B h T x (18 / 3 * ℓ) (by linarith)
    have hsubA : F x ⊆ {ω | 18 / 3 * ℓ ≤
        |((aliveCount B h T ω x : ℕ) : ℝ) - (T : ℝ) / N|} := by
      intro ω hω
      have hω' : (T : ℝ) / N + 18 / 3 * ℓ ≤ (aliveCount B h T ω x : ℝ) := hω
      have hsx : 18 / 3 * ℓ ≤ (aliveCount B h T ω x : ℝ) - (T : ℝ) / N := by linarith
      exact le_abs.mpr (Or.inl hsx)
    have hbound := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (hexp ((T : ℝ) / N) hTnn le_rfl) (by norm_num : (0 : ℝ) ≤ 2))
    exact hle.trans ((measure_mono hsubA).trans (hBern.trans hbound))
  -- Ghost tail: `ν_ghost(L̃ ≤ h - 1 - 6ℓ)` is at most `2 N^{-K}`.
  have hGhost : ∀ x : B.V, μ (Prod.snd ⁻¹' G x) ≤ ENNReal.ofReal (2 * N ^ (-K)) := by
    intro x
    have hle : μ (Prod.snd ⁻¹' G x) ≤ ghostLaw B h (G x) := by
      rw [← hsnd]
      exact Measure.le_map_apply measurable_snd.aemeasurable _
    have hBern : ghostLaw B h {U | 18 / 3 * ℓ ≤
        |((ghostCount B h U x : ℕ) : ℝ) - ((h : ℝ) - 1)|} ≤
        ENNReal.ofReal (2 * Real.exp (-((18 / 3 * ℓ) ^ 2 / 2) /
          (((h : ℝ) - 1) + 18 / 3 * ℓ / 3))) :=
      wellspread_ghost_tail B h hh1 x (18 / 3 * ℓ) (by linarith)
    have hsubG : G x ⊆ {U | 18 / 3 * ℓ ≤
        |((ghostCount B h U x : ℕ) : ℝ) - ((h : ℝ) - 1)|} := by
      intro U hU
      have hU' : (ghostCount B h U x : ℝ) ≤ (h : ℝ) - 1 - 18 / 3 * ℓ := hU
      have hsx : 18 / 3 * ℓ ≤ -((ghostCount B h U x : ℝ) - ((h : ℝ) - 1)) := by linarith
      exact le_abs.mpr (Or.inr hsx)
    have hbound := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (hexp ((h : ℝ) - 1) (by linarith) (by linarith)) (by norm_num : (0 : ℝ) ≤ 2))
    exact hle.trans ((measure_mono hsubG).trans (hBern.trans hbound))
  -- Per vertex: two marginal tails.
  have hPer : ∀ x : B.V,
      μ (Prod.fst ⁻¹' F x ∪ Prod.snd ⁻¹' G x) ≤ ENNReal.ofReal (4 * N ^ (-K)) := by
    intro x
    refine (measure_union_le _ _).trans ?_
    refine (add_le_add (hAlive x) (hGhost x)).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add (mul_nonneg (by norm_num) hNK) (mul_nonneg (by norm_num) hNK)]
    congr 1
    ring
  -- Union bound over the N vertices, then the polynomial comparison.
  calc μ (Prod.fst ⁻¹' {ω : TrajSeq B | ω ∈ outerFill B h T ∧
          ∃ x : B.V, 18 * ℓ < (frozenCount B h T ω x : ℝ)})
      ≤ μ (⋃ x, (Prod.fst ⁻¹' F x ∪ Prod.snd ⁻¹' G x)) := measure_mono_ae hsub
    _ ≤ ∑ x, μ (Prod.fst ⁻¹' F x ∪ Prod.snd ⁻¹' G x) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _x : B.V, ENNReal.ofReal (4 * N ^ (-K)) :=
        Finset.sum_le_sum fun x _ => hPer x
    _ = ENNReal.ofReal (N * (4 * N ^ (-K))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
    _ ≤ ENNReal.ofReal (N ^ (-(ν + 1))) :=
        ENNReal.ofReal_le_ofReal (wellspread_final_power N ν K hN4 hKν)
