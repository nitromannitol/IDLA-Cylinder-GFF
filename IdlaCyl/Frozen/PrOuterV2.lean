/-
The outer bound `pr:outer` as a Frozen statement (V2), outer task 10.
Source: paper/idla-cylinder-gff.tex, tex:1262-1266 (statement), proof tex:1373-1435.

Route (DECOMPOSITION task 10): choose all constants before `B` and `T`; apply the inner
bound, `le_wellspread_v2` and `le_released_v2` at parameter `ν + 1`; take
`h = ⌊T/N - ℓ_{ν+1}⌋`, `m = ⌈C₂ ℓ_{ν+1}⌉₊ + 1`, `r = C₃ m`; feed `outer_height_comparison`;
bound the three bad events by `N^{-(ν+2)}` each; finally use `ℓ_{ν+1} = ρ ℓ_ν` with
`ρ = (2√(ν+5))/(2√(ν+4))` (`innerWidth_succ`).
-/
import IdlaCyl.Support.Outer.HeightComparison
import IdlaCyl.Support.Outer.StoppedBookkeeping
import IdlaCyl.Support.PrInnerStopped.Composition
import IdlaCyl.Frozen.LeWellspreadV2
import IdlaCyl.Frozen.LeReleasedV2

namespace IdlaCyl.Frozen

open IdlaCyl MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- The stopped-cluster fill event is contained in the inner failure event at the same height:
if `R_h ⊆ Ā_h(T)` then `R_{h-1} ⊆ Ā_h(T)`. -/
theorem pr_outer_v2_fill_subset (B : Base) (h : ℤ) (T : ℕ) :
    {ω : TrajSeq B | ω ∉ outerFill B h T} ⊆
      {ω : TrajSeq B | ¬ R B (h : ℝ) ⊆ stoppedCluster B h ω T} := by
  intro ω hω
  simp only [Set.mem_setOf_eq, outerFill] at hω ⊢
  intro hR
  have hle : ((h - 1 : ℤ) : ℝ) ≤ (h : ℝ) := by push_cast; linarith
  exact hω ((R_mono hle).trans hR)

/-- Width lower bound: with `log N ≥ 1` and `T/N ≥ K log N`, `ℓ_ν ≥ 2√(ν+4) √K log N`. -/
theorem pr_outer_v2_width_lower (ν K : ℝ) (hν : 0 < ν) (hK : 0 ≤ K) (B : Base) (T : ℕ)
    (hlogN : 1 ≤ Real.log (B.card : ℝ))
    (hTN : K * Real.log (B.card : ℝ) ≤ (T : ℝ) / (B.card : ℝ)) :
    2 * Real.sqrt (ν + 4) * Real.sqrt K * Real.log (B.card : ℝ) ≤ innerWidth ν B.card T := by
  have hlog0 : 0 ≤ Real.log (B.card : ℝ) := by linarith
  have hL : Real.log (B.card : ℝ) ≤ PrInnerTail.logTerm (B.card : ℝ) (T : ℝ) := by
    unfold PrInnerTail.logTerm
    linarith [le_max_right (Real.log ((T : ℝ) / (B.card : ℝ))) 0]
  have hq : K * Real.log (B.card : ℝ) * Real.log (B.card : ℝ) ≤
      (T : ℝ) / (B.card : ℝ) * PrInnerTail.logTerm (B.card : ℝ) (T : ℝ) :=
    mul_le_mul hTN hL hlog0 (le_trans (mul_nonneg hK hlog0) hTN)
  have hsq : Real.sqrt K * Real.log (B.card : ℝ) ≤
      Real.sqrt ((T : ℝ) / (B.card : ℝ) * PrInnerTail.logTerm (B.card : ℝ) (T : ℝ)) := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, Real.sq_sqrt hK]
    nlinarith [hq]
  unfold innerWidth
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hsq (by positivity)

/-- A nonnegative number whose square is at least one is at least one. -/
theorem pr_outer_v2_one_le_of_sq (x : ℝ) (hx : 0 ≤ x) (h : 1 ≤ x ^ 2) : 1 ≤ x := by
  nlinarith

/-- The arithmetic of the final union bound: `3 a ≤ a N` once `3 ≤ N`. -/
theorem pr_outer_v2_three_le (a b X N : ℝ) (ha : 0 ≤ a) (hb : b ≤ a) (hN : 3 ≤ N)
    (hX : X = a * N) : a + a + b ≤ X := by
  nlinarith

/-- The printed proposition (tex:1262-1266): for every $\n > 0$ there exist
$C' = C'(\n) < \infty$ and $K' = K'(\n) < \infty$ such that, for every integer
$T \geq K' N \log N$ and with $r \coloneqq C' \ell_*$,
$\bbP ( A(T) \nsubseteq R_{T/N + r} ) \leq N^{-(\n+1)}$ for $N$ large enough.
Here $\ell_*$ is `innerWidth ν N T`, $A(T)$ is `clusterTraj B ω T`, and $N$ is `B.card`. -/
-- FROZEN-STATEMENT-BEGIN
theorem pr_outer_v2 (ν : ℝ) (hν : 0 < ν) :
    ∃ C' K' : ℝ, 0 < C' ∧ 0 < K' ∧ ∃ N₀ : ℕ,
      ∀ B : Base, N₀ ≤ B.card → ∀ T : ℕ,
        K' * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (T : ℝ) →
        idlaMeasure B {ω : TrajSeq B |
          ¬ (clusterTraj B ω T ⊆ R B ((T : ℝ) / (B.card : ℝ) +
            C' * innerWidth ν B.card T))} ≤
          ENNReal.ofReal ((B.card : ℝ) ^ (-(ν + 1)))
-- FROZEN-STATEMENT-END
  := by
  obtain ⟨C₂, hC₂, N₁, hW⟩ := le_wellspread_v2 (ν + 1) (by linarith)
  obtain ⟨C₃, K₁, hC₃, hK₁, N₂, hR⟩ := le_released_v2 (ν + 1) (by linarith)
  -- constants: c₀ = C₁(ν+1); K' dominates the inner threshold, the release size and w_ν ≥ 1
  have hc₀ : 0 < 2 * Real.sqrt (ν + 1 + 4) := by
    have := Real.sqrt_pos.mpr (show (0 : ℝ) < ν + 1 + 4 by linarith)
    linarith
  have hsqrt4 : 0 < Real.sqrt (ν + 4) := Real.sqrt_pos.mpr (by linarith)
  have hρ : 0 ≤ (2 * Real.sqrt (ν + 5)) / (2 * Real.sqrt (ν + 4)) := by positivity
  have hK'pos : 0 < 16 * (2 * Real.sqrt (ν + 1 + 4)) ^ 2 +
      (K₁ / (C₂ * (2 * Real.sqrt (ν + 1 + 4)))) ^ 2 + 1 / (4 * (ν + 4)) := by
    have h1 : 0 < 16 * (2 * Real.sqrt (ν + 1 + 4)) ^ 2 := by positivity
    have h2 : 0 ≤ (K₁ / (C₂ * (2 * Real.sqrt (ν + 1 + 4)))) ^ 2 := sq_nonneg _
    have h3 : 0 < 1 / (4 * (ν + 4)) := by apply div_pos one_pos; linarith
    linarith
  refine ⟨C₃ * (C₂ * ((2 * Real.sqrt (ν + 5)) / (2 * Real.sqrt (ν + 4))) + 2),
    16 * (2 * Real.sqrt (ν + 1 + 4)) ^ 2 +
      (K₁ / (C₂ * (2 * Real.sqrt (ν + 1 + 4)))) ^ 2 + 1 / (4 * (ν + 4)),
    mul_pos hC₃ (by have := mul_nonneg hC₂.le hρ; linarith), hK'pos,
    N₁ + N₂ + ⌈256 * (2 * Real.sqrt (ν + 1 + 4)) ^ 4⌉₊ + 3, ?_⟩
  intro B hB T hT
  set K' : ℝ := 16 * (2 * Real.sqrt (ν + 1 + 4)) ^ 2 +
    (K₁ / (C₂ * (2 * Real.sqrt (ν + 1 + 4)))) ^ 2 + 1 / (4 * (ν + 4)) with hK'def
  set ρ : ℝ := (2 * Real.sqrt (ν + 5)) / (2 * Real.sqrt (ν + 4)) with hρdef
  have hK0 : 0 ≤ K' := by linarith
  have hN1' : N₁ ≤ B.card := by omega
  have hN2' : N₂ ≤ B.card := by omega
  have hNc : ⌈256 * (2 * Real.sqrt (ν + 1 + 4)) ^ 4⌉₊ + 3 ≤ B.card := by omega
  have hNr : (⌈256 * (2 * Real.sqrt (ν + 1 + 4)) ^ 4⌉₊ : ℝ) + 3 ≤ (B.card : ℝ) := by
    exact_mod_cast hNc
  have hN256 : 256 * (2 * Real.sqrt (ν + 1 + 4)) ^ 4 + 1 ≤ (B.card : ℝ) := by
    linarith [Nat.le_ceil (256 * (2 * Real.sqrt (ν + 1 + 4)) ^ 4)]
  have hcast0 : (0 : ℝ) ≤ (⌈256 * (2 * Real.sqrt (ν + 1 + 4)) ^ 4⌉₊ : ℝ) := Nat.cast_nonneg _
  have hN3 : (3 : ℝ) ≤ (B.card : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (B.card : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (B.card : ℝ) := by linarith
  have hlogN : 1 ≤ Real.log (B.card : ℝ) := by
    rw [Real.le_log_iff_exp_le hNpos]
    have he := Real.exp_one_lt_d9
    norm_num at he
    linarith
  have hlog0 : 0 ≤ Real.log (B.card : ℝ) := by linarith
  -- the inner, wellspread and release hypotheses at the shared threshold
  have hA : 16 * (2 * Real.sqrt (ν + 1 + 4)) ^ 2 ≤ K' := by
    rw [hK'def]
    have : 0 ≤ (K₁ / (C₂ * (2 * Real.sqrt (ν + 1 + 4)))) ^ 2 := sq_nonneg _
    have : 0 < 1 / (4 * (ν + 4)) := by apply div_pos one_pos; linarith
    linarith
  have hTW : 16 * (2 * Real.sqrt (ν + 1 + 4)) ^ 2 * (B.card : ℝ) * Real.log (B.card : ℝ) ≤
      (T : ℝ) := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hNpos.le) hlog0
    linarith
  have hTN : K' * Real.log (B.card : ℝ) ≤ (T : ℝ) / (B.card : ℝ) := by
    rw [le_div_iff₀ hNpos]
    linarith [hT]
  -- widths: ℓ_{ν+1} = ρ ℓ_ν, and the size bounds on w_ν and ℓ_{ν+1}
  have hw1 : innerWidth (ν + 1) B.card T = ρ * innerWidth ν B.card T :=
    innerWidth_succ ν hν B.card T
  have hwν1 : 1 ≤ innerWidth ν B.card T := by
    have hlow := pr_outer_v2_width_lower ν K' hν hK0 B T hlogN hTN
    have hK'ge : 1 / (4 * (ν + 4)) ≤ K' := by
      rw [hK'def]
      have : 0 ≤ (K₁ / (C₂ * (2 * Real.sqrt (ν + 1 + 4)))) ^ 2 := sq_nonneg _
      have : 0 < 16 * (2 * Real.sqrt (ν + 1 + 4)) ^ 2 := by positivity
      linarith
    have hsq : (2 * Real.sqrt (ν + 4) * Real.sqrt K') ^ 2 = 4 * (ν + 4) * K' := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt hK0]
      ring
    have hge : 1 ≤ 4 * (ν + 4) * K' := by
      rw [div_le_iff₀ (by linarith)] at hK'ge
      linarith
    have hx0 : 0 ≤ 2 * Real.sqrt (ν + 4) * Real.sqrt K' := by positivity
    have h4 : 1 ≤ 2 * Real.sqrt (ν + 4) * Real.sqrt K' := by
      apply pr_outer_v2_one_le_of_sq _ hx0
      rw [hsq]
      exact hge
    exact le_trans (one_le_mul_of_one_le_of_one_le h4 hlogN) hlow
  have hlowC : K₁ * Real.log (B.card : ℝ) ≤ C₂ * innerWidth (ν + 1) B.card T := by
    have hw1lo := pr_outer_v2_width_lower (ν + 1) K' (by linarith) hK0 B T hlogN hTN
    have hpos : 0 < C₂ * (2 * Real.sqrt (ν + 1 + 4)) := mul_pos hC₂ hc₀
    have hdiv : K₁ / (C₂ * (2 * Real.sqrt (ν + 1 + 4))) * (C₂ * (2 * Real.sqrt (ν + 1 + 4))) = K₁ :=
      div_mul_cancel₀ _ hpos.ne'
    have hsq' : (K₁ / (C₂ * (2 * Real.sqrt (ν + 1 + 4)))) ^ 2 ≤ K' := by
      rw [hK'def]
      have : 0 ≤ 16 * (2 * Real.sqrt (ν + 1 + 4)) ^ 2 := by positivity
      have : 0 ≤ 1 / (4 * (ν + 4)) := by apply div_nonneg zero_le_one; linarith
      linarith
    have hsK : K₁ / (C₂ * (2 * Real.sqrt (ν + 1 + 4))) ≤ Real.sqrt K' :=
      (le_abs_self _).trans (Real.abs_le_sqrt hsq')
    have hK1 : K₁ ≤ Real.sqrt K' * (C₂ * (2 * Real.sqrt (ν + 1 + 4))) := by
      have := mul_le_mul_of_nonneg_right hsK hpos.le
      rw [hdiv] at this
      exact this
    calc K₁ * Real.log (B.card : ℝ) ≤ Real.sqrt K' * (C₂ * (2 * Real.sqrt (ν + 1 + 4))) * Real.log (B.card : ℝ) :=
          mul_le_mul_of_nonneg_right hK1 hlog0
      _ = C₂ * (2 * Real.sqrt (ν + 1 + 4) * Real.sqrt K' * Real.log (B.card : ℝ)) := by ring
      _ ≤ C₂ * innerWidth (ν + 1) B.card T := mul_le_mul_of_nonneg_left hw1lo hC₂.le
  -- the integer objects m and h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈C₂ * innerWidth (ν + 1) B.card T⌉₊ + 1 := ⟨_, rfl⟩
  have hw1nn : 0 ≤ C₂ * innerWidth (ν + 1) B.card T :=
    mul_nonneg hC₂.le (innerWidth_nonneg _ _ _)
  have hmup : (m : ℝ) ≤ C₂ * innerWidth (ν + 1) B.card T + 2 := by
    rw [hm]; push_cast
    linarith [Nat.ceil_lt_add_one hw1nn]
  have hCm : C₂ * innerWidth (ν + 1) B.card T ≤ (m : ℝ) := by
    rw [hm]; push_cast
    linarith [Nat.le_ceil (C₂ * innerWidth (ν + 1) B.card T)]
  have hmK : K₁ * Real.log (B.card : ℝ) ≤ (m : ℝ) := le_trans hlowC hCm
  set h : ℤ := ⌊(T : ℝ) / (B.card : ℝ) - innerWidth (ν + 1) B.card T⌋ with hhdef
  have hfl : (h : ℝ) ≤ (T : ℝ) / (B.card : ℝ) - innerWidth (ν + 1) B.card T :=
    Int.floor_le _
  have hhT : (h : ℝ) ≤ (T : ℝ) / (B.card : ℝ) := by
    linarith [innerWidth_nonneg (ν + 1) B.card T]
  -- the inner bound at ν + 1, the wellspread bound and the release bound
  obtain ⟨hh1, -, hfill⟩ := pr_inner_probability_bound B (ν + 1) (by linarith) hN256 T hTW h rfl
  have hWB : idlaMeasure B {ω : TrajSeq B | ω ∈ outerFill B h T ∧
      ∃ x : B.V, C₂ * innerWidth (ν + 1) B.card T < (frozenCount B h T ω x : ℝ)} ≤
      ENNReal.ofReal ((B.card : ℝ) ^ (-((ν + 1) + 1))) :=
    hW B hN1' T hTW
  have hRB := hR B hN2' m hmK
  have hcomp := outer_height_comparison B h hh1 T m (C₃ * (m : ℝ))
  -- the height reduction: h + C₃ m ≤ T/N + C' ℓ_ν
  have hmle : (m : ℝ) ≤ (C₂ * ρ + 2) * innerWidth ν B.card T := by
    have := hmup
    rw [hw1] at this
    linarith [hwν1]
  have hle : (h : ℝ) + C₃ * (m : ℝ) ≤
      (T : ℝ) / (B.card : ℝ) + C₃ * (C₂ * ρ + 2) * innerWidth ν B.card T := by
    have h3 := mul_le_mul_of_nonneg_left hmle hC₃.le
    have e : C₃ * (C₂ * ρ + 2) * innerWidth ν B.card T = C₃ * ((C₂ * ρ + 2) * innerWidth ν B.card T) := by
      ring
    linarith
  have hsub : {ω : TrajSeq B | ¬ (clusterTraj B ω T ⊆ R B ((T : ℝ) / (B.card : ℝ) +
      C₃ * (C₂ * ρ + 2) * innerWidth ν B.card T))} ⊆
      {ω : TrajSeq B | ¬ clusterTraj B ω T ⊆ R B ((h : ℝ) + C₃ * (m : ℝ))} := by
    intro ω hω hin
    exact hω (hin.trans (R_mono hle))
  -- the bad event splits into fill failure and an excessive frozen multiplicity
  have hbad_sub : {ω : TrajSeq B | ω ∉ outerFill B h T ∨ ∃ x : B.V, m < frozenCount B h T ω x} ⊆
      {ω : TrajSeq B | ω ∉ outerFill B h T} ∪ {ω : TrajSeq B | ω ∈ outerFill B h T ∧
        ∃ x : B.V, C₂ * innerWidth (ν + 1) B.card T < (frozenCount B h T ω x : ℝ)} := by
    rintro ω (hω | ⟨x, hx⟩)
    · exact Or.inl hω
    · by_cases hf : ω ∈ outerFill B h T
      · exact Or.inr ⟨hf, x, lt_of_le_of_lt hCm (by exact_mod_cast hx)⟩
      · exact Or.inl hf
  have h1 : idlaMeasure B {ω : TrajSeq B | ω ∉ outerFill B h T} ≤
      ENNReal.ofReal ((B.card : ℝ) ^ (-((ν + 1) + 1))) :=
    (measure_mono (pr_outer_v2_fill_subset B h T)).trans hfill
  have hbad_le : idlaMeasure B {ω : TrajSeq B | ω ∉ outerFill B h T ∨
      ∃ x : B.V, m < frozenCount B h T ω x} ≤
      ENNReal.ofReal ((B.card : ℝ) ^ (-((ν + 1) + 1))) +
        ENNReal.ofReal ((B.card : ℝ) ^ (-((ν + 1) + 1))) :=
    ((measure_mono hbad_sub).trans (measure_union_le _ _)).trans (add_le_add h1 hWB)
  -- the arithmetic: 3 N^{-(ν+2)} ≤ N^{-(ν+1)}
  have hsum : ENNReal.ofReal ((B.card : ℝ) ^ (-((ν + 1) + 1))) +
      ENNReal.ofReal ((B.card : ℝ) ^ (-((ν + 1) + 1))) +
      ENNReal.ofReal ((B.card : ℝ) ^ (-((ν + 1) + 2))) ≤
      ENNReal.ofReal ((B.card : ℝ) ^ (-(ν + 1))) := by
    have ha0 : 0 ≤ (B.card : ℝ) ^ (-((ν + 1) + 1)) := Real.rpow_nonneg hNpos.le _
    have hb0 : 0 ≤ (B.card : ℝ) ^ (-((ν + 1) + 2)) := Real.rpow_nonneg hNpos.le _
    rw [← ENNReal.ofReal_add ha0 ha0, ← ENNReal.ofReal_add (by linarith) hb0]
    apply ENNReal.ofReal_le_ofReal
    have hble : (B.card : ℝ) ^ (-((ν + 1) + 2)) ≤ (B.card : ℝ) ^ (-((ν + 1) + 1)) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hX : (B.card : ℝ) ^ (-(ν + 1)) =
        (B.card : ℝ) ^ (-((ν + 1) + 1)) * (B.card : ℝ) := by
      rw [← Real.rpow_add_one hNpos.ne']
      congr 1
      ring
    exact pr_outer_v2_three_le _ _ _ _ ha0 hble hN3 hX
  refine (measure_mono hsub).trans (hcomp.trans ?_)
  calc _ ≤ ENNReal.ofReal ((B.card : ℝ) ^ (-((ν + 1) + 1))) +
        ENNReal.ofReal ((B.card : ℝ) ^ (-((ν + 1) + 1))) +
        ENNReal.ofReal ((B.card : ℝ) ^ (-((ν + 1) + 2))) :=
      add_le_add hbad_le hRB
    _ ≤ ENNReal.ofReal ((B.card : ℝ) ^ (-(ν + 1))) := hsum
