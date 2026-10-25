module

/-
The canonical score martingale of `pr:inner` / `lem:M lower tail`
(`paper/idla-cylinder-gff.tex:1189`, `tex:1194-1197`), on the `TrajSeq`/`idlaMeasure`
carrier.

`H_ζ = IdlaCyl.hitProb B ζ` (`Support/FirstHit.lean`) is the probability that a
cylinder walk from its argument first reaches the stopping layer at `ζ`; it is
discrete harmonic on `R_{ζ.2-1}` (`hitProb_harmonic`) and takes values in `[0,1]`.
The paper's score is

  `M_ζ(t) = ∑_{s=1}^t ( H_ζ(X̄_s, Ȳ_s) − 1/N )`,

where `(X̄_s, Ȳ_s) = stoppedSettleSite B h ω (s-1)` are the exit locations added by
the stopped process `Ā_h` (`Support/Stopped.lean`).

This file lands the setup and every *deterministic* hypothesis of Freedman's
inequality (`External.freedman_of_latticeProb`): `M_ζ(0) = 0`, the increment
bound `|M_ζ(i+1) − M_ζ(i)| ≤ 1`, and the Freedman application reducing the tail
to the paper's `exp(−ℓ²N/(4T))`.  The one remaining input is the per-step
conditional-mean / variance identity

  `E[ H_ζ(X̄_t, Ȳ_t) | 𝓕_{t-1} ] = (1/N) ∑_x H_ζ(x,0) = 1/N`   (`tex:1198-1206`),

which needs the optional stopping `hitProb_exit_mean` applied to the random set
`stoppedCluster ∩ R_{h-1}` together with `hitProb_layer_sum`; it is carried as the
explicit hypothesis `hvar` (and the martingale property `hmart`) below.

Everything is on the canonical carrier; no `Driver`/`driverLaw`/`cluster`.
-/
public import IdlaCyl.Support.Stopped
public import IdlaCyl.Support.HarmonicStoppedMass
public import IdlaCyl.Support.FirstHit
public import IdlaCyl.Support.Filtration
public import IdlaCyl.External.Discharge.Freedman

@[expose] public section

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

variable (B : Base)

/-- The stopped score `M_ζ(t) = ∑_{s<t} (H_ζ(X̄_s, Ȳ_s) − 1/N)` (`tex:1189`), built
from the exit locations `stoppedSettleSite B h ω s` of `Ā_h`. -/
noncomputable def stoppedScore (h : ℤ) (ζ : Site B) (t : ℕ) (ω : TrajSeq B) : ℝ :=
  ∑ s ∈ Finset.range t,
    (hitProb B ζ (stoppedSettleSite B h ω s) - 1 / (B.card : ℝ))

@[simp]
theorem stoppedScore_zero (h : ℤ) (ζ : Site B) (ω : TrajSeq B) :
    stoppedScore B h ζ 0 ω = 0 := by
  simp [stoppedScore]

/-- **The increment is in `[-1/N, 1]`, hence bounded by `1`** (`tex:1204`):
`H_ζ ∈ [0,1]`, so `H_ζ(X̄_s, Ȳ_s) − 1/N ∈ [-1/N, 1]`. -/
theorem abs_stoppedScore_increment (h : ℤ) (ζ : Site B) (s : ℕ) (ω : TrajSeq B) :
    |stoppedScore B h ζ (s + 1) ω - stoppedScore B h ζ s ω| ≤ 1 := by
  have h1 : 0 ≤ hitProb B ζ (stoppedSettleSite B h ω s) := hitProb_nonneg B ζ _
  have h2 : hitProb B ζ (stoppedSettleSite B h ω s) ≤ 1 := hitProb_le_one B ζ _
  have hN : (1 : ℝ) ≤ (B.card : ℝ) := by
    have h2' : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
    linarith
  have hNpos : (0 : ℝ) < (B.card : ℝ) := lt_of_lt_of_le zero_lt_one hN
  have hdiv : 1 / (B.card : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hNpos, one_mul]; exact hN
  have hdiv0 : 0 ≤ 1 / (B.card : ℝ) := by positivity
  rw [stoppedScore, stoppedScore, Finset.sum_range_succ]
  simp only [add_sub_cancel_left]
  rw [abs_le]
  constructor <;> linarith

/-- **`lem:M lower tail`** (`tex:1194-1197`), reduced to Freedman's two
probabilistic hypotheses.

Given the martingale property of `stoppedScore` (its per-step conditional mean is
zero, `tex:1198-1206`) and the predictable quadratic variation bound `≤ T/N`
(which is the same identity plus `H_ζ² ≤ H_ζ`, `tex:1207-1208`), Freedman's
inequality gives

  `P(M_ζ(T) ≤ −ℓ) ≤ exp(−ℓ² N/(4T))`   for `0 ≤ ℓ ≤ T/(2N)`. -/
theorem stoppedScore_lower_tail_of (h : ℤ) (ζ : Site B) (T : ℕ) (ℓ : ℝ)
    (hT1 : 1 ≤ T)
    (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ (T : ℝ) / (2 * (B.card : ℝ)))
    (hmart : Martingale (fun t ω => stoppedScore B h ζ t ω)
      (idlaFiltration B) (idlaMeasure B))
    (hvar : ∀ᵐ ω ∂(idlaMeasure B), ∑ i ∈ Finset.range T,
        (idlaMeasure B)[fun ω' => (stoppedScore B h ζ (i + 1) ω' - stoppedScore B h ζ i ω') ^ 2
            | idlaFiltration B i] ω ≤ (T : ℝ) / (B.card : ℝ)) :
    idlaMeasure B {ω | stoppedScore B h ζ T ω ≤ -ℓ}
      ≤ ENNReal.ofReal (Real.exp (-(ℓ ^ 2 * (B.card : ℝ) / (4 * T)))) := by
  have hN : (1 : ℝ) ≤ (B.card : ℝ) := by
    have h2' : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
    linarith
  have hNpos : (0 : ℝ) < (B.card : ℝ) := lt_of_lt_of_le zero_lt_one hN
  have hv : 0 ≤ (T : ℝ) / (B.card : ℝ) := div_nonneg (Nat.cast_nonneg T) hNpos.le
  have hmain := LatticeProb.freedman (P := idlaMeasure B) (ℱ := idlaFiltration B)
    (M := fun t ω => stoppedScore B h ζ t ω) (n := T)
    hmart (by funext ω; exact stoppedScore_zero B h ζ ω)
    (b := 1) (v := (T : ℝ) / (B.card : ℝ)) (by norm_num) hv
    (fun i _ ω => abs_stoppedScore_increment B h ζ i ω) hvar ℓ hℓ0
  have h3 : ℓ ≤ 3 * (T : ℝ) / (B.card : ℝ) := by
    have hT : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (B.card : ℝ))] at hℓ
    rw [le_div_iff₀ hNpos]
    nlinarith [hℓ, hT, hN]
  have hge : ℓ ^ 2 * (B.card : ℝ) / (4 * T)
      ≤ ℓ ^ 2 / (2 * ((T : ℝ) / (B.card : ℝ) + 1 * ℓ / 3)) := by
    have hstep : (B.card : ℝ) * (2 * ((T : ℝ) / (B.card : ℝ) + 1 * ℓ / 3))
        ≤ 4 * (T : ℝ) := by
      have h3' : ℓ * (B.card : ℝ) ≤ 3 * (T : ℝ) := by
        rw [le_div_iff₀ hNpos] at h3; linarith [h3]
      field_simp
      nlinarith [h3']
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * T)
      (by positivity : (0 : ℝ) < 2 * ((T : ℝ) / (B.card : ℝ) + 1 * ℓ / 3))]
    nlinarith [hstep, sq_nonneg ℓ]
  have hneg : -(ℓ ^ 2 / (2 * ((T : ℝ) / (B.card : ℝ) + 1 * ℓ / 3)))
      ≤ -(ℓ ^ 2 * (B.card : ℝ) / (4 * T)) := neg_le_neg hge
  calc idlaMeasure B {ω | stoppedScore B h ζ T ω ≤ -ℓ}
      = ENNReal.ofReal ((idlaMeasure B {ω | stoppedScore B h ζ T ω ≤ -ℓ}).toReal) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal
          (Real.exp (-(ℓ ^ 2 / (2 * ((T : ℝ) / (B.card : ℝ) + 1 * ℓ / 3))))) :=
        ENNReal.ofReal_le_ofReal hmain
    _ ≤ ENNReal.ofReal (Real.exp (-(ℓ ^ 2 * (B.card : ℝ) / (4 * T)))) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hneg)

end IdlaCyl
