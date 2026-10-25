module

/-
The martingale array of the Gaussian fluctuation proof (`paper/idla-cylinder-gff.tex:893-912`).

The increments are `𝒳_{k,N} = (N a_N)^{-1/2} ψ(X_k, Y_k)` (`tex:893-897`), where
`(X_k, Y_k)` is the settling site of the `k`-th walker.  Their partial sums
`M_N(t) = ∑_{k ≤ t} 𝒳_{k,N}` form a martingale for the natural filtration of the
IDLA process, and `Q_N = ∑_k 𝒳_{k,N}²` is the quadratic mass.

The partial sums are a constant multiple of the harmonic martingale `M(t)` of
`le:martingale`, so the martingale property is inherited from
`Frozen.le_martingale_v2`.  The almost-sure identities with the pairing and with
the quadratic mass use `harmonicMartingale_eq_pairing`, `clusterPlusFinset_eq_image`
and `range_settleSite_injective`.
-/
public import IdlaCyl.Frozen.LeMartingaleV2
public import IdlaCyl.Definitions.ShapeEvent
public import IdlaCyl.Support.PsiSlab
public import IdlaCyl.Support.HarmonicExtension
public import IdlaCyl.Support.Martingale
public import IdlaCyl.Support.CanonicalExit
public import IdlaCyl.Support.Replace.ModeExpansion

@[expose] public section

namespace IdlaCyl

open IdlaCyl.Defs Filter MeasureTheory

/-- The normalised increment `𝒳_{k,N} = ψ(X_k, Y_k)/√(N a_N)` (`tex:893-897`), with
`ψ = psi U K α y₀ N` evaluated at the settling site of the `k`-th walker. -/
noncomputable def gffIncrement (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (N k : ℕ)
    (ω : TrajSeq (U.B N)) : ℝ :=
  (Real.sqrt ((N : ℝ) * U.a N))⁻¹ * psi U K α y₀ N (settleSite (U.B N) ω k)

/-- The mode-sum harmonic extension is the `psiExt` of the truncated coefficients. -/
private theorem gffIncrement_harmAt_eq (B : Base) (S : SpectralData B) (a : ℝ) (h : ℤ)
    (K : ℕ) (α : ℕ → ℝ → ℝ) (hK : K ≤ B.card) :
    harmAt B S a h K α = psiExt B S h (psiCoeff K α a h) := by
  rw [psiExt_psiCoeff_eq_modeSumPsi B S h K α hK a]
  funext p
  simp only [harmAt, modeSumPsi, exponentialMode, mul_assoc]

/-- The truncated mode sum is discrete harmonic. -/
private theorem gffIncrement_harmAt_harmonic (B : Base) (S : SpectralData B) (a : ℝ) (h : ℤ)
    (K : ℕ) (α : ℕ → ℝ → ℝ) (hK : K ≤ B.card) :
    DiscreteHarmonic B (harmAt B S a h K α) := by
  rw [gffIncrement_harmAt_eq B S a h K α hK]
  exact psiExt_discreteHarmonic B S h _

/-- The truncated mode sum has zero horizontal average on every layer, as the
difference of the test function and its error. -/
private theorem gffIncrement_harmAt_zeroAverage (B : Base) (S : SpectralData B) (a : ℝ)
    (h : ℤ) (K : ℕ) (α : ℕ → ℝ → ℝ) (hK : K ≤ B.card) :
    ZeroHorizontalAverage B (harmAt B S a h K α) := by
  intro y
  have hsplit : ∑ x : B.V, harmAt B S a h K α (x, y)
      = ∑ x : B.V, testAt B S a K α (x, y)
        - ∑ x : B.V, (testAt B S a K α (x, y) - harmAt B S a h K α (x, y)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have h1 : ∑ x : B.V, testAt B S a K α (x, y) = 0 :=
    Replace.testAt_zeroHorizontalAverage B S a K α hK y
  have h2 : ∑ x : B.V, (testAt B S a K α (x, y) - harmAt B S a h K α (x, y)) = 0 :=
    Replace.error_zeroHorizontalAverage B S a h K α hK y
  rw [hsplit, h1, h2, sub_zero]

/-- A mode sum `∑_{k=2}^N α_k f_k e^{q_k(y-h)}` decays downwards at the rate `q_2`
for every reference height `h`: below level `0` the factor `e^{-q_k h}` is a
constant, and `q_k ≥ q_2` gives `e^{q_k y} ≤ e^{q_2 y}`. -/
private theorem gffIncrement_psiExt_expDecayBelow (B : Base) (S : SpectralData B) (h : ℤ)
    (α : ℕ → ℝ) : ExpDecayBelow B (psiExt B S h α) := by
  have hqc : ∀ k ∈ Finset.Icc 2 B.card, S.qk 2 ≤ S.qk k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hx1 : 0 < 2 - S.lam 2 := by
      have := S.lam_two_lt B.nontrivial
      linarith
    have hx2 : 0 < 2 - S.lam k := by
      have hle1 : S.lam k ≤ 1 := by
        calc S.lam k ≤ S.lam 1 := S.antitone 1 k le_rfl (by omega) hk.2
          _ = 1 := S.lam_one
      linarith
    exact (Real.arcosh_le_arcosh hx1 hx2).mpr (by
      have := S.antitone 2 k (by norm_num) hk.1 hk.2
      linarith)
  refine ⟨∑ k ∈ Finset.Icc 2 B.card, |α k| * (∑ x : B.V, |S.f k x|) * Real.exp (-(S.qk k * h)),
    S.qk 2, S.qk_pos le_rfl B.nontrivial, fun p hp => ?_⟩
  have hy : (p.2 : ℝ) ≤ 0 := by exact_mod_cast hp
  calc |psiExt B S h α p|
      ≤ ∑ k ∈ Finset.Icc 2 B.card,
          |α k| * |S.f k p.1| * Real.exp (S.qk k * ((p.2 : ℝ) - (h : ℝ))) := by
        rw [psiExt]
        refine (Finset.abs_sum_le_sum_abs
          (fun k => α k * exponentialMode B (S.f k) (S.qk k) (h : ℝ) p)
          (Finset.Icc 2 B.card)).trans ?_
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        unfold exponentialMode
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact le_of_eq (mul_assoc _ _ _).symm
    _ ≤ ∑ k ∈ Finset.Icc 2 B.card,
          |α k| * (∑ x : B.V, |S.f k x|) * Real.exp (-(S.qk k * h)) * Real.exp (S.qk 2 * p.2) := by
        apply Finset.sum_le_sum
        intro k hk
        have hα : 0 ≤ |α k| := abs_nonneg _
        have hS : 0 ≤ ∑ x : B.V, |S.f k x| := Finset.sum_nonneg fun x _ => abs_nonneg _
        have hf : |S.f k p.1| ≤ ∑ x : B.V, |S.f k x| :=
          Finset.single_le_sum (f := fun x => |S.f k x|) (fun x _ => abs_nonneg _)
            (Finset.mem_univ p.1)
        have hexp : Real.exp (S.qk k * ((p.2 : ℝ) - (h : ℝ)))
            ≤ Real.exp (-(S.qk k * h)) * Real.exp (S.qk 2 * p.2) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hm := mul_le_mul_of_nonpos_right (hqc k hk) hy
          linarith
        have h1 : |α k| * |S.f k p.1| * Real.exp (S.qk k * ((p.2 : ℝ) - (h : ℝ)))
            ≤ |α k| * (∑ x : B.V, |S.f k x|) * Real.exp (S.qk k * ((p.2 : ℝ) - (h : ℝ))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf hα) (Real.exp_pos _).le
        have h2 : |α k| * (∑ x : B.V, |S.f k x|) * Real.exp (S.qk k * ((p.2 : ℝ) - (h : ℝ)))
            ≤ |α k| * (∑ x : B.V, |S.f k x|) *
              (Real.exp (-(S.qk k * h)) * Real.exp (S.qk 2 * p.2)) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hα hS)
        exact h1.trans (h2.trans (le_of_eq (by ring)))
    _ = (∑ k ∈ Finset.Icc 2 B.card,
          |α k| * (∑ x : B.V, |S.f k x|) * Real.exp (-(S.qk k * h))) * Real.exp (S.qk 2 * p.2) := by
        rw [Finset.sum_mul]

/-- The truncated mode sum decays downwards (`ExpDecayBelow`). -/
private theorem gffIncrement_harmAt_expDecay (B : Base) (S : SpectralData B) (a : ℝ)
    (h : ℤ) (K : ℕ) (α : ℕ → ℝ → ℝ) (hK : K ≤ B.card) :
    ExpDecayBelow B (harmAt B S a h K α) := by
  rw [gffIncrement_harmAt_eq B S a h K α hK]
  exact gffIncrement_psiExt_expDecayBelow B S h _

/-- The partial sum of the increments is `√(N a_N)⁻¹ · N` times the harmonic
statistic of `le:martingale`, for every time and every trajectory. -/
private theorem gffIncrement_sum_eq_card_mul (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ)
    (y₀ : ℝ) (N : ℕ) (t : ℕ) (ω : TrajSeq (U.B N)) :
    ∑ k ∈ Finset.range t, gffIncrement U K α y₀ N k ω
      = ((Real.sqrt ((N : ℝ) * U.a N))⁻¹ * ((U.B N).card : ℝ))
        * harmonicMartingale (U.B N) (psi U K α y₀ N) t ω := by
  have hc : ((U.B N).card : ℝ) ≠ 0 := by
    have h2 := (U.B N).nontrivial
    have h3 : (U.B N).card ≠ 0 := by
      change Fintype.card (U.B N).V ≠ 0
      omega
    exact_mod_cast h3
  unfold gffIncrement harmonicMartingale
  rw [← Finset.mul_sum]
  field_simp

/-- **The martingale property** (`tex:893-912`): the partial sums of the increments
`𝒳_{k,N}` form a martingale for the natural filtration of the IDLA process. -/
theorem gffIncrement_martingale (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (N : ℕ)
    (hK : K ≤ (U.B N).card) :
    Martingale (fun t ω => ∑ k ∈ Finset.range t, gffIncrement U K α y₀ N k ω)
      (idlaFiltration (U.B N)) (idlaMeasure (U.B N)) := by
  have hharm : DiscreteHarmonic (U.B N) (psi U K α y₀ N) :=
    gffIncrement_harmAt_harmonic (U.B N) (U.S N) (U.a N) (height U y₀ N : ℤ) K α hK
  have hzero : ZeroHorizontalAverage (U.B N) (psi U K α y₀ N) :=
    gffIncrement_harmAt_zeroAverage (U.B N) (U.S N) (U.a N) (height U y₀ N : ℤ) K α hK
  have hdecay : ExpDecayBelow (U.B N) (psi U K α y₀ N) :=
    gffIncrement_harmAt_expDecay (U.B N) (U.S N) (U.a N) (height U y₀ N : ℤ) K α hK
  have hM := Martingale.smul ((Real.sqrt ((N : ℝ) * U.a N))⁻¹ * ((U.B N).card : ℝ))
    (Frozen.le_martingale_v2 (U.B N) (psi U K α y₀ N) hharm hzero hdecay)
  convert hM using 1
  funext t ω
  simp only [Pi.smul_apply, smul_eq_mul]
  exact gffIncrement_sum_eq_card_mul U K α y₀ N t ω

/-- **The pairing identity** (`tex:893-912`): almost surely, the partial sum of the
increments is `√(N a_N)⁻¹` times the pairing `⟪D_t, ψ⟫`. -/
theorem gffIncrement_sum_eq_pairing (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (N : ℕ)
    (hN : 2 ≤ N) (hK : K ≤ (U.B N).card) (t : ℕ) :
    ∀ᵐ ω ∂idlaMeasure (U.B N), ∑ k ∈ Finset.range t, gffIncrement U K α y₀ N k ω =
      (Real.sqrt ((N : ℝ) * U.a N))⁻¹ * pairingTraj (U.B N) ω t (psi U K α y₀ N) := by
  have hharm : DiscreteHarmonic (U.B N) (psi U K α y₀ N) :=
    gffIncrement_harmAt_harmonic (U.B N) (U.S N) (U.a N) (height U y₀ N : ℤ) K α hK
  have hzero : ZeroHorizontalAverage (U.B N) (psi U K α y₀ N) :=
    gffIncrement_harmAt_zeroAverage (U.B N) (U.S N) (U.a N) (height U y₀ N : ℤ) K α hK
  have hc : ((U.B N).card : ℝ) ≠ 0 := by
    have h3 : (U.B N).card ≠ 0 := by
      rw [U.card_eq N hN]
      omega
    exact_mod_cast h3
  filter_upwards [harmonicMartingale_eq_pairing (U.B N) (psi U K α y₀ N) hzero t] with ω hω
  rw [gffIncrement_sum_eq_card_mul U K α y₀ N t ω, hω]
  field_simp

/-- **The quadratic mass** (`tex:1005-1009`): almost surely, the sum of the squared
increments up to the paper's time `T = N ⌊y₀ a_N⌋` is the quadratic mass `Q_N`. -/
theorem gffIncrement_sq_sum_eq_qmass (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (N : ℕ)
    (hN : 2 ≤ N) :
    ∀ᵐ ω ∂idlaMeasure (U.B N), ∑ k ∈ Finset.range (time U y₀ N), (gffIncrement U K α y₀ N k ω) ^ 2
      = qmass U K α y₀ N ω := by
  have hall : ∀ᵐ ω ∂idlaMeasure (U.B N), ∀ j, exitTime' (U.B N) (clusterTraj (U.B N) ω j) (ω j) ≠ ⊤ :=
    MeasureTheory.ae_all_iff.mpr fun j => exitTraj_ae_finite (U.B N) j
  filter_upwards [hall] with ω hω
  have hinj := range_settleSite_injective (U.B N) ω (time U y₀ N) hω
  have hcard : (U.B N).card = N := U.card_eq N hN
  have hpos : 0 < (N : ℝ) * U.a N :=
    mul_pos (by exact_mod_cast (show 0 < N by omega)) (U.a_pos N)
  have hcoef : (Real.sqrt ((N : ℝ) * U.a N))⁻¹ ^ 2 = 1 / ((N : ℝ) * U.a N) := by
    rw [inv_pow, Real.sq_sqrt hpos.le, one_div]
  have hL : ∀ k, (gffIncrement U K α y₀ N k ω) ^ 2
      = 1 / ((N : ℝ) * U.a N) * psi U K α y₀ N (settleSite (U.B N) ω k) ^ 2 := by
    intro k
    unfold gffIncrement
    rw [mul_pow, hcoef]
  rw [Finset.sum_congr rfl (fun k _ => hL k), ← Finset.mul_sum]
  unfold qmass QN
  rw [hcard, clusterPlusFinset_eq_image (U.B N) ω (time U y₀ N) hω,
    Finset.sum_image (fun i hi j hj h => hinj i hi j hj h)]

end IdlaCyl
