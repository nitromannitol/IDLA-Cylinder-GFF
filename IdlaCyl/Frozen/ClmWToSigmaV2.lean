module

/-
The limit of the rectangular quadratic mass (`clm:W to sigma`,
`paper/idla-cylinder-gff.tex:1040-1043`).

The printed lemma reads: "We have $W_N \to \sigma^2(\phi)$ as $N \to \infty$." The Lean
states that `wmass` (the paper's `W_N`, `tex:904`) tends to `variance` (the paper's
`σ²(φ)`, `tex:407`) as `N → ∞`, under the coefficient regularity `regular` (`tex:401`)
and the spectral assumption `U.SpectralAssumption` (`tex:404`).
-/
public import IdlaCyl.Definitions.RectangularMass
public import IdlaCyl.Support.WnLimit
public import IdlaCyl.Support.RectangularVariance

@[expose] public section

namespace IdlaCyl.Frozen

open IdlaCyl.Defs

/-- The harmonic extension is the mode sum `modeSumPsi` with coefficients `α_k(h/a)`
evaluated at the reference height (`tex:755-758`). -/
private theorem clm_w_to_sigma_v2_harmAt_eq (B : Base) (S : SpectralData B) (a : ℝ) (h : ℤ)
    (K : ℕ) (α : ℕ → ℝ → ℝ) :
    harmAt B S a h K α = modeSumPsi B S h K (fun k => α k ((h : ℝ) / a)) := by
  funext p
  unfold harmAt modeSumPsi exponentialMode
  exact Finset.sum_congr rfl fun k _ => by simp only [mul_assoc]

/-- Algebra of the rescaled rate: for `a ≠ 0`, the exponentials in `Setup.Wn` are the
exponentials of the un-rescaled closed form, `(a q)(h/a) = q h` and `(a q)/a = q`. -/
private theorem clm_w_to_sigma_v2_rescale (a q h : ℝ) (ha : a ≠ 0) :
    Real.exp (-2 * (a * q) * (h / a)) = Real.exp (-2 * q * h) ∧
      Real.exp (-2 * (a * q) / a) = Real.exp (-2 * q) := by
  refine ⟨congrArg Real.exp ?_, congrArg Real.exp ?_⟩
  · rw [show -2 * (a * q) * (h / a) = -2 * q * h * (a / a) by ring, div_self ha, mul_one]
  · rw [div_eq_iff ha]
    ring

/-- For `N ≥ 2` and `K ≤ N`, the rectangular mass `W_N` equals the closed form of
`Setup.Wn`, the finite identity `tex:1045-1052` with `h = ⌊y₀ a_N⌋`. -/
private theorem clm_w_to_sigma_v2_wmass_eq_Wn (U : Setup) (y₀ : ℝ) (K : ℕ) (α : ℕ → ℝ → ℝ)
    (N : ℕ) (hN : 2 ≤ N) (hKN : K ≤ N) :
    wmass U K α y₀ N = Setup.Wn U K α y₀ N := by
  obtain ⟨x⟩ := (U.B N).connected.nonempty
  have hK : K ≤ (U.B N).card := by
    rw [U.card_eq N hN]
    exact hKN
  have hpsi : psi U K α y₀ N = modeSumPsi (U.B N) (U.S N) (height U y₀ N : ℤ) K
      (fun k => α k (((height U y₀ N : ℤ) : ℝ) / U.a N)) :=
    clm_w_to_sigma_v2_harmAt_eq (U.B N) (U.S N) (U.a N) (height U y₀ N : ℤ) K α
  have hmass : wmass U K α y₀ N = ∑ k ∈ Finset.Icc 2 K,
      α k (((height U y₀ N : ℕ) : ℝ) / U.a N) ^ 2 *
        (1 - Real.exp (-2 * (U.S N).qk k * (height U y₀ N : ℝ))) /
          (U.a N * (1 - Real.exp (-2 * (U.S N).qk k))) := by
    have h1 := rectangle_WN_eq_closedForm (U.B N) (U.S N) (U.a N) (U.a_pos N)
      (height U y₀ N) K hK (fun k => α k (((height U y₀ N : ℤ) : ℝ) / U.a N))
      (fun _ _ => (x, 0))
    rw [← hpsi] at h1
    push_cast at h1
    exact h1
  rw [hmass]
  unfold Setup.Wn height
  dsimp only
  refine Finset.sum_congr rfl fun k _ => ?_
  obtain ⟨e1, e2⟩ := clm_w_to_sigma_v2_rescale (U.a N) ((U.S N).qk k)
    ((⌊y₀ * U.a N⌋₊ : ℕ) : ℝ) (U.a_pos N).ne'
  rw [e1, e2]

-- FROZEN-STATEMENT-BEGIN
theorem clm_w_to_sigma_v2 (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K) :
    Filter.Tendsto (fun N => wmass U K α y₀ N) Filter.atTop
      (nhds (variance K α γ y₀))
-- FROZEN-STATEMENT-END
  := by
  have _h2K : 2 ≤ K := hK
  have hcont : ∀ k, 2 ≤ k → k ≤ K → ContinuousAt (α k) y₀ := by
    intro k hk2 hkK
    obtain ⟨s, hs, hd, -⟩ := hα k hk2 hkK
    exact (hd y₀ (mem_of_mem_nhds hs)).continuousAt
  have heq : Filter.EventuallyEq Filter.atTop
      (fun N => Setup.Wn U K α y₀ N) (fun N => wmass U K α y₀ N) := by
    filter_upwards [Filter.eventually_ge_atTop (max K 2)] with N hN
    exact (clm_w_to_sigma_v2_wmass_eq_Wn U y₀ K α N
      (le_trans (le_max_right K 2) hN) (le_trans (le_max_left K 2) hN)).symm
  exact Filter.Tendsto.congr' heq (Setup.Wn_tendsto U γ K hspec α y₀ hy₀ hcont)

/-- Nonvacuity: constant coefficients satisfy `regular` at every `y₀`. -/
example (K : ℕ) (y₀ : ℝ) : regular (fun _ _ => (1 : ℝ)) K y₀ := by
  intro k _ _
  exact ⟨Set.univ, Filter.univ_mem, fun y _ => differentiableAt_const _, 0, fun y _ => by simp⟩

/-- Nonvacuity: for `K = 2` the variance is its `k = 2` term, here with constant
coefficients and rate `1`. -/
example (y₀ : ℝ) :
    variance 2 (fun _ _ => (1 : ℝ)) (fun _ => (1 : ℝ)) y₀ = (1 - Real.exp (-2 * y₀)) / 2 := by
  simp [variance]

end IdlaCyl.Frozen
