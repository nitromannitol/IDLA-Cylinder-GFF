module

/-
`W_N → σ²(φ)` (`clm:W to sigma`, `tex:1041-1058`).

Using `eqn:psi squared` (`IdlaCyl.psiExt_layer_sq`) and the change of variable
`r = h - y`, the paper writes

  `W_N = ∑_{k=2}^K α_k(h/a_N)² (1 - e^{-2 q_k^N h/a_N}) / (a_N (1 - e^{-2 q_k^N/a_N}))`,

where `h = T/N = ⌊y₀ a_N⌋` and `q_k^N = a_N q_k^N` is the rescaled rate, whose
limit is `γ_k` (`IdlaCyl.Setup.qkN_tendsto`).  This file defines `W_N` in that
closed form and proves the limit `σ²(φ)`.

The analytic content is isolated in `tendsto_one_sub_exp_div` and
`tendsto_varianceFactor`.
-/
public import IdlaCyl.Support.SpectralLimit
public import IdlaCyl.Support.DiscreteVariance

@[expose] public section

namespace IdlaCyl

open Filter
open scoped Topology BigOperators

/-- `(1 - e^u)/u → -1` as `u → 0` away from `0`: the derivative of `exp` at the
origin. -/
theorem tendsto_one_sub_exp_div :
    Tendsto (fun u : ℝ => (1 - Real.exp u) / u) (𝓝[≠] 0) (𝓝 (-1)) := by
  have h := (Real.hasDerivAt_exp (0 : ℝ)).tendsto_slope
  have heq : (fun u : ℝ => (1 - Real.exp u) / u) = fun u : ℝ => -slope Real.exp 0 u := by
    funext u
    simp only [slope, vsub_eq_sub, Real.exp_zero, sub_zero]
    rw [inv_eq_one_div]
    ring
  rw [heq]
  simpa using h.neg

/-- The per-mode analytic limit: with `h_N → y₀`, `q_N → γ > 0` and `a_N → ∞`,
the paper's factor `(1 - e^{-2 q_N h_N})/(a_N (1 - e^{-2 q_N/a_N}))` tends to
`(1 - e^{-2γ y₀})/(2γ)`. -/
theorem tendsto_varianceFactor {a h q : ℕ → ℝ} {y₀ γ : ℝ}
    (ha : Tendsto a atTop atTop) (ha_pos : ∀ N, 0 < a N)
    (hh : Tendsto h atTop (𝓝 y₀)) (hq : Tendsto q atTop (𝓝 γ)) (hγ : 0 < γ) :
    Tendsto (fun N => (1 - Real.exp (-2 * q N * h N)) / (a N * (1 - Real.exp (-2 * q N / a N))))
      atTop (𝓝 ((1 - Real.exp (-2 * γ * y₀)) / (2 * γ))) := by
  -- the denominator tends to `2γ`
  have hqpos : ∀ᶠ N in atTop, 0 < q N := hq.eventually (eventually_gt_nhds hγ)
  have hu : Tendsto (fun N => -2 * q N / a N) atTop (𝓝 0) := by
    have h := (hq.const_mul (-2)).div_atTop ha
    simpa using h
  have hune : ∀ᶠ N in atTop, (-2 * q N / a N) ≠ 0 := by
    filter_upwards [hqpos] with N hN
    have : (-2 * q N) / a N = -(2 * q N / a N) := by ring
    rw [this]
    exact neg_ne_zero.mpr (ne_of_gt (div_pos (by linarith) (ha_pos N)))
  have huw : Tendsto (fun N => -2 * q N / a N) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hu, hune⟩
  have hratio : Tendsto (fun N => (1 - Real.exp (-2 * q N / a N)) / (-2 * q N / a N))
      atTop (𝓝 (-1)) := tendsto_one_sub_exp_div.comp huw
  have hden : Tendsto (fun N => a N * (1 - Real.exp (-2 * q N / a N))) atTop (𝓝 (2 * γ)) := by
    have h := (hq.const_mul (-2)).mul hratio
    have h' : Tendsto (fun N => a N * (1 - Real.exp (-2 * q N / a N))) atTop
        (𝓝 ((-2 * γ) * (-1))) := by
      refine h.congr' ?_
      filter_upwards [hqpos] with N hqN
      have haN' : a N ≠ 0 := ne_of_gt (ha_pos N)
      have hqN' : q N ≠ 0 := ne_of_gt hqN
      field_simp
    simpa using h'
  -- the numerator
  have hnum : Tendsto (fun N => 1 - Real.exp (-2 * q N * h N)) atTop
      (𝓝 (1 - Real.exp (-2 * γ * y₀))) := by
    have harg : Tendsto (fun N => -2 * q N * h N) atTop (𝓝 (-2 * γ * y₀)) := by
      have h := (hq.const_mul (-2)).mul hh
      simpa [mul_assoc, mul_comm, mul_left_comm] using h
    exact tendsto_const_nhds.sub (Real.continuous_exp.tendsto _ |>.comp harg)
  -- divide
  have hden_ne : (2 * γ) ≠ 0 := by positivity
  have hdiv := hnum.div hden hden_ne
  refine hdiv.congr' ?_
  filter_upwards with N
  rfl

namespace Setup

variable (U : Setup)

/-- The paper's `W_N` in the closed form of `eqn:W to sigma` (`tex:1052`), with
`q_k^N = a_N q_k^N` the rescaled rate. -/
noncomputable def Wn (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (N : ℕ) : ℝ :=
  let hN : ℝ := (⌊y₀ * U.a N⌋₊ : ℝ) / U.a N
  ∑ k ∈ Finset.Icc 2 K,
    α k hN ^ 2 * (1 - Real.exp (-2 * (U.a N * (U.S N).qk k) * hN)) /
      (U.a N * (1 - Real.exp (-2 * (U.a N * (U.S N).qk k) / U.a N)))

/-- **`clm:W to sigma`** (`tex:1041-1058`): `W_N → σ²(φ)`. -/
theorem Wn_tendsto (γ : ℕ → ℝ) (K : ℕ) (hspec : U.SpectralAssumption γ K)
    (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (hcont : ∀ k, 2 ≤ k → k ≤ K → ContinuousAt (α k) y₀) :
    Tendsto (fun N => Wn U K α y₀ N) atTop
      (𝓝 (∑ k ∈ Finset.Icc 2 K,
        α k y₀ ^ 2 * (1 - Real.exp (-2 * γ k * y₀)) / (2 * γ k))) := by
  have hfloor : Tendsto (fun N => (⌊y₀ * U.a N⌋₊ : ℝ) / U.a N) atTop (𝓝 y₀) :=
    (tendsto_nat_floor_mul_div_atTop (le_of_lt hy₀)).comp U.a_tendsto
  rw [show (fun N => Wn U K α y₀ N) = fun N =>
      ∑ k ∈ Finset.Icc 2 K,
        α k ((⌊y₀ * U.a N⌋₊ : ℝ) / U.a N) ^ 2 *
          ((1 - Real.exp (-2 * (U.a N * (U.S N).qk k) * ((⌊y₀ * U.a N⌋₊ : ℝ) / U.a N))) /
            (U.a N * (1 - Real.exp (-2 * (U.a N * (U.S N).qk k) / U.a N)))) from by
    funext N; simp only [Wn]; ring_nf]
  refine tendsto_finsetSum _ fun k hk => ?_
  rw [Finset.mem_Icc] at hk
  have hqk : Tendsto (fun N => U.a N * (U.S N).qk k) atTop (𝓝 (γ k)) :=
    U.qkN_tendsto γ K hspec k (by omega) hk.2
  have hγk : 0 < γ k := (hspec k (by omega) hk.2).2
  have hcontk : Tendsto (fun N => α k ((⌊y₀ * U.a N⌋₊ : ℝ) / U.a N) ^ 2) atTop
      (𝓝 (α k y₀ ^ 2)) :=
    ((hcont k (by omega) hk.2).tendsto.comp hfloor).pow 2
  have hfac := tendsto_varianceFactor (a := U.a) (h := fun N => (⌊y₀ * U.a N⌋₊ : ℝ) / U.a N)
    (q := fun N => U.a N * (U.S N).qk k) U.a_tendsto U.a_pos hfloor hqk hγk
  simpa only [mul_div_assoc] using hcontk.mul hfac

end Setup

end IdlaCyl
