/-
Sequence rectangular closed form and limit. Source: paper/idla-cylinder-gff.tex, tex:1041-1062.
-/
import IdlaCyl.Support.WnLimit
import IdlaCyl.Support.DiscreteVariance
import IdlaCyl.Support.GffSeq.SpectralLimit
import IdlaCyl.Support.Torus.Sequence
/-
`W_N → σ²(φ)` (`clm:W to sigma`, `tex:1041-1058`).

Using `eqn:psi squared` (`IdlaCyl.psiExt_layer_sq`) and the change of variable
`r = h - y`, the paper writes

  `W_N = ∑_{k=2}^K α_k(h/a_N)² (1 - e^{-2 q_k^N h/a_N}) / (a_N (1 - e^{-2 q_k^N/a_N}))`,

where `h = T/N = ⌊y₀ a_N⌋` and `q_k^N = a_N q_k^N` is the rescaled rate, whose
limit is `γ_k` (`IdlaCyl.SequenceSetup.qkN_tendsto`).  This file defines `W_N` in that
closed form and proves the limit `σ²(φ)`.

The analytic content is isolated in `tendsto_one_sub_exp_div` and
`tendsto_varianceFactor`.
-/

namespace IdlaCyl.GffSeq

open Filter
open scoped Topology BigOperators

variable (U : SequenceSetup)

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
    qkN_tendsto U γ K hspec k (by omega) hk.2
  have hγk : 0 < γ k := (hspec k (by omega) hk.2).2
  have hcontk : Tendsto (fun N => α k ((⌊y₀ * U.a N⌋₊ : ℝ) / U.a N) ^ 2) atTop
      (𝓝 (α k y₀ ^ 2)) :=
    ((hcont k (by omega) hk.2).tendsto.comp hfloor).pow 2
  have hfac := tendsto_varianceFactor (a := U.a) (h := fun N => (⌊y₀ * U.a N⌋₊ : ℝ) / U.a N)
    (q := fun N => U.a N * (U.S N).qk k) U.a_tendsto U.a_pos hfloor hqk hγk
  simpa only [mul_div_assoc] using hcontk.mul hfac

end IdlaCyl.GffSeq
