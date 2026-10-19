/-
The elementary asymptotic behind `Assumption a:spectral` (`tex:323-326`):
`arcosh (1 + x) / sqrt (2 x) → 1` as `x → 0+`.

This is the analytic crux of the paper's `q_k^N ~ sqrt(2(1-λ_k^N))`, which turns
`a_N sqrt(2(1-λ_k^N)) → γ_k` into `a_N q_k^N → γ_k`
(`qkN_tendsto`).  The proof uses the explicit logarithm form of `arcosh` and the
derivative of `log` at `1`.
-/
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace IdlaCyl

open Filter
open scoped Topology

/-- `log (1 + t) / t → 1` as `t → 0` away from `0`: the derivative of `log` at
`1`, written at the origin. -/
theorem tendsto_log_one_add_div :
    Tendsto (fun t : ℝ => Real.log (1 + t) / t) (𝓝[≠] 0) (𝓝 1) := by
  have h := (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope
  have hshift : Tendsto (fun t : ℝ => 1 + t) (𝓝[≠] 0) (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : Continuous fun t : ℝ => 1 + t := continuous_const.add continuous_id
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
      intro h
      exact ht (by linarith)
  have hcomp := h.comp hshift
  have heq : (fun t : ℝ => slope Real.log 1 (1 + t)) = fun t : ℝ => Real.log (1 + t) / t := by
    funext t
    simp only [slope, vsub_eq_sub, Real.log_one, sub_zero, smul_eq_mul]
    rw [inv_eq_one_div]
    ring_nf
  change Tendsto (fun t : ℝ => slope Real.log 1 (1 + t)) (𝓝[≠] 0) (𝓝 1⁻¹) at hcomp
  rw [heq] at hcomp
  simpa using hcomp

/-- **The asymptotic** (`tex:322-326`): `arcosh (1 + x) / sqrt (2 x) → 1` as
`x → 0+`. -/
theorem tendsto_arcosh_one_add :
    Tendsto (fun x : ℝ => Real.arcosh (1 + x) / Real.sqrt (2 * x)) (𝓝[>] 0) (𝓝 1) := by
  have hid : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) :=
    (continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  -- the same expression in the variable `s = sqrt (2 x)`
  have hF : Tendsto (fun s : ℝ => Real.arcosh (1 + s ^ 2 / 2) / s) (𝓝[>] 0) (𝓝 1) := by
    have hphi : Tendsto (fun s : ℝ => s / 2 + Real.sqrt (1 + s ^ 2 / 4)) (𝓝[>] 0) (𝓝 1) := by
      have h1 : Tendsto (fun s : ℝ => s / 2) (𝓝[>] 0) (𝓝 0) := by
        have h := hid.div_const 2
        simpa using h
      have h2 : Tendsto (fun s : ℝ => Real.sqrt (1 + s ^ 2 / 4)) (𝓝[>] 0) (𝓝 1) := by
        have hsq : Tendsto (fun s : ℝ => 1 + s ^ 2 / 4) (𝓝[>] 0) (𝓝 1) := by
          have hs : Tendsto (fun s : ℝ => s ^ 2) (𝓝[>] 0) (𝓝 (0 ^ 2)) := hid.pow 2
          simpa using tendsto_const_nhds.add (hs.div_const 4)
        simpa using hsq.sqrt
      simpa using h1.add h2
    have hsphi : Tendsto (fun s : ℝ => s * (s / 2 + Real.sqrt (1 + s ^ 2 / 4)))
        (𝓝[>] 0) (𝓝 0) := by
      have h := hid.mul hphi
      simpa using h
    have hsphi_ne : Tendsto (fun s : ℝ => s * (s / 2 + Real.sqrt (1 + s ^ 2 / 4)))
        (𝓝[>] 0) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hsphi, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have hspos : 0 < Real.sqrt (1 + s ^ 2 / 4) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg s])
      have h1 : 0 < s / 2 := by linarith [show (0:ℝ) < s from hs]
      exact ne_of_gt (mul_pos hs (by linarith))
    have hlog := tendsto_log_one_add_div.comp hsphi_ne
    have hprod := hphi.mul hlog
    have heq : (fun s : ℝ => (s / 2 + Real.sqrt (1 + s ^ 2 / 4))
          * (Real.log (1 + s * (s / 2 + Real.sqrt (1 + s ^ 2 / 4)))
              / (s * (s / 2 + Real.sqrt (1 + s ^ 2 / 4)))))
        =ᶠ[𝓝[>] 0] fun s : ℝ => Real.arcosh (1 + s ^ 2 / 2) / s := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs0 : 0 ≤ s := le_of_lt hs
      have harg : Real.arcosh (1 + s ^ 2 / 2)
          = Real.log (1 + s * (s / 2 + Real.sqrt (1 + s ^ 2 / 4))) := by
        rw [Real.arcosh]
        congr 1
        have hsq : (1 + s ^ 2 / 2) ^ 2 - 1 = s ^ 2 * (1 + s ^ 2 / 4) := by ring
        rw [hsq, Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs0]
        ring
      have hspos : 0 < Real.sqrt (1 + s ^ 2 / 4) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg s])
      have hphi_ne : s / 2 + Real.sqrt (1 + s ^ 2 / 4) ≠ 0 := by linarith
      have hsne : s ≠ 0 := ne_of_gt hs
      rw [harg]
      field_simp
    have hgoal := Tendsto.congr' heq hprod
    simpa using hgoal
  have hsqrt : Tendsto (fun x : ℝ => Real.sqrt (2 * x)) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h : Tendsto (fun x : ℝ => 2 * x) (𝓝[>] 0) (𝓝 0) := by
        have hcont : Tendsto (fun x : ℝ => 2 * x) (𝓝 0) (𝓝 (2 * 0)) :=
          (continuous_const.mul continuous_id).tendsto 0
        rw [mul_zero] at hcont
        exact hcont.mono_left nhdsWithin_le_nhds
      simpa using h.sqrt
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : (0 : ℝ) < x := hx
      simp only [Set.mem_Ioi]
      exact Real.sqrt_pos.mpr (by linarith)
  refine (hF.comp hsqrt).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (0 : ℝ) < x := hx
  have hsq : (Real.sqrt (2 * x)) ^ 2 = 2 * x := Real.sq_sqrt (by linarith)
  show Real.arcosh (1 + (Real.sqrt (2 * x)) ^ 2 / 2) / Real.sqrt (2 * x)
      = Real.arcosh (1 + x) / Real.sqrt (2 * x)
  rw [hsq]
  ring_nf

end IdlaCyl
