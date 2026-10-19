/-
The height-restricted bound on the rectangular mass in condition (b) of the
proof of `th:GFF` (`paper/idla-cylinder-gff.tex:1088-1102`).

Cauchy–Schwarz over the modes `2 ≤ k ≤ K` at a fixed vertex, together with
Bessel's bound `∑_{k=2}^K f_k(x)² ≤ N`, bounds `ψ(x,y)²/(N a_N)` by
`(1/a_N) ∑_k α_k(h/a_N)² e^{2 q_k (y - h)}`, where `h = ⌊y₀ a_N⌋`.  Below the
height `h + d_N` the exponential is at most `e^{2 q_k d_N}`, and `q_k d_N =
(a_N q_k)(d_N/a_N) → 0`, so the bound tends to zero.
-/
import IdlaCyl.Definitions.RectangularMass
import IdlaCyl.Support.SpectralLimit
import IdlaCyl.Support.EigenBessel
import IdlaCyl.Support.Replace.Asymptotics

namespace IdlaCyl

open IdlaCyl.Defs Filter

/-- Below the height `T/N + d_N`, the rectangular mass integrand `ψ²/(N a_N)`
is bounded by a sequence `b_N` tending to zero, provided `d_N/a_N → 0`. -/
theorem psi_sq_div_le_of_height_le (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀) (K : ℕ) (hK : 2 ≤ K)
    (α : ℕ → ℝ → ℝ) (hα : regular α K y₀) (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K)
    (d : ℕ → ℝ) (hd : Tendsto (fun N => d N / U.a N) atTop (nhds 0)) :
    ∃ b : ℕ → ℝ, Tendsto b atTop (nhds 0) ∧ ∀ᶠ N in atTop, ∀ p : Site (U.B N),
      (p.2 : ℝ) ≤ (height U y₀ N : ℝ) + d N →
        (psi U K α y₀ N p) ^ 2 / ((N : ℝ) * U.a N) ≤ b N := by
  -- `q_k d_N → 0`, since `a_N q_k → γ_k` and `d_N / a_N → 0`
  have hqd : ∀ k, 2 ≤ k → k ≤ K → Tendsto (fun N => (U.S N).qk k * d N) atTop (nhds 0) := by
    intro k hk hkK
    have h := (U.qkN_tendsto γ K hspec k hk hkK).mul hd
    rw [mul_zero] at h
    refine Tendsto.congr (fun N => ?_) h
    have ha : U.a N ≠ 0 := (U.a_pos N).ne'
    field_simp
  -- `exp (2 q_k d_N) → 1`
  have hexp : ∀ k, 2 ≤ k → k ≤ K →
      Tendsto (fun N => Real.exp (2 * ((U.S N).qk k * d N))) atTop (nhds 1) := by
    intro k hk hkK
    have h := (Real.continuous_exp.tendsto (2 * 0)).comp ((hqd k hk hkK).const_mul 2)
    rw [mul_zero, Real.exp_zero] at h
    exact h
  -- the coefficients `α_k(h/a_N)` converge to `α_k(y₀)`
  have hcoef : ∀ k, 2 ≤ k → k ≤ K →
      Tendsto (fun N => α k ((height U y₀ N : ℝ) / U.a N)) atTop (nhds (α k y₀)) := by
    intro k hk hkK
    obtain ⟨s, hs, hdiff, -⟩ := hα k hk hkK
    have hc : ContinuousAt (α k) y₀ := (hdiff y₀ (mem_of_mem_nhds hs)).continuousAt
    exact hc.tendsto.comp (Replace.height_ratio_tendsto U y₀ hy₀.le)
  -- the height-restricted coefficient sum `G_N`
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ → ℝ, ∀ N, G N = ∑ k ∈ Finset.Icc 2 K,
      α k ((height U y₀ N : ℝ) / U.a N) ^ 2 * Real.exp (2 * ((U.S N).qk k * d N)) :=
    ⟨fun N => ∑ k ∈ Finset.Icc 2 K,
      α k ((height U y₀ N : ℝ) / U.a N) ^ 2 * Real.exp (2 * ((U.S N).qk k * d N)),
      fun N => rfl⟩
  have hG : Tendsto G atTop (nhds (∑ k ∈ Finset.Icc 2 K, α k y₀ ^ 2 * 1)) := by
    refine Tendsto.congr (fun N => (hGdef N).symm) ?_
    apply tendsto_finsetSum
    intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
    exact ((hcoef k h1 h2).pow 2).mul (hexp k h1 h2)
  refine ⟨fun N => G N / U.a N, hG.div_atTop U.a_tendsto, ?_⟩
  filter_upwards [eventually_ge_atTop K] with N hKN
  intro p hp
  have hN2 : 2 ≤ N := le_trans hK hKN
  have hcard : (U.B N).card = N := U.card_eq N hN2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  -- the exponents `q_k` are nonnegative on the modes `2 ≤ k ≤ K ≤ N`
  have hq : ∀ k ∈ Finset.Icc 2 K, 0 ≤ (U.S N).qk k := by
    intro k hk
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
    exact ((U.S N).qk_pos h1 (by rw [hcard]; omega)).le
  -- Bessel's bound at the vertex `p.1`
  have hf : ∑ k ∈ Finset.Icc 2 K, (U.S N).f k p.1 ^ 2 ≤ (N : ℝ) := by
    have h := sum_sq_eigen_le_card (U.B N) (U.S N) K (by rw [hcard]; exact hKN) p.1
    rw [hcard] at h
    exact h
  -- the mode expansion of `ψ`
  have hpsi : psi U K α y₀ N p = ∑ k ∈ Finset.Icc 2 K, (U.S N).f k p.1 *
      (α k ((height U y₀ N : ℝ) / U.a N) *
        Real.exp ((U.S N).qk k * ((p.2 : ℝ) - (height U y₀ N : ℝ)))) := by
    simp only [psi, harmAt, Int.cast_natCast]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hsq : ∀ t : ℝ, Real.exp t ^ 2 = Real.exp (2 * t) := fun t => by
    rw [two_mul, Real.exp_add, sq]
  -- the coefficient sum is bounded by the height-restricted sum `G_N`
  have hsum_g : ∑ k ∈ Finset.Icc 2 K,
      (α k ((height U y₀ N : ℝ) / U.a N) *
        Real.exp ((U.S N).qk k * ((p.2 : ℝ) - (height U y₀ N : ℝ)))) ^ 2 ≤ G N := by
    rw [hGdef]
    refine Finset.sum_le_sum fun k hk => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
    have hyd : (U.S N).qk k * ((p.2 : ℝ) - (height U y₀ N : ℝ)) ≤ (U.S N).qk k * d N :=
      mul_le_mul_of_nonneg_left (by linarith) (hq k hk)
    have he : Real.exp ((U.S N).qk k * ((p.2 : ℝ) - (height U y₀ N : ℝ))) ^ 2
        ≤ Real.exp (2 * ((U.S N).qk k * d N)) := by
      rw [hsq]
      exact Real.exp_le_exp.mpr (by linarith)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left he (sq_nonneg _)
  have hpsi_sq : (psi U K α y₀ N p) ^ 2 ≤ (N : ℝ) * G N := by
    rw [hpsi]
    refine le_trans (Finset.sum_mul_sq_le_sq_mul_sq _ _ _) ?_
    exact mul_le_mul hf hsum_g (Finset.sum_nonneg fun k _ => sq_nonneg _) (Nat.cast_nonneg N)
  calc (psi U K α y₀ N p) ^ 2 / ((N : ℝ) * U.a N)
      ≤ ((N : ℝ) * G N) / ((N : ℝ) * U.a N) :=
        div_le_div_of_nonneg_right hpsi_sq (mul_pos hNpos (U.a_pos N)).le
    _ = G N / U.a N := mul_div_mul_left _ _ hNpos.ne'

end IdlaCyl
