/-
The spectral rate limit `a_N q_k^N → γ_k`.

`Assumption a:spectral` (`tex:323-326`) gives
`a_N sqrt(2(1-λ_k^N)) → γ_k`.  Since `q_k^N = arcosh(2 - λ_k^N) = arcosh(1 +
(1-λ_k^N))` and `arcosh(1+x)/sqrt(2x) → 1` (`Support/ArcoshAsymptotic.lean`), and
`1 - λ_k^N → 0`, the two converge together:

  `a_N q_k^N = (a_N sqrt(2(1-λ_k^N))) · (q_k^N / sqrt(2(1-λ_k^N))) → γ_k · 1`.

This is the hypothesis `q_k^N → γ_k` used in `clm:W to sigma` (`tex:1053-1058`).
-/
import IdlaCyl.Support.ArcoshAsymptotic
import IdlaCyl.Support.Spectral

namespace IdlaCyl

open Filter
open scoped Topology

namespace Setup

variable (U : Setup)

/-- **`q_k^N → γ_k`** (`tex:323-326`, `def:qk`): the spectral rates rescaled by
`a_N` converge to the limits asserted by `Assumption a:spectral`. -/
theorem qkN_tendsto (γ : ℕ → ℝ) (K : ℕ) (hspec : U.SpectralAssumption γ K)
    (k : ℕ) (hk : 2 ≤ k) (hkK : k ≤ K) :
    Tendsto (fun N => U.a N * (U.S N).qk k) atTop (𝓝 (γ k)) := by
  have hf : Tendsto (fun N => U.a N * Real.sqrt (2 * (1 - (U.S N).lam k))) atTop
      (𝓝 (γ k)) := (hspec k hk hkK).1
  -- eventually `k ≤ N`, so the spectral data is on its paper range
  have hcard : ∀ᶠ N in atTop, k ≤ (U.B N).card := by
    filter_upwards [eventually_ge_atTop k] with N hN
    rw [U.card_eq N (by omega)]
    exact hN
  have hlt1 : ∀ᶠ N in atTop, (U.S N).lam k < 1 := by
    filter_upwards [hcard] with N hN
    exact lt_of_le_of_lt
      ((U.S N).antitone 2 k (by norm_num) hk hN)
      ((U.S N).lam_two_lt (le_trans hk hN))
  have hxpos : ∀ᶠ N in atTop, 0 < 1 - (U.S N).lam k :=
    hlt1.mono fun N hN => sub_pos.mpr hN
  -- `sqrt(2(1-λ_k)) → 0`
  have hg : Tendsto (fun N => Real.sqrt (2 * (1 - (U.S N).lam k))) atTop (𝓝 0) := by
    refine (hf.div_atTop U.a_tendsto).congr' ?_
    filter_upwards with N
    have ha : U.a N ≠ 0 := ne_of_gt (U.a_pos N)
    field_simp
  -- `1 - λ_k → 0`
  have hx : Tendsto (fun N => 1 - (U.S N).lam k) atTop (𝓝 0) := by
    have h := (hg.pow 2).div_const 2
    have h2 : Tendsto (fun N => 1 - (U.S N).lam k) atTop (𝓝 (0 ^ 2 / 2)) := by
      refine h.congr' ?_
      filter_upwards [hxpos] with N hN
      have hnn : 0 ≤ 2 * (1 - (U.S N).lam k) := by linarith
      rw [Real.sq_sqrt hnn]
      ring
    simpa using h2
  -- the ratio is `arcosh(1+x)/sqrt(2x) → 1`
  have hq : Tendsto (fun N => (U.S N).qk k / Real.sqrt (2 * (1 - (U.S N).lam k)))
      atTop (𝓝 1) := by
    have hxw : Tendsto (fun N => 1 - (U.S N).lam k) atTop (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hx, hxpos.mono fun N hN => by simpa only [Set.mem_Ioi] using hN⟩
    refine (tendsto_arcosh_one_add.comp hxw).congr' ?_
    filter_upwards with N
    simp only [Function.comp_apply]
    rw [SpectralData.qk, show (2 : ℝ) - (U.S N).lam k = 1 + (1 - (U.S N).lam k) by ring]
  -- combine
  have h := hf.mul hq
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [hxpos] with N hN
  have hroot : Real.sqrt (2 * (1 - (U.S N).lam k)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  field_simp

end Setup

end IdlaCyl
