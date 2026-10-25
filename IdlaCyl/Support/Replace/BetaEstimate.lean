module

public import IdlaCyl.Support.Replace.Asymptotics
public import IdlaCyl.Support.Replace.CoefficientRegularity
public import IdlaCyl.Support.SpectralLimit

@[expose] public section

/-!
The uniform coefficient and layer bounds in the replacement lemma
(`tex:805-826`). They follow from the printed regularity and spectral
assumptions and from `d_N/a_N → 0`.
-/

namespace IdlaCyl.Replace

open Defs Filter
open scoped Topology BigOperators

/-- For each fixed mode, the beta coefficient is uniformly `O(d_N/a_N)`
on every layer of the shape slab. -/
theorem eventually_beta_le (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K)
    (d : ℕ → ℝ) (hd : ∀ N, 0 < d N)
    (hwidth : Tendsto (fun N => d N / U.a N) atTop (nhds 0))
    (k : ℕ) (hk : 2 ≤ k) (hkK : k ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N in atTop, ∀ y ∈ slabHeights (U.B N) (time U y₀ N) (d N),
      |beta (U.B N) (U.S N) (U.a N) (height U y₀ N : ℤ) α y k| ≤ C * (d N / U.a N) := by
  obtain ⟨r, L, hr, hL, hlip⟩ := regular_lipschitz α K y₀ hα k hk hkK
  let A := |α k y₀| + L * r
  let Q := |γ k| + 1
  have hA : 0 ≤ A := add_nonneg (abs_nonneg _) (mul_nonneg hL hr.le)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hheight : Tendsto (fun N => |(height U y₀ N : ℝ) / U.a N - y₀|)
      atTop (nhds 0) := by
    simpa only [sub_self, abs_zero] using
      ((height_ratio_tendsto U y₀ hy₀.le).sub (tendsto_const_nhds (x := y₀))).abs
  have hclose : ∀ᶠ N in atTop, |(height U y₀ N : ℝ) / U.a N - y₀| + d N / U.a N < r := by
    have hlim : Tendsto (fun N => |(height U y₀ N : ℝ) / U.a N - y₀| + d N / U.a N)
        atTop (nhds 0) := by simpa only [add_zero] using hheight.add hwidth
    exact hlim.eventually (gt_mem_nhds hr)
  have hsmall : ∀ᶠ N in atTop, d N / U.a N < 1 :=
    hwidth.eventually (gt_mem_nhds zero_lt_one)
  have hq : ∀ᶠ N in atTop, |U.a N * (U.S N).qk k| < Q :=
    (U.qkN_tendsto γ K hspec k hk hkK).abs.eventually (gt_mem_nhds (lt_add_one _))
  refine ⟨L + A * Real.exp Q * Q, add_nonneg hL
    (mul_nonneg (mul_nonneg hA (Real.exp_pos Q).le) hQ), ?_⟩
  filter_upwards [hclose, hsmall, hq] with N hcloseN hsmallN hqN
  intro y hy
  have ha := U.a_pos N
  have hδ : 0 ≤ d N / U.a N := (div_pos (hd N) ha).le
  have hhn : |(height U y₀ N : ℝ) / U.a N - y₀| ≤ r := by linarith
  have hdist : |(y : ℝ) / U.a N - (height U y₀ N : ℝ) / U.a N| ≤ d N / U.a N := by
    rw [← sub_div, abs_div, abs_of_pos ha]
    exact div_le_div_of_nonneg_right (slabHeights_abs_sub_le U y₀ N (d N) y hy) ha.le
  have hyn : |(y : ℝ) / U.a N - y₀| ≤ r := by
    calc
      _ = |((y : ℝ) / U.a N - (height U y₀ N : ℝ) / U.a N) +
          ((height U y₀ N : ℝ) / U.a N - y₀)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ r := by linarith
  have hval : |α k ((height U y₀ N : ℝ) / U.a N)| ≤ A := by
    have h := hlip ((height U y₀ N : ℝ) / U.a N) y₀ hhn
      (by simp only [sub_self, abs_zero]; exact hr.le)
    calc
      _ ≤ |α k ((height U y₀ N : ℝ) / U.a N) - α k y₀| + |α k y₀| := by
        simpa only [sub_add_cancel] using abs_add_le
          (α k ((height U y₀ N : ℝ) / U.a N) - α k y₀) (α k y₀)
      _ ≤ L * r + |α k y₀| := add_le_add
        (h.trans (mul_le_mul_of_nonneg_left hhn hL)) le_rfl
      _ = A := by dsimp only [A]; ring
  simpa only [Int.cast_natCast] using beta_le (U.B N) (U.S N) (U.a N)
    (height U y₀ N : ℤ) y α k L A Q (d N / U.a N) ha hL hA hQ hsmallN.le
    (by simpa only [Int.cast_natCast] using hdist)
    (by simpa only [Int.cast_natCast] using
      hlip ((y : ℝ) / U.a N) ((height U y₀ N : ℝ) / U.a N) hyn hhn)
    (by simpa only [Int.cast_natCast] using hval) hqN.le

/-- The uniform layer bound `eq:layerL2`, with all coefficient bounds derived
from regularity and the finite spectral assumption. -/
theorem eventually_error_layerMeanSquare_le (U : Setup) (y₀ : ℝ) (hy₀ : 0 < y₀)
    (K : ℕ) (α : ℕ → ℝ → ℝ) (hα : regular α K y₀)
    (γ : ℕ → ℝ) (hspec : U.SpectralAssumption γ K)
    (d : ℕ → ℝ) (hd : ∀ N, 0 < d N)
    (hwidth : Tendsto (fun N => d N / U.a N) atTop (nhds 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N in atTop,
      ∀ y ∈ slabHeights (U.B N) (time U y₀ N) (d N),
        layerMeanSquare (U.B N)
          (fun p => testAt (U.B N) (U.S N) (U.a N) K α p - psi U K α y₀ N p) y ≤
            C * (d N / U.a N) ^ 2 := by
  classical
  let s := Finset.Icc 2 K
  have hex (k : s) : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N in atTop,
      ∀ y ∈ slabHeights (U.B N) (time U y₀ N) (d N),
        |beta (U.B N) (U.S N) (U.a N) (height U y₀ N : ℤ) α y k| ≤ C * (d N / U.a N) :=
    eventually_beta_le U y₀ hy₀ K α hα γ hspec d hd hwidth k
      (Finset.mem_Icc.mp k.property).1 (Finset.mem_Icc.mp k.property).2
  choose c hc he using hex
  let cc (k : ℕ) := if hk : k ∈ s then c ⟨k, hk⟩ else 0
  let C : ℝ := ∑ k ∈ s, (cc k) ^ 2
  have hcall : ∀ᶠ N in atTop, ∀ k : s,
      ∀ y ∈ slabHeights (U.B N) (time U y₀ N) (d N),
        |beta (U.B N) (U.S N) (U.a N) (height U y₀ N : ℤ) α y k| ≤
          c k * (d N / U.a N) := Filter.eventually_all.2 he
  refine ⟨C, Finset.sum_nonneg (fun _ _ => sq_nonneg _), ?_⟩
  filter_upwards [hcall, eventually_ge_atTop (max K 2)] with N hN hlarge
  intro y hy
  have hK : K ≤ (U.B N).card := by rw [U.card_eq N (by omega)]; omega
  change layerMeanSquare (U.B N) (fun p => testAt (U.B N) (U.S N) (U.a N) K α p -
    harmAt (U.B N) (U.S N) (U.a N) (height U y₀ N : ℤ) K α p) y ≤ _
  rw [error_layerMeanSquare (U.B N) (U.S N) (U.a N) (height U y₀ N : ℤ) K α hK]
  calc
    _ ≤ ∑ k ∈ s, (cc k) ^ 2 * (d N / U.a N) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hcoeff := hN ⟨k, hk⟩ y hy
      have hpos : 0 ≤ c ⟨k, hk⟩ * (d N / U.a N) :=
        mul_nonneg (hc ⟨k, hk⟩) (div_nonneg (hd N).le (U.a_pos N).le)
      have hs := (sq_le_sq₀ (abs_nonneg _) hpos).mpr hcoeff
      have hcc : cc k = c ⟨k, hk⟩ := dif_pos hk
      rw [hcc]
      simpa only [sq_abs, mul_pow] using hs
    _ = C * (d N / U.a N) ^ 2 := by rw [Finset.sum_mul]

end IdlaCyl.Replace
