import IdlaCyl.Support.Replace.ModeExpansion

/-!
The mean-value input in the replacement coefficient estimate (`tex:805-817`).
The derivative bound is obtained from the literal `regular` predicate.
-/

namespace IdlaCyl.Replace

open Defs
open scoped Topology

/-- Each regular coefficient is Lipschitz on a closed neighbourhood of the
reference height, with a nonnegative constant chosen before the two arguments. -/
theorem regular_lipschitz (α : ℕ → ℝ → ℝ) (K : ℕ) (y₀ : ℝ)
    (hα : regular α K y₀) (k : ℕ) (hk : 2 ≤ k) (hkK : k ≤ K) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ∀ x y : ℝ,
      |x - y₀| ≤ r → |y - y₀| ≤ r → |α k x - α k y| ≤ L * |x - y| := by
  obtain ⟨s, hs, hdiff, M, hM⟩ := hα k hk hkK
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hs
  have hin (x : ℝ) (hx : x ∈ Set.Icc (y₀ - r / 2) (y₀ + r / 2)) : x ∈ s := by
    apply hrs
    rw [Metric.mem_ball, Real.dist_eq]
    have habs : |x - y₀| ≤ r / 2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact lt_of_le_of_lt habs (by linarith)
  refine ⟨r / 2, max M 0, by linarith, le_max_right _ _, ?_⟩
  intro x y hx hy
  have hx' : x ∈ Set.Icc (y₀ - r / 2) (y₀ + r / 2) := by
    have hh := abs_le.mp hx
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hy' : y ∈ Set.Icc (y₀ - r / 2) (y₀ + r / 2) := by
    have hh := abs_le.mp hy
    exact ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun z hz => hdiff z (hin z hz))
    (fun z hz => show ‖deriv (α k) z‖ ≤ max M 0 from
      (by simpa only [Real.norm_eq_abs] using (hM z (hin z hz)).trans (le_max_left M 0)))
    (convex_Icc (y₀ - r / 2) (y₀ + r / 2)) hy' hx'
  simpa only [Real.norm_eq_abs] using h

/-- The exponential function is Lipschitz on `[-Q,Q]`, with constant `exp Q`. -/
theorem exp_sub_one_le (Q t : ℝ) (hQ : 0 ≤ Q) (ht : |t| ≤ Q) :
    |Real.exp t - 1| ≤ Real.exp Q * |t| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x (_ : x ∈ Set.Icc (-Q) Q) => Real.differentiableAt_exp)
    (fun x (hx : x ∈ Set.Icc (-Q) Q) => show ‖deriv Real.exp x‖ ≤ Real.exp Q from by
      rw [Real.deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
      exact Real.exp_le_exp.mpr hx.2)
    (convex_Icc (-Q) Q) (show (0 : ℝ) ∈ Set.Icc (-Q) Q by exact ⟨by linarith, hQ⟩)
    (show t ∈ Set.Icc (-Q) Q from abs_le.mp ht)
  simpa only [Real.exp_zero, sub_zero, Real.norm_eq_abs] using h

/-- The mean-value and exponential estimates give the beta bound in
`eq:betabd`. The small parameter is the distance divided by `a`. -/
theorem beta_le (B : Base) (S : SpectralData B) (a : ℝ) (h y : ℤ)
    (α : ℕ → ℝ → ℝ) (k : ℕ) (L A Q δ : ℝ)
    (ha : 0 < a) (hL : 0 ≤ L) (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (hδ1 : δ ≤ 1)
    (hxy : |(y : ℝ) / a - (h : ℝ) / a| ≤ δ)
    (hlip : |α k ((y : ℝ) / a) - α k ((h : ℝ) / a)| ≤
      L * |(y : ℝ) / a - (h : ℝ) / a|)
    (hval : |α k ((h : ℝ) / a)| ≤ A) (hq : |a * S.qk k| ≤ Q) :
    |beta B S a h α y k| ≤ (L + A * Real.exp Q * Q) * δ := by
  have he : S.qk k * ((y : ℝ) - (h : ℝ)) =
      (a * S.qk k) * ((y : ℝ) / a - (h : ℝ) / a) := by
    field_simp [ha.ne']
  have ht : |S.qk k * ((y : ℝ) - (h : ℝ))| ≤ Q * δ := by
    rw [he, abs_mul]
    exact mul_le_mul hq hxy (abs_nonneg _) hQ
  have htQ : |S.qk k * ((y : ℝ) - (h : ℝ))| ≤ Q :=
    ht.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hδ1 hQ)
  have hex : |Real.exp (S.qk k * ((y : ℝ) - (h : ℝ))) - 1| ≤
      Real.exp Q * (Q * δ) :=
    (exp_sub_one_le Q _ hQ htQ).trans
      (mul_le_mul_of_nonneg_left ht (Real.exp_pos Q).le)
  have hd : |α k ((y : ℝ) / a) - α k ((h : ℝ) / a)| ≤ L * δ :=
    hlip.trans (mul_le_mul_of_nonneg_left hxy hL)
  unfold beta
  calc
    _ = |(α k ((y : ℝ) / a) - α k ((h : ℝ) / a)) -
        α k ((h : ℝ) / a) * (Real.exp (S.qk k * ((y : ℝ) - (h : ℝ))) - 1)| := by
      congr 1
      ring
    _ ≤ |α k ((y : ℝ) / a) - α k ((h : ℝ) / a)| +
        |α k ((h : ℝ) / a)| * |Real.exp (S.qk k * ((y : ℝ) - (h : ℝ))) - 1| := by
      simpa only [abs_mul] using abs_sub
        (α k ((y : ℝ) / a) - α k ((h : ℝ) / a))
        (α k ((h : ℝ) / a) * (Real.exp (S.qk k * ((y : ℝ) - (h : ℝ))) - 1))
    _ ≤ L * δ + A * (Real.exp Q * (Q * δ)) :=
      add_le_add hd (mul_le_mul hval hex (abs_nonneg _) hA)
    _ = (L + A * Real.exp Q * Q) * δ := by ring

/-- The zero coefficient family satisfies the printed regularity assumption. -/
theorem regular_zero (K : ℕ) (y₀ : ℝ) : regular (fun _ _ => 0) K y₀ := by
  intro k _ _
  refine ⟨Set.univ, Filter.univ_mem, (fun _ _ => differentiableAt_const _), 0, ?_⟩
  intro y _
  simp only [deriv_const, abs_zero, le_refl]

end IdlaCyl.Replace
