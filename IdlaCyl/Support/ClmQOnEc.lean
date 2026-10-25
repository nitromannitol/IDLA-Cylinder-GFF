module

/-
The canonical `clm:Q on E^c` (`paper/idla-cylinder-gff.tex:915-918`), the first
step in the proof of Theorem 1.3 (`th:GFF`).

The paper's claim is

  `𝔼( Q_N 1_{E^c} ) → 0   as N → ∞`,

where `Q_N = (1/(N a_N)) ∑_{A_+(T)} |ψ|²` (`Support/ClmQWFinal.lean`), `T = N⌊y₀ a_N⌋`,
and `E = goodEvent T Δ_N = {R_{T/N-Δ_N} ⊆ A(T) ⊆ R_{T/N+Δ_N}}`.

This file proves the deterministic and probabilistic inputs of the argument:

* `integral_qN_indicator_compl`: the set-integral form of `𝔼(Q_N 1_{E^c})`;
* `measurableSet_goodEvent`: the good event `E` is measurable;
* `qN_le_slabUpTo`: if `A(T) ⊆ R_h` then `Q_N` is at most the quadratic mass of
  the slab `R_h \ R_0`;
* `slabUpTo_psiExt_le`, `qN_psiExt_le_at_height`: the `eqn:Eh` bound
  `Q_N ≤ (1/(N a_N)) · h · N · ∑_{k=2}^K α_k(h_c/a)² e^{2 q_k(h-h_c)}` on the
  event `A(T) ⊆ R_h` (`tex:941-967`).

## Remaining step

The paper finishes `clm:Q on Ec` (`tex:919-999`) by the annuli decomposition
`E^c = ⋃_{j=2}^J (E_j \ E_{j-1})` with `E_j = {A(T) ⊆ R_{h_j}}`,
`h_2 = ⌈a_N √log N⌉` and `h_j = h_{j-1}⌈a_N/√log N⌉`, using
`P(E_j \ E_{j-1}) ≤ e^{-h_{j-1}}` (`pr:apriori` height tails,
`CanonicalApriori.idlaMeasure_not_subset_le_tsum_layerMean`), and summing
`qN_psiExt_le_at_height` at `h_j`.  The remaining analytic step is the one
already recorded in `CanonicalApriori.lean`: the binomial sum bound
`∑_{m > h} N^{-(m-1)} C(T,m) ≤ e^{-h}` for `T ≥ K_0 N log N`, together with
`J e^{-h_2/2} → 0` and `N^{-ν/2} → 0`.

Note.  A bound `𝔼(Q_N 1_{E^c}) ≤ C · P(E^c)` with a *constant* `C` is false:
`Q_N` is not bounded on `E^c` (the cluster can reach height `T`, where
`|ψ|² ∼ exp(2 q_k (T - T/N))` is enormous).  The paper controls `Q_N` on each
annulus `E_j \ E_{j-1}` by `qN_psiExt_le_at_height` at `h_j` before multiplying
by the height tail.
-/
public import IdlaCyl.Support.ClmQWFinal
public import IdlaCyl.Support.CanonicalApriori
public import IdlaCyl.Support.CanonicalShape

@[expose] public section

namespace IdlaCyl

open MeasureTheory Filter
open scoped BigOperators ENNReal

variable (B : Base)

theorem measurableSet_goodEvent (T : ℕ) (Δ : ℝ) :
    MeasurableSet (goodEvent B T Δ) := by
  simpa only [goodEvent] using
    measurableSet_shapeTraj B T ((T : ℝ) / (B.card : ℝ) - Δ)
      ((T : ℝ) / (B.card : ℝ) + Δ)

theorem integral_qN_indicator_compl (a : ℕ → ℝ) (T : ℕ) (Δ : ℝ) (ψ : Site B → ℝ) :
    ∫ ω, QN B a T ψ ω * (goodEvent B T Δ)ᶜ.indicator (fun _ => (1 : ℝ)) ω
        ∂(idlaMeasure B)
      = ∫ ω in (goodEvent B T Δ)ᶜ, QN B a T ψ ω ∂(idlaMeasure B) := by
  rw [← integral_indicator (measurableSet_goodEvent B T Δ).compl]
  apply integral_congr_ae
  filter_upwards with ω
  by_cases h : ω ∈ (goodEvent B T Δ)ᶜ
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; ring
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; ring

theorem qN_le_slabUpTo (a : ℕ → ℝ) (ha : 0 ≤ a B.card) (T : ℕ) (ψ : Site B → ℝ)
    (ω : TrajSeq B) {h : ℤ} (_h1 : 1 ≤ h) (hsub : clusterTraj B ω T ⊆ R B (h : ℝ)) :
    QN B a T ψ ω ≤ 1 / ((B.card : ℝ) * a B.card) *
      ∑ p ∈ (Finset.univ : Finset B.V).product (Finset.Icc 1 h), ψ p ^ 2 := by
  have hN : (0 : ℝ) < (B.card : ℝ) := by
    have h2 : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
    linarith
  have haN : 0 ≤ 1 / ((B.card : ℝ) * a B.card) :=
    div_nonneg zero_le_one (mul_nonneg (le_of_lt hN) ha)
  unfold QN
  apply mul_le_mul_of_nonneg_left _ haN
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    refine Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
    · exact (mem_clusterPlusFinset_iff B ω T p).mp hp |>.2
    · have hpcl : p ∈ clusterTraj B ω T := mem_clusterPlusFinset_cluster B ω T hp
      have hR := hsub hpcl
      rw [mem_R] at hR
      exact_mod_cast hR
  · intro p _ _; exact sq_nonneg _


/-- The paper's slab up to height `h`: `R_h \ R_0 = V_N × {1, …, h}`, as a `Finset`. -/
noncomputable def slabUpToFinset (h : ℤ) : Finset (Site B) :=
  (Finset.univ : Finset B.V).product (Finset.Icc 1 h)

/-- The quadratic mass over a height slab, for the harmonic extension. -/
theorem slabUpTo_psiExt_le (S : SpectralData B) (hc : ℤ) (K : ℕ) (α : ℕ → ℝ → ℝ)
    (hK : K ≤ B.card) (a : ℝ) {h : ℤ} (hh : 1 ≤ h) :
    ∑ p ∈ slabUpToFinset B h, (psiExt B S hc (psiCoeff K α a hc) p) ^ 2
      ≤ (h : ℝ) * (B.card : ℝ) *
        ∑ k ∈ Finset.Icc 2 K, (α k ((hc : ℝ) / a)) ^ 2 *
          Real.exp (2 * S.qk k * ((h : ℝ) - (hc : ℝ))) := by
  change ∑ p ∈ (Finset.univ : Finset B.V) ×ˢ Finset.Icc 1 h,
      (psiExt B S hc (psiCoeff K α a hc) p) ^ 2 ≤
    (h : ℝ) * (B.card : ℝ) *
      ∑ k ∈ Finset.Icc 2 K, (α k ((hc : ℝ) / a)) ^ 2 *
        Real.exp (2 * S.qk k * ((h : ℝ) - (hc : ℝ)))
  rw [Finset.sum_product]
  rw [Finset.sum_comm]
  have hlayer : ∀ y : ℤ, (∑ x : B.V, (psiExt B S hc (psiCoeff K α a hc) (x, y)) ^ 2)
      = (B.card : ℝ) * ∑ k ∈ Finset.Icc 2 K,
          (α k ((hc : ℝ) / a)) ^ 2 * Real.exp (2 * S.qk k * ((y : ℝ) - (hc : ℝ))) := by
    intro y
    rw [← card_mul_layerMeanSquare B (psiExt B S hc (psiCoeff K α a hc)) y]
    rw [psiExt_psiCoeff_eq_modeSumPsi B S hc K α hK a]
    rw [modeSumPsi_layerMeanSquare B S hc K (fun k => α k ((hc : ℝ) / a)) hK y]
  calc
    ∑ y ∈ Finset.Icc 1 h, ∑ x : B.V, (psiExt B S hc (psiCoeff K α a hc) (x, y)) ^ 2
        = ∑ y ∈ Finset.Icc 1 h, (B.card : ℝ) *
            ∑ k ∈ Finset.Icc 2 K, (α k ((hc : ℝ) / a)) ^ 2 *
              Real.exp (2 * S.qk k * ((y : ℝ) - (hc : ℝ))) := by
          exact Finset.sum_congr rfl fun y _ => hlayer y
    _ ≤ ∑ _y ∈ Finset.Icc 1 h, (B.card : ℝ) *
            ∑ k ∈ Finset.Icc 2 K, (α k ((hc : ℝ) / a)) ^ 2 *
              Real.exp (2 * S.qk k * ((h : ℝ) - (hc : ℝ))) := by
          apply Finset.sum_le_sum
          intro y hy
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg B.card)
          apply Finset.sum_le_sum
          intro k hk
          apply mul_le_mul_of_nonneg_left
          · apply Real.exp_le_exp.mpr
            have hk' := Finset.mem_Icc.mp hk
            have hq : 0 ≤ S.qk k := le_of_lt (S.qk_pos hk'.1 (le_trans hk'.2 hK))
            have hy_le : (y : ℝ) ≤ (h : ℝ) := by
              exact_mod_cast (Finset.mem_Icc.mp hy).2
            nlinarith
          · exact sq_nonneg _
    _ = (h : ℝ) * (B.card : ℝ) *
          ∑ k ∈ Finset.Icc 2 K, (α k ((hc : ℝ) / a)) ^ 2 *
            Real.exp (2 * S.qk k * ((h : ℝ) - (hc : ℝ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have hcard : ((Finset.Icc 1 h).card : ℝ) = (h : ℝ) := by
            rw [Int.card_Icc]
            rw [show (h + 1 - 1 : ℤ) = h from by ring]
            exact_mod_cast Int.toNat_of_nonneg (by omega)
          rw [hcard]
          ring

/-- **`Q_N` on the height event** (`tex:970-967`, `eqn:Eh`): if the cluster is
contained in `R_h`, then `Q_N` is at most
`(1/(N a_N)) · h · N · ∑_{k=2}^K α_k(h_c/a)² e^{2 q_k(h-h_c)}`. -/
theorem qN_psiExt_le_at_height (S : SpectralData B) (K : ℕ) (α : ℕ → ℝ → ℝ)
    (hK : K ≤ B.card) (a : ℝ) (ha : 0 ≤ a) (hc : ℤ) (T : ℕ) (ω : TrajSeq B)
    {h : ℤ} (hh : 1 ≤ h)
    (hsub : clusterTraj B ω T ⊆ R B (h : ℝ)) :
    QN B (fun _ => a) T (psiExt B S hc (psiCoeff K α a hc)) ω
      ≤ 1 / ((B.card : ℝ) * a) *
        ((h : ℝ) * (B.card : ℝ) *
          ∑ k ∈ Finset.Icc 2 K, (α k ((hc : ℝ) / a)) ^ 2 *
            Real.exp (2 * S.qk k * ((h : ℝ) - (hc : ℝ)))) := by
  have hN : (0 : ℝ) < (B.card : ℝ) := by
    have h2 : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
    linarith
  have h1 := qN_le_slabUpTo B (fun _ => a) ha T
    (psiExt B S hc (psiCoeff K α a hc)) ω hh hsub
  change QN B (fun _ => a) T (psiExt B S hc (psiCoeff K α a hc)) ω
      ≤ 1 / ((B.card : ℝ) * a) * ∑ p ∈ slabUpToFinset B h,
        (psiExt B S hc (psiCoeff K α a hc) p) ^ 2 at h1
  have h2 := slabUpTo_psiExt_le B S hc K α hK a hh
  calc QN B (fun _ => a) T (psiExt B S hc (psiCoeff K α a hc)) ω
      ≤ 1 / ((B.card : ℝ) * a) *
          ∑ p ∈ slabUpToFinset B h, (psiExt B S hc (psiCoeff K α a hc) p) ^ 2 := h1
    _ ≤ 1 / ((B.card : ℝ) * a) *
          ((h : ℝ) * (B.card : ℝ) *
            ∑ k ∈ Finset.Icc 2 K, (α k ((hc : ℝ) / a)) ^ 2 *
              Real.exp (2 * S.qk k * ((h : ℝ) - (hc : ℝ)))) :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg zero_le_one (mul_nonneg (le_of_lt hN) ha))

end IdlaCyl
