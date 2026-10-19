/-
The inner-tail bound of `pr:inner` (`paper/idla-cylinder-gff.tex:1160-1165`, `tex:1221-1251`),
assembled from the monotone coupling, the slab union bound, and the per-site estimate of
`BoundaryMeasure.lean` at the paper's constants `C_1 = 2√(ν+4)` and `K_0 = 16 C_1²`.

For `N = |V_N|`, `T ≥ K_0 N log N`, `ℓ_* = C_1 √((T/N) L_T)` with `L_T = log N + log_+(T/N)`, and
`h = ⌊T/N - ℓ_*⌋`, the chain is
`P(A(T) ⊉ R_h) ≤ P(Ā_h(T) ⊉ R_h) ≤ ∑_{ζ ∈ slab} P(ζ ∉ Ā_{ζ_2}(T)) ≤ T e^{-(ν+4)L_T} ≤ N^{-(ν+1)}`.
-/
import IdlaCyl.Support.PrInnerStopped.BoundaryMeasure
import IdlaCyl.Support.PrInnerInclusion
import IdlaCyl.Support.PrInnerTail.SlabUnion
import IdlaCyl.Support.PrInnerTail.Threshold

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open IdlaCyl.PrInnerTail

/-- **The inner-tail bound of `pr:inner`** (`tex:1160-1165`).  With the paper's constants
`C_1 = 2√(ν+4)` and `K_0 = 16 C_1²`, for `N` large (`256 C_1⁴ + 1 ≤ N`) and `T ≥ K_0 N log N`,
the height `h = ⌊T/N - ℓ_*⌋` is at least `1`, and the printed chain holds:
`P(A(T) ⊉ R_h) ≤ P(Ā_h(T) ⊉ R_h) ≤ N^{-(ν+1)}`, where `A(T) = clusterTraj B ω T` is the IDLA
cluster and `Ā_h(T) = stoppedCluster B h ω T` is the stopped cluster.  The first inequality is
`pr_inner_ineq_first`; the second is the slab union bound with the height reduction, the per-site
estimate, and the threshold arithmetic. -/
theorem pr_inner_probability_bound (B : Base) (ν : ℝ) (hν : 0 < ν)
    (hN : 256 * (2 * Real.sqrt (ν + 4)) ^ 4 + 1 ≤ (B.card : ℝ))
    (T : ℕ)
    (hT : 16 * (2 * Real.sqrt (ν + 4)) ^ 2 * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (T : ℝ))
    (h : ℤ)
    (hh_def : h = ⌊(T : ℝ) / (B.card : ℝ)
      - 2 * Real.sqrt (ν + 4)
        * Real.sqrt ((T : ℝ) / (B.card : ℝ) * logTerm (B.card : ℝ) (T : ℝ))⌋) :
    1 ≤ h ∧
      idlaMeasure B {ω : TrajSeq B | ¬ R B (h : ℝ) ⊆ clusterTraj B ω T}
        ≤ idlaMeasure B {ω : TrajSeq B | ¬ R B (h : ℝ) ⊆ stoppedCluster B h ω T} ∧
      idlaMeasure B {ω : TrajSeq B | ¬ R B (h : ℝ) ⊆ stoppedCluster B h ω T}
        ≤ ENNReal.ofReal ((B.card : ℝ) ^ (-(ν + 1))) := by
  have hN2 : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
  have hN1 : (1 : ℝ) ≤ (B.card : ℝ) := by linarith
  have hsq : Real.sqrt (ν + 4) ^ 2 = ν + 4 := Real.sq_sqrt (by linarith)
  have hC0 : (0 : ℝ) ≤ 2 * Real.sqrt (ν + 4) := by positivity
  have hC2 : (2 * Real.sqrt (ν + 4)) ^ 2 = 4 * (ν + 4) := by
    rw [mul_pow, hsq]
    norm_num
  have hlogN : (0 : ℝ) < Real.log (B.card : ℝ) := Real.log_pos (by linarith)
  have hCpos : (0 : ℝ) < 2 * Real.sqrt (ν + 4) := by
    have : (0 : ℝ) < Real.sqrt (ν + 4) := Real.sqrt_pos.mpr (by linarith)
    linarith
  have hTpos : (0 : ℝ) < (T : ℝ) := by
    have : (0 : ℝ) < 16 * (2 * Real.sqrt (ν + 4)) ^ 2 * (B.card : ℝ) * Real.log (B.card : ℝ) := by
      have hN0 : (0 : ℝ) < (B.card : ℝ) := by linarith
      positivity
    linarith
  have hT1 : 1 ≤ T := by
    have : 0 < T := by exact_mod_cast hTpos
    omega
  -- the abbreviations of the paper: `N`, `C_1`, `L_T`, `ℓ_*`
  set N : ℝ := (B.card : ℝ) with hNdef
  set C : ℝ := 2 * Real.sqrt (ν + 4) with hCdef
  set L : ℝ := logTerm N (T : ℝ) with hLdef
  set ℓ : ℝ := C * Real.sqrt ((T : ℝ) / N * L) with hℓdef
  have hℓ0 : 0 ≤ ℓ := mul_nonneg hC0 (Real.sqrt_nonneg _)
  have hLnn : 0 ≤ L := logTerm_nonneg N (T : ℝ) hN1
  -- the threshold lemmas: `ℓ_* ≤ T/(2N)` and the exponent comparison
  have hℓle : ℓ ≤ (T : ℝ) / (2 * N) := ell_star_le_half N (T : ℝ) C hC0 hN hT
  have hCsq : 16 ≤ C ^ 2 := by
    rw [hC2]
    linarith
  have hlog_half : (1 / 2 : ℝ) ≤ Real.log N := by
    have h1 : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hN2
    have h2 : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      norm_num at this ⊢
      linarith
    linarith
  have hprod : 16 * (1 / 2 : ℝ) ≤ C ^ 2 * Real.log N :=
    mul_le_mul hCsq hlog_half (by norm_num) (by positivity)
  have hTN : 8 * C ^ 2 * Real.log N ≤ (T : ℝ) / (2 * N) := by
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * N)]
    nlinarith [hT]
  have hT_over : 1 ≤ (T : ℝ) / (2 * N) := by
    have : (1 : ℝ) ≤ 8 * C ^ 2 * Real.log N := by nlinarith [hprod]
    linarith
  have hNne : N ≠ 0 := ne_of_gt (by linarith)
  have hsplitN : (T : ℝ) / N = 2 * ((T : ℝ) / (2 * N)) := by
    field_simp
  have hmain : (1 : ℝ) ≤ (T : ℝ) / N - ℓ := by linarith
  -- `h ≥ 1`, and `h + ℓ ≤ T/N`
  have hh1 : 1 ≤ h := by
    rw [hh_def]
    exact Int.le_floor.mpr (by push_cast; linarith)
  have hhN : (h : ℝ) + ℓ ≤ (T : ℝ) / N := by
    have hfl := Int.floor_le ((T : ℝ) / N - ℓ)
    rw [← hh_def] at hfl
    linarith
  have hhT : (h : ℝ) ≤ (T : ℝ) / N := by linarith
  have hcoupl := pr_inner_ineq_first B hh1 T
  have hslab := pr_inner_slab_reduced_le B h T
  -- every slab site satisfies the per-site estimate with exponent `(ν+4) L_T`
  have hsite : ∀ ζ ∈ slab B h, idlaMeasure B {ω : TrajSeq B | ζ ∉ stoppedCluster B ζ.2 ω T}
      ≤ ENNReal.ofReal (Real.exp (-((ν + 4) * L))) := by
    intro ζ hζ
    obtain ⟨hζ1, hζ2⟩ := (mem_slab B h ζ).mp hζ
    have hζN : (ζ.2 : ℝ) + ℓ ≤ (T : ℝ) / N := by
      have : (ζ.2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hζ2
      linarith
    refine (measure_not_mem_stoppedCluster_le_exp B ζ.2 hζ1 ζ rfl T hT1 ℓ hℓ0 hℓle hζN).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hexp := ell_star_exponent_ge N (T : ℝ) C ν hN1 hTpos (le_of_eq hC2.symm)
    have hexp' : (ν + 4) * L ≤ ℓ ^ 2 * N / (4 * (T : ℝ)) := by
      rw [hℓdef]
      exact hexp
    exact neg_le_neg hexp'
  -- the slab sum, its cardinality, and the threshold identity
  have hsum : ∑ ζ ∈ slab B h, idlaMeasure B {ω : TrajSeq B | ζ ∉ stoppedCluster B ζ.2 ω T}
      ≤ ENNReal.ofReal (N ^ (-(ν + 1))) := by
    calc ∑ ζ ∈ slab B h, idlaMeasure B {ω : TrajSeq B | ζ ∉ stoppedCluster B ζ.2 ω T}
        ≤ ∑ _ζ ∈ slab B h, ENNReal.ofReal (Real.exp (-((ν + 4) * L))) :=
          Finset.sum_le_sum hsite
      _ = ((slab B h).card : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-((ν + 4) * L))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal (((slab B h).card : ℝ) * Real.exp (-((ν + 4) * L))) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (N ^ (-(ν + 1))) := by
          apply ENNReal.ofReal_le_ofReal
          have hcard : ((slab B h).card : ℝ) ≤ (T : ℝ) := card_slab_le B h T hhT
          have hexp0 : 0 ≤ Real.exp (-((ν + 4) * L)) := (Real.exp_pos _).le
          have hthr := mul_exp_neg_logTerm_le N (T : ℝ) ν hN1 (by positivity) (by linarith)
          rw [neg_mul] at hthr
          calc ((slab B h).card : ℝ) * Real.exp (-((ν + 4) * L))
              ≤ (T : ℝ) * Real.exp (-((ν + 4) * L)) :=
                mul_le_mul_of_nonneg_right hcard hexp0
            _ ≤ N ^ (-(ν + 1)) := hthr
  exact ⟨hh1, hcoupl, hslab.trans hsum⟩

end IdlaCyl
