import IdlaCyl.Support.Reduction.Block.BlockArith
import IdlaCyl.Support.Reduction.Block.QuantArith
import IdlaCyl.Support.Reduction.Block.SpectralCompare
import IdlaCyl.Support.Reduction.Block.ExplicitComparison
import IdlaCyl.Support.Reduction.TraceGlue
import IdlaCyl.Support.Reduction.CouplingBasic
import IdlaCyl.Support.Obligations

/-!
# The quantitative block reduction, assembled from one block round

Given one block round as a hypothesis `hround`, the cluster at time `T` is coupled with the
cluster at an earlier time `T'`, shifted by a multiple `k` of the number of vertices, with a
failure allowance that is explicit in the base and the spectral data.

The round states that a block of height `H` taken from time `t` is coupled with the cluster
at time `t - N H ⌊t / (2 N H)⌋`, with the explicit allowance `explicitEta`. The proof iterates
the round along the trace of `block_trace`, glues the rounds with `glue_flat_trace`, and bounds
the summed allowances by the explicit constants of `QuantArith`.

The main results are the endpoint couplings:
* `quant_cluster_coupling_of_round`: for every `ε ∈ (0, 1)`, the cluster at time `T` is coupled
  with the cluster at a time `T' < 6 N H`, where `H = ⌈4 √τ_rel log (2 U² / ε)⌉` and `U = max N T`;
* `strong_cluster_coupling_of_round`: with allowance `N^{-(ν+1)}`, the time `T'` is bounded by
  `√τ_rel` and by `√(2 τ_mix)`, up to a logarithm and an explicit constant;
* `alpha_cluster_coupling_of_round`: with allowance `N^{-(ν+1)}`, the time `T'` is bounded by
  `α Defs.sharp B`, once `N` is large enough in terms of `α`, `ν` and `m`.
-/

namespace IdlaCyl.Reduction

open MeasureTheory

/-- The relaxation time is at least one: the gap `1 - λ₂` lies in `(0, 1]`. -/
theorem one_le_relaxTime {B : Base} (S : SpectralData B) (hN : 2 ≤ B.card) :
    1 ≤ S.relaxTime := by
  have hl0 : 0 ≤ S.lam 2 := S.lam_nonneg 2 (by norm_num) hN
  have hl1 : S.lam 2 < 1 := S.lam_two_lt hN
  have hg : 0 < 1 - S.lam 2 := by linarith
  unfold SpectralData.relaxTime SpectralData.gap
  rw [le_div_iff₀ hg]
  linarith

/-- The square root of the relaxation time is at least one. -/
theorem one_le_sqrt_relaxTime {B : Base} (S : SpectralData B) (hN : 2 ≤ B.card) :
    1 ≤ Real.sqrt S.relaxTime := by
  have h := one_le_relaxTime S hN
  simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt h

/-- The quantitative endpoint coupling of the block reduction, from one block round as a
hypothesis. The block height is `H = ⌈4 √τ_rel log (2 U² / ε)⌉` with `U = max N T`; the
time `T'` is below `6 N H`, and the allowance is any `ε ∈ (0, 1)`. -/
theorem quant_cluster_coupling_of_round
    (hround : ∀ (B : Base) (S : SpectralData B) (H t : ℕ), 1 ≤ H → 3 * (2 * (B.card * H)) ≤ t →
      ClusterCoupling B (flatClusterLaw B t)
        (flatClusterLaw B (t - B.card * H * (t / (2 * (B.card * H)))))
        (H * (t / (2 * (B.card * H))))
        ((((t / (2 * (B.card * H)) : ℕ) : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4))
          + 2 * ((t : ℝ) * explicitEta B S H)))
    (B : Base) (S : SpectralData B) (T : ℕ) (hT : 1 ≤ T) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ T' k : ℕ, 1 ≤ T' ∧ T' ≤ T ∧
      T' < 6 * (B.card * ⌈4 * Real.sqrt S.relaxTime * Real.log (2 * ((max B.card T : ℕ) : ℝ) ^ 2 / ε)⌉₊) ∧
      T' + B.card * k = T ∧ ClusterCoupling B (flatClusterLaw B T) (flatClusterLaw B T') k ε := by
  have hN : 2 ≤ B.card := B.nontrivial
  have hcard : 0 < B.card := by omega
  have hcardR : (0 : ℝ) < B.card := by exact_mod_cast hcard
  have hρ1 : 1 ≤ Real.sqrt S.relaxTime := one_le_sqrt_relaxTime S hN
  obtain ⟨U, hU⟩ : ∃ U : ℕ, U = max B.card T := ⟨_, rfl⟩
  have hU1 : 1 ≤ U := by rw [hU]; exact le_max_of_le_left hcard
  have hTU : T ≤ U := by rw [hU]; exact le_max_right _ _
  have hNU : B.card ≤ U := by rw [hU]; exact le_max_left _ _
  rw [← hU]
  obtain ⟨H, hH⟩ : ∃ H : ℕ,
      H = ⌈4 * Real.sqrt S.relaxTime * Real.log (2 * (U : ℝ) ^ 2 / ε)⌉₊ := ⟨_, rfl⟩
  rw [← hH]
  have hU1R : (1 : ℝ) ≤ U := by exact_mod_cast hU1
  have hlog2 : (1 : ℝ) / 4 ≤ Real.log (2 * (U : ℝ) ^ 2 / ε) := by
    have h2 : (2 : ℝ) ≤ 2 * (U : ℝ) ^ 2 / ε := by
      rw [le_div_iff₀ hε]
      nlinarith
    have hl := Real.log_le_log (by norm_num) h2
    have hl2 := Real.log_two_gt_d9
    linarith
  have hx1 : (1 : ℝ) ≤ 4 * Real.sqrt S.relaxTime * Real.log (2 * (U : ℝ) ^ 2 / ε) := by
    have h4 : (1 : ℝ) ≤ 4 * Real.sqrt S.relaxTime := by linarith
    nlinarith [mul_nonneg (sub_nonneg.2 h4) (sub_nonneg.2 hlog2)]
  have hH1R : (1 : ℝ) ≤ H := by
    rw [hH]; exact hx1.trans (Nat.le_ceil _)
  have hH1 : 1 ≤ H := by exact_mod_cast hH1R
  have hH0 : 0 < H := by omega
  obtain ⟨R, t, ℓ, h0, htimes, hsteps, hlast1, hlast2, hvol, hsum, _⟩ :=
    block_trace B.card H T hcard hH0 hT
  -- every step is at least three blocks long
  have hstep : ∀ i : Fin R, 3 * (2 * (B.card * H)) ≤ t i.castSucc := by
    intro i
    obtain ⟨hℓ3, hℓdef, _⟩ := hsteps i
    have h3 : 3 ≤ t i.castSucc / (2 * (B.card * H)) := by rw [← hℓdef]; exact hℓ3
    exact (Nat.le_div_iff_mul_le (Nat.mul_pos (by norm_num) (Nat.mul_pos hcard hH0))).mp h3
  -- the explicit allowance of one step is `(ℓ + 3) ε / (2U)`
  have hstepEps : ∀ i : Fin R, ((ℓ i : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4))
      + 2 * ((t i.castSucc : ℝ) * explicitEta B S H) ≤ ((ℓ i : ℝ) + 3) * (ε / (2 * U)) := by
    intro i
    obtain ⟨_, _, _⟩ := hsteps i
    have htc : t i.castSucc ≤ U := ((htimes i.castSucc).2).trans hTU
    have hNHU : B.card * H ≤ U := by
      have h1 := hstep i
      omega
    have hm := block_mass_le B.card H U (Real.sqrt S.relaxTime) ε hU1 hρ1 hε hε1 hNHU hH
    have hs := stop_exp_le B.card (t i.castSucc) U H (Real.sqrt S.relaxTime) ε hN hNU htc
      hρ1 hε hε1 hH
    have hs' : (t i.castSucc : ℝ) * explicitEta B S H ≤ ε / (2 * U) := by
      unfold explicitEta
      exact hs
    have hA : ((ℓ i : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4))
        ≤ ((ℓ i : ℝ) + 1) * (ε / (2 * U)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    have hB : 2 * ((t i.castSucc : ℝ) * explicitEta B S H) ≤ 2 * (ε / (2 * U)) := by
      linarith
    have hC : ((ℓ i : ℝ) + 3) * (ε / (2 * U))
        = ((ℓ i : ℝ) + 1) * (ε / (2 * U)) + 2 * (ε / (2 * U)) := by ring
    linarith
  -- the summed allowances
  have hsum_le : ∑ i : Fin R, (((ℓ i : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4))
      + 2 * ((t i.castSucc : ℝ) * explicitEta B S H)) ≤ ε := by
    calc _ ≤ ∑ i : Fin R, ((ℓ i : ℝ) + 3) * (ε / (2 * U)) :=
          Finset.sum_le_sum fun i _ => hstepEps i
      _ ≤ ε := block_sum_le ℓ T B.card H U ε hε.le hU1 hTU (fun i => (hsteps i).1) hsum
  -- one round for each step
  have hc : ∀ i : Fin R, ClusterCoupling B (flatClusterLaw B (t i.castSucc))
      (flatClusterLaw B (t i.succ)) (H * ℓ i)
      (((ℓ i : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4))
        + 2 * ((t i.castSucc : ℝ) * explicitEta B S H)) := by
    intro i
    obtain ⟨_, hℓdef, hnext⟩ := hsteps i
    have hh := hround B S H (t i.castSucc) hH1 (hstep i)
    have hnextEq : t i.succ = t i.castSucc - B.card * H * (t i.castSucc / (2 * (B.card * H))) := by
      rw [← hℓdef]; omega
    rw [← hnextEq, ← hℓdef] at hh
    exact hh
  have hε0 : ∀ i : Fin R, 0 ≤ ((ℓ i : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4))
      + 2 * ((t i.castSucc : ℝ) * explicitEta B S H) := fun i =>
    add_nonneg (mul_nonneg (by positivity) (by positivity))
      (mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (explicitEta_nonneg B S H)))
  have hglue := glue_flat_trace B R t (fun i => H * ℓ i)
    (fun i => ((ℓ i : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4))
      + 2 * ((t i.castSucc : ℝ) * explicitEta B S H)) hε0 hc
  rw [h0] at hglue
  have hfin := clusterCoupling_mono B (flatClusterLaw B T) (flatClusterLaw B (t (Fin.last R)))
    (∑ i, H * ℓ i) _ _ hsum_le hglue
  refine ⟨t (Fin.last R), ∑ i, H * ℓ i, hlast1, (htimes (Fin.last R)).2, hlast2, ?_, hfin⟩
  rw [← Finset.mul_sum, ← mul_assoc]
  exact hvol

/-- The strong endpoint coupling: with allowance `N^{-(ν+1)}` and the explicit constants
`6 (4 (ν + 2 m + 2) + 1)`, the time `T'` is bounded by `√τ_rel N log N` and by
`√(2 τ_mix) N log N`, for every `T ≤ N^m`. -/
theorem strong_cluster_coupling_of_round
    (hround : ∀ (B : Base) (S : SpectralData B) (H t : ℕ), 1 ≤ H → 3 * (2 * (B.card * H)) ≤ t →
      ClusterCoupling B (flatClusterLaw B t)
        (flatClusterLaw B (t - B.card * H * (t / (2 * (B.card * H)))))
        (H * (t / (2 * (B.card * H))))
        ((((t / (2 * (B.card * H)) : ℕ) : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4))
          + 2 * ((t : ℝ) * explicitEta B S H)))
    (ν : ℝ) (hν : 0 < ν) (m : ℝ) (hm : 1 ≤ m) (B : Base) (hN : 3 ≤ B.card)
    (S : SpectralData B) (T : ℕ) (hT : 1 ≤ T) (hTm : (T : ℝ) ≤ (B.card : ℝ) ^ m) :
    ∃ T' k : ℕ, 1 ≤ T' ∧ T' ≤ T ∧
     (T' : ℝ) ≤ 6 * (4 * (ν + 2 * m + 2) + 1) * B.card * Real.sqrt S.relaxTime * Real.log B.card ∧
     (T' : ℝ) ≤ Real.sqrt 2 * (6 * (4 * (ν + 2 * m + 2) + 1)) * B.card * Real.sqrt (mixingTime B) * Real.log B.card ∧
     T' + B.card * k = T ∧
     ClusterCoupling B (flatClusterLaw B T) (flatClusterLaw B T') k ((B.card : ℝ) ^ (-(ν + 1))) := by
  have hNR : (3 : ℝ) ≤ B.card := by exact_mod_cast hN
  have hN2 : 2 ≤ B.card := by omega
  have hm0 : 0 ≤ m := by linarith
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = (B.card : ℝ) ^ (-(ν + 1)) := ⟨_, rfl⟩
  have hε : 0 < ε := by
    rw [hεdef]; exact Real.rpow_pos_of_pos (by linarith) _
  have hε1 : ε < 1 := by
    rw [hεdef]; exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  obtain ⟨T', k, h1, hTT, hT', hEq, hcc⟩ :=
    quant_cluster_coupling_of_round hround B S T hT ε hε hε1
  have hlog := log_a_le B.card T (max B.card T) ν m hN hm hTm rfl ε hεdef
  have hH := H_le_log B.card (max B.card T)
    ⌈4 * Real.sqrt S.relaxTime * Real.log (2 * ((max B.card T : ℕ) : ℝ) ^ 2 / ε)⌉₊
    (Real.sqrt S.relaxTime) ν m ε hN (le_max_of_le_left (by omega)) (one_le_sqrt_relaxTime S hN2)
    hε hε1 rfl hlog
  have hT'R : (T' : ℝ) ≤ 6 * ((B.card : ℝ) * ⌈4 * Real.sqrt S.relaxTime *
      Real.log (2 * ((max B.card T : ℕ) : ℝ) ^ 2 / ε)⌉₊) := by
    exact_mod_cast hT'.le
  have hq1 := six_NH_le_quantD B.card
    ⌈4 * Real.sqrt S.relaxTime * Real.log (2 * ((max B.card T : ℕ) : ℝ) ^ 2 / ε)⌉₊
    (Real.sqrt S.relaxTime) ν m hH
  have hq2 := six_NH_le_quantC B.card
    ⌈4 * Real.sqrt S.relaxTime * Real.log (2 * ((max B.card T : ℕ) : ℝ) ^ 2 / ε)⌉₊
    (Real.sqrt S.relaxTime) (mixingTime B : ℝ) ν m hν.le hm0 hN hH
    (sqrt_relaxTime_le S hN2)
  unfold quantD at hq1
  unfold quantC quantD at hq2
  refine ⟨T', k, h1, hTT, ?_, ?_, hEq, ?_⟩
  · linarith
  · linarith
  · rw [← hεdef]; exact hcc

/-- The coupling with a time bound `α Defs.sharp B`, from the block round as a hypothesis, for
`N` large in terms of `α`, `ν` and `m`. The spectral datum is supplied by `spectralData_exists`. -/
theorem alpha_cluster_coupling_of_round
    (hround : ∀ (B : Base) (S : SpectralData B) (H t : ℕ), 1 ≤ H → 3 * (2 * (B.card * H)) ≤ t →
      ClusterCoupling B (flatClusterLaw B t)
        (flatClusterLaw B (t - B.card * H * (t / (2 * (B.card * H)))))
        (H * (t / (2 * (B.card * H))))
        ((((t / (2 * (B.card * H)) : ℕ) : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 4))
          + 2 * ((t : ℝ) * explicitEta B S H)))
    (ν : ℝ) (hν : 0 < ν) (m : ℝ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) (B : Base)
    (hN : max 3 ⌈Real.exp (Real.sqrt 2 * (6 * (4 * (ν + 2 * m + 2) + 1)) / α)⌉₊ ≤ B.card)
    (T : ℕ) (hT : 1 ≤ T) (hTm : (T : ℝ) ≤ (B.card : ℝ) ^ m) :
    ∃ T' k : ℕ, 1 ≤ T' ∧ (T' : ℝ) ≤ α * Defs.sharp B ∧ T' + B.card * k = T ∧
      ClusterCoupling B (flatClusterLaw B T) (flatClusterLaw B T') k ((B.card : ℝ) ^ (-(ν + 1))) := by
  obtain ⟨S⟩ := spectralData_exists B
  have hN3 : 3 ≤ B.card := (le_max_left _ _).trans hN
  have hNC : ⌈Real.exp (Real.sqrt 2 * (6 * (4 * (ν + 2 * m + 2) + 1)) / α)⌉₊ ≤ B.card :=
    (le_max_right _ _).trans hN
  obtain ⟨T', k, h1, _, _, hbound, hT', hcc⟩ :=
    strong_cluster_coupling_of_round hround ν hν m hm B hN3 S T hT hTm
  refine ⟨T', k, h1, ?_, hT', hcc⟩
  have hC := C_mul_le_sharp B (Real.sqrt 2 * (6 * (4 * (ν + 2 * m + 2) + 1))) α hα hN3 hNC
  exact hbound.trans hC

end IdlaCyl.Reduction
