import IdlaCyl.Support.Reduction.Assemble
import IdlaCyl.Support.Reduction.TraceGlue
import IdlaCyl.Support.Reduction.CouplingBasic
import IdlaCyl.Support.Reduction.MixingScale
import IdlaCyl.Support.Reduction.Block.BlockArith

/-!
# Assembly of the block reduction

For every `ν > 0` and `m ≥ 1` there is a cutoff `N₀` such that, for every base with at least
`N₀` vertices and every time `0 < T ≤ N^m`, the flat cluster at time `T` is coupled with the
flat cluster at some time `T' ≤ α T^♯` (where `T^♯ = Defs.sharp B`), shifted by some `k` with
`T' + N k = T`, with failure allowance `N^{-(ν+1)}`.

The proof iterates one block round along the trace of `block_trace`, glues the rounds with
`glue_flat_trace`, and bounds the summed failure allowances by `block_error_sum`. The round
is taken as a hypothesis: the statement `hround` is the conclusion of a single block round,
with the block height `H`, the time `t`, and the failure allowance written out.
-/

namespace IdlaCyl.Reduction

open MeasureTheory

/-- The cluster coupling of the block reduction at a fixed coefficient `α`, from the block
round as a hypothesis. The round exponent is `q = ⌈m⌉₊` and the round failure exponent is
`γ = ν + q + 2`; the block height `H = ⌈B₀ √τ log N⌉₊` and the cutoff are chosen after `α`. -/
theorem block_cluster_coupling_of_round
    (hround : ∀ (r : ℕ) (p : ℝ), 0 < p → ∃ b : ℝ, 1 ≤ b ∧ ∃ N₀ : ℕ, ∀ B : Base,
      N₀ ≤ B.card → ∀ H t : ℕ, 1 ≤ H →
      b * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ) ≤ (H : ℝ) →
      0 < t → t ≤ B.card ^ r → 3 * (2 * (B.card * H)) ≤ t →
      ClusterCoupling B (flatClusterLaw B t)
        (flatClusterLaw B (t - B.card * H * (t / (2 * (B.card * H)))))
        (H * (t / (2 * (B.card * H))))
        ((((t / (2 * (B.card * H)) : ℕ) : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8))
          + 2 * (B.card : ℝ) ^ (-p)))
    (ν : ℝ) (hν : 0 < ν) (m : ℝ) (hm : 1 ≤ m) (α : ℝ) (hα : 0 < α) :
    ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card → ∀ T : ℕ, 0 < T → (T : ℝ) ≤ (B.card : ℝ) ^ m →
      ∃ T' k : ℕ, 1 ≤ T' ∧ (T' : ℝ) ≤ α * Defs.sharp B ∧ T' + B.card * k = T ∧
        ClusterCoupling B (flatClusterLaw B T) (flatClusterLaw B T') k
          ((B.card : ℝ) ^ (-(ν + 1))) := by
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = ⌈m⌉₊ := ⟨_, rfl⟩
  have hmq : m ≤ (q : ℝ) := by rw [hq]; exact Nat.le_ceil m
  have hq1 : (1 : ℝ) ≤ q := hm.trans hmq
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = (ν + 1) + (q : ℝ) + 1 := ⟨_, rfl⟩
  have hγ : 0 < γ := by
    have := (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
    rw [hγdef]; linarith
  obtain ⟨b, hb, N₁, hr⟩ := hround q γ hγ
  obtain ⟨B₀, hB₀def⟩ : ∃ B₀ : ℝ, B₀ = max b (8 * (γ + q)) := ⟨_, rfl⟩
  have hbB₀ : b ≤ B₀ := by rw [hB₀def]; exact le_max_left _ _
  have hγB : 8 * (γ + q) ≤ B₀ := by rw [hB₀def]; exact le_max_right _ _
  have hB₀1 : 1 ≤ B₀ := hb.trans hbB₀
  have hB₀ : 0 ≤ B₀ := by linarith
  refine ⟨max N₁ (max 3 ⌈Real.exp (6 * (B₀ + 1) / α)⌉₊), ?_⟩
  intro B hN T hT hTm
  have hN₁ : N₁ ≤ B.card := (le_max_left _ _).trans hN
  have hN3 : 3 ≤ B.card := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNe : ⌈Real.exp (6 * (B₀ + 1) / α)⌉₊ ≤ B.card :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hcard : 0 < B.card := by omega
  have hcardR : (0 : ℝ) < B.card := card_real_pos B
  have hN3R : (3 : ℝ) ≤ B.card := by exact_mod_cast hN3
  have hcardOne : (1 : ℝ) ≤ B.card := by linarith
  have hlog1 : 1 ≤ Real.log (B.card : ℝ) := by
    rw [Real.le_log_iff_exp_le hcardR]
    exact (Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3)).le.trans hN3R
  have hlogα : 6 * (B₀ + 1) / α ≤ Real.log (B.card : ℝ) := by
    rw [Real.le_log_iff_exp_le hcardR]
    exact (Nat.le_ceil _).trans (by exact_mod_cast hNe)
  have hτ : (1 : ℝ) ≤ (mixingTime B : ℝ) := by exact_mod_cast manuscript_mixing_pos B
  have hsqrt : 1 ≤ Real.sqrt (mixingTime B : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hτ
  have hL0 : 0 ≤ Real.log (B.card : ℝ) := by linarith
  have hs0 : 0 ≤ Real.sqrt (mixingTime B : ℝ) := Real.sqrt_nonneg _
  obtain ⟨H, hHdef⟩ : ∃ H : ℕ,
      H = ⌈B₀ * Real.sqrt (mixingTime B : ℝ) * Real.log (B.card : ℝ)⌉₊ := ⟨_, rfl⟩
  have hbase : B₀ * Real.sqrt (mixingTime B : ℝ) * Real.log (B.card : ℝ) ≤ (H : ℝ) := by
    rw [hHdef]; exact Nat.le_ceil _
  have hH1R : (1 : ℝ) ≤ H :=
    (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hB₀1 hsqrt) hlog1).trans hbase
  have hH1 : 1 ≤ H := by exact_mod_cast hH1R
  have hH0 : 0 < H := by omega
  have hbH : b * Real.sqrt (mixingTime B : ℝ) * Real.log (B.card : ℝ) ≤ (H : ℝ) :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbB₀ hs0) hL0).trans hbase
  have hTr : T ≤ B.card ^ q := by
    have hh := hTm.trans (Real.rpow_le_rpow_of_exponent_le hcardOne hmq)
    rw [Real.rpow_natCast] at hh
    exact_mod_cast hh
  obtain ⟨R, t, ℓ, h0, htimes, hsteps, hlast1, hlast2, hvol, hsum, _⟩ :=
    block_trace B.card H T hcard hH0 hT
  -- every step is at least three blocks long
  have hstep : ∀ i : Fin R, 3 * (2 * (B.card * H)) ≤ t i.castSucc := by
    intro i
    obtain ⟨hℓ3, hℓdef, _⟩ := hsteps i
    have h3 : 3 ≤ t i.castSucc / (2 * (B.card * H)) := by rw [← hℓdef]; exact hℓ3
    exact (Nat.le_div_iff_mul_le (Nat.mul_pos (by norm_num) (Nat.mul_pos hcard hH0))).mp h3
  -- one round for each step
  have hc : ∀ i : Fin R, ClusterCoupling B (flatClusterLaw B (t i.castSucc))
      (flatClusterLaw B (t i.succ)) (H * ℓ i)
      (((ℓ i : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8))
        + 2 * (B.card : ℝ) ^ (-γ)) := by
    intro i
    obtain ⟨_, hℓdef, hnext⟩ := hsteps i
    have hh := hr B hN₁ H (t i.castSucc) hH1 hbH (htimes i.castSucc).1
      ((htimes i.castSucc).2.trans hTr) (hstep i)
    have hnextEq : t i.succ = t i.castSucc - B.card * H * (t i.castSucc / (2 * (B.card * H))) := by
      rw [← hℓdef]; omega
    rw [← hnextEq, ← hℓdef] at hh
    exact hh
  have hε : ∀ i : Fin R, 0 ≤ ((ℓ i : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8))
      + 2 * (B.card : ℝ) ^ (-γ) := fun i => by positivity
  have hglue := glue_flat_trace B R t (fun i => H * ℓ i)
    (fun i => ((ℓ i : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8))
      + 2 * (B.card : ℝ) ^ (-γ)) hε hc
  -- the summed failure allowances
  have hsum_le : ∑ i : Fin R, (((ℓ i : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8))
      + 2 * (B.card : ℝ) ^ (-γ)) ≤ (B.card : ℝ) ^ (-(ν + 1)) := by
    rcases Nat.eq_zero_or_pos R with hR0 | hRpos
    · subst hR0
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      positivity
    · have h1 := hstep ⟨0, hRpos⟩
      have h2 := (htimes (⟨0, hRpos⟩ : Fin R).castSucc).2
      have hNHT : B.card * H ≤ B.card ^ q := by
        have h3 : B.card * H ≤ T := by omega
        exact h3.trans hTr
      have hNHR : (B.card : ℝ) * H ≤ (B.card : ℝ) ^ q := by exact_mod_cast hNHT
      have hf := block_tail_le B.card H q B₀ (mixingTime B : ℝ) γ hB₀ hτ hlog1 hγB hHdef hNHR
      rw [← neg_div] at hf
      exact block_error_sum ℓ T B.card H q (ν + 1) γ ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8))
        ((B.card : ℝ) ^ (-γ)) (by omega) (fun i => (hsteps i).1) hsum hTr hγdef hf le_rfl
  rw [h0] at hglue
  have hfin := clusterCoupling_mono B (flatClusterLaw B T) (flatClusterLaw B (t (Fin.last R)))
    (∑ i, H * ℓ i) _ _ hsum_le hglue
  refine ⟨t (Fin.last R), ∑ i, H * ℓ i, hlast1, ?_, ?_, hfin⟩
  · have htime := block_time_le_sharp_base B H B₀ α hB₀ hτ hlog1 hα hlogα hHdef
    have hlt : (t (Fin.last R) : ℝ) < 6 * ((B.card : ℝ) * H) := by exact_mod_cast hlast2
    exact hlt.le.trans htime
  · rw [← Finset.mul_sum, ← mul_assoc]
    exact hvol

/-- The block reduction, from the block round as a hypothesis: the statement of
`Frozen.pr_reduction` (with the coefficient `α = 1`), for the probability conversion of
`pr_reduction_alpha_of_silvestri`. -/
theorem pr_reduction_of_round
    (hround : ∀ (r : ℕ) (p : ℝ), 0 < p → ∃ b : ℝ, 1 ≤ b ∧ ∃ N₀ : ℕ, ∀ B : Base,
      N₀ ≤ B.card → ∀ H t : ℕ, 1 ≤ H →
      b * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ) ≤ (H : ℝ) →
      0 < t → t ≤ B.card ^ r → 3 * (2 * (B.card * H)) ≤ t →
      ClusterCoupling B (flatClusterLaw B t)
        (flatClusterLaw B (t - B.card * H * (t / (2 * (B.card * H)))))
        (H * (t / (2 * (B.card * H))))
        ((((t / (2 * (B.card * H)) : ℕ) : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8))
          + 2 * (B.card : ℝ) ^ (-p)))
    (ν : ℝ) (hν : 0 < ν) (m : ℝ) (hm : 1 ≤ m) :
    ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card → ∀ T : ℕ,
      Defs.sharp B ≤ (T : ℝ) → (T : ℝ) ≤ (B.card : ℝ) ^ m →
      ∃ T' k : ℕ,
        1 ≤ T' ∧ (T' : ℝ) ≤ Defs.sharp B ∧ T' + B.card * k = T ∧
        ∃ μ : Measure (TrajSeq B × TrajSeq B),
          μ.map (Prod.fst : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
          μ.map (Prod.snd : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
          ENNReal.ofReal (1 - (B.card : ℝ) ^ (-(ν + 1))) ≤
            μ {p | clusterTraj B p.1 T =
              Reduction.shiftCluster B k (clusterTraj B p.2 T')} := by
  obtain ⟨N₀, hc⟩ := block_cluster_coupling_of_round hround ν hν m hm 1 one_pos
  refine ⟨N₀, fun B hN T hlow hhigh => ?_⟩
  have hT : 0 < T := Nat.cast_pos.mp (lt_of_lt_of_le (reduction_sharp_pos B) hlow)
  obtain ⟨T', k, hT', hscale, hvol, hcouple⟩ := hc B hN T hT hhigh
  obtain ⟨μ, hf, hs, he⟩ := lift_cluster_coupling B T T' k _ hcouple
  haveI : IsProbabilityMeasure μ := coupling_isProbability B μ hf
  refine ⟨T', k, hT', by simpa only [one_mul] using hscale, hvol, μ, hf, hs, ?_⟩
  let E := {p : TrajSeq B × TrajSeq B | clusterTraj B p.1 T =
    shiftCluster B k (clusterTraj B p.2 T')}
  have hE : MeasurableSet E := measurableSet_cluster_eq_shift B T T' k
  have hε : 0 ≤ (B.card : ℝ) ^ (-(ν + 1)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hreal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) he
  rw [ENNReal.toReal_ofReal hε] at hreal
  have hcompl := probReal_compl_eq_one_sub (μ := μ) hE
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ E)).mpr
  change (μ Eᶜ).toReal ≤ _ at hreal
  change (μ Eᶜ).toReal = 1 - (μ E).toReal at hcompl
  linarith

/-- The proposition `IdlaCyl.pr_reduction_alpha`, with the coefficient `α = 1`, from the block
round as a hypothesis. -/
theorem pr_reduction_alpha_of_round
    (hround : ∀ (r : ℕ) (p : ℝ), 0 < p → ∃ b : ℝ, 1 ≤ b ∧ ∃ N₀ : ℕ, ∀ B : Base,
      N₀ ≤ B.card → ∀ H t : ℕ, 1 ≤ H →
      b * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ) ≤ (H : ℝ) →
      0 < t → t ≤ B.card ^ r → 3 * (2 * (B.card * H)) ≤ t →
      ClusterCoupling B (flatClusterLaw B t)
        (flatClusterLaw B (t - B.card * H * (t / (2 * (B.card * H)))))
        (H * (t / (2 * (B.card * H))))
        ((((t / (2 * (B.card * H)) : ℕ) : ℝ) + 1) * ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8))
          + 2 * (B.card : ℝ) ^ (-p))) :
    IdlaCyl.pr_reduction_alpha := by
  intro ν hν m hm
  obtain ⟨N₀, hc⟩ := pr_reduction_of_round hround ν hν m hm
  refine ⟨1, one_pos, N₀, fun B hN T hlow hhigh => ?_⟩
  obtain ⟨T', k, h1, h2, h3, h4⟩ := hc B hN T (by rw [one_mul] at hlow; exact hlow) hhigh
  exact ⟨T', k, h1, by rw [one_mul]; exact h2, h3, h4⟩

end IdlaCyl.Reduction
