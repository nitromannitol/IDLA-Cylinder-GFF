import IdlaCyl.Support.Reduction.Target
import IdlaCyl.Support.MaxFluctUpToSharp
import IdlaCyl.Support.ShapeModerate
import IdlaCyl.Support.CanonicalShape

/-!
# The shape bound at every time, from the finite-coefficient reduction

Source: `paper/idla-cylinder-gff.tex`, `tex:271-280` (`th:max_fluct`). The width is
`IdlaCyl.Defs.delta B C T`, the printed `Δ_N` of `tex:273`. Times up to `T^♯` are
covered by `max_fluct_upto_sharp` and `shape_moderate`. Times beyond are carried by the
finite-coefficient reduction `pr_reduction_alpha` (`tex:270-282`, `tex:1119-1136`),
which enters as a hypothesis.
-/

namespace IdlaCyl

open IdlaCyl.Defs MeasureTheory

/-- Membership in a half-plane is preserved when the cluster is shifted and the bound too. -/
theorem reduce_R_subset_shift_iff (B : Base) (x : ℝ) (k : ℕ) (A : Set (Site B)) :
    R B x ⊆ Reduction.shiftCluster B k A ↔ R B (x - k) ⊆ A := by
  constructor
  · intro h q hq
    have hq' : (q.1, q.2 + (k : ℤ)) ∈ Reduction.shiftCluster B k A := by
      apply h
      show ((q.2 + (k : ℤ) : ℤ) : ℝ) ≤ x
      have hq2 : ((q.2 : ℤ) : ℝ) ≤ x - (k : ℝ) := hq
      push_cast at hq2 ⊢
      linarith
    rw [Reduction.mem_shiftCluster] at hq'
    simpa using hq'
  · intro h q hq
    rw [Reduction.mem_shiftCluster]
    apply h
    show ((q.2 - (k : ℤ) : ℤ) : ℝ) ≤ x - (k : ℝ)
    have hq2 : ((q.2 : ℤ) : ℝ) ≤ x := hq
    push_cast at hq2 ⊢
    linarith

/-- A shifted cluster lies in a half-plane exactly when the unshifted cluster lies in the
half-plane lowered by the shift. -/
theorem reduce_shiftCluster_subset_R_iff (B : Base) (x : ℝ) (k : ℕ) (A : Set (Site B)) :
    Reduction.shiftCluster B k A ⊆ R B x ↔ A ⊆ R B (x - k) := by
  constructor
  · intro h q hq
    have hmem : (q.1, q.2 + (k : ℤ)) ∈ Reduction.shiftCluster B k A := by
      rw [Reduction.mem_shiftCluster]
      simpa using hq
    have hR := h hmem
    show ((q.2 : ℤ) : ℝ) ≤ x - (k : ℝ)
    have hR2 : ((q.2 + (k : ℤ) : ℤ) : ℝ) ≤ x := hR
    push_cast at hR2 ⊢
    linarith
  · intro h q hq
    rw [Reduction.mem_shiftCluster] at hq
    have hR := h hq
    show ((q.2 : ℤ) : ℝ) ≤ x
    have hR2 : ((q.2 - (k : ℤ) : ℤ) : ℝ) ≤ x - (k : ℝ) := hR
    push_cast at hR2 ⊢
    linarith

/-- The shape event at `(T, d)` for a shifted cluster is the shape event at `(T', d)` for the
unshifted cluster, when `T / N = T' / N + k`. -/
theorem reduce_shape_shift_iff (B : Base) (T T' k : ℕ)
    (hT : (T : ℝ) / (B.card : ℝ) = (T' : ℝ) / (B.card : ℝ) + (k : ℝ)) (d : ℝ)
    (A : Set (Site B)) :
    (R B ((Int.floor ((T : ℝ) / (B.card : ℝ) - d) : ℤ) : ℝ) ⊆ Reduction.shiftCluster B k A ∧
        Reduction.shiftCluster B k A ⊆ R B ((T : ℝ) / (B.card : ℝ) + d)) ↔
      (R B ((Int.floor ((T' : ℝ) / (B.card : ℝ) - d) : ℤ) : ℝ) ⊆ A ∧
        A ⊆ R B ((T' : ℝ) / (B.card : ℝ) + d)) := by
  have hfl : ((Int.floor ((T : ℝ) / (B.card : ℝ) - d) : ℤ) : ℝ) - (k : ℝ) =
      ((Int.floor ((T' : ℝ) / (B.card : ℝ) - d) : ℤ) : ℝ) := by
    have h1 : (T : ℝ) / (B.card : ℝ) - d = ((T' : ℝ) / (B.card : ℝ) - d) + ((k : ℤ) : ℝ) := by
      push_cast
      linarith
    have h2 : Int.floor ((T : ℝ) / (B.card : ℝ) - d) =
        Int.floor ((T' : ℝ) / (B.card : ℝ) - d) + (k : ℤ) := by
      rw [h1, Int.floor_add_intCast]
    rw [h2]
    push_cast
    ring
  have hup : (T : ℝ) / (B.card : ℝ) + d - (k : ℝ) = (T' : ℝ) / (B.card : ℝ) + d := by
    linarith
  rw [reduce_R_subset_shift_iff, reduce_shiftCluster_subset_R_iff, hfl, hup]

/-- The coupling transfers the failure probability at time `T` to time `T'` up to the
coupling defect `x`. -/
theorem reduce_measure_shape_le (B : Base) (T T' k : ℕ)
    (hT : (T : ℝ) / (B.card : ℝ) = (T' : ℝ) / (B.card : ℝ) + (k : ℝ)) (d x : ℝ)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (μ : Measure (TrajSeq B × TrajSeq B))
    (hfst : μ.map (Prod.fst : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B)
    (hsnd : μ.map (Prod.snd : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B)
    (hcouple : ENNReal.ofReal (1 - x) ≤
      μ {p | clusterTraj B p.1 T = Reduction.shiftCluster B k (clusterTraj B p.2 T')}) :
    idlaMeasure B (eventAt B T d)ᶜ ≤
      ENNReal.ofReal x + idlaMeasure B (eventAt B T' d)ᶜ := by
  have hprob : IsProbabilityMeasure μ := Reduction.coupling_isProbability B μ hfst
  have hE : MeasurableSet {p : TrajSeq B × TrajSeq B |
      clusterTraj B p.1 T = Reduction.shiftCluster B k (clusterTraj B p.2 T')} :=
    Reduction.measurableSet_cluster_eq_shift B T T' k
  have hS : MeasurableSet (eventAt B T d) := by
    unfold eventAt
    exact measurableSet_shapeTraj B T _ _
  have hS' : MeasurableSet (eventAt B T' d) := by
    unfold eventAt
    exact measurableSet_shapeTraj B T' _ _
  have key : ∀ p ∈ {p : TrajSeq B × TrajSeq B |
      clusterTraj B p.1 T = Reduction.shiftCluster B k (clusterTraj B p.2 T')},
      (p.1 ∈ eventAt B T d ↔ p.2 ∈ eventAt B T' d) := by
    intro p hp
    have hp' : clusterTraj B p.1 T = Reduction.shiftCluster B k (clusterTraj B p.2 T') := hp
    simp only [eventAt, Set.mem_setOf_eq]
    rw [hp']
    exact reduce_shape_shift_iff B T T' k hT d (clusterTraj B p.2 T')
  have hsub : Prod.fst ⁻¹' (eventAt B T d)ᶜ ⊆
      {p : TrajSeq B × TrajSeq B |
        clusterTraj B p.1 T = Reduction.shiftCluster B k (clusterTraj B p.2 T')}ᶜ ∪
        Prod.snd ⁻¹' (eventAt B T' d)ᶜ := by
    intro p hp
    by_cases hpE : p ∈ {p : TrajSeq B × TrajSeq B |
        clusterTraj B p.1 T = Reduction.shiftCluster B k (clusterTraj B p.2 T')}
    · right
      show p.2 ∉ eventAt B T' d
      intro hS2
      exact (show p.1 ∉ eventAt B T d from hp) ((key p hpE).mpr hS2)
    · exact Or.inl hpE
  have hfst' : idlaMeasure B (eventAt B T d)ᶜ =
      μ (Prod.fst ⁻¹' (eventAt B T d)ᶜ) := by
    rw [← hfst, Measure.map_apply measurable_fst hS.compl]
  have hsnd' : μ (Prod.snd ⁻¹' (eventAt B T' d)ᶜ) = idlaMeasure B (eventAt B T' d)ᶜ := by
    rw [← hsnd, Measure.map_apply measurable_snd hS'.compl]
  have hEc : μ {p : TrajSeq B × TrajSeq B |
        clusterTraj B p.1 T = Reduction.shiftCluster B k (clusterTraj B p.2 T')}ᶜ ≤
      ENNReal.ofReal x := by
    have hsum : ENNReal.ofReal x + ENNReal.ofReal (1 - x) = 1 := by
      rw [← ENNReal.ofReal_add hx (by linarith)]
      norm_num
    refine ENNReal.le_of_add_le_add_right (ENNReal.ofReal_ne_top (r := 1 - x)) ?_
    calc μ {p : TrajSeq B × TrajSeq B |
            clusterTraj B p.1 T = Reduction.shiftCluster B k (clusterTraj B p.2 T')}ᶜ
          + ENNReal.ofReal (1 - x)
        ≤ μ {p : TrajSeq B × TrajSeq B |
            clusterTraj B p.1 T = Reduction.shiftCluster B k (clusterTraj B p.2 T')}ᶜ
          + μ {p : TrajSeq B × TrajSeq B |
            clusterTraj B p.1 T = Reduction.shiftCluster B k (clusterTraj B p.2 T')} :=
          add_le_add (le_refl _) hcouple
      _ = μ {p : TrajSeq B × TrajSeq B |
            clusterTraj B p.1 T = Reduction.shiftCluster B k (clusterTraj B p.2 T')}
          + μ {p : TrajSeq B × TrajSeq B |
            clusterTraj B p.1 T = Reduction.shiftCluster B k (clusterTraj B p.2 T')}ᶜ :=
          add_comm _ _
      _ = μ Set.univ := measure_add_measure_compl hE
      _ = 1 := measure_univ
      _ = ENNReal.ofReal x + ENNReal.ofReal (1 - x) := hsum.symm
  calc idlaMeasure B (eventAt B T d)ᶜ = μ (Prod.fst ⁻¹' (eventAt B T d)ᶜ) := hfst'
    _ ≤ μ {p : TrajSeq B × TrajSeq B |
            clusterTraj B p.1 T = Reduction.shiftCluster B k (clusterTraj B p.2 T')}ᶜ
          + μ (Prod.snd ⁻¹' (eventAt B T' d)ᶜ) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal x + idlaMeasure B (eventAt B T' d)ᶜ :=
        add_le_add hEc (le_of_eq hsnd')

/-- The logarithm truncation `log₊` is monotone on nonnegative arguments. -/
theorem reduce_logPlus_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    logPlus x ≤ logPlus y := by
  unfold logPlus
  rcases hx.eq_or_lt with h | h
  · rw [← h, Real.log_zero]
    exact max_le (le_max_right _ _) (le_max_right _ _)
  · exact max_le_max (Real.log_le_log h hxy) le_rfl

/-- The threshold `T^♯` is nonnegative. -/
theorem reduce_sharp_nonneg (B : Base) : 0 ≤ sharp B := by
  unfold sharp
  positivity

/-- The width `delta` is nondecreasing in the time. -/
theorem reduce_delta_mono_time (B : Base) (C : ℝ) (hC : 0 ≤ C) (hN : 1 ≤ (B.card : ℝ))
    {T T' : ℕ} (h : T' ≤ T) : delta B C T' ≤ delta B C T := by
  have hNpos : (0 : ℝ) < B.card := by linarith
  have hlog : 0 ≤ Real.log (B.card : ℝ) := Real.log_nonneg hN
  have hT'T : (T' : ℝ) ≤ (T : ℝ) := by exact_mod_cast h
  have hmin : min (T' : ℝ) (sharp B) ≤ min (T : ℝ) (sharp B) := min_le_min_right _ hT'T
  have hs0 : 0 ≤ min (T' : ℝ) (sharp B) := le_min (by positivity) (reduce_sharp_nonneg B)
  have hL : Real.log (B.card : ℝ) + logPlus ((T' : ℝ) / (B.card : ℝ)) ≤
      Real.log (B.card : ℝ) + logPlus ((T : ℝ) / (B.card : ℝ)) :=
    add_le_add (le_refl _) (reduce_logPlus_mono (by positivity) (by gcongr))
  unfold delta
  refine mul_le_mul_of_nonneg_left ?_ hC
  refine max_le_max le_rfl ?_
  refine Real.sqrt_le_sqrt ?_
  exact mul_le_mul (div_le_div_of_nonneg_right hmin hNpos.le) hL
    (add_nonneg hlog (le_max_right _ _))
    (div_nonneg (le_min (by positivity) (reduce_sharp_nonneg B)) hNpos.le)

/-- The width `delta` is nondecreasing in the constant. -/
theorem reduce_delta_mono_C (B : Base) (C₁ C : ℝ) (hC : C₁ ≤ C) (hN : 1 ≤ (B.card : ℝ))
    (T : ℕ) : delta B C₁ T ≤ delta B C T := by
  have hlog : 0 ≤ Real.log (B.card : ℝ) := Real.log_nonneg hN
  unfold delta
  exact mul_le_mul_of_nonneg_right hC (le_max_of_le_left hlog)

/-- Two copies of the failure bound at level `ν + 1` fit under the bound at level `ν`. -/
theorem reduce_rpow_double_le (n ν : ℝ) (hn : 2 ≤ n) :
    n ^ (-(ν + 1)) + n ^ (-(ν + 1)) ≤ n ^ (-ν) := by
  have hpos : 0 < n := by linarith
  have hpow : n ^ (-(ν + 1)) = n ^ (-ν) * n⁻¹ := by
    rw [show -(ν + 1) = -ν + -1 by ring, Real.rpow_add hpos, Real.rpow_neg_one]
  have hp0 : 0 ≤ n ^ (-ν) := Real.rpow_nonneg hpos.le _
  have hinv : n⁻¹ ≤ 1 / 2 := by
    nlinarith [mul_nonneg (inv_pos.mpr hpos).le (sub_nonneg.mpr hn), inv_mul_cancel₀ hpos.ne']
  rw [hpow]
  linarith [mul_le_mul_of_nonneg_left hinv hp0]

/-- The shape bound at all times up to a fixed multiple of `T^♯`, with width `delta`.
The constant `C` and the size `N₀` depend on `ν`, `m` and `α` only. -/
theorem reduce_shape_upto_scale (ν : ℝ) (hν : 0 < ν) (m : ℝ) (hm : 1 ≤ m) (α : ℝ)
    (hα : 1 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card → ∀ t : ℕ,
      1 ≤ t → (t : ℝ) ≤ (B.card : ℝ) ^ m → (t : ℝ) ≤ α * sharp B →
      idlaMeasure B (eventAt B t (delta B C t))ᶜ ≤ ENNReal.ofReal ((B.card : ℝ) ^ (-ν)) := by
  obtain ⟨C₁, hC₁, N₁, hup⟩ := max_fluct_upto_sharp ν hν m hm
  obtain ⟨Cm, K, hCm, hK, N₂, hmod⟩ := shape_moderate ν hν
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = max C₁ (Cm * (2 * Real.sqrt (ν + 4)) * Real.sqrt α) :=
    ⟨_, rfl⟩
  have hC0 : 0 < C := by
    rw [hCdef]
    exact lt_of_lt_of_le hC₁ (le_max_left _ _)
  have hC1 : C₁ ≤ C := by
    rw [hCdef]
    exact le_max_left _ _
  have hC2 : Cm * (2 * Real.sqrt (ν + 4)) * Real.sqrt α ≤ C := by
    rw [hCdef]
    exact le_max_right _ _
  have hα0 : 0 ≤ α := by linarith
  refine ⟨C, hC0, max N₁ (max N₂ (⌈Real.exp K⌉₊ + 2)), ?_⟩
  intro B hB t ht1 htm htα
  have hBN₁ : N₁ ≤ B.card := le_trans (le_max_left _ _) hB
  have hBN₂ : N₂ ≤ B.card :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  have hBexp : ⌈Real.exp K⌉₊ + 2 ≤ B.card :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  have hN2 : (2 : ℝ) ≤ (B.card : ℝ) := by
    have h2 : 2 ≤ B.card := by omega
    exact_mod_cast h2
  have hNpos : (0 : ℝ) < (B.card : ℝ) := by linarith
  have hN1 : (1 : ℝ) ≤ (B.card : ℝ) := by linarith
  have hlog0 : 0 ≤ Real.log (B.card : ℝ) := Real.log_nonneg hN1
  by_cases hsm : (t : ℝ) ≤ sharp B
  · -- times up to the threshold
    have hw : delta B C₁ t ≤ delta B C t := reduce_delta_mono_C B C₁ C hC1 hN1 t
    have hsub : (eventAt B t (delta B C t))ᶜ ⊆ (eventAt B t (delta B C₁ t))ᶜ :=
      Set.compl_subset_compl.mpr (eventAt_mono_width B t hw)
    exact (measure_mono hsub).trans (hup B hBN₁ t ht1 htm hsm)
  · -- times beyond the threshold, where `shape_moderate` applies
    rw [not_le] at hsm
    have hτ : 0 < mixingTime B := by
      by_contra hτ0
      have hz : mixingTime B = 0 := by omega
      have hsh0 : sharp B = 0 := by
        unfold sharp
        rw [hz]
        simp
      rw [hsh0, mul_zero] at htα
      have ht1R : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
      linarith
    have hτ1 : (1 : ℝ) ≤ Real.sqrt (mixingTime B) := by
      have h1 : (1 : ℝ) ≤ (mixingTime B : ℝ) := by exact_mod_cast hτ
      have h2 := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_one] at h2
    have hsharp_lb : (B.card : ℝ) * (Real.log (B.card : ℝ)) ^ 2 ≤ sharp B := by
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hτ1 hNpos.le) (sq_nonneg (Real.log (B.card : ℝ)))
      unfold sharp
      calc (B.card : ℝ) * (Real.log (B.card : ℝ)) ^ 2
          = (B.card : ℝ) * 1 * (Real.log (B.card : ℝ)) ^ 2 := by ring
        _ ≤ _ := h
    have hexpK : Real.exp K ≤ (B.card : ℝ) := by
      have h1 : Real.exp K ≤ (⌈Real.exp K⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈Real.exp K⌉₊ : ℝ) ≤ (B.card : ℝ) := by
        have h3 : ⌈Real.exp K⌉₊ ≤ B.card := by omega
        exact_mod_cast h3
      exact h1.trans h2
    have hKlog : K ≤ Real.log (B.card : ℝ) := by
      have h := Real.log_le_log (Real.exp_pos K) hexpK
      rwa [Real.log_exp] at h
    have hKL : K * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (t : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left hKlog (mul_nonneg hNpos.le hlog0)
      have h2 : K * (B.card : ℝ) * Real.log (B.card : ℝ) ≤
          (B.card : ℝ) * (Real.log (B.card : ℝ)) ^ 2 := by
        nlinarith [h1]
      linarith
    have hX : 0 ≤ Real.log (B.card : ℝ) + logPlus ((t : ℝ) / (B.card : ℝ)) :=
      add_nonneg hlog0 (le_max_right _ _)
    have hsq : Real.sqrt ((t : ℝ) / (B.card : ℝ) *
        (Real.log (B.card : ℝ) + logPlus ((t : ℝ) / (B.card : ℝ)))) ≤
        Real.sqrt α * Real.sqrt (sharp B / (B.card : ℝ) *
          (Real.log (B.card : ℝ) + logPlus ((t : ℝ) / (B.card : ℝ)))) := by
      rw [← Real.sqrt_mul hα0]
      apply Real.sqrt_le_sqrt
      have htn : (t : ℝ) / (B.card : ℝ) ≤ α * (sharp B / (B.card : ℝ)) := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right htα hNpos.le
      calc (t : ℝ) / (B.card : ℝ) * (Real.log (B.card : ℝ) + logPlus ((t : ℝ) / (B.card : ℝ)))
          ≤ α * (sharp B / (B.card : ℝ)) *
            (Real.log (B.card : ℝ) + logPlus ((t : ℝ) / (B.card : ℝ))) :=
            mul_le_mul_of_nonneg_right htn hX
        _ = α * (sharp B / (B.card : ℝ) *
            (Real.log (B.card : ℝ) + logPlus ((t : ℝ) / (B.card : ℝ)))) := by ring
    have hlt : PrInnerTail.logTerm (B.card : ℝ) (t : ℝ) =
        Real.log (B.card : ℝ) + logPlus ((t : ℝ) / (B.card : ℝ)) := rfl
    have hiw : innerWidth ν B.card t = 2 * Real.sqrt (ν + 4) *
        Real.sqrt ((t : ℝ) / (B.card : ℝ) *
          (Real.log (B.card : ℝ) + logPlus ((t : ℝ) / (B.card : ℝ)))) := by
      unfold innerWidth
      rw [hlt]
    have hdl : delta B C t = C * max (Real.log (B.card : ℝ))
        (Real.sqrt (sharp B / (B.card : ℝ) *
          (Real.log (B.card : ℝ) + logPlus ((t : ℝ) / (B.card : ℝ))))) := by
      unfold delta
      rw [min_eq_right hsm.le]
    have hcm0 : 0 ≤ Cm * (2 * Real.sqrt (ν + 4)) := mul_nonneg hCm.le (by positivity)
    have hwidth : Cm * innerWidth ν B.card t ≤ delta B C t := by
      rw [hiw, hdl]
      calc Cm * (2 * Real.sqrt (ν + 4) * Real.sqrt ((t : ℝ) / (B.card : ℝ) *
              (Real.log (B.card : ℝ) + logPlus ((t : ℝ) / (B.card : ℝ)))))
          = (Cm * (2 * Real.sqrt (ν + 4))) * Real.sqrt ((t : ℝ) / (B.card : ℝ) *
              (Real.log (B.card : ℝ) + logPlus ((t : ℝ) / (B.card : ℝ)))) := by ring
        _ ≤ (Cm * (2 * Real.sqrt (ν + 4))) * (Real.sqrt α * Real.sqrt (sharp B / (B.card : ℝ) *
              (Real.log (B.card : ℝ) + logPlus ((t : ℝ) / (B.card : ℝ))))) :=
            mul_le_mul_of_nonneg_left hsq hcm0
        _ = (Cm * (2 * Real.sqrt (ν + 4)) * Real.sqrt α) * Real.sqrt (sharp B / (B.card : ℝ) *
              (Real.log (B.card : ℝ) + logPlus ((t : ℝ) / (B.card : ℝ)))) := by ring
        _ ≤ C * Real.sqrt (sharp B / (B.card : ℝ) *
              (Real.log (B.card : ℝ) + logPlus ((t : ℝ) / (B.card : ℝ)))) :=
            mul_le_mul_of_nonneg_right hC2 (Real.sqrt_nonneg _)
        _ ≤ C * max (Real.log (B.card : ℝ)) (Real.sqrt (sharp B / (B.card : ℝ) *
              (Real.log (B.card : ℝ) + logPlus ((t : ℝ) / (B.card : ℝ))))) :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) hC0.le
    have hsub : (eventAt B t (delta B C t))ᶜ ⊆
        (eventAt B t (Cm * innerWidth ν B.card t))ᶜ :=
      Set.compl_subset_compl.mpr (eventAt_mono_width B t hwidth)
    exact (measure_mono hsub).trans (hmod B hBN₂ t hKL)

/-- The shape bound for every time, with the finite-coefficient reduction as a premise.
The constant `C` and the size `N₀` are chosen before the base and the time. -/
theorem max_fluct_of_reduction (hred : pr_reduction_alpha) (ν : ℝ) (hν : 0 < ν) (m : ℝ)
    (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card → ∀ T : ℕ,
      1 ≤ T → (T : ℝ) ≤ (B.card : ℝ) ^ m →
      idlaMeasure B (eventAt B T (delta B C T))ᶜ ≤ ENNReal.ofReal ((B.card : ℝ) ^ (-ν)) := by
  obtain ⟨α, hα, Nh, hredN⟩ := hred ν hν m hm
  obtain ⟨C, hC, N₃, hL⟩ :=
    reduce_shape_upto_scale (ν + 1) (by linarith) m hm (max 1 α) (le_max_left _ _)
  refine ⟨C, hC, max (max Nh N₃) 2, ?_⟩
  intro B hB T hT1 hTm
  have hBNh : Nh ≤ B.card := ((le_max_left Nh N₃).trans (le_max_left _ 2)).trans hB
  have hBN₃ : N₃ ≤ B.card := ((le_max_right Nh N₃).trans (le_max_left _ 2)).trans hB
  have h2 : 2 ≤ B.card := (le_max_right _ 2).trans hB
  have hN2 : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast h2
  have hN1 : (1 : ℝ) ≤ (B.card : ℝ) := by linarith
  have hNpos : (0 : ℝ) < (B.card : ℝ) := by linarith
  have hx0 : 0 ≤ (B.card : ℝ) ^ (-(ν + 1)) := Real.rpow_nonneg hNpos.le _
  have hx1 : (B.card : ℝ) ^ (-(ν + 1)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hmono : ENNReal.ofReal ((B.card : ℝ) ^ (-(ν + 1))) ≤
      ENNReal.ofReal ((B.card : ℝ) ^ (-ν)) :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  by_cases hTα : (T : ℝ) ≤ max 1 α * sharp B
  · -- the time lies below `max 1 α · T^♯`, where the scale lemma applies directly
    exact (hL B hBN₃ T hT1 hTm hTα).trans hmono
  · -- the time lies above `α · T^♯`, where the reduction applies
    rw [not_le] at hTα
    have hαT : α * sharp B ≤ (T : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (reduce_sharp_nonneg B)) hTα.le
    obtain ⟨T', k, hT'1, hT'α, hTk, μ, hfst, hsnd, hcouple⟩ := hredN B hBNh T hαT hTm
    have hT'T : T' ≤ T := by
      rw [← hTk]
      exact Nat.le_add_right _ _
    have hTR : (T : ℝ) = (T' : ℝ) + (B.card : ℝ) * (k : ℝ) := by
      exact_mod_cast hTk.symm
    have hratio : (T : ℝ) / (B.card : ℝ) = (T' : ℝ) / (B.card : ℝ) + (k : ℝ) := by
      rw [hTR, add_div, mul_div_cancel_left₀ _ hNpos.ne']
    have hmeas := reduce_measure_shape_le B T T' k hratio (delta B C T)
      ((B.card : ℝ) ^ (-(ν + 1))) hx0 hx1 μ hfst hsnd hcouple
    have hdm : delta B C T' ≤ delta B C T := reduce_delta_mono_time B C hC.le hN1 hT'T
    have hsubT' : (eventAt B T' (delta B C T))ᶜ ⊆ (eventAt B T' (delta B C T'))ᶜ :=
      Set.compl_subset_compl.mpr (eventAt_mono_width B T' hdm)
    have hT'm : (T' : ℝ) ≤ (B.card : ℝ) ^ m :=
      (show (T' : ℝ) ≤ (T : ℝ) by exact_mod_cast hT'T).trans hTm
    have hT'α' : (T' : ℝ) ≤ max 1 α * sharp B :=
      hT'α.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (reduce_sharp_nonneg B))
    have hT'bd := hL B hBN₃ T' hT'1 hT'm hT'α'
    calc idlaMeasure B (eventAt B T (delta B C T))ᶜ
        ≤ ENNReal.ofReal ((B.card : ℝ) ^ (-(ν + 1))) +
          idlaMeasure B (eventAt B T' (delta B C T))ᶜ := hmeas
      _ ≤ ENNReal.ofReal ((B.card : ℝ) ^ (-(ν + 1))) +
          ENNReal.ofReal ((B.card : ℝ) ^ (-(ν + 1))) :=
          add_le_add le_rfl ((measure_mono hsubT').trans hT'bd)
      _ = ENNReal.ofReal ((B.card : ℝ) ^ (-(ν + 1)) + (B.card : ℝ) ^ (-(ν + 1))) :=
          (ENNReal.ofReal_add hx0 hx0).symm
      _ ≤ ENNReal.ofReal ((B.card : ℝ) ^ (-ν)) :=
          ENNReal.ofReal_le_ofReal (reduce_rpow_double_le (B.card : ℝ) ν hN2)

end IdlaCyl
