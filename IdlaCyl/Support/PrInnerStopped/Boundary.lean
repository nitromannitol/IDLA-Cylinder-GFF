/-
The pathwise boundary inclusion of the stopped score (`paper/idla-cylinder-gff.tex:1236-1251`).

If the site `ζ` on the stopping layer `h` is not in the stopped cluster `Ā_h(T)`, then the stopped
score `M_ζ(T) = ∑_{s<T} (H_ζ(X̄_s, Ȳ_s) - 1/N)` is below `-ℓ` whenever `h + ℓ ≤ T/N`.  The proof is
pathwise.  A settle site on the stopping layer is different from `ζ`, so its hitting probability
vanishes (`hitProb_at_layer`).  The settle sites strictly below the stopping layer are pairwise
distinct points of `R_{h-1} ∖ R_0`, and the hitting probabilities on that set sum to `h - 1`
(`hitProb_layer_sum`).
-/
import IdlaCyl.Support.PrInnerStopped.Filtration
import IdlaCyl.Support.StoppedScoreMartingale
import IdlaCyl.Support.Recurrence.Discharge

namespace IdlaCyl

open MeasureTheory Finset

variable (B : Base)

/-- The stopped cluster is nondecreasing in time. -/
theorem stoppedCluster_monotone (h : ℤ) (ω : TrajSeq B) : Monotone (stoppedCluster B h ω) :=
  monotone_nat_of_le_succ fun _ => Set.subset_union_left

/-- The `s`-th stopped settle site joins the stopped cluster at time `s + 1`. -/
theorem stoppedSettleSite_mem_succ (h : ℤ) (ω : TrajSeq B) (s : ℕ) :
    stoppedSettleSite B h ω s ∈ stoppedCluster B h ω (s + 1) :=
  Set.mem_union_right _ (Set.mem_singleton _)

/-- The stopped cluster contains `R_0` at every time. -/
theorem subset_R_zero_stoppedCluster (h : ℤ) (ω : TrajSeq B) (t : ℕ) {p : Site B}
    (hp : p ∈ R B 0) : p ∈ stoppedCluster B h ω t := by
  rw [stoppedCluster_eq_union]
  exact Or.inl hp

/-- A site of the stopping layer other than `ζ` has hitting probability `0`. -/
theorem hitProb_eq_zero_of_layer (ζ p : Site B) (hp : p.2 = ζ.2) (hne : p ≠ ζ) :
    hitProb B ζ p = 0 := by
  have hpx : p = (p.1, ζ.2) := Prod.ext rfl hp
  rw [hpx, hitProb_at_layer, if_neg]
  intro hx
  exact hne (Prod.ext hx hp)

/-- The hitting probabilities on the layers `1, …, h-1` sum to `h - 1` (`tex:1240-1241`). -/
theorem sum_hitProb_layers_below (h : ℤ) (hh : 1 ≤ h) (ζ : Site B) (hζ : ζ.2 = h) :
    ∑ p ∈ (Finset.univ : Finset B.V) ×ˢ Finset.Icc (1 : ℤ) (h - 1), hitProb B ζ p
      = (h : ℝ) - 1 := by
  rw [Finset.sum_product, Finset.sum_comm]
  have hlay : ∀ y ∈ Finset.Icc (1 : ℤ) (h - 1), ∑ x : B.V, hitProb B ζ (x, y) = 1 := by
    intro y hy
    rw [Finset.mem_Icc] at hy
    exact hitProb_layer_sum B ζ y (by omega) External.lazyRwRecurrent_holds
  rw [Finset.sum_congr rfl hlay, Finset.sum_const, Int.card_Icc, nsmul_eq_mul, mul_one]
  have hk : ((h - 1 + 1 - 1).toNat : ℤ) = h - 1 := by
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) hk
  push_cast at hcast
  linarith

/-- The settle sites strictly below the stopping layer are pairwise distinct (`tex:1236-1240`). -/
theorem stoppedSettleSite_injOn_below (h : ℤ) (T : ℕ) (ω : TrajSeq B)
    (hfin : ∀ t, exitTime' B (stoppedCluster B h ω t ∩ R B ((h : ℝ) - 1)) (ω t) ≠ ⊤) :
    Set.InjOn (stoppedSettleSite B h ω)
      ((Finset.range T).filter (fun s => (stoppedSettleSite B h ω s).2 < h) : Set ℕ) := by
  intro s hs t ht hst
  rw [Finset.mem_coe, Finset.mem_filter] at hs ht
  rcases lt_trichotomy s t with hlt | heq | hgt
  · exfalso
    have hmem : stoppedSettleSite B h ω s ∈ stoppedCluster B h ω t :=
      stoppedCluster_monotone B h ω (Nat.succ_le_of_lt hlt) (stoppedSettleSite_mem_succ B h ω s)
    rw [hst] at hmem
    exact stoppedSettleSite_notMem_of_lt B h ω t (hfin t) ht.2 hmem
  · exact heq
  · exfalso
    have hmem : stoppedSettleSite B h ω t ∈ stoppedCluster B h ω s :=
      stoppedCluster_monotone B h ω (Nat.succ_le_of_lt hgt) (stoppedSettleSite_mem_succ B h ω t)
    rw [← hst] at hmem
    exact stoppedSettleSite_notMem_of_lt B h ω s (hfin s) hs.2 hmem

/-- **The settle sites below the stopping layer carry total hitting probability at most `h - 1`**
(`tex:1242`). -/
theorem sum_hitProb_stoppedSettleSite_below_le (h : ℤ) (hh : 1 ≤ h) (ζ : Site B) (hζ : ζ.2 = h)
    (T : ℕ) (ω : TrajSeq B)
    (hfin : ∀ t, exitTime' B (stoppedCluster B h ω t ∩ R B ((h : ℝ) - 1)) (ω t) ≠ ⊤) :
    ∑ s ∈ (Finset.range T).filter (fun s => (stoppedSettleSite B h ω s).2 < h),
        hitProb B ζ (stoppedSettleSite B h ω s) ≤ (h : ℝ) - 1 := by
  have himg : ((Finset.range T).filter (fun s => (stoppedSettleSite B h ω s).2 < h)).image
      (stoppedSettleSite B h ω) ⊆ (Finset.univ : Finset B.V) ×ˢ Finset.Icc (1 : ℤ) (h - 1) := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨s, hs, rfl⟩ := hp
    rw [Finset.mem_filter] at hs
    rw [Finset.mem_product, Finset.mem_Icc]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · by_contra hc
      have hle0 : (stoppedSettleSite B h ω s).2 ≤ 0 := by omega
      have hR0 : stoppedSettleSite B h ω s ∈ R B 0 := mem_R.mpr (by exact_mod_cast hle0)
      exact (stoppedSettleSite_notMem_of_lt B h ω s (hfin s) hs.2)
        (subset_R_zero_stoppedCluster B h ω s hR0)
    · have := hs.2
      omega
  have himg_sum : ∑ p ∈ ((Finset.range T).filter (fun s => (stoppedSettleSite B h ω s).2 < h)).image
      (stoppedSettleSite B h ω), hitProb B ζ p
      = ∑ s ∈ (Finset.range T).filter (fun s => (stoppedSettleSite B h ω s).2 < h),
          hitProb B ζ (stoppedSettleSite B h ω s) :=
    Finset.sum_image fun s hs t ht hst =>
      stoppedSettleSite_injOn_below B h T ω hfin hs ht hst
  calc ∑ s ∈ (Finset.range T).filter (fun s => (stoppedSettleSite B h ω s).2 < h),
          hitProb B ζ (stoppedSettleSite B h ω s)
      = ∑ p ∈ ((Finset.range T).filter (fun s => (stoppedSettleSite B h ω s).2 < h)).image
          (stoppedSettleSite B h ω), hitProb B ζ p := himg_sum.symm
    _ ≤ ∑ p ∈ (Finset.univ : Finset B.V) ×ˢ Finset.Icc (1 : ℤ) (h - 1), hitProb B ζ p :=
        Finset.sum_le_sum_of_subset_of_nonneg himg fun p _ _ => hitProb_nonneg B ζ p
    _ = (h : ℝ) - 1 := sum_hitProb_layers_below B h hh ζ hζ

/-- **Boundary inclusion, pathwise** (`tex:1236-1251`).  If `ζ` is not in the stopped cluster
`Ā_h(T)` and `h + ℓ ≤ T/N`, then `M_ζ(T) < -ℓ`. -/
theorem stoppedScoreOf_lt_neg_of_not_mem (h : ℤ) (hh : 1 ≤ h) (ζ : Site B) (hζ : ζ.2 = h)
    (T : ℕ) (ℓ : ℝ) (ω : TrajSeq B)
    (hadm : ∀ j, CylAdmissible B (ω j)) (h0 : ∀ j, ω j 0 ∈ R B 0)
    (hfin : ∀ t, exitTime' B (stoppedCluster B h ω t ∩ R B ((h : ℝ) - 1)) (ω t) ≠ ⊤)
    (hnot : ζ ∉ stoppedCluster B h ω T)
    (hℓ : (h : ℝ) + ℓ ≤ (T : ℝ) / (B.card : ℝ)) :
    stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T ω < -ℓ := by
  have hlevel : ∀ s, (stoppedSettleSite B h ω s).2 ≤ h :=
    fun s => stoppedSettleSite_ver_le B h hh ω hadm h0 hfin s
  -- no settle site before time `T` is `ζ`, since the cluster at time `T` misses `ζ`
  have hne : ∀ s < T, stoppedSettleSite B h ω s ≠ ζ := by
    intro s hs heq
    apply hnot
    have hmem : stoppedSettleSite B h ω s ∈ stoppedCluster B h ω T :=
      stoppedCluster_monotone B h ω (Nat.succ_le_of_lt hs) (stoppedSettleSite_mem_succ B h ω s)
    rw [heq] at hmem
    exact hmem
  -- at the stopping layer the hitting probability vanishes off `ζ`
  have hzero : ∀ s ∈ Finset.range T, ¬ (stoppedSettleSite B h ω s).2 < h →
      hitProb B ζ (stoppedSettleSite B h ω s) = 0 := by
    intro s hs hnlt
    have hlay : (stoppedSettleSite B h ω s).2 = ζ.2 := by
      rw [hζ]
      have := hlevel s
      omega
    exact hitProb_eq_zero_of_layer B ζ _ hlay (hne s (Finset.mem_range.mp hs))
  have hsplit : ∑ s ∈ Finset.range T, hitProb B ζ (stoppedSettleSite B h ω s)
      = ∑ s ∈ (Finset.range T).filter (fun s => (stoppedSettleSite B h ω s).2 < h),
          hitProb B ζ (stoppedSettleSite B h ω s) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun s hs => ?_
    split_ifs with hlt
    · rfl
    · exact hzero s hs hlt
  have hbound := sum_hitProb_stoppedSettleSite_below_le B h hh ζ hζ T ω hfin
  have hsc : stoppedScoreOf B h (fun p => hitProb B ζ p - 1 / (B.card : ℝ)) T ω
      = ∑ s ∈ Finset.range T, hitProb B ζ (stoppedSettleSite B h ω s)
        - (T : ℝ) / (B.card : ℝ) := by
    simp only [stoppedScoreOf]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hsc, hsplit]
  linarith

end IdlaCyl
