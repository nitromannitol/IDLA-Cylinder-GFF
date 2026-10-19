/-
One raw-layer reduction round with correct continuations on every failed history.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396,1440-1453;
Both uses of the citation retain its base-size cutoff.
-/
import IdlaCyl.Support.Reduction.CountableProbability
import IdlaCyl.Support.Reduction.RoundDeep
import IdlaCyl.Support.Reduction.RoundRemaining
import IdlaCyl.Support.Reduction.RoundCounts
import IdlaCyl.Support.Reduction.BindCouplings
import IdlaCyl.Support.Reduction.ShiftCoupling
import IdlaCyl.Support.Reduction.ShiftLaws

namespace IdlaCyl.Reduction

open MeasureTheory

/-- A valid active round preserves both canonical marginals and charges four failures. -/
theorem one_round (hsil : External.silvestri_prop2)
    (r : ℕ) (p : ℝ) (hp : 0 < p) :
    ∃ b : ℝ, 1 ≤ b ∧ ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card →
      ∀ (M β t : ℕ) (q : ℝ),
      2 * B.card ≤ M → 0 < β →
      b * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ) ≤ (β : ℝ) →
      (q + 1) * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (M : ℝ) →
      0 < t → t ≤ B.card ^ r → 3 * β ≤ t / M →
      ClusterCoupling B (flatClusterLaw B t)
        (flatClusterLaw B (t - B.card * (t / M))) (t / M)
        (roundError B p q (t / M) β) := by
  classical
  obtain ⟨b₁, hb₁, N₁, hdeep⟩ := silvestri_deep_comparison hsil r p hp
  obtain ⟨b₂, hb₂, N₂, hrest⟩ := silvestri_shallow_comparison hsil r p hp
  refine ⟨max b₁ b₂, hb₁.trans (le_max_left _ _), max N₁ N₂, ?_⟩
  intro B hN M β t q hM hβ hbuf hcoupon ht htr hgo
  let ℓ := t / M
  let ρ := t % M
  let D := (M - B.card) * (ℓ - β)
  let Q := (M - B.card) * β + ρ
  let F := shiftFinite B ℓ (resumeEmpty B)
  let π := layeredPause B M ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ)
  let A := goodPaused B M ℓ ρ
  let C : Set (ResumeFinite B) :=
    {c | c ∈ filled B ((ℓ : ℤ) + (β : ℤ)) ∧ SeedConnected B (resumeSeed B c)}
  let Fd := layerGrowthLaw B F (ℓ : ℤ) D
  let G := fun c : ResumeFinite B => layerGrowthLaw B c (ℓ : ℤ) Q
  have hNpos : 0 < B.card := lt_of_lt_of_le (by decide : 0 < 2) B.nontrivial
  have hlog : 0 ≤ Real.log (B.card : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B.card))
  have hbsmall (a : ℝ) (ha : a ≤ max b₁ b₂) :
      a * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ) ≤ (β : ℝ) :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ha (Real.sqrt_nonneg _)) hlog).trans hbuf
  have hℓ : 3 * β ≤ ℓ := hgo
  have hβℓ : β ≤ ℓ := by omega
  have hcounts := round_comparison_counts B.card M β t hNpos hM hβ hgo
  change 0 < D ∧ 0 < Q ∧ M * β ≤ D ∧ D ≤ t ∧ Q ≤ t ∧
    D + Q = t - B.card * ℓ ∧ (t - B.card * ℓ) + B.card * ℓ = t at hcounts
  have htime : M * ℓ + ρ = t := by
    have hv : ρ + M * ℓ = t := Nat.mod_add_div t M
    omega
  have hdeep' (s : ResumeState B × ℕ) (hs : s ∈ A) :
      ClusterCoupling B (resumeRun B s.1.1 (deepQueue B β ℓ s)) Fd 0
        ((B.card : ℝ) ^ (-p)) :=
    hdeep B ((le_max_left N₁ N₂).trans hN) M β ℓ ρ hM hβ hℓ
      (hbsmall b₁ (le_max_left _ _)) (hcounts.2.2.2.1.trans htr) s hs
  have hrest' (s : ResumeState B × ℕ) (hs : s ∈ A) (c : ResumeFinite B)
      (hc : c ∈ C) :
      ClusterCoupling B
        ((resumeRun B c (shallowQueue B β ℓ s)).bind
          (fun d => layerGrowthLaw B d 0 ρ)) (G c) 0 ((B.card : ℝ) ^ (-p)) :=
    hrest B ((le_max_right N₁ N₂).trans hN) M β ℓ ρ hβℓ hcounts.2.1
      (hcounts.2.2.2.2.1.trans htr) (hbsmall b₂ (le_max_right _ _)) s hs c hc.1 hc.2
  let U := fun s : ResumeState B × ℕ => if s ∈ A then
    resumeRun B s.1.1 (deepQueue B β ℓ s) else Measure.dirac s.1.1
  let V := fun (s : ResumeState B × ℕ) (c : ResumeFinite B) => if s ∈ A then
    (resumeRun B c (shallowQueue B β ℓ s)).bind (fun d => layerGrowthLaw B d 0 ρ)
    else finishUniform B s.1 s.2
  haveI (s : ResumeState B × ℕ) : IsProbabilityMeasure (U s) := by
    dsimp only [U]
    split <;> infer_instance
  haveI (s : ResumeState B × ℕ) (c : ResumeFinite B) : IsProbabilityMeasure (V s c) := by
    dsimp only [V]
    split <;> infer_instance
  let J := fun s : ResumeState B × ℕ => if hs : s ∈ A then
    Classical.choose (hdeep' s hs) else (U s).prod Fd
  have hJ (s : ResumeState B × ℕ) :
      (J s).map Prod.fst = U s ∧ (J s).map Prod.snd = Fd := by
    dsimp only [J]
    split_ifs with hs
    · have hj := Classical.choose_spec (hdeep' s hs)
      exact ⟨by simpa only [U, if_pos hs] using hj.1, hj.2.1⟩
    · simp only [Measure.map_fst_prod, Measure.map_snd_prod, measure_univ, one_smul,
        and_self]
  haveI (s : ResumeState B × ℕ) : IsProbabilityMeasure (J s) :=
    probability_of_first_marginal (J s) (U s) (hJ s).1
  let K := fun (s : ResumeState B × ℕ) (c d : ResumeFinite B) =>
    if hs : s ∈ A ∧ c = d ∧ d ∈ C then
      Classical.choose (hrest' s hs.1 c (hs.2.1.symm ▸ hs.2.2))
    else (V s c).prod (G d)
  have hK (s : ResumeState B × ℕ) (c d : ResumeFinite B) :
      (K s c d).map Prod.fst = V s c ∧ (K s c d).map Prod.snd = G d := by
    dsimp only [K]
    split_ifs with hs
    · have hk := Classical.choose_spec (hrest' s hs.1 c (hs.2.1.symm ▸ hs.2.2))
      exact ⟨by simpa only [V, if_pos hs.1] using hk.1, hk.2.1.trans (congrArg G hs.2.1)⟩
    · simp only [Measure.map_fst_prod, Measure.map_snd_prod, measure_univ, one_smul,
        and_self]
  haveI (s : ResumeState B × ℕ) (c d : ResumeFinite B) : IsProbabilityMeasure (K s c d) :=
    probability_of_first_marginal (K s c d) (V s c) (hK s c d).1
  let η := π.bind (fun s => (J s).bind (fun cd => K s cd.1 cd.2))
  have hmarg := bind_coupling_marginals π U Fd J V G K
    (fun _ => measurable_of_countable _) (measurable_of_countable _) hJ hK
  have hUV (s : ResumeState B × ℕ) : (U s).bind (V s) = finishUniform B s.1 s.2 := by
    by_cases hs : s ∈ A
    · simpa only [U, V, if_pos hs] using
        (finishUniform_split B M β ℓ ρ hβℓ s hs).symm
    · simp only [U, V, if_neg hs, Measure.dirac_bind (measurable_of_countable _)]
  have hηfst : η.map Prod.fst = flatClusterLaw B t := by
    rw [hmarg.1]
    simp_rw [hUV]
    rw [layeredPause_finish, htime]
  have hηsnd : η.map Prod.snd = layerGrowthLaw B F (ℓ : ℤ) (t - B.card * ℓ) := by
    rw [hmarg.2, measure_univ, one_smul]
    change (layerGrowthLaw B F (ℓ : ℤ) D).bind
      (fun c => layerGrowthLaw B c (ℓ : ℤ) Q) = _
    rw [← layerGrowthLaw_add, hcounts.2.2.2.2.2.1]
  have hfill0 : Fd (filled B ((ℓ : ℤ) + (β : ℤ)))ᶜ ≤
      ENNReal.ofReal ((β : ℝ) * (B.card : ℝ) ^ (-q)) := by
    apply (layerGrowthLaw_failure_mono B F (ℓ : ℤ) ((ℓ : ℤ) + (β : ℤ))
      (M * β) D hcounts.2.2.1).trans
    exact canonical_buffer_fill B F (ℓ : ℤ) (ℓ : ℤ) le_rfl
      (by simpa only [F, resumeSeed_shiftFinite_empty, Int.cast_natCast] using
        (Set.Subset.rfl : R B (ℓ : ℝ) ⊆ R B (ℓ : ℝ))) M β q hcoupon
  -- The deep growth starts from the rectangle `R_ℓ` with walkers on layer `ℓ`, so its seeds are
  -- almost surely connected, as Silvestri's Proposition 2 requires of the shallow comparison.
  have hseedF : resumeSeed B F = R B (((ℓ : ℤ)) : ℝ) := by
    rw [resumeSeed_shiftFinite_empty, Int.cast_natCast]
  have hconn0 : Fd {c | ¬ SeedConnected B (resumeSeed B c)} = 0 :=
    layerGrowthLaw_not_seedConnected B F (ℓ : ℤ) (by rw [hseedF]; exact seedConnected_R B _)
      (by rw [hseedF]) D
  have hfill : Fd Cᶜ ≤ ENNReal.ofReal ((β : ℝ) * (B.card : ℝ) ^ (-q)) := by
    have hsub : Cᶜ ⊆ (filled B ((ℓ : ℤ) + (β : ℤ)))ᶜ ∪
        {c | ¬ SeedConnected B (resumeSeed B c)} := by
      intro c hc
      by_cases h1 : c ∈ filled B ((ℓ : ℤ) + (β : ℤ))
      · exact Or.inr (fun h2 => hc ⟨h1, h2⟩)
      · exact Or.inl h1
    calc Fd Cᶜ ≤ Fd ((filled B ((ℓ : ℤ) + (β : ℤ)))ᶜ ∪
          {c | ¬ SeedConnected B (resumeSeed B c)}) := measure_mono hsub
      _ ≤ Fd (filled B ((ℓ : ℤ) + (β : ℤ)))ᶜ + Fd {c | ¬ SeedConnected B (resumeSeed B c)} :=
          measure_union_le _ _
      _ ≤ _ := by rw [hconn0, add_zero]; exact hfill0
  have hgood (s : ResumeState B × ℕ) (hs : s ∈ A) :
      ((J s).bind (fun cd => K s cd.1 cd.2)) (matchShift B 0)ᶜ ≤
        ENNReal.ofReal ((β : ℝ) * (B.card : ℝ) ^ (-q) + 2 * (B.card : ℝ) ^ (-p)) := by
    let E : Set (ResumeFinite B × ResumeFinite B) := {cd | cd.1 = cd.2 ∧ cd.2 ∈ C}
    have hmatch : J s (matchShift B 0)ᶜ ≤ ENNReal.ofReal ((B.card : ℝ) ^ (-p)) := by
      dsimp only [J]
      rw [dif_pos hs]
      exact (Classical.choose_spec (hdeep' s hs)).2.2
    have hbuffer : J s (Prod.snd ⁻¹' Cᶜ) ≤
        ENNReal.ofReal ((β : ℝ) * (B.card : ℝ) ^ (-q)) := by
      rw [← Measure.map_apply measurable_snd (Set.to_countable _).measurableSet, (hJ s).2]
      exact hfill
    have hE : J s Eᶜ ≤ J s (matchShift B 0)ᶜ + J s (Prod.snd ⁻¹' Cᶜ) := by
      apply (measure_mono (show Eᶜ ⊆ (matchShift B 0)ᶜ ∪ Prod.snd ⁻¹' Cᶜ from ?_)).trans
        (measure_union_le _ _)
      intro cd hbad
      by_cases heq : cd.1 = cd.2
      · exact Or.inr (fun hc => hbad ⟨heq, hc⟩)
      · exact Or.inl (fun hm => heq ((mem_matchShift_zero B cd).mp hm))
    calc
      _ ≤ J s Eᶜ + ENNReal.ofReal ((B.card : ℝ) ^ (-p)) :=
        bind_failure_le (J s) (fun cd => K s cd.1 cd.2) E (matchShift B 0)ᶜ
          (Set.to_countable _).measurableSet (Set.to_countable _).measurableSet _ (by
            intro cd hcd
            dsimp only [K]
            rw [dif_pos ⟨hs, hcd⟩]
            exact (Classical.choose_spec (hrest' s hs cd.1 (hcd.1.symm ▸ hcd.2))).2.2)
      _ ≤ (ENNReal.ofReal ((B.card : ℝ) ^ (-p)) +
            ENNReal.ofReal ((β : ℝ) * (B.card : ℝ) ^ (-q))) +
            ENNReal.ofReal ((B.card : ℝ) ^ (-p)) :=
        add_le_add (hE.trans (add_le_add hmatch hbuffer)) le_rfl
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  have hfail : η (matchShift B 0)ᶜ ≤ ENNReal.ofReal (roundError B p q ℓ β) := by
    calc
      _ ≤ π Aᶜ + ENNReal.ofReal
          ((β : ℝ) * (B.card : ℝ) ^ (-q) + 2 * (B.card : ℝ) ^ (-p)) :=
        bind_failure_le π (fun s => (J s).bind (fun cd => K s cd.1 cd.2)) A
          (matchShift B 0)ᶜ (Set.to_countable _).measurableSet
          (Set.to_countable _).measurableSet _ hgood
      _ ≤ ENNReal.ofReal ((ℓ : ℝ) * (B.card : ℝ) ^ (-q)) +
          ENNReal.ofReal ((β : ℝ) * (B.card : ℝ) ^ (-q) + 2 * (B.card : ℝ) ^ (-p)) :=
        add_le_add (layeredPause_good B M ℓ ρ q hcoupon) le_rfl
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        simp only [roundError, Nat.cast_add]
        ring
  apply clusterCoupling_unshift_second B ℓ (flatClusterLaw B t)
    (flatClusterLaw B (t - B.card * ℓ)) (roundError B p q ℓ β)
  refine ⟨η, hηfst, ?_, hfail⟩
  simpa only [flatClusterLaw, layerGrowthLaw_map_shiftFinite, zero_add] using hηsnd

end IdlaCyl.Reduction
