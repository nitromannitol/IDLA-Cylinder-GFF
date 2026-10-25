module

/-
One block reduction round with the three comparison inputs as hypotheses.
Source: paper/idla-cylinder-gff.tex, tex:1227-1251 (block filling), tex:1385-1396,1440-1453.
-/
public import IdlaCyl.Support.Reduction.Block.BlockBuffer
public import IdlaCyl.Support.Reduction.Block.BlockCompare
public import IdlaCyl.Support.Reduction.BindCouplings
public import IdlaCyl.Support.Reduction.BufferGrowth
public import IdlaCyl.Support.Reduction.CountableProbability
public import IdlaCyl.Support.Reduction.LayerPause
public import IdlaCyl.Support.Reduction.SeedGrowth
public import IdlaCyl.Support.Reduction.ShiftCoupling
public import IdlaCyl.Support.Reduction.ShiftLaws

@[expose] public section

/-!
# One block reduction round from abstract comparison inputs

Fix a base `B` with `N = B.card`, a block height `H`, a layer count `ℓ ≥ 3`, a pause `π` on the
resumption states `(ResumeState B, ℕ)`, and a good set `A` of states whose deep and shallow
queues have the block lengths. For `t = 2 N H ℓ + ρ` additions, the flat cluster at time `t`
is coupled with the flat cluster at time `t - N H ℓ`, shifted by `ℓ H`.

The round takes three inputs as hypotheses rather than from the Silvestri comparisons:

* `hdeep`: deep resumptions from a seed `R_{ℓH}` couple with canonical growth, with error `εd`;
* `hshallow`: shallow resumptions on a connected seed filling the rectangle of height `(ℓ+1) H`
  couple with canonical growth, with error `εs`;
* `hbuf`: canonical growth from layer `ℓH` with `N H (ℓ-1)` additions fills the rectangle of
  height `(ℓ+1) H` except with probability `εb`.

The failure allowance of the coupling is `εA + εb + εd + εs`. The corollary
`block_round_of_ledger'` supplies the three inputs from the Silvestri comparisons and the
canonical block fill, and recovers the round with allowance `εA + N H e^{-H/8} + 2 N^{-p}`.
-/

namespace IdlaCyl.Reduction

open MeasureTheory

/-- One block reduction round over a fixed base, with the deep comparison, the shallow comparison
and the buffer fill supplied as hypotheses. The deep and shallow comparisons have errors `εd` and
`εs`, and the buffer fill has failure probability at most `εb`. -/
theorem block_round_of_ledger_gen (B : Base) (H ℓ ρ t : ℕ)
    (π : Measure (ResumeState B × ℕ)) [IsProbabilityMeasure π]
    (A : Set (ResumeState B × ℕ)) (deepQ shallowQ : ResumeState B × ℕ → List (Site B))
    (εA εd εs εb : ℝ) (hεA : 0 ≤ εA) (hεd : 0 ≤ εd) (hεs : 0 ≤ εs) (hεb : 0 ≤ εb)
    (hdeep : ∀ (F : ResumeFinite B) (L : List (Site B)),
      resumeSeed B F = R B ((ℓ * H : ℕ) : ℝ) →
      (∀ z ∈ L, z.2 ≤ (((ℓ - 1) * H : ℕ) : ℤ)) → L.length = B.card * H * (ℓ - 1) →
      ClusterCoupling B (resumeRun B F L)
        (layerGrowthLaw B (shiftFinite B (ℓ * H) (resumeEmpty B)) ((ℓ * H : ℕ) : ℤ) L.length)
        0 εd)
    (hshallow : ∀ (c : ResumeFinite B) (L : List (Site B)),
      c ∈ filled B (((ℓ + 1) * H : ℕ) : ℤ) → SeedConnected B (resumeSeed B c) →
      (∀ z ∈ L, z.2 ≤ ((ℓ * H : ℕ) : ℤ)) → L.length = B.card * H →
      ClusterCoupling B ((resumeRun B c L).bind (fun C => layerGrowthLaw B C 0 ρ))
        (layerGrowthLaw B c ((ℓ * H : ℕ) : ℤ) (L.length + ρ)) 0 εs)
    (hbuf : layerGrowthLaw B (shiftFinite B (ℓ * H) (resumeEmpty B)) ((ℓ * H : ℕ) : ℤ)
      (B.card * H * (ℓ - 1)) (filled B (((ℓ + 1) * H : ℕ) : ℤ))ᶜ ≤ ENNReal.ofReal εb)
    (hℓ3 : 3 ≤ ℓ) (htime : t = 2 * B.card * H * ℓ + ρ)
    (hfin : π.bind (fun s => finishUniform B s.1 s.2) = flatClusterLaw B t)
    (hπA : π Aᶜ ≤ ENNReal.ofReal εA)
    (hsplit : ∀ s ∈ A, resumeSeed B s.1.1 = R B ((ℓ * H : ℕ) : ℝ) ∧ s.2 = ρ ∧
      (deepQ s).length = B.card * H * (ℓ - 1) ∧ (∀ z ∈ deepQ s, z.2 ≤ (((ℓ - 1) * H : ℕ) : ℤ)) ∧
      (shallowQ s).length = B.card * H ∧ (∀ z ∈ shallowQ s, z.2 ≤ ((ℓ * H : ℕ) : ℤ)) ∧
      finishUniform B s.1 s.2 = (resumeRun B s.1.1 (deepQ s)).bind
        (fun C => (resumeRun B C (shallowQ s)).bind (fun D => layerGrowthLaw B D 0 ρ))) :
    ClusterCoupling B (flatClusterLaw B t) (flatClusterLaw B (t - B.card * H * ℓ)) (H * ℓ)
      (εA + εb + εd + εs) := by
  classical
  let Fd := layerGrowthLaw B (shiftFinite B (ℓ * H) (resumeEmpty B)) ((ℓ * H : ℕ) : ℤ)
    (B.card * H * (ℓ - 1))
  let F := shiftFinite B (ℓ * H) (resumeEmpty B)
  let C : Set (ResumeFinite B) :=
    {c | c ∈ filled B (((ℓ + 1) * H : ℕ) : ℤ) ∧ SeedConnected B (resumeSeed B c)}
  let G := fun c : ResumeFinite B => layerGrowthLaw B c ((ℓ * H : ℕ) : ℤ) (B.card * H + ρ)
  -- Counting: the deep and shallow lengths add up to `t - N H ℓ`.
  have hP : 2 * B.card * H * ℓ = 2 * (B.card * H * ℓ) := by ring
  have hQ : B.card * H * ℓ = B.card * H * (ℓ - 1) + B.card * H := by
    have hℓ' : ℓ = (ℓ - 1) + 1 := by omega
    calc B.card * H * ℓ = B.card * H * ((ℓ - 1) + 1) := by rw [← hℓ']
      _ = _ := by ring
  have hsub : B.card * H * (ℓ - 1) + (B.card * H + ρ) = t - B.card * H * ℓ := by
    omega
  have hseedF : resumeSeed B F = R B (((ℓ * H : ℕ) : ℤ) : ℝ) := by
    rw [resumeSeed_shiftFinite_empty, Int.cast_natCast]
  -- Deep comparison, with the queue length read off the hypothesis on `A`.
  have hdeep' (s : ResumeState B × ℕ) (hs : s ∈ A) :
      ClusterCoupling B (resumeRun B s.1.1 (deepQ s)) Fd 0 εd := by
    obtain ⟨hseed, -, hDlen, hDst, -⟩ := hsplit s hs
    have hc := hdeep s.1.1 (deepQ s) hseed hDst hDlen
    rw [hDlen] at hc
    exact hc
  -- Shallow comparison on a connected seed filling the rectangle of height `(ℓ+1) H`.
  have hrest' (s : ResumeState B × ℕ) (hs : s ∈ A) (c : ResumeFinite B) (hc : c ∈ C) :
      ClusterCoupling B ((resumeRun B c (shallowQ s)).bind (fun d => layerGrowthLaw B d 0 ρ))
        (G c) 0 εs := by
    obtain ⟨-, -, -, -, hSlen, hSst, -⟩ := hsplit s hs
    have hc' := hshallow c (shallowQ s) hc.1 hc.2 hSst hSlen
    rw [hSlen] at hc'
    exact hc'
  let U := fun s : ResumeState B × ℕ => if s ∈ A then
    resumeRun B s.1.1 (deepQ s) else Measure.dirac s.1.1
  let V := fun (s : ResumeState B × ℕ) (c : ResumeFinite B) => if s ∈ A then
    (resumeRun B c (shallowQ s)).bind (fun d => layerGrowthLaw B d 0 ρ)
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
    · obtain ⟨-, -, -, -, -, -, hfs⟩ := hsplit s hs
      simpa only [U, V, if_pos hs] using hfs.symm
    · simp only [U, V, if_neg hs, Measure.dirac_bind (measurable_of_countable _)]
  have hηfst : η.map Prod.fst = flatClusterLaw B t := by
    rw [hmarg.1]
    simp_rw [hUV]
    exact hfin
  have hηsnd : η.map Prod.snd = layerGrowthLaw B F ((ℓ * H : ℕ) : ℤ) (t - B.card * H * ℓ) := by
    rw [hmarg.2, measure_univ, one_smul]
    change (layerGrowthLaw B F ((ℓ * H : ℕ) : ℤ) (B.card * H * (ℓ - 1))).bind
      (fun c => layerGrowthLaw B c ((ℓ * H : ℕ) : ℤ) (B.card * H + ρ)) = _
    rw [← layerGrowthLaw_add, hsub]
  -- The buffer fill from `R_{ℓH}` fails with probability at most `εb`.
  have hconn0 : Fd {c | ¬ SeedConnected B (resumeSeed B c)} = 0 :=
    layerGrowthLaw_not_seedConnected B F (((ℓ * H : ℕ) : ℤ))
      (by rw [hseedF]; exact seedConnected_R B _) (by rw [hseedF]) _
  have hfill : Fd Cᶜ ≤ ENNReal.ofReal εb := by
    have hsub' : Cᶜ ⊆ (filled B (((ℓ + 1) * H : ℕ) : ℤ))ᶜ ∪
        {c | ¬ SeedConnected B (resumeSeed B c)} := by
      intro c hc
      by_cases h1 : c ∈ filled B (((ℓ + 1) * H : ℕ) : ℤ)
      · exact Or.inr (fun h2 => hc ⟨h1, h2⟩)
      · exact Or.inl h1
    calc Fd Cᶜ ≤ Fd ((filled B (((ℓ + 1) * H : ℕ) : ℤ))ᶜ ∪
          {c | ¬ SeedConnected B (resumeSeed B c)}) := measure_mono hsub'
      _ ≤ Fd (filled B (((ℓ + 1) * H : ℕ) : ℤ))ᶜ + Fd {c | ¬ SeedConnected B (resumeSeed B c)} :=
          measure_union_le _ _
      _ ≤ _ := by rw [hconn0, add_zero]; exact hbuf
  have hgood (s : ResumeState B × ℕ) (hs : s ∈ A) :
      ((J s).bind (fun cd => K s cd.1 cd.2)) (matchShift B 0)ᶜ ≤
        ENNReal.ofReal (εd + εb + εs) := by
    let E : Set (ResumeFinite B × ResumeFinite B) := {cd | cd.1 = cd.2 ∧ cd.2 ∈ C}
    have hmatch : J s (matchShift B 0)ᶜ ≤ ENNReal.ofReal εd := by
      dsimp only [J]
      rw [dif_pos hs]
      exact (Classical.choose_spec (hdeep' s hs)).2.2
    have hbuffer : J s (Prod.snd ⁻¹' Cᶜ) ≤ ENNReal.ofReal εb := by
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
      _ ≤ J s Eᶜ + ENNReal.ofReal εs :=
        bind_failure_le (J s) (fun cd => K s cd.1 cd.2) E (matchShift B 0)ᶜ
          (Set.to_countable _).measurableSet (Set.to_countable _).measurableSet _ (by
            intro cd hcd
            dsimp only [K]
            rw [dif_pos ⟨hs, hcd⟩]
            exact (Classical.choose_spec (hrest' s hs cd.1 (hcd.1.symm ▸ hcd.2))).2.2)
      _ ≤ (ENNReal.ofReal εd + ENNReal.ofReal εb) + ENNReal.ofReal εs :=
        add_le_add (hE.trans (add_le_add hmatch hbuffer)) le_rfl
      _ = _ := by
        rw [← ENNReal.ofReal_add hεd hεb, ← ENNReal.ofReal_add (add_nonneg hεd hεb) hεs]
  have hfail : η (matchShift B 0)ᶜ ≤ ENNReal.ofReal (εA + εb + εd + εs) := by
    calc
      _ ≤ π Aᶜ + ENNReal.ofReal (εd + εb + εs) :=
        bind_failure_le π (fun s => (J s).bind (fun cd => K s cd.1 cd.2)) A
          (matchShift B 0)ᶜ (Set.to_countable _).measurableSet
          (Set.to_countable _).measurableSet _ hgood
      _ ≤ ENNReal.ofReal εA + ENNReal.ofReal (εd + εb + εs) := add_le_add hπA le_rfl
      _ = _ := by
        rw [← ENNReal.ofReal_add hεA (add_nonneg (add_nonneg hεd hεb) hεs)]
        congr 1
        ring
  rw [Nat.mul_comm H ℓ]
  apply clusterCoupling_unshift_second B (ℓ * H) (flatClusterLaw B t)
    (flatClusterLaw B (t - B.card * H * ℓ))
  refine ⟨η, hηfst, ?_, hfail⟩
  simpa only [flatClusterLaw, layerGrowthLaw_map_shiftFinite, zero_add] using hηsnd

/-- **One block reduction round** (`tex:1385-1453`), with the Silvestri comparisons and the
canonical block fill supplied by the existing lemmas. This is the round of `block_round_of_ledger`,
recovered from `block_round_of_ledger_gen` with `εd = εs = N^{-p}` and
`εb = N H e^{-H/8}`. -/
theorem block_round_of_ledger' (hsil : External.silvestri_prop2)
    (r : ℕ) (p : ℝ) (hp : 0 < p) :
    ∃ b : ℝ, 1 ≤ b ∧ ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card →
    ∀ (H ℓ ρ t : ℕ) (π : Measure (ResumeState B × ℕ)) [IsProbabilityMeasure π]
      (A : Set (ResumeState B × ℕ))
      (deepQ shallowQ : ResumeState B × ℕ → List (Site B)) (εA : ℝ), 0 ≤ εA →
    1 ≤ H → b * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ) ≤ (H : ℝ) → 3 ≤ ℓ →
    t = 2 * B.card * H * ℓ + ρ → t ≤ B.card ^ r →
    π.bind (fun s => finishUniform B s.1 s.2) = flatClusterLaw B t → π Aᶜ ≤ ENNReal.ofReal εA →
    (∀ s ∈ A, resumeSeed B s.1.1 = R B ((ℓ * H : ℕ) : ℝ) ∧ s.2 = ρ ∧
      (deepQ s).length = B.card * H * (ℓ - 1) ∧ (∀ z ∈ deepQ s, z.2 ≤ (((ℓ - 1) * H : ℕ) : ℤ)) ∧
      (shallowQ s).length = B.card * H ∧ (∀ z ∈ shallowQ s, z.2 ≤ ((ℓ * H : ℕ) : ℤ)) ∧
      finishUniform B s.1 s.2 = (resumeRun B s.1.1 (deepQ s)).bind
        (fun C => (resumeRun B C (shallowQ s)).bind (fun D => layerGrowthLaw B D 0 ρ))) →
    ClusterCoupling B (flatClusterLaw B t) (flatClusterLaw B (t - B.card * H * ℓ)) (H * ℓ)
      (εA + (B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8) + 2 * (B.card : ℝ) ^ (-p)) := by
  classical
  obtain ⟨b₁, hb₁, N₁, hdeep⟩ := block_deep_comparison hsil r p hp
  obtain ⟨b₂, hb₂, N₂, hrest⟩ := block_shallow_comparison hsil r p hp
  refine ⟨max b₁ b₂, hb₁.trans (le_max_left _ _), max N₁ N₂, ?_⟩
  intro B hN H ℓ ρ t π _ A deepQ shallowQ εA hεA hH hbH hℓ3 htime htr hfin hπA hsplit
  have hNpos : 0 < B.card := lt_of_lt_of_le (by decide : 0 < 2) B.nontrivial
  have hHpos : 0 < H := by omega
  have hNH : 0 < B.card * H := Nat.mul_pos hNpos hHpos
  have hℓ1 : 1 ≤ ℓ := by omega
  have hlog : 0 ≤ Real.log (B.card : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B.card))
  have hbsmall (a : ℝ) (ha : a ≤ max b₁ b₂) :
      a * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ) ≤ (H : ℝ) :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ha (Real.sqrt_nonneg _)) hlog).trans hbH
  have hP : 2 * B.card * H * ℓ = 2 * (B.card * H * ℓ) := by ring
  have hQ : B.card * H * ℓ = B.card * H * (ℓ - 1) + B.card * H := by
    have hℓ' : ℓ = (ℓ - 1) + 1 := by omega
    calc B.card * H * ℓ = B.card * H * ((ℓ - 1) + 1) := by rw [← hℓ']
      _ = _ := by ring
  have hsub : B.card * H * (ℓ - 1) + (B.card * H + ρ) = t - B.card * H * ℓ := by
    omega
  have hDpos : 0 < B.card * H * (ℓ - 1) := Nat.mul_pos hNH (by omega)
  have hDle : B.card * H * (ℓ - 1) ≤ B.card ^ r := by omega
  have hSpos : 0 < B.card * H + ρ := by omega
  have hSle : B.card * H + ρ ≤ B.card ^ r := by omega
  have hfillset : filled B (((ℓ * H : ℕ) : ℤ) + (H : ℤ)) = filled B (((ℓ + 1) * H : ℕ) : ℤ) := by
    congr 1
    push_cast
    ring
  have hn : 2 * B.card * H ≤ B.card * H * (ℓ - 1) := by
    have h2 : 2 ≤ ℓ - 1 := by omega
    calc 2 * B.card * H = B.card * H * 2 := by ring
      _ ≤ B.card * H * (ℓ - 1) := Nat.mul_le_mul (le_refl _) h2
  have hbuf : layerGrowthLaw B (shiftFinite B (ℓ * H) (resumeEmpty B)) ((ℓ * H : ℕ) : ℤ)
      (B.card * H * (ℓ - 1)) (filled B (((ℓ + 1) * H : ℕ) : ℤ))ᶜ ≤
      ENNReal.ofReal ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8)) := by
    rw [← hfillset]
    exact canonical_block_fill B (ℓ * H) ((ℓ * H : ℕ) : ℤ) le_rfl H hHpos
      (B.card * H * (ℓ - 1)) hn
  have hdeepB : ∀ (F : ResumeFinite B) (L : List (Site B)),
      resumeSeed B F = R B ((ℓ * H : ℕ) : ℝ) →
      (∀ z ∈ L, z.2 ≤ (((ℓ - 1) * H : ℕ) : ℤ)) → L.length = B.card * H * (ℓ - 1) →
      ClusterCoupling B (resumeRun B F L)
        (layerGrowthLaw B (shiftFinite B (ℓ * H) (resumeEmpty B)) ((ℓ * H : ℕ) : ℤ) L.length)
        0 ((B.card : ℝ) ^ (-p)) := by
    intro F L hseed hst hlen
    have hc := hdeep B ((le_max_left N₁ N₂).trans hN) H ℓ F L hℓ1
      (hbsmall b₁ (le_max_left _ _)) hseed hst (by rw [hlen]; exact hDpos)
      (by rw [hlen]; exact hDle)
    rw [hlen] at hc ⊢
    exact hc
  have hshallowB : ∀ (c : ResumeFinite B) (L : List (Site B)),
      c ∈ filled B (((ℓ + 1) * H : ℕ) : ℤ) → SeedConnected B (resumeSeed B c) →
      (∀ z ∈ L, z.2 ≤ ((ℓ * H : ℕ) : ℤ)) → L.length = B.card * H →
      ClusterCoupling B ((resumeRun B c L).bind (fun C => layerGrowthLaw B C 0 ρ))
        (layerGrowthLaw B c ((ℓ * H : ℕ) : ℤ) (L.length + ρ)) 0 ((B.card : ℝ) ^ (-p)) := by
    intro c L hc hconn hst hlen
    have hc' := hrest B ((le_max_right N₁ N₂).trans hN) H ℓ ρ c L
      (hbsmall b₂ (le_max_right _ _)) hc hconn hst (by rw [hlen]; exact hSpos)
      (by rw [hlen]; exact hSle)
    rw [hlen] at hc' ⊢
    exact hc'
  have key := block_round_of_ledger_gen B H ℓ ρ t π A deepQ shallowQ εA
    ((B.card : ℝ) ^ (-p)) ((B.card : ℝ) ^ (-p)) ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8))
    hεA (by positivity) (by positivity) (by positivity) hdeepB hshallowB hbuf hℓ3 htime
    hfin hπA hsplit
  have e : εA + (B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8) + (B.card : ℝ) ^ (-p)
      + (B.card : ℝ) ^ (-p) = εA + (B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8)
        + 2 * (B.card : ℝ) ^ (-p) := by ring
  rw [e] at key
  exact key

end IdlaCyl.Reduction
