module

public import IdlaCyl.Support.Reduction.Block.FutureLift
public import Mathlib.Probability.ProductMeasure
public import IdlaCyl.Support.Reduction.Block.BlockStopped
public import IdlaCyl.Support.Outer.GhostMarkov
public import IdlaCyl.Support.Outer.ResumeStopped
public import IdlaCyl.Support.Reduction.SeedGrowth

@[expose] public section

/-!
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.

# The future pair of a first hit of a layer

For a layer `k`, the future pair is a law on pairs of walks. The first walk is a uniform walk
from layer `0`, refreshed at its first exit from the half-cylinder `R_{k-1}`; that exit is the
first hit of layer `k`. The second walk is the continuation after that exit, translated down by
`k`. The first marginal is the uniform walk law (`futurePair_fst`), and so is the second
(`futurePair_snd`). Almost surely the second walk is the translate of a tail of the first, spliced
in at the exit time, and the prefix before the splice stays at height at most `k`
(`futurePair_splice`).

The file also splits an infinite product of walk laws into its first `T` coordinates and the
shifted tail (`infinitePi_split`, `infinitePi_split_map`). Concatenating an independent finite
product with an infinite product is again the infinite product, so the first `T` walkers and the
later walkers can be drawn separately.
-/

namespace IdlaCyl.Reduction

open MeasureTheory ProbabilityTheory

/-- The exit set of the future pair: the half-cylinder `R_{k-1}` below layer `k`. -/
abbrev futureSet (B : Base) (k : ℕ) : Set (Site B) := R B (((k : ℤ) : ℝ) - 1)

/-- The refreshed first walk: a uniform walk from layer `0`, refreshed at its first exit from
`futureSet B k`. -/
noncomputable def futureSpliced (B : Base) (k : ℕ) : Measure (ℕ → Site B) :=
  (walkLawUniform B).bind (ghostExitRefreshKernel B (futureSet B k))

/-- The future pair law: the refreshed first walk, paired with its continuation after the exit
from `futureSet B k`, translated down by `k`. -/
noncomputable def futurePair (B : Base) (k : ℕ) :
    Measure ((ℕ → Site B) × (ℕ → Site B)) :=
  (futureSpliced B k).map
    (fun W => (W, outerShiftPath B (-(k : ℤ)) (resumeTail B (futureSet B k) W)))

/-- Translating a site down by `h` and then up by `h` is the identity. -/
theorem outerShift_neg_cancel (B : Base) (h : ℤ) (p : Site B) :
    outerShift B h (outerShift B (-h) p) = p := by
  change (p.1, p.2 + -h + h) = p
  simp

/-- The map sending a refreshed walk to the future pair is measurable. -/
theorem measurable_futurePair_map (B : Base) (k : ℕ) :
    Measurable (fun W : ℕ → Site B =>
      (W, outerShiftPath B (-(k : ℤ)) (resumeTail B (futureSet B k) W))) :=
  measurable_id.prodMk ((measurable_outerShiftPath B _).comp (measurable_resumeTail B _))

/-- Before its exit time, a walk with finite exit time stays in the set it exits from. -/
theorem resumeCut_mem (B : Base) (S : Set (Site B)) (W : ℕ → Site B)
    (hW : exitTime' B S W ≠ ⊤) {i : ℕ} (hi : i < resumeCut B S W) : W i ∈ S := by
  obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.mp hW
  have hexit : exitTime' B S W = (l : ℕ∞) := hl.symm
  have hcut : resumeCut B S W = l := by
    unfold resumeCut
    rw [hexit, untopA_natCast]
  obtain ⟨-, hbefore⟩ := (exitTime'_eq_coe_iff B S W l).mp hexit
  exact hbefore i (by omega)

/-- The refreshed first walk has the uniform walk law: refreshing a uniform walk at its first exit
from `futureSet B k` does not change its law. -/
theorem futureSpliced_eq (B : Base) (k : ℕ) : futureSpliced B k = walkLawUniform B := by
  have h0 : walkLawUniform B = (layerLawAt B 0).bind (walkPathLaw B) :=
    walkLawUniformAt_eq_bind B 0
  unfold futureSpliced
  rw [h0, Measure.bind_bind (measurable_of_countable (walkPathLaw B)).aemeasurable
    (ghostExitRefreshKernel B (futureSet B k)).measurable.aemeasurable]
  congr 1
  funext p
  exact walkPathLaw_bind_ghostExitRefresh_of_subset B p (futureSet B k) (k : ℤ) subset_rfl

/-- The first marginal of the future pair is the uniform walk law. -/
theorem futurePair_fst (B : Base) (k : ℕ) :
    (futurePair B k).map Prod.fst = walkLawUniform B := by
  unfold futurePair
  rw [Measure.map_map measurable_fst (measurable_futurePair_map B k), futureSpliced_eq]
  show (walkLawUniform B).map id = walkLawUniform B
  exact Measure.map_id

/-- The second marginal of the future pair is the uniform walk law: the continuation after the
first hit of layer `k`, translated down by `k`, is again a uniform walk. -/
theorem futurePair_snd (B : Base) (k : ℕ) :
    (futurePair B k).map Prod.snd = walkLawUniform B := by
  unfold futurePair
  rw [Measure.map_map measurable_snd (measurable_futurePair_map B k), futureSpliced_eq]
  exact walkLawUniform_map_blockTail B k

/-- Almost surely in the future pair, the second walk is the translate of a tail of the first:
the first walk is spliced into it at a time `τ` whose prefix stays at height at most `k`. -/
theorem futurePair_splice (B : Base) (k : ℕ) :
    ∀ᵐ p ∂futurePair B k, ∃ τ : ℕ, (∀ i < τ, (p.1 i).2 ≤ (k : ℤ)) ∧
      ∀ n : ℕ, p.1 (τ + n) = outerShift B (k : ℤ) (p.2 n) := by
  have hset : MeasurableSet {p : (ℕ → Site B) × (ℕ → Site B) | ∃ τ : ℕ,
      (∀ i < τ, (p.1 i).2 ≤ (k : ℤ)) ∧ ∀ n : ℕ, p.1 (τ + n) = outerShift B (k : ℤ) (p.2 n)} := by
    have hsplit : {p : (ℕ → Site B) × (ℕ → Site B) | ∃ τ : ℕ,
        (∀ i < τ, (p.1 i).2 ≤ (k : ℤ)) ∧ ∀ n : ℕ, p.1 (τ + n) = outerShift B (k : ℤ) (p.2 n)} =
        ⋃ τ : ℕ, ((⋂ i : ℕ, {p : (ℕ → Site B) × (ℕ → Site B) | i < τ → (p.1 i).2 ≤ (k : ℤ)}) ∩
          ⋂ n : ℕ, {p : (ℕ → Site B) × (ℕ → Site B) |
            p.1 (τ + n) = outerShift B (k : ℤ) (p.2 n)}) := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter]
    rw [hsplit]
    refine MeasurableSet.iUnion fun τ => MeasurableSet.inter (MeasurableSet.iInter fun i => ?_)
      (MeasurableSet.iInter fun n => ?_)
    · by_cases hi : i < τ
      · simp only [hi, true_implies]
        exact measurableSet_le (measurable_snd.comp ((measurable_pi_apply i).comp measurable_fst))
          measurable_const
      · simp [hi]
    · exact measurableSet_eq_fun
        ((measurable_pi_apply (τ + n)).comp measurable_fst)
        ((measurable_of_countable (outerShift B (k : ℤ))).comp
          ((measurable_pi_apply n).comp measurable_snd))
  unfold futurePair
  rw [ae_map_iff (measurable_futurePair_map B k).aemeasurable hset, futureSpliced_eq]
  have hfin : ∀ᵐ W ∂walkLawUniform B, exitTime' B (futureSet B k) W ≠ ⊤ := by
    unfold walkLawUniform
    filter_upwards [walkLawUniformAt_ae_hits B 0 (k : ℤ)] with W hW
    obtain ⟨n, hn⟩ := hW
    exact exitTime'_ne_top_of_height B (S := futureSet B k) (h := (k : ℤ)) (subset_refl _)
      hn.symm.le
  filter_upwards [hfin] with W hW
  refine ⟨resumeCut B (futureSet B k) W, fun i hi => ?_, fun n => ?_⟩
  · have h1 := mem_R.mp (resumeCut_mem B (futureSet B k) W hW hi)
    have h2 : (((W i).2 : ℤ) : ℝ) ≤ (((k : ℤ)) : ℝ) := by linarith
    exact_mod_cast h2
  · show W (resumeCut B (futureSet B k) W + n) =
      outerShift B (k : ℤ) (outerShift B (-(k : ℤ)) (resumeTail B (futureSet B k) W n))
    rw [outerShift_neg_cancel]
    rfl

section SplitInfinitePi


variable {X : Type*} [MeasurableSpace X]

/-- Concatenate a finite prefix and an infinite tail. -/
def splitAppend (T : ℕ) (q : (Fin T → X) × (ℕ → X)) : ℕ → X :=
  fun j => if h : j < T then q.1 ⟨j, h⟩ else q.2 (j - T)

/-- The prefix indices of a finite set of naturals. -/
def splitFin (T : ℕ) (s : Finset ℕ) : Finset (Fin T) :=
  Finset.univ.filter (fun i : Fin T => (i : ℕ) ∈ s)

/-- The tail indices of a finite set of naturals, shifted down by `T`. -/
def splitTail (T : ℕ) (s : Finset ℕ) : Finset ℕ :=
  (s.filter (fun i => ¬ i < T)).image (fun i => i - T)

theorem measurable_splitAppend (T : ℕ) : Measurable (splitAppend (X := X) T) := by
  refine measurable_pi_iff.mpr fun j => ?_
  by_cases h : j < T
  · have : (fun q : (Fin T → X) × (ℕ → X) => splitAppend T q j) = fun q => q.1 ⟨j, h⟩ := by
      funext q; simp [splitAppend, h]
    rw [this]; exact (measurable_pi_apply _).comp measurable_fst
  · have : (fun q : (Fin T → X) × (ℕ → X) => splitAppend T q j) = fun q => q.2 (j - T) := by
      funext q; simp [splitAppend, h]
    rw [this]; exact (measurable_pi_apply _).comp measurable_snd

omit [MeasurableSpace X] in
theorem splitAppend_lt (T : ℕ) (q : (Fin T → X) × (ℕ → X)) (i : Fin T) :
    splitAppend T q i = q.1 i := by
  unfold splitAppend
  rw [dif_pos i.2]

omit [MeasurableSpace X] in
theorem splitAppend_ge (T : ℕ) (q : (Fin T → X) × (ℕ → X)) {j : ℕ} (hj : T ≤ j) :
    splitAppend T q j = q.2 (j - T) := by
  unfold splitAppend
  rw [dif_neg (by omega)]

/-- Concatenating an independent finite product and infinite product gives the infinite product. -/
theorem infinitePi_split (T : ℕ) (μ : Measure X) [IsProbabilityMeasure μ] :
    ((Measure.pi fun _ : Fin T => μ).prod (Measure.infinitePi fun _ : ℕ => μ)).map
      (splitAppend (X := X) T) = Measure.infinitePi fun _ : ℕ => μ := by
  refine Measure.eq_infinitePi (fun _ : ℕ => μ) ?_
  intro s t ht
  have hpre : splitAppend (X := X) T ⁻¹' Set.pi (↑s) t =
      Set.pi (↑(splitFin T s)) (fun i : Fin T => t i) ×ˢ
        Set.pi (↑(splitTail T s)) (fun j => t (j + T)) := by
    ext ⟨a, b⟩
    constructor
    · intro h
      have h' : ∀ j ∈ s, splitAppend T (a, b) j ∈ t j := h
      refine ⟨fun i hi => ?_, fun j hj => ?_⟩
      · have hi' : (i : ℕ) ∈ s := by
          simpa [splitFin] using hi
        have := h' i hi'
        rwa [splitAppend_lt] at this
      · obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hj)
        obtain ⟨his, hTi⟩ := Finset.mem_filter.mp hi
        have hT : T ≤ i := by simp at hTi; omega
        have := h' i his
        rw [splitAppend_ge T _ hT] at this
        have hi_eq : j + T = i := by omega
        show (a, b).2 j ∈ t (j + T)
        rw [hi_eq, ← hij]
        exact this
    · rintro ⟨ha, hb⟩ j hj
      show splitAppend T (a, b) j ∈ t j
      by_cases hjT : j < T
      · have hjs : j ∈ s := Finset.mem_coe.mp hj
        have hmem : (⟨j, hjT⟩ : Fin T) ∈ (↑(splitFin T s) : Set (Fin T)) := by
          simp [splitFin, hjs]
        have := ha ⟨j, hjT⟩ hmem
        have h2 : splitAppend T (a, b) j = a ⟨j, hjT⟩ := by
          unfold splitAppend; rw [dif_pos hjT]
        rw [h2]; exact this
      · have hmem : j - T ∈ (↑(splitTail T s) : Set ℕ) := by
          simp only [splitTail, Finset.coe_image, Finset.coe_filter, Set.mem_image,
            Set.mem_setOf_eq]
          exact ⟨j, ⟨hj, by omega⟩, rfl⟩
        have : (a, b).2 (j - T) ∈ t (j - T + T) := hb (j - T) hmem
        rw [Nat.sub_add_cancel (by omega : T ≤ j)] at this
        rw [splitAppend_ge T _ (by omega : T ≤ j)]
        exact this
  rw [Measure.map_apply (measurable_splitAppend T)
    (MeasurableSet.pi (Finset.countable_toSet s) fun i _ => ht i), hpre, Measure.prod_prod,
    Measure.pi_pi_finset, Measure.infinitePi_pi (fun _ : ℕ => μ) (t := fun j => t (j + T))
      (fun j _ => ht (j + T))]
  have hS1 : ∏ i ∈ splitFin T s, μ (t i) = ∏ i ∈ s.filter (fun i => i < T), μ (t i) := by
    refine Finset.prod_bij (fun (i : Fin T) _ => (i : ℕ)) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [splitFin, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact Finset.mem_filter.mpr ⟨hi, i.2⟩
    · intro a _ b _ h
      exact Fin.ext h
    · intro b hb
      obtain ⟨hbs, hbT⟩ := Finset.mem_filter.mp hb
      exact ⟨⟨b, hbT⟩, by simp [splitFin, hbs], rfl⟩
    · intro i _
      rfl
  have hS2 : ∏ j ∈ splitTail T s, μ (t (j + T)) = ∏ i ∈ s.filter (fun i => ¬ i < T), μ (t i) := by
    unfold splitTail
    rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro i hi
      obtain ⟨-, hiT⟩ := Finset.mem_filter.mp hi
      rw [Nat.sub_add_cancel (by omega : T ≤ i)]
    · intro x hx y hy hxy
      obtain ⟨-, hx'⟩ := Finset.mem_filter.mp hx
      obtain ⟨-, hy'⟩ := Finset.mem_filter.mp hy
      simp only at hxy hx' hy'
      omega
  rw [hS1, hS2, Finset.prod_filter_mul_prod_filter_not]

/-- Splitting an infinite product into its first `T` coordinates and the shifted tail is
measure-preserving onto the product of the finite and the infinite product laws. -/
theorem infinitePi_split_map (T : ℕ) (μ : Measure X) [IsProbabilityMeasure μ] :
    (Measure.infinitePi fun _ : ℕ => μ).map
      (fun ω : ℕ → X => ((fun i : Fin T => ω i), (fun s : ℕ => ω (T + s)))) =
      (Measure.pi fun _ : Fin T => μ).prod (Measure.infinitePi fun _ : ℕ => μ) := by
  have hD : Measurable (fun ω : ℕ → X => ((fun i : Fin T => ω i), (fun s : ℕ => ω (T + s)))) :=
    (measurable_pi_iff.mpr fun i => measurable_pi_apply _).prodMk
      (measurable_pi_iff.mpr fun s => measurable_pi_apply _)
  conv_lhs => rw [← infinitePi_split T μ]
  rw [Measure.map_map hD (measurable_splitAppend T)]
  have hid : ((fun ω : ℕ → X => ((fun i : Fin T => ω i), (fun s : ℕ => ω (T + s)))) ∘
      splitAppend (X := X) T) = id := by
    funext q
    show ((fun i : Fin T => splitAppend T q i), (fun s : ℕ => splitAppend T q (T + s))) = q
    refine Prod.ext (funext fun i => splitAppend_lt T q i) (funext fun s => ?_)
    show splitAppend T q (T + s) = q.2 s
    rw [splitAppend_ge T q (by omega : T ≤ T + s), Nat.add_sub_cancel_left]
  rw [hid, Measure.map_id]

end SplitInfinitePi

end IdlaCyl.Reduction
