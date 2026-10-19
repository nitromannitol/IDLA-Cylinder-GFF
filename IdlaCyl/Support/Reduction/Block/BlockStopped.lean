import IdlaCyl.Support.Reduction.Block.BlockFill
import IdlaCyl.Support.Reduction.EntranceTail
import IdlaCyl.Support.Reduction.LayerEntrance
import IdlaCyl.Support.Outer.Translation
import IdlaCyl.Support.PrInnerStopped.Filtration

/-!
Source: paper/idla-cylinder-gff.tex, tex:1147-1156, tex:1227-1251.

# Stopped growth of a block from an exact rectangle

For a general seed `S` the stopped cluster `stoppedFrom B h S ω` runs the stopped
recursion of `stoppedCluster` from `S` instead of from `R_0`; with `S = R_0` it is
`stoppedCluster`. When the seed is the rectangle `R_a` and the stopping height is `a + H`,
the stopped cluster is the vertical translate by `a` of the stopped cluster of height `H`
computed from the tails of the walks after their first entrance to layer `a`, moved down by `a`.
Under the uniform release law these tails are again independent uniform walks, so the
block-filling bound `stopped_block_fill_ge` transfers to the seed `R_a`.
-/

namespace IdlaCyl.Reduction

open MeasureTheory
open scoped ENNReal

/-- The stopped cluster from a general seed `S`: `S` at time `0`, and at each step the exit
site from the part of the current set lying in `R_{h-1}` is added (`tex:1147-1152`). -/
noncomputable def stoppedFrom (B : Base) (h : ℤ) (S : Set (Site B)) (ω : TrajSeq B) :
    ℕ → Set (Site B)
  | 0 => S
  | t + 1 => stoppedFrom B h S ω t ∪
      {exitSite' B (stoppedFrom B h S ω t ∩ R B ((h : ℝ) - 1)) (ω t)}

/-- The general-seed stopped cluster with seed `R_0` is `stoppedCluster`. -/
theorem stoppedFrom_zero_seed_apply (B : Base) (h : ℤ) (ω : TrajSeq B) (t : ℕ) :
    stoppedFrom B h (R B 0) ω t = stoppedCluster B h ω t := by
  induction t with
  | zero => rfl
  | succ n ih => simp only [stoppedFrom, stoppedCluster, ih]

/-- The general-seed stopped cluster with seed `R_0` is `stoppedCluster`. -/
theorem stoppedFrom_zero_seed (B : Base) (h : ℤ) (ω : TrajSeq B) :
    stoppedFrom B h (R B 0) ω = stoppedCluster B h ω :=
  funext (stoppedFrom_zero_seed_apply B h ω)

/-- The seed is contained in the stopped cluster at every time. -/
theorem seed_subset_stoppedFrom (B : Base) (h : ℤ) (S : Set (Site B)) (ω : TrajSeq B)
    (t : ℕ) : S ⊆ stoppedFrom B h S ω t := by
  induction t with
  | zero => exact Set.Subset.rfl
  | succ n ih => exact ih.trans Set.subset_union_left

/-- A walk that has left a set `S` by time `j` has exit time at most `j`. -/
theorem exitTime'_le_of_not_mem (B : Base) (S : Set (Site B)) (X : ℕ → Site B) (j : ℕ)
    (hj : X j ∉ S) : exitTime' B S X ≤ (j : ℕ∞) :=
  MeasureTheory.hittingAfter_le_of_mem (u := fun (k : ℕ) (Y : ℕ → Site B) => Y k)
    (s := Sᶜ) (n := 0) (i := j) (ω := X) (Nat.zero_le j) hj

/-- A walk that has left a set `S` at some time has finite exit time from `S`. -/
theorem exitTime'_ne_top_of_not_mem (B : Base) (S : Set (Site B)) (X : ℕ → Site B) (j : ℕ)
    (hj : X j ∉ S) : exitTime' B S X ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.coe_ne_top j) (exitTime'_le_of_not_mem B S X j hj)

/-- Before a finite exit from `S`, the walk stays in `S`, up to the exit time. -/
theorem exitTime'_prefix_mem (B : Base) (S : Set (Site B)) (X : ℕ → Site B)
    (hf : exitTime' B S X ≠ ⊤) (i : ℕ) (hi : i < resumeCut B S X) : X i ∈ S := by
  obtain ⟨l, hl⟩ := WithTop.ne_top_iff_exists.mp hf
  have hexit : exitTime' B S X = (l : ℕ∞) := hl.symm
  have hcut : resumeCut B S X = l := by
    rw [resumeCut, hexit, untopA_natCast]
  obtain ⟨_, hbefore⟩ := (exitTime'_eq_coe_iff B S X l).mp hexit
  rw [hcut] at hi
  exact hbefore i hi

/-- Vertical translation by `-h` undoes vertical translation by `h` on paths. -/
theorem outerShiftPath_outerShiftPath_neg (B : Base) (h : ℤ) (X : ℕ → Site B) :
    outerShiftPath B h (outerShiftPath B (-h) X) = X := by
  funext n
  change outerShift B h (outerShift B (-h) (X n)) = X n
  refine Prod.ext rfl ?_
  change (X n).2 + -h + h = (X n).2
  ring

/-- The walk's tail after its first entrance to layer `a`, moved down by `a` so that it
starts on layer `0`. -/
noncomputable def blockTail (B : Base) (a : ℕ) (ω : TrajSeq B) : TrajSeq B :=
  fun i => outerShiftPath B (-(a : ℤ)) (resumeTail B (R B (((a : ℤ) : ℝ) - 1)) (ω i))

/-- Moving the shifted tail back up recovers the tail after the first entrance to layer `a`. -/
theorem outerShiftPath_blockTail (B : Base) (a : ℕ) (ω : TrajSeq B) (i : ℕ) :
    outerShiftPath B (a : ℤ) (blockTail B a ω i) =
      resumeTail B (R B (((a : ℤ) : ℝ) - 1)) (ω i) :=
  outerShiftPath_outerShiftPath_neg B (a : ℤ) _

/-- Pathwise translation: the stopped cluster from the rectangle `R_a` with stopping height
`a + H` is the vertical translate by `a` of the stopped cluster of height `H` run on the
shifted tails (`tex:1147-1156`). Exits from a set containing `R_a` read only the tail after
the first entrance to layer `a` (`exitSite_skip_prefix`), and translation commutes with
exits (`exitSite'_outerShift`). -/
theorem stoppedFrom_rect_eq_shift (B : Base) (a H : ℕ) (hH : 1 ≤ H) (ω : TrajSeq B)
    (hadm : ∀ i, CylAdmissible B (ω i)) (h0 : ∀ i, (ω i 0).2 = 0)
    (hall : ∀ i (j : ℤ), ∃ n, (ω i n).2 = j) (t : ℕ) :
    stoppedFrom B ((a : ℤ) + (H : ℤ)) (R B (a : ℝ)) ω t =
      outerShift B (a : ℤ) '' stoppedCluster B (H : ℤ) (blockTail B a ω) t := by
  induction t with
  | zero =>
    show R B (a : ℝ) = outerShift B (a : ℤ) '' R B 0
    rw [outerShift_image_R]
    simp
  | succ n ih =>
    have hR : ((((a : ℤ) + (H : ℤ) : ℤ) : ℝ) - 1) = (((H : ℤ) : ℝ) - 1) + ((a : ℤ) : ℝ) := by
      push_cast
      ring
    have hS : stoppedFrom B ((a : ℤ) + (H : ℤ)) (R B (a : ℝ)) ω n ∩
        R B ((((a : ℤ) + (H : ℤ) : ℤ) : ℝ) - 1) =
        outerShift B (a : ℤ) '' (stoppedCluster B (H : ℤ) (blockTail B a ω) n ∩
          R B (((H : ℤ) : ℝ) - 1)) := by
      rw [ih, Set.image_inter (outerShift B (a : ℤ)).injective, outerShift_image_R, hR]
    have hitne : hitLevel B (a : ℤ) (ω n) ≠ ⊤ := by
      intro htop
      obtain ⟨m, hm⟩ := hall n (a : ℤ)
      exact (hitLevel_eq_top_iff B (a : ℤ) (ω n)).mp htop m hm
    have h00 : (ω n 0).2 ≤ (a : ℤ) := by
      rw [h0 n]
      omega
    have hfin0 : exitTime' B (R B (((a : ℤ) : ℝ) - 1)) (ω n) ≠ ⊤ := by
      rw [exit_lower_eq_hit B (a : ℤ) (ω n) (hadm n) h00 hitne]
      exact hitne
    have hfinS : exitTime' B (stoppedFrom B ((a : ℤ) + (H : ℤ)) (R B (a : ℝ)) ω n ∩
        R B ((((a : ℤ) + (H : ℤ) : ℤ) : ℝ) - 1)) (ω n) ≠ ⊤ := by
      obtain ⟨m, hm⟩ := hall n ((a : ℤ) + (H : ℤ))
      refine exitTime'_ne_top_of_not_mem B _ (ω n) m fun hmem => ?_
      have h2 := mem_R.mp hmem.2
      rw [hm] at h2
      linarith
    have hpre : ∀ i < resumeCut B (R B (((a : ℤ) : ℝ) - 1)) (ω n),
        ω n i ∈ stoppedFrom B ((a : ℤ) + (H : ℤ)) (R B (a : ℝ)) ω n ∩
          R B ((((a : ℤ) + (H : ℤ) : ℤ) : ℝ) - 1) := by
      intro i hi
      have hmem := exitTime'_prefix_mem B _ (ω n) hfin0 i hi
      have hH' : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
      refine ⟨seed_subset_stoppedFrom B _ _ ω n ((R_mono (by push_cast; linarith)) hmem),
        (R_mono (by push_cast; linarith)) hmem⟩
    have hexit : exitSite' B (stoppedFrom B ((a : ℤ) + (H : ℤ)) (R B (a : ℝ)) ω n ∩
        R B ((((a : ℤ) + (H : ℤ) : ℤ) : ℝ) - 1)) (ω n) =
        outerShift B (a : ℤ) (exitSite' B (stoppedCluster B (H : ℤ) (blockTail B a ω) n ∩
          R B (((H : ℤ) : ℝ) - 1)) (blockTail B a ω n)) := by
      have hskip : exitSite' B (stoppedFrom B ((a : ℤ) + (H : ℤ)) (R B (a : ℝ)) ω n ∩
          R B ((((a : ℤ) + (H : ℤ) : ℤ) : ℝ) - 1)) (ω n) =
          exitSite' B (stoppedFrom B ((a : ℤ) + (H : ℤ)) (R B (a : ℝ)) ω n ∩
          R B ((((a : ℤ) + (H : ℤ) : ℤ) : ℝ) - 1))
            (outerShiftPath B (a : ℤ) (blockTail B a ω n)) := by
        rw [outerShiftPath_blockTail]
        exact exitSite_skip_prefix B _ (ω n) _ hpre hfinS
      rw [hskip, hS, exitSite'_outerShift]
    simp only [stoppedFrom, stoppedCluster]
    rw [hexit, ih, Set.image_union, Set.image_singleton]

/-- Translating the uniform starting layer translates the uniform walk law. -/
theorem layerLawAt_map_outerShift (B : Base) (k h : ℤ) :
    (layerLawAt B k).map (outerShift B h) = layerLawAt B (k + h) := by
  unfold layerLawAt
  rw [Measure.map_sum (measurable_of_countable (outerShift B h)).aemeasurable]
  congr 1
  funext x
  rw [Measure.map_smul, Measure.map_dirac' (measurable_of_countable (outerShift B h))]
  rfl

/-- Pushing a measure forward and then binding is binding the composite kernel. -/
theorem bind_map_site (B : Base) (μ : Measure (Site B)) (f : Site B → Site B)
    (g : Site B → Measure (ℕ → Site B)) :
    (μ.map f).bind g = μ.bind (fun x => g (f x)) := by
  have hf : Measurable (fun x : Site B => (Measure.dirac (f x) : Measure (Site B))) :=
    Measure.measurable_dirac.comp (measurable_of_countable f)
  rw [← Measure.bind_dirac_eq_map μ (measurable_of_countable f), Measure.bind_bind
    hf.aemeasurable (measurable_of_countable g).aemeasurable]
  congr 1
  funext x
  exact Measure.dirac_bind (measurable_of_countable g) (f x)

/-- The uniform walk law is invariant under vertical translation, up to the start layer. -/
theorem walkLawUniformAt_map_outerShift (B : Base) (k h : ℤ) :
    (walkLawUniformAt B k).map (outerShiftPath B h) = walkLawUniformAt B (k + h) := by
  rw [walkLawUniformAt_eq_bind, resume_map_bind _ _ _ (measurable_of_countable (walkPathLaw B))
    (measurable_outerShiftPath B h)]
  simp_rw [walkPathLaw_map_outerShift]
  rw [walkLawUniformAt_eq_bind, ← layerLawAt_map_outerShift B k h, bind_map_site]

/-- Shifting the tail of a uniform walk started on layer `0` gives a uniform walk started on
layer `0`: the tails are again uniform walks (`tex:1385-1396`). -/
theorem walkLawUniform_map_blockTail (B : Base) (a : ℕ) :
    (walkLawUniform B).map (fun X : ℕ → Site B =>
      outerShiftPath B (-(a : ℤ)) (resumeTail B (R B (((a : ℤ) : ℝ) - 1)) X)) =
      walkLawUniform B := by
  have hr : Measurable (resumeTail B (R B (((a : ℤ) : ℝ) - 1))) := measurable_resumeTail B _
  unfold walkLawUniform
  have h1 : (walkLawUniformAt B 0).map (fun X : ℕ → Site B =>
      outerShiftPath B (-(a : ℤ)) (resumeTail B (R B (((a : ℤ) : ℝ) - 1)) X)) =
      ((walkLawUniformAt B 0).map (resumeTail B (R B (((a : ℤ) : ℝ) - 1)))).map
        (outerShiftPath B (-(a : ℤ))) :=
    (Measure.map_map (measurable_outerShiftPath B _) hr).symm
  rw [h1, entrance_tail_law B 0 (a : ℤ) (by positivity), walkLawUniformAt_map_outerShift,
    add_neg_cancel]

/-- The uniform walk law on the blocks: shifting every walk's tail after its first entrance to
layer `a` and moving it down by `a` preserves `idlaMeasure` (`tex:1385-1396`). -/
theorem idlaMeasure_map_blockTail (B : Base) (a : ℕ) :
    (idlaMeasure B).map (blockTail B a) = idlaMeasure B := by
  have hg : Measurable (fun X : ℕ → Site B =>
      outerShiftPath B (-(a : ℤ)) (resumeTail B (R B (((a : ℤ) : ℝ) - 1)) X)) :=
    (measurable_outerShiftPath B _).comp (measurable_resumeTail B _)
  have hmap := Measure.infinitePi_map_pi
    (μ := fun _ : ℕ => walkLawUniform B) (f := fun _ : ℕ => fun X : ℕ → Site B =>
      outerShiftPath B (-(a : ℤ)) (resumeTail B (R B (((a : ℤ) : ℝ) - 1)) X))
    (fun _ => hg)
  unfold idlaMeasure
  exact hmap.trans (congrArg Measure.infinitePi (funext fun _ => walkLawUniform_map_blockTail B a))

/-- The block shift is measurable on trajectories. -/
theorem measurable_blockTail (B : Base) (a : ℕ) : Measurable (blockTail B a) :=
  measurable_pi_iff.mpr fun i =>
    (measurable_outerShiftPath B _).comp ((measurable_resumeTail B _).comp (measurable_pi_apply i))

/-- Membership of a fixed site in the stopped cluster is a measurable event. -/
theorem measurableSet_mem_stoppedCluster_site (B : Base) (h : ℤ) (T : ℕ) (p : Site B) :
    MeasurableSet {ω : TrajSeq B | p ∈ stoppedCluster B h ω T} := by
  have hset : {ω : TrajSeq B | p ∈ stoppedCluster B h ω T} =
      {ω : TrajSeq B | p ∈ R B 0} ∪
        ⋃ j ∈ Finset.range T, {ω : TrajSeq B | stoppedSettleSite B h ω j = p} := by
    ext ω
    simp [stoppedCluster_eq_union]
  rw [hset]
  refine MeasurableSet.union (MeasurableSet.const _) ?_
  exact Finset.measurableSet_biUnion _ fun j _ =>
    measurable_stoppedSettleSite B h j (measurableSet_singleton p)

/-- The failure event `R_r ⊄ Ā_h(T)` is measurable. -/
theorem measurableSet_not_subset_stoppedCluster (B : Base) (h : ℤ) (r : ℝ) (T : ℕ) :
    MeasurableSet {ω : TrajSeq B | ¬ R B r ⊆ stoppedCluster B h ω T} := by
  have hset : {ω : TrajSeq B | ¬ R B r ⊆ stoppedCluster B h ω T} =
      ⋃ p : Site B, {ω : TrajSeq B | p ∈ R B r} ∩
        {ω : TrajSeq B | p ∈ stoppedCluster B h ω T}ᶜ := by
    ext ω
    simp [Set.subset_def]
  rw [hset]
  exact MeasurableSet.iUnion fun p =>
    (MeasurableSet.const _).inter (measurableSet_mem_stoppedCluster_site B h T p).compl

/-- **Block filling from the rectangle `R_a`** (`tex:1227-1251`).  With `2 N H` releases the
stopped cluster from `R_a` at height `a + H` fills `R_{a+H}` except on an event of probability
at most `N H e^{-H/8}`.  The pathwise shift `stoppedFrom_rect_eq_shift` holds almost surely, and
the shifted tails have the law `idlaMeasure`, so the bound of `stopped_block_fill_ge` transfers. -/
theorem stoppedFrom_block_fill (B : Base) (a H M : ℕ) (hH : 1 ≤ H)
    (hM : 2 * B.card * H ≤ M) :
    idlaMeasure B {ω : TrajSeq B | ¬ R B ((a + H : ℕ) : ℝ) ⊆
      stoppedFrom B ((a + H : ℕ) : ℤ) (R B a) ω M} ≤
      ENNReal.ofReal ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8)) := by
  have hcast : ((a + H : ℕ) : ℤ) = (a : ℤ) + (H : ℤ) := by push_cast; ring
  have hRcast : ((a + H : ℕ) : ℝ) = (H : ℝ) + ((a : ℤ) : ℝ) := by push_cast; ring
  have hae : ∀ᵐ ω ∂(idlaMeasure B), ∀ i, CylAdmissible B (ω i) ∧ (ω i 0).2 = 0 ∧
      ∀ j : ℤ, ∃ n, (ω i n).2 = j :=
    layerDriving_ae_good B 0
  have hcongr : {ω : TrajSeq B | ¬ R B ((a + H : ℕ) : ℝ) ⊆
        stoppedFrom B ((a + H : ℕ) : ℤ) (R B a) ω M} =ᵐ[idlaMeasure B]
      blockTail B a ⁻¹' {X : TrajSeq B | ¬ R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) X M} := by
    filter_upwards [hae] with ω hω
    have hsh := stoppedFrom_rect_eq_shift B a H hH ω (fun i => (hω i).1)
      (fun i => (hω i).2.1) (fun i j => (hω i).2.2 j) M
    show (¬ R B ((a + H : ℕ) : ℝ) ⊆ stoppedFrom B ((a + H : ℕ) : ℤ) (R B a) ω M) =
      (¬ R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) (blockTail B a ω) M)
    rw [hcast, hsh, hRcast, ← outerShift_image_R B (a : ℤ) (H : ℝ),
      Set.image_subset_image_iff (outerShift B (a : ℤ)).injective]
  have hmeasG : MeasurableSet {X : TrajSeq B | ¬ R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) X M} :=
    measurableSet_not_subset_stoppedCluster B (H : ℤ) (H : ℝ) M
  calc idlaMeasure B {ω : TrajSeq B | ¬ R B ((a + H : ℕ) : ℝ) ⊆
        stoppedFrom B ((a + H : ℕ) : ℤ) (R B a) ω M}
      = idlaMeasure B (blockTail B a ⁻¹' {X : TrajSeq B | ¬ R B (H : ℝ) ⊆
          stoppedCluster B (H : ℤ) X M}) := measure_congr hcongr
    _ = (idlaMeasure B).map (blockTail B a) {X : TrajSeq B | ¬ R B (H : ℝ) ⊆
          stoppedCluster B (H : ℤ) X M} :=
        (Measure.map_apply (measurable_blockTail B a) hmeasG).symm
    _ = idlaMeasure B {X : TrajSeq B | ¬ R B (H : ℝ) ⊆ stoppedCluster B (H : ℤ) X M} := by
        rw [idlaMeasure_map_blockTail]
    _ ≤ ENNReal.ofReal ((B.card : ℝ) * H * Real.exp (-(H : ℝ) / 8)) :=
        stopped_block_fill_ge B H hH M hM

end IdlaCyl.Reduction
