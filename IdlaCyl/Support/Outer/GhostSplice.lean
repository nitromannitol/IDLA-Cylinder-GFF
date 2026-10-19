/-
Site-indexed ghost splicing for the outer bound.
Source: paper/idla-cylinder-gff.tex, tex:1271-1305.

The input consists of an independent canonical trajectory driver and one walk
from each interior site. A settled particle keeps its stopped prefix and uses
that site's ghost for its continuation. Ghosts are shared with the full paths;
independence concerns the stopped history only.
-/
import IdlaCyl.Support.Outer.StoppedBookkeeping
import IdlaCyl.Support.Outer.GhostMarkov
import IdlaCyl.Support.Outer.GhostExitSwap
import IdlaCyl.Support.StoppedAe

attribute [local instance] Classical.propDecidable

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

/-- The natural exit index, read only on the finite-exit event in pathwise uses. -/
def ghostSpliceIndex (B : Base) (h : ℤ) (ω : TrajSeq B) (j : ℕ) : ℕ :=
  WithTop.untopA (exitTime' B (stoppedCluster B h ω j ∩ R B ((h : ℝ) - 1)) (ω j))

/-- Splice the ghost at each interior settlement among the first `T` particles.
The unchanged branch covers freezing, unused labels, and exceptional inputs. -/
def ghostSpliceTraj (B : Base) (h : ℤ) (T : ℕ)
    (ω : TrajSeq B) (U : GhostDriver B h) : TrajSeq B :=
  fun j => if j < T then
    if hz : stoppedSettleSite B h ω j ∈ outerInterior B h then
      ghostSplicePath B (ω j) (U ⟨stoppedSettleSite B h ω j, hz⟩)
        (ghostSpliceIndex B h ω j)
    else ω j
  else ω j

/-- The concrete forward coupling, as the pushforward of independent inputs. -/
def outerGhostMeasure (B : Base) (h : ℤ) (T : ℕ) :
    Measure (TrajSeq B × GhostDriver B h) :=
  ((idlaMeasure B).prod (ghostLaw B h)).map
    (fun p => (ghostSpliceTraj B h T p.1 p.2, p.2))

private theorem measurable_ghostHistoryIndex (B : Base) (h : ℤ) (j : ℕ) :
    Measurable (fun p : (Fin j → Site B) × (ℕ → Site B) =>
      WithTop.untopA (exitTime' B ((R B 0 ∪ Set.range p.1) ∩ R B ((h : ℝ) - 1)) p.2)) := by
  apply measurable_from_prod_countable_right
  intro s
  change Measurable (fun X : ℕ → Site B =>
    WithTop.untopA (exitTime' B ((R B 0 ∪ Set.range s) ∩ R B ((h : ℝ) - 1)) X))
  exact measurable_ghostExitIndex B ((R B 0 ∪ Set.range s) ∩ R B ((h : ℝ) - 1))

private theorem ghostSpliceIndex_eq_history (B : Base) (h : ℤ) (j : ℕ) (ω : TrajSeq B) :
    ghostSpliceIndex B h ω j = WithTop.untopA
      (exitTime' B ((R B 0 ∪ Set.range (fun i : Fin j => stoppedSettleSite B h ω i)) ∩
        R B ((h : ℝ) - 1)) (ω j)) := by
  unfold ghostSpliceIndex
  rw [measurable_stoppedCluster_eq B h
    (s := fun i : Fin j => stoppedSettleSite B h ω i) (fun _ => rfl)]

/-- The random splice index is measurable, including its exceptional total branch. -/
theorem measurable_ghostSpliceIndex (B : Base) (h : ℤ) (j : ℕ) :
    Measurable (fun ω : TrajSeq B => ghostSpliceIndex B h ω j) := by
  have hH : Measurable (fun ω : TrajSeq B => fun i : Fin j => stoppedSettleSite B h ω i) :=
    measurable_pi_iff.mpr fun i => measurable_stoppedSettleSite B h i
  have hf := (measurable_ghostHistoryIndex B h j).comp (hH.prodMk (measurable_pi_apply j))
  have heq : (fun ω : TrajSeq B => ghostSpliceIndex B h ω j) =
      fun ω => WithTop.untopA
        (exitTime' B ((R B 0 ∪ Set.range (fun i : Fin j => stoppedSettleSite B h ω i)) ∩
          R B ((h : ℝ) - 1)) (ω j)) :=
    funext (ghostSpliceIndex_eq_history B h j)
  rw [heq]
  exact hf

private theorem measurable_ghostSelect (B : Base) (h : ℤ) :
    Measurable (fun p : Site B × GhostDriver B h =>
      if hz : p.1 ∈ outerInterior B h then p.2 ⟨p.1, hz⟩ else fun _ => p.1) := by
  apply measurable_from_prod_countable_right
  intro z
  dsimp only
  by_cases hz : z ∈ outerInterior B h
  · simpa only [dif_pos hz] using
      (measurable_pi_apply (⟨z, hz⟩ : ↥(outerInterior B h)))
  · simpa only [dif_neg hz] using
      (measurable_const : Measurable (fun _ : GhostDriver B h => fun _ : ℕ => z))

/-- The full forward splice is a measurable map of the independent inputs. -/
theorem measurable_ghostSpliceTraj (B : Base) (h : ℤ) (T : ℕ) :
    Measurable (fun p : TrajSeq B × GhostDriver B h => ghostSpliceTraj B h T p.1 p.2) := by
  apply measurable_pi_iff.mpr
  intro j
  by_cases hj : j < T
  · have hz : Measurable (fun p : TrajSeq B × GhostDriver B h =>
        stoppedSettleSite B h p.1 j) := (measurable_stoppedSettleSite B h j).comp measurable_fst
    have hY := (measurable_ghostSelect B h).comp (hz.prodMk measurable_snd)
    have hX : Measurable (fun p : TrajSeq B × GhostDriver B h => p.1 j) :=
      (measurable_pi_apply j).comp measurable_fst
    have hk : Measurable (fun p : TrajSeq B × GhostDriver B h => ghostSpliceIndex B h p.1 j) :=
      (measurable_ghostSpliceIndex B h j).comp measurable_fst
    have hs := (measurable_ghostSplicePath B).comp ((hX.prodMk hY).prodMk hk)
    have heq : (fun p : TrajSeq B × GhostDriver B h => ghostSpliceTraj B h T p.1 p.2 j) =
        fun p => if stoppedSettleSite B h p.1 j ∈ outerInterior B h then
          ghostSplicePath B (p.1 j)
            (if hz : stoppedSettleSite B h p.1 j ∈ outerInterior B h then
              p.2 ⟨stoppedSettleSite B h p.1 j, hz⟩ else fun _ => stoppedSettleSite B h p.1 j)
            (ghostSpliceIndex B h p.1 j) else p.1 j := by
      funext p
      dsimp only [ghostSpliceTraj, if_pos hj]
      split_ifs <;> rfl
    rw [heq]
    exact Measurable.ite (hz (Set.to_countable (outerInterior B h : Set (Site B))).measurableSet) hs hX
  · simp only [ghostSpliceTraj, if_neg hj]
    exact (measurable_pi_apply j).comp measurable_fst

/-- The forward coupling has total mass one; its map cannot take the zero branch. -/
instance outerGhostMeasure_isProbability (B : Base) (h : ℤ) (T : ℕ) :
    IsProbabilityMeasure (outerGhostMeasure B h T) :=
  Measure.isProbabilityMeasure_map
    ((measurable_ghostSpliceTraj B h T).prodMk measurable_snd).aemeasurable

/-- Every stopped prefix is retained through its exit index, on every input. -/
theorem ghostSpliceTraj_prefix (B : Base) (h : ℤ) (T : ℕ)
    (ω : TrajSeq B) (U : GhostDriver B h) (j n : ℕ)
    (hn : n ≤ ghostSpliceIndex B h ω j) :
    ghostSpliceTraj B h T ω U j n = ω j n := by
  unfold ghostSpliceTraj
  split_ifs <;> simp only [ghostSplicePath, if_pos hn]

private theorem ghostSpliceIndex_spec (B : Base) (h : ℤ) (ω : TrajSeq B) (j : ℕ)
    (hfin : exitTime' B (stoppedCluster B h ω j ∩ R B ((h : ℝ) - 1)) (ω j) ≠ ⊤) :
    exitTime' B (stoppedCluster B h ω j ∩ R B ((h : ℝ) - 1)) (ω j) =
      (ghostSpliceIndex B h ω j : ℕ∞) := by
  unfold ghostSpliceIndex
  rw [untopA_eq_toNat hfin]
  exact (ENat.coe_toNat hfin).symm

private theorem exitSite'_eq_of_prefix (B : Base) (S : Set (Site B))
    (X Y : ℕ → Site B) (k : ℕ) (hk : exitTime' B S X = (k : ℕ∞))
    (hXY : ∀ n ≤ k, Y n = X n) : exitSite' B S Y = exitSite' B S X := by
  have hspec := (exitTime'_eq_coe_iff B S X k).mp hk
  have hY : exitTime' B S Y = (k : ℕ∞) :=
    (exitTime'_eq_coe_iff B S Y k).mpr
      ⟨by rw [hXY k le_rfl]; exact hspec.1,
        fun n hn => by rw [hXY n hn.le]; exact hspec.2 n hn⟩
  change Y (WithTop.untopA (exitTime' B S Y)) = X (WithTop.untopA (exitTime' B S X))
  rw [hY, hk, untopA_natCast]
  exact hXY k le_rfl

/-- Splicing after the stopped exits preserves the entire stopped cluster process. -/
theorem stoppedCluster_ghostSpliceTraj (B : Base) (h : ℤ) (T : ℕ)
    (ω : TrajSeq B) (U : GhostDriver B h)
    (hfin : ∀ j, exitTime' B (stoppedCluster B h ω j ∩ R B ((h : ℝ) - 1)) (ω j) ≠ ⊤)
    (t : ℕ) :
    stoppedCluster B h (ghostSpliceTraj B h T ω U) t = stoppedCluster B h ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change stoppedCluster B h (ghostSpliceTraj B h T ω U) t ∪
      {exitSite' B (stoppedCluster B h (ghostSpliceTraj B h T ω U) t ∩ R B ((h : ℝ) - 1))
        (ghostSpliceTraj B h T ω U t)} =
      stoppedCluster B h ω t ∪
        {exitSite' B (stoppedCluster B h ω t ∩ R B ((h : ℝ) - 1)) (ω t)}
    rw [ih, exitSite'_eq_of_prefix B _ (ω t) (ghostSpliceTraj B h T ω U t)
      (ghostSpliceIndex B h ω t) (ghostSpliceIndex_spec B h ω t (hfin t))
      (ghostSpliceTraj_prefix B h T ω U t)]

/-- In particular every stopped settling/freezing site is unchanged. -/
theorem stoppedSettleSite_ghostSpliceTraj (B : Base) (h : ℤ) (T : ℕ)
    (ω : TrajSeq B) (U : GhostDriver B h)
    (hfin : ∀ j, exitTime' B (stoppedCluster B h ω j ∩ R B ((h : ℝ) - 1)) (ω j) ≠ ⊤)
    (j : ℕ) :
    stoppedSettleSite B h (ghostSpliceTraj B h T ω U) j = stoppedSettleSite B h ω j := by
  unfold stoppedSettleSite
  rw [stoppedCluster_ghostSpliceTraj B h T ω U hfin]
  exact exitSite'_eq_of_prefix B _ (ω j) (ghostSpliceTraj B h T ω U j)
    (ghostSpliceIndex B h ω j) (ghostSpliceIndex_spec B h ω j (hfin j))
    (ghostSpliceTraj_prefix B h T ω U j)

/-- The ghost coordinate is literally retained, so it has the prescribed product law. -/
theorem outerGhostMeasure_map_snd (B : Base) (h : ℤ) (T : ℕ) :
    (outerGhostMeasure B h T).map Prod.snd = ghostLaw B h := by
  rw [outerGhostMeasure, Measure.map_map measurable_snd
    ((measurable_ghostSpliceTraj B h T).prodMk measurable_snd)]
  change ((idlaMeasure B).prod (ghostLaw B h)).map Prod.snd = ghostLaw B h
  rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- The ghosts are independent of the stopped settlement tuple. -/
theorem outerGhostMeasure_map_history_ghost (B : Base) (h : ℤ) (hh : 1 ≤ h) (T : ℕ) :
    (outerGhostMeasure B h T).map
      (fun p => ((fun j : Fin T => stoppedSettleSite B h p.1 j), p.2)) =
    ((idlaMeasure B).map (fun ω => fun j : Fin T => stoppedSettleSite B h ω j)).prod
      (ghostLaw B h) := by
  have hH : Measurable (fun ω : TrajSeq B => fun j : Fin T => stoppedSettleSite B h ω j) :=
    measurable_pi_iff.mpr fun j => measurable_stoppedSettleSite B h j
  have hHG : Measurable (fun p : TrajSeq B × GhostDriver B h =>
      ((fun j : Fin T => stoppedSettleSite B h p.1 j), p.2)) :=
    (hH.comp measurable_fst).prodMk measurable_snd
  rw [outerGhostMeasure, Measure.map_map hHG
    ((measurable_ghostSpliceTraj B h T).prodMk measurable_snd)]
  have heq : (fun p : TrajSeq B × GhostDriver B h =>
      ((fun j : Fin T => stoppedSettleSite B h (ghostSpliceTraj B h T p.1 p.2) j), p.2))
      =ᵐ[(idlaMeasure B).prod (ghostLaw B h)]
      (fun p => ((fun j : Fin T => stoppedSettleSite B h p.1 j), p.2)) := by
    have hf := (measurePreserving_fst (μ := idlaMeasure B) (ν := ghostLaw B h)).quasiMeasurePreserving.ae
      (stoppedCluster_ae_exit_ne_top B)
    filter_upwards [hf] with p hp
    apply Prod.ext
    · funext j
      exact stoppedSettleSite_ghostSpliceTraj B h T p.1 p.2 (fun i => hp i h hh) j
    · rfl
  change ((idlaMeasure B).prod (ghostLaw B h)).map
    (fun p => ((fun j : Fin T => stoppedSettleSite B h (ghostSpliceTraj B h T p.1 p.2) j), p.2)) = _
  rw [Measure.map_congr heq]
  change ((idlaMeasure B).prod (ghostLaw B h)).map
    (Prod.map (fun ω => fun j : Fin T => stoppedSettleSite B h ω j) id) = _
  rw [← Measure.map_prod_map _ _ hH measurable_id, Measure.map_id]

private theorem ghostSplice_mem_interior (B : Base) (h : ℤ) (ω : TrajSeq B) (j : ℕ)
    (hfin : exitTime' B (stoppedCluster B h ω j ∩ R B ((h : ℝ) - 1)) (ω j) ≠ ⊤)
    (hlt : (stoppedSettleSite B h ω j).2 < h) :
    stoppedSettleSite B h ω j ∈ outerInterior B h := by
  rw [mem_outerInterior]
  refine ⟨mem_R.mpr ?_, fun h0 => ?_⟩
  · have : (stoppedSettleSite B h ω j).2 ≤ h - 1 := by omega
    exact_mod_cast this
  · exact stoppedSettleSite_notMem_of_lt B h ω j hfin hlt
      (subset_R_zero_stoppedCluster B h ω j h0)

private theorem ghostSplicePath_firstHit (B : Base) (h : ℤ) (X Y : ℕ → Site B) (k : ℕ)
    (hX : ∀ n ≤ k, (X n).2 < h) (hY0 : (Y 0).2 < h)
    (hY : hitLevel B h Y ≠ ⊤) :
    firstHitSite B h (ghostSplicePath B X Y k) = firstHitSite B h Y := by
  let m := (hitLevel B h Y).toNat
  have hm : hitLevel B h Y = (m : ℕ∞) := (ENat.coe_toNat hY).symm
  have hspec := (hitLevel_eq_coe_iff B h Y m).mp hm
  have hmpos : 0 < m := by
    by_contra hn
    have : m = 0 := by omega
    rw [this] at hspec
    omega
  have hhit : hitLevel B h (ghostSplicePath B X Y k) = ((k + m : ℕ) : ℕ∞) := by
    apply (hitLevel_eq_coe_iff B h _ _).mpr
    constructor
    · simpa only [ghostSplicePath, if_neg (by omega : ¬ k + m ≤ k), Nat.add_sub_cancel_left]
        using hspec.1
    · intro n hn
      by_cases hnk : n ≤ k
      · simpa only [ghostSplicePath, if_pos hnk] using ne_of_lt (hX n hnk)
      · simpa only [ghostSplicePath, if_neg hnk] using hspec.2 (n - k) (by omega)
  rw [firstHitSite_eq_of_hitLevel_eq B h _ _ hhit,
    firstHitSite_eq_of_hitLevel_eq B h Y m hm]
  simp only [ghostSplicePath, if_neg (by omega : ¬ k + m ≤ k), Nat.add_sub_cancel_left]

/-- An interior-settled particle's spliced first hit is its site's ghost first hit. -/
theorem ghostSpliceTraj_firstHit_interior (B : Base) (h : ℤ) (T : ℕ)
    (ω : TrajSeq B) (U : GhostDriver B h) (j : ℕ) (hj : j < T)
    (hfin : exitTime' B (stoppedCluster B h ω j ∩ R B ((h : ℝ) - 1)) (ω j) ≠ ⊤)
    (hz : stoppedSettleSite B h ω j ∈ outerInterior B h)
    (hU0 : ∀ z : ↥(outerInterior B h), U z 0 = z.val)
    (hUfin : ∀ z : ↥(outerInterior B h), hitLevel B h (U z) ≠ ⊤) :
    firstHitSite B h (ghostSpliceTraj B h T ω U j) =
      firstHitSite B h (U ⟨stoppedSettleSite B h ω j, hz⟩) := by
  have hzlt : (stoppedSettleSite B h ω j).2 < h := by
    have hzR := ((mem_outerInterior B h _).mp hz).1
    have : (stoppedSettleSite B h ω j).2 ≤ h - 1 := by exact_mod_cast mem_R.mp hzR
    omega
  have hk := ghostSpliceIndex_spec B h ω j hfin
  have hspec := (exitTime'_eq_coe_iff B _ (ω j) _).mp hk
  have hsite : ω j (ghostSpliceIndex B h ω j) = stoppedSettleSite B h ω j := rfl
  rw [ghostSpliceTraj, if_pos hj, dif_pos hz]
  apply ghostSplicePath_firstHit B h
  · intro n hn
    rcases lt_or_eq_of_le hn with hlt | rfl
    · have hnR := mem_R.mp (hspec.2 n hlt).2
      have : (ω j n).2 ≤ h - 1 := by exact_mod_cast hnR
      omega
    · rw [hsite]
      exact hzlt
  · rw [hU0]
    exact hzlt
  · exact hUfin _

/-- A frozen particle's first hit is exactly its freezing site. -/
theorem ghostSpliceTraj_firstHit_frozen (B : Base) (h : ℤ) (T : ℕ)
    (ω : TrajSeq B) (U : GhostDriver B h) (j : ℕ)
    (hfin : exitTime' B (stoppedCluster B h ω j ∩ R B ((h : ℝ) - 1)) (ω j) ≠ ⊤)
    (hz : (stoppedSettleSite B h ω j).2 = h) :
    firstHitSite B h (ghostSpliceTraj B h T ω U j) = stoppedSettleSite B h ω j := by
  have hk := ghostSpliceIndex_spec B h ω j hfin
  have hspec := (exitTime'_eq_coe_iff B _ (ω j) _).mp hk
  have hsite : ω j (ghostSpliceIndex B h ω j) = stoppedSettleSite B h ω j := rfl
  have hhit : hitLevel B h (ghostSpliceTraj B h T ω U j) =
      (ghostSpliceIndex B h ω j : ℕ∞) := by
    apply (hitLevel_eq_coe_iff B h _ _).mpr
    constructor
    · rw [ghostSpliceTraj_prefix B h T ω U j _ le_rfl, hsite, hz]
    · intro n hn
      rw [ghostSpliceTraj_prefix B h T ω U j n hn.le]
      have hnR := mem_R.mp (hspec.2 n hn).2
      have : (ω j n).2 ≤ h - 1 := by exact_mod_cast hnR
      omega
  rw [firstHitSite_eq_of_hitLevel_eq B h _ _ hhit,
    ghostSpliceTraj_prefix B h T ω U j _ le_rfl, hsite]

/-- The alive/frozen/ghost identity for the constructed splice, on the fill event. -/
theorem aliveCount_ghostSpliceTraj_on_fill (B : Base) (h : ℤ) (hh : 1 ≤ h) (T : ℕ)
    (ω : TrajSeq B) (U : GhostDriver B h)
    (hadm : ∀ j, CylAdmissible B (ω j)) (h0 : ∀ j, ω j 0 ∈ R B 0)
    (hfin : ∀ j, exitTime' B (stoppedCluster B h ω j ∩ R B ((h : ℝ) - 1)) (ω j) ≠ ⊤)
    (hU0 : ∀ z : ↥(outerInterior B h), U z 0 = z.val)
    (hUfin : ∀ z : ↥(outerInterior B h), hitLevel B h (U z) ≠ ⊤)
    (hG : ω ∈ outerFill B h T) (x : B.V) :
    aliveCount B h T (ghostSpliceTraj B h T ω U) x =
      frozenCount B h T ω x + ghostCount B h U x := by
  let S := (Finset.range T).filter (fun j => ∃ z : ↥(outerInterior B h),
    stoppedSettleSite B h ω j = z.val ∧ firstHitSite B h (U z) = (x, h))
  have hlt (j : ℕ) (hj : j ∈ S) : (stoppedSettleSite B h ω j).2 < h := by
    obtain ⟨z, hz, _⟩ := (Finset.mem_filter.mp hj).2
    rw [hz]
    have hzR := ((mem_outerInterior B h z.val).mp z.property).1
    have : z.val.2 ≤ h - 1 := by exact_mod_cast mem_R.mp hzR
    omega
  have hpartition : (Finset.range T).filter
      (fun j => firstHitSite B h (ghostSpliceTraj B h T ω U j) = (x, h)) =
      ((Finset.range T).filter (fun j => stoppedSettleSite B h ω j = (x, h))) ∪ S := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_union, S]
    constructor
    · rintro ⟨hj, hhit⟩
      by_cases hz : stoppedSettleSite B h ω j ∈ outerInterior B h
      · refine Or.inr ⟨hj, ⟨⟨stoppedSettleSite B h ω j, hz⟩, rfl, ?_⟩⟩
        rw [← ghostSpliceTraj_firstHit_interior B h T ω U j
          (Finset.mem_range.mp hj) (hfin j) hz hU0 hUfin]
        exact hhit
      · have hzle := stoppedSettleSite_ver_le B h hh ω hadm h0 hfin j
        have hzeq : (stoppedSettleSite B h ω j).2 = h := by
          by_contra heq
          exact hz (ghostSplice_mem_interior B h ω j (hfin j) (by omega))
        exact Or.inl ⟨hj, (ghostSpliceTraj_firstHit_frozen B h T ω U j (hfin j) hzeq).symm.trans hhit⟩
    · rintro (⟨hj, hz⟩ | ⟨hj, z, hz, hhit⟩)
      · exact ⟨hj, (ghostSpliceTraj_firstHit_frozen B h T ω U j (hfin j)
          (congrArg Prod.snd hz)).trans hz⟩
      · have hzmem : stoppedSettleSite B h ω j ∈ outerInterior B h := hz ▸ z.property
        refine ⟨hj, ?_⟩
        rw [ghostSpliceTraj_firstHit_interior B h T ω U j
          (Finset.mem_range.mp hj) (hfin j) hzmem hU0 hUfin]
        have heq : (⟨stoppedSettleSite B h ω j, hzmem⟩ : ↥(outerInterior B h)) = z :=
          Subtype.ext hz
        rw [heq]
        exact hhit
  have hdisj : Disjoint
      ((Finset.range T).filter (fun j => stoppedSettleSite B h ω j = (x, h))) S := by
    apply Finset.disjoint_left.mpr
    intro j hj hjS
    have hz := congrArg Prod.snd (Finset.mem_filter.mp hj).2
    have := hlt j hjS
    omega
  have hcard : S.card = ghostCount B h U x := by
    let f : (j : ℕ) → j ∈ S → ↥(outerInterior B h) :=
      fun j hj => Classical.choose (Finset.mem_filter.mp hj).2
    have hf (j : ℕ) (hj : j ∈ S) :
        stoppedSettleSite B h ω j = (f j hj).val ∧ firstHitSite B h (U (f j hj)) = (x, h) :=
      Classical.choose_spec (Finset.mem_filter.mp hj).2
    unfold ghostCount
    apply Finset.card_bij f
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf j hj).2⟩
    · intro j hj k hk heq
      apply stoppedSettleSite_injOn_below B h T ω hfin
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, hlt j hj⟩
      · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1, hlt k hk⟩
      · exact (hf j hj).1.trans ((congrArg Subtype.val heq).trans (hf k hk).1.symm)
    · intro z hz
      have hzA := (outerFill_iff B h T ω).mp hG z.val z.property
      rw [stoppedCluster_eq_union] at hzA
      have hz0 := ((mem_outerInterior B h z.val).mp z.property).2
      obtain ⟨j, hj, hjz⟩ := Finset.mem_image.mp (hzA.resolve_left hz0)
      have hjS : j ∈ S := Finset.mem_filter.mpr
        ⟨hj, ⟨z, hjz, (Finset.mem_filter.mp hz).2⟩⟩
      exact ⟨j, hjS, Subtype.ext ((hf j hjS).1.symm.trans hjz)⟩
  unfold aliveCount frozenCount
  rw [hpartition, Finset.card_union_of_disjoint hdisj, hcard]

/-- The a.e. count identity under the explicit coupling; no marginal-law assumption is used. -/
theorem outerGhostMeasure_ae_count (B : Base) (h : ℤ) (hh : 1 ≤ h) (T : ℕ) :
    ∀ᵐ p ∂outerGhostMeasure B h T, p.1 ∈ outerFill B h T → ∀ x : B.V,
      aliveCount B h T p.1 x = frozenCount B h T p.1 x + ghostCount B h p.2 x := by
  have hω := (measurePreserving_fst (μ := idlaMeasure B) (ν := ghostLaw B h)).quasiMeasurePreserving.ae
    (idlaMeasure_ae_stopped_hyp B)
  have hU0 := (measurePreserving_snd (μ := idlaMeasure B) (ν := ghostLaw B h)).quasiMeasurePreserving.ae
    (ghostLaw_ae_start B h)
  have hUf := (measurePreserving_snd (μ := idlaMeasure B) (ν := ghostLaw B h)).quasiMeasurePreserving.ae
    (ghostLaw_ae_hitLevel_ne_top B h)
  have hP : MeasurableSet {p : TrajSeq B × GhostDriver B h |
      p.1 ∈ outerFill B h T → ∀ x : B.V,
        aliveCount B h T p.1 x = frozenCount B h T p.1 x + ghostCount B h p.2 x} := by
    have hAll : MeasurableSet {p : TrajSeq B × GhostDriver B h | ∀ x : B.V,
        aliveCount B h T p.1 x = frozenCount B h T p.1 x + ghostCount B h p.2 x} := by
      rw [Set.setOf_forall]
      apply MeasurableSet.iInter
      intro x
      exact measurableSet_eq_fun ((measurable_aliveCount B h T x).comp measurable_fst)
        (((measurable_frozenCount B h T x).comp measurable_fst).add
          ((measurable_ghostCount B h x).comp measurable_snd))
    simp only [imp_iff_not_or]
    exact ((measurableSet_outerFill B h T).preimage measurable_fst).compl.union hAll
  apply (ae_map_iff
    ((measurable_ghostSpliceTraj B h T).prodMk measurable_snd).aemeasurable hP).mpr
  filter_upwards [hω, hU0, hUf] with p hp hstart hhit
  have hfin := fun j => hp.2.2.1 j h hh
  have hsites := stoppedSettleSite_ghostSpliceTraj B h T p.1 p.2 hfin
  intro hG x
  have hG' : p.1 ∈ outerFill B h T := by
    change R B ((h - 1 : ℤ) : ℝ) ⊆ stoppedCluster B h p.1 T
    rw [← stoppedCluster_ghostSpliceTraj B h T p.1 p.2 hfin T]
    exact hG
  have hfrozen : frozenCount B h T (ghostSpliceTraj B h T p.1 p.2) x = frozenCount B h T p.1 x := by
    simp only [frozenCount, hsites]
  rw [hfrozen]
  exact aliveCount_ghostSpliceTraj_on_fill B h hh T p.1 p.2 hp.1 hp.2.1 hfin hstart hhit hG' x

/-- Appending one released particle changes only its own full-path coordinate. -/
theorem ghostSpliceTraj_succ (B : Base) (h : ℤ) (T : ℕ) (ω : TrajSeq B) (U : GhostDriver B h) :
    ghostSpliceTraj B h (T + 1) ω U =
      if hz : stoppedSettleSite B h ω T ∈ outerInterior B h then
        Function.update (ghostSpliceTraj B h T ω U) T
          (ghostSplicePath B (ω T) (U ⟨stoppedSettleSite B h ω T, hz⟩) (ghostSpliceIndex B h ω T))
      else ghostSpliceTraj B h T ω U := by
  have hne (j : ℕ) (hj : j ≠ T) :
      ghostSpliceTraj B h (T + 1) ω U j = ghostSpliceTraj B h T ω U j := by
    unfold ghostSpliceTraj
    by_cases hjT : j < T
    · rw [if_pos (by omega : j < T + 1), if_pos hjT]
    · rw [if_neg (by omega : ¬ j < T + 1), if_neg hjT]
  funext j
  by_cases hj : j = T
  · subst j
    by_cases hz : stoppedSettleSite B h ω T ∈ outerInterior B h
    · rw [dif_pos hz, Function.update_self]
      unfold ghostSpliceTraj
      rw [if_pos (Nat.lt_succ_self T), dif_pos hz]
    · rw [dif_neg hz]
      unfold ghostSpliceTraj
      rw [if_pos (Nat.lt_succ_self T), dif_neg hz, if_neg (lt_irrefl T)]
  · split_ifs with hz
    · rw [Function.update_of_ne hj]
      exact hne j hj
    · exact hne j hj

private def ghostSwapLocal (B : Base) (h : ℤ) (j : ℕ) (ω : TrajSeq B)
    (q : (ℕ → Site B) × GhostDriver B h) : (ℕ → Site B) × GhostDriver B h :=
  ghostExitSwap B h (stoppedCluster B h ω j ∩ R B ((h : ℝ) - 1)) q

private theorem measurable_ghostSwapLocal_history (B : Base) (h : ℤ) (j : ℕ) :
    Measurable (fun p : (Fin j → Site B) × ((ℕ → Site B) × GhostDriver B h) =>
      ghostExitSwap B h ((R B 0 ∪ Set.range p.1) ∩ R B ((h : ℝ) - 1)) p.2) := by
  apply measurable_from_prod_countable_right
  intro s
  change Measurable (ghostExitSwap B h ((R B 0 ∪ Set.range s) ∩ R B ((h : ℝ) - 1)))
  exact measurable_ghostExitSwap B h _

private theorem ghostSwapLocal_eq_history (B : Base) (h : ℤ) (j : ℕ) (ω : TrajSeq B)
    (q : (ℕ → Site B) × GhostDriver B h) :
    ghostSwapLocal B h j ω q =
      ghostExitSwap B h ((R B 0 ∪ Set.range (fun i : Fin j => stoppedSettleSite B h ω i)) ∩
        R B ((h : ℝ) - 1)) q := by
  unfold ghostSwapLocal
  rw [measurable_stoppedCluster_eq B h
    (s := fun i : Fin j => stoppedSettleSite B h ω i) (fun _ => rfl)]

private theorem measurable_ghostSwapLocal (B : Base) (h : ℤ) (j : ℕ) :
    Measurable (fun p : TrajSeq B × ((ℕ → Site B) × GhostDriver B h) =>
      ghostSwapLocal B h j p.1 p.2) := by
  have hH : Measurable (fun ω : TrajSeq B => fun i : Fin j => stoppedSettleSite B h ω i) :=
    measurable_pi_iff.mpr fun i => measurable_stoppedSettleSite B h i
  have hm := (measurable_ghostSwapLocal_history B h j).comp
    ((hH.comp (measurable_fst : Measurable
      (Prod.fst : TrajSeq B × ((ℕ → Site B) × GhostDriver B h) → TrajSeq B))).prodMk measurable_snd)
  have heq : (fun p : TrajSeq B × ((ℕ → Site B) × GhostDriver B h) => ghostSwapLocal B h j p.1 p.2) =
      fun p => ghostExitSwap B h
        ((R B 0 ∪ Set.range (fun i : Fin j => stoppedSettleSite B h p.1 i)) ∩ R B ((h : ℝ) - 1)) p.2 :=
    funext fun p => ghostSwapLocal_eq_history B h j p.1 p.2
  rw [heq]
  exact hm

private def ghostSwapSelected (B : Base) (h : ℤ) (j : ℕ)
    (p : TrajSeq B × GhostDriver B h) : (ℕ → Site B) × GhostDriver B h :=
  ghostSwapLocal B h j p.1 (p.1 j, p.2)

private theorem measurable_ghostSwapInput (B : Base) (h : ℤ) (j : ℕ) :
    Measurable (fun p : TrajSeq B × GhostDriver B h => (p.1, (p.1 j, p.2))) := by
  have hω : Measurable (fun p : TrajSeq B × GhostDriver B h => p.1) := measurable_fst
  have hX : Measurable (fun p : TrajSeq B × GhostDriver B h => p.1 j) :=
    (measurable_pi_apply j).comp hω
  have hU : Measurable (fun p : TrajSeq B × GhostDriver B h => p.2) := measurable_snd
  exact hω.prodMk (hX.prodMk hU)

private theorem ghostSwapSelected_eq_comp (B : Base) (h : ℤ) (j : ℕ) :
    ghostSwapSelected B h j =
      (fun q : TrajSeq B × ((ℕ → Site B) × GhostDriver B h) => ghostSwapLocal B h j q.1 q.2) ∘
        (fun p : TrajSeq B × GhostDriver B h => (p.1, (p.1 j, p.2))) := rfl

private theorem measurable_ghostSwapSelected (B : Base) (h : ℤ) (j : ℕ) :
    Measurable (ghostSwapSelected B h j) := by
  rw [ghostSwapSelected_eq_comp]
  exact Measurable.comp
    (g := fun q : TrajSeq B × ((ℕ → Site B) × GhostDriver B h) => ghostSwapLocal B h j q.1 q.2)
    (f := fun p : TrajSeq B × GhostDriver B h => (p.1, (p.1 j, p.2)))
    (measurable_ghostSwapLocal B h j) (measurable_ghostSwapInput B h j)

private theorem measurable_ghostSwapInstall (B : Base) (h : ℤ) (j : ℕ) :
    Measurable (fun q : TrajSeq B × ((ℕ → Site B) × GhostDriver B h) =>
      (Function.update q.1 j q.2.1, q.2.2)) := by
  have hin : Measurable (fun q : TrajSeq B × ((ℕ → Site B) × GhostDriver B h) => (q.1, q.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hup : Measurable (fun p : TrajSeq B × (ℕ → Site B) => Function.update p.1 j p.2) :=
    measurable_update'
  have hU : Measurable (fun q : TrajSeq B × ((ℕ → Site B) × GhostDriver B h) => q.2.2) :=
    measurable_snd.comp measurable_snd
  exact (hup.comp hin).prodMk hU

/-- One chronological exchange, saving the discarded continuation in its site coordinate. -/
def ghostSwapStep (B : Base) (h : ℤ) (j : ℕ) (p : TrajSeq B × GhostDriver B h) :
    TrajSeq B × GhostDriver B h :=
  let q := ghostSwapSelected B h j p
  (Function.update p.1 j q.1, q.2)

/-- A chronological exchange is measurable on the entire augmented state. -/
theorem measurable_ghostSwapStep (B : Base) (h : ℤ) (j : ℕ) : Measurable (ghostSwapStep B h j) :=
  (measurable_ghostSwapInstall B h j).comp
    (measurable_fst.prodMk (measurable_ghostSwapSelected B h j))

/-- Each chronological exchange preserves the full canonical driver/site-ghost product law. -/
theorem measurePreserving_ghostSwapStep (B : Base) (h : ℤ) (j : ℕ) :
    MeasurePreserving (ghostSwapStep B h j) ((idlaMeasure B).prod (ghostLaw B h))
      ((idlaMeasure B).prod (ghostLaw B h)) := by
  let π : TrajSeq B × ((ℕ → Site B) × GhostDriver B h) → TrajSeq B × GhostDriver B h :=
    fun q => (Function.update q.1 j q.2.1, q.2.2)
  have hπ : MeasurePreserving π
      ((idlaMeasure B).prod ((walkLawUniform B).prod (ghostLaw B h)))
      ((idlaMeasure B).prod (ghostLaw B h)) :=
    ((measurePreserving_ghostOverwrite (fun _ : ℕ => walkLawUniform B) j).prod
      (MeasurePreserving.id (ghostLaw B h))).comp
      (MeasurePreserving.symm MeasurableEquiv.prodAssoc
        (measurePreserving_prodAssoc (idlaMeasure B) (walkLawUniform B) (ghostLaw B h)))
  have hskew : MeasurePreserving
      (fun q : TrajSeq B × ((ℕ → Site B) × GhostDriver B h) =>
        (q.1, ghostSwapLocal B h j q.1 q.2))
      ((idlaMeasure B).prod ((walkLawUniform B).prod (ghostLaw B h)))
      ((idlaMeasure B).prod ((walkLawUniform B).prod (ghostLaw B h))) :=
    (MeasurePreserving.id (idlaMeasure B)).skew_product (measurable_ghostSwapLocal B h j)
      (Filter.Eventually.of_forall fun ω =>
        (measurePreserving_ghostExitSwap_uniform B h
          (stoppedCluster B h ω j ∩ R B ((h : ℝ) - 1)) Set.inter_subset_right).map_eq)
  have heq : ghostSwapStep B h j ∘ π =
      π ∘ (fun q : TrajSeq B × ((ℕ → Site B) × GhostDriver B h) =>
        (q.1, ghostSwapLocal B h j q.1 q.2)) := by
    funext q
    have hc : stoppedCluster B h (Function.update q.1 j q.2.1) j = stoppedCluster B h q.1 j := by
      apply stoppedCluster_congr B h
      intro i hi
      exact Function.update_of_ne (by omega) _ _
    simp only [Function.comp_apply, π, ghostSwapStep, ghostSwapSelected, ghostSwapLocal,
      hc, Function.update_self, Function.update_idem]
  refine ⟨measurable_ghostSwapStep B h j, ?_⟩
  calc
    ((idlaMeasure B).prod (ghostLaw B h)).map (ghostSwapStep B h j) =
        (((idlaMeasure B).prod ((walkLawUniform B).prod (ghostLaw B h))).map π).map (ghostSwapStep B h j) :=
      congrArg (fun μ => μ.map (ghostSwapStep B h j)) hπ.map_eq.symm
    _ = ((idlaMeasure B).prod ((walkLawUniform B).prod (ghostLaw B h))).map
        (ghostSwapStep B h j ∘ π) :=
      Measure.map_map (measurable_ghostSwapStep B h j) hπ.measurable
    _ = ((idlaMeasure B).prod (ghostLaw B h)) := by
      rw [heq]
      exact (hπ.comp hskew).map_eq

/-- Perform the first `T` chronological exchanges. The ghost state now contains saved old tails;
it is distinct from the original ghosts retained by `outerGhostMeasure`. -/
def ghostSwapIter (B : Base) (h : ℤ) : ℕ → (TrajSeq B × GhostDriver B h) → TrajSeq B × GhostDriver B h
  | 0 => id
  | T + 1 => ghostSwapStep B h T ∘ ghostSwapIter B h T

/-- The entire chronological exchange sequence preserves the product law. -/
theorem measurePreserving_ghostSwapIter (B : Base) (h : ℤ) (T : ℕ) :
    MeasurePreserving (ghostSwapIter B h T) ((idlaMeasure B).prod (ghostLaw B h))
      ((idlaMeasure B).prod (ghostLaw B h)) := by
  induction T with
  | zero => exact MeasurePreserving.id _
  | succ T ih => exact (measurePreserving_ghostSwapStep B h T).comp ih

private theorem ghostSwapIter_splice_invariant (B : Base) (h : ℤ)
    (ω : TrajSeq B) (U : GhostDriver B h)
    (hfin : ∀ j, exitTime' B (stoppedCluster B h ω j ∩ R B ((h : ℝ) - 1)) (ω j) ≠ ⊤)
    (T : ℕ) :
    (ghostSwapIter B h T (ω, U)).1 = ghostSpliceTraj B h T ω U ∧
      ∀ z : ↥(outerInterior B h), (∀ j < T, stoppedSettleSite B h ω j ≠ z.val) →
        (ghostSwapIter B h T (ω, U)).2 z = U z := by
  induction T with
  | zero =>
    constructor
    · funext j
      simp only [ghostSwapIter, id_eq, ghostSpliceTraj, not_lt_zero, if_false]
    · intro z _
      rfl
  | succ T ih =>
    let q := ghostSwapIter B h T (ω, U)
    have hq : q.1 = ghostSpliceTraj B h T ω U := ih.1
    have hpath : q.1 T = ω T := by
      rw [hq]
      unfold ghostSpliceTraj
      rw [if_neg (lt_irrefl T)]
    have hc : stoppedCluster B h q.1 T = stoppedCluster B h ω T := by
      rw [hq]
      exact stoppedCluster_ghostSpliceTraj B h T ω U hfin T
    have hstep : ghostSwapStep B h T q =
        if hz : stoppedSettleSite B h ω T ∈ outerInterior B h then
          (Function.update q.1 T
            (ghostSplicePath B (ω T) (q.2 ⟨stoppedSettleSite B h ω T, hz⟩) (ghostSpliceIndex B h ω T)),
            Function.update q.2 ⟨stoppedSettleSite B h ω T, hz⟩
              (fun n => ω T (n + ghostSpliceIndex B h ω T)))
        else q := by
      unfold ghostSwapStep ghostSwapSelected ghostSwapLocal ghostExitSwap
      simp only [hc, hpath]
      change (let r := if hz : stoppedSettleSite B h ω T ∈ outerInterior B h then
          (ghostSplicePath B (ω T) (q.2 ⟨stoppedSettleSite B h ω T, hz⟩) (ghostSpliceIndex B h ω T),
            Function.update q.2 ⟨stoppedSettleSite B h ω T, hz⟩
              (fun n => ω T (n + ghostSpliceIndex B h ω T))) else (ω T, q.2)
        ; (Function.update q.1 T r.1, r.2)) = _
      split_ifs with hz
      · rfl
      · apply Prod.ext
        · exact (congrArg (Function.update q.1 T) hpath.symm).trans (Function.update_eq_self T q.1)
        · rfl
    change (ghostSwapStep B h T q).1 = ghostSpliceTraj B h (T + 1) ω U ∧
      ∀ z : ↥(outerInterior B h), (∀ j < T + 1, stoppedSettleSite B h ω j ≠ z.val) →
        (ghostSwapStep B h T q).2 z = U z
    rw [hstep, ghostSpliceTraj_succ]
    split_ifs with hz
    · have hzlt : (stoppedSettleSite B h ω T).2 < h := by
        have hzR := ((mem_outerInterior B h _).mp hz).1
        have : (stoppedSettleSite B h ω T).2 ≤ h - 1 := by exact_mod_cast mem_R.mp hzR
        omega
      have hnot := stoppedSettleSite_notMem_of_lt B h ω T (hfin T) hzlt
      have hprior : ∀ j < T, stoppedSettleSite B h ω j ≠ stoppedSettleSite B h ω T := by
        intro j hj heq
        apply hnot
        rw [← heq]
        exact stoppedCluster_monotone B h ω (Nat.succ_le_of_lt hj)
          (stoppedSettleSite_mem_succ B h ω j)
      have hghost := ih.2 ⟨stoppedSettleSite B h ω T, hz⟩ hprior
      constructor
      · dsimp only
        rw [hq, hghost]
      · intro z havoid
        have hne : z ≠ (⟨stoppedSettleSite B h ω T, hz⟩ : ↥(outerInterior B h)) := by
          intro heq
          exact havoid T (by omega) (congrArg Subtype.val heq).symm
        change Function.update q.2 ⟨stoppedSettleSite B h ω T, hz⟩
          (fun n => ω T (n + ghostSpliceIndex B h ω T)) z = U z
        rw [Function.update_of_ne hne]
        exact ih.2 z (fun j hj => havoid j (by omega))
    · exact ⟨hq, fun z havoid => ih.2 z (fun j hj => havoid j (by omega))⟩

/-- Distinct interior settlements make the chronological exchange driver equal the direct splice. -/
theorem ghostSwapIter_fst (B : Base) (h : ℤ) (T : ℕ) (ω : TrajSeq B) (U : GhostDriver B h)
    (hfin : ∀ j, exitTime' B (stoppedCluster B h ω j ∩ R B ((h : ℝ) - 1)) (ω j) ≠ ⊤) :
    (ghostSwapIter B h T (ω, U)).1 = ghostSpliceTraj B h T ω U :=
  (ghostSwapIter_splice_invariant B h ω U hfin T).1

/-- The full alive trajectory stream retains its canonical independent walk law. -/
theorem outerGhostMeasure_map_fst (B : Base) (h : ℤ) (hh : 1 ≤ h) (T : ℕ) :
    (outerGhostMeasure B h T).map Prod.fst = idlaMeasure B := by
  rw [outerGhostMeasure, Measure.map_map measurable_fst
    ((measurable_ghostSpliceTraj B h T).prodMk measurable_snd)]
  change ((idlaMeasure B).prod (ghostLaw B h)).map (fun p => ghostSpliceTraj B h T p.1 p.2) = _
  have heq : (fun p : TrajSeq B × GhostDriver B h => ghostSpliceTraj B h T p.1 p.2)
      =ᵐ[(idlaMeasure B).prod (ghostLaw B h)] (Prod.fst ∘ ghostSwapIter B h T) := by
    have hfinite := (measurePreserving_fst (μ := idlaMeasure B) (ν := ghostLaw B h)).quasiMeasurePreserving.ae
      (stoppedCluster_ae_exit_ne_top B)
    filter_upwards [hfinite] with p hp
    exact (ghostSwapIter_fst B h T p.1 p.2 (fun j => hp j h hh)).symm
  rw [Measure.map_congr heq, ← Measure.map_map measurable_fst
    (measurePreserving_ghostSwapIter B h T).measurable,
    (measurePreserving_ghostSwapIter B h T).map_eq, Measure.map_fst_prod,
    measure_univ, one_smul]

/-- The site-ghost coupling, with both marginals and independence of the stopped history. -/
theorem outer_ghost_coupling (B : Base) (h : ℤ) (hh : 1 ≤ h) (T : ℕ) :
    ∃ μ : Measure (TrajSeq B × GhostDriver B h),
      IsProbabilityMeasure μ ∧
      μ.map Prod.fst = idlaMeasure B ∧
      μ.map Prod.snd = ghostLaw B h ∧
      μ.map (fun p => ((fun j : Fin T => stoppedSettleSite B h p.1 j), p.2)) =
        ((idlaMeasure B).map (fun ω => fun j : Fin T => stoppedSettleSite B h ω j)).prod
          (ghostLaw B h) ∧
      (∀ᵐ p ∂μ, p.1 ∈ outerFill B h T → ∀ x : B.V,
        aliveCount B h T p.1 x = frozenCount B h T p.1 x + ghostCount B h p.2 x) := by
  exact ⟨outerGhostMeasure B h T, inferInstance, outerGhostMeasure_map_fst B h hh T,
    outerGhostMeasure_map_snd B h T, outerGhostMeasure_map_history_ghost B h hh T,
    outerGhostMeasure_ae_count B h hh T⟩

/-- The coupling is nonzero on the concrete two-vertex cylinder, with two ghosts at height 2. -/
example : outerGhostMeasure PrInnerTail.K2 2 3 Set.univ = 1 := measure_univ

example : (outerGhostMeasure PrInnerTail.K2 2 3).map Prod.snd = ghostLaw PrInnerTail.K2 2 :=
  outerGhostMeasure_map_snd PrInnerTail.K2 2 3

example : (outerInterior PrInnerTail.K2 2).card = 2 := by
  rw [outerInterior_card]
  rfl

example : (outerGhostMeasure PrInnerTail.K2 2 3).map
    (fun p => ((fun j : Fin 3 => stoppedSettleSite PrInnerTail.K2 2 p.1 j), p.2)) =
    ((idlaMeasure PrInnerTail.K2).map
      (fun ω => fun j : Fin 3 => stoppedSettleSite PrInnerTail.K2 2 ω j)).prod
      (ghostLaw PrInnerTail.K2 2) :=
  outerGhostMeasure_map_history_ghost PrInnerTail.K2 2 (by norm_num) 3

example : (outerGhostMeasure PrInnerTail.K2 2 3).map Prod.fst = idlaMeasure PrInnerTail.K2 :=
  outerGhostMeasure_map_fst PrInnerTail.K2 2 (by norm_num) 3

example : outerGhostMeasure PrInnerTail.K2 1 0 Set.univ = 1 := measure_univ

/- A genuine continuation from vertex 0 at height 1 changes the full alive
path after its stopped prefix, while keeping the settlement itself fixed. -/
example : ghostSplicePath PrInnerTail.K2
    (fun n => ((0 : Fin 2), (n : ℤ)))
    (fun n => if n = 0 then ((0 : Fin 2), (1 : ℤ)) else ((1 : Fin 2), (n : ℤ))) 1 1 =
      ((0 : Fin 2), (1 : ℤ)) := by
  norm_num [ghostSplicePath]
  rfl

example : ghostSplicePath PrInnerTail.K2
    (fun n => ((0 : Fin 2), (n : ℤ)))
    (fun n => if n = 0 then ((0 : Fin 2), (1 : ℤ)) else ((1 : Fin 2), (n : ℤ))) 1 2 =
      ((1 : Fin 2), (1 : ℤ)) := by
  norm_num [ghostSplicePath]
  rfl

end
end IdlaCyl
