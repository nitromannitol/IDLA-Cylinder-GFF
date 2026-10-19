/-
Finite-prefix Markov factorization for ghost splicing.
Source: paper/idla-cylinder-gff.tex, tex:1271-1280.

This module derives deterministic-cut continuation laws from the canonical
finite-cylinder probabilities. No strong Markov assertion is supplied as an
input. Random stopped cuts and adaptive selection of distinct site ghosts are
separate steps.
-/
import IdlaCyl.Support.FirstHit
import IdlaCyl.Support.StoppedAe

attribute [local instance] Classical.propDecidable

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

/-- Keep the prefix through `k`; read the fresh continuation after `k`. -/
def ghostSplicePath (B : Base) (X Y : ℕ → Site B) (k : ℕ) : ℕ → Site B :=
  fun n => if n ≤ k then X n else Y (n - k)

theorem measurable_ghostSplicePath (B : Base) :
    Measurable (fun p : ((ℕ → Site B) × (ℕ → Site B)) × ℕ =>
      ghostSplicePath B p.1.1 p.1.2 p.2) := by
  apply measurable_pi_iff.mpr
  intro n
  apply measurable_from_prod_countable_left
  intro k
  dsimp only [ghostSplicePath]
  by_cases hn : n ≤ k
  · simp only [if_pos hn]
    exact (measurable_pi_apply n).comp measurable_fst
  · simp only [if_neg hn]
    exact (measurable_pi_apply (n - k)).comp measurable_snd


theorem measurable_ghostExitIndex (B : Base) (S : Set (Site B)) :
    Measurable (fun X : ℕ → Site B => WithTop.untopA (exitTime' B S X)) := by
  have hu : Adapted
      (⊤ : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Site B)))
      (fun k (X : ℕ → Site B) => X k) := fun k => measurable_pi_apply k
  have ht : IsStoppingTime
      (⊤ : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Site B)))
      (exitTime' B S) :=
    hu.isStoppingTime_hittingAfter (Set.to_countable S).measurableSet.compl
  exact ht.measurable'.untopA

private theorem ghost_pathWeight_add (B : Base) (k n : ℕ) (f : ℕ → Site B) :
    pathWeight B (k + n) f =
      pathWeight B k f * pathWeight B n (fun i => f (i + k)) := by
  unfold pathWeight
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [Nat.add_comm, Nat.add_assoc]

/-- On a finite prefix cylinder, the continuation is a fresh walk from its last site.
This is a proved equality of finite measures, obtained from the cylinder weights. -/
theorem walkPathLaw_restrict_pathCyl_splice (B : Base) (p : Site B) (k : ℕ)
    (f : ℕ → Site B) :
    (walkPathLaw B p).restrict (pathCyl B k f) =
      (walkPathLaw B p (pathCyl B k f)) •
        (walkPathLaw B (f k)).map (fun Y => ghostSplicePath B f Y k) := by
  have hmap : Measurable (fun Y => ghostSplicePath B f Y k) :=
    (measurable_ghostSplicePath B).comp
      ((measurable_const.prodMk measurable_id).prodMk measurable_const)
  letI : IsFiniteMeasure
      ((walkPathLaw B p (pathCyl B k f)) •
        (walkPathLaw B (f k)).map (fun Y => ghostSplicePath B f Y k)) :=
    Measure.smul_finite _ (measure_ne_top _ _)
  apply measure_ext_of_pathCyl B
  intro b g
  rw [Measure.restrict_apply (measurableSet_pathCyl B b g), Measure.smul_apply,
    smul_eq_mul, Measure.map_apply hmap (measurableSet_pathCyl B b g)]
  by_cases hb : b ≤ k
  · by_cases hc : ∀ i ≤ b, f i = g i
    · have hleft : pathCyl B b g ∩ pathCyl B k f = pathCyl B k f := by
        apply Set.inter_eq_right.mpr
        intro X hX i hi
        exact (hX i (hi.trans hb)).trans (hc i hi)
      have hright : (fun Y => ghostSplicePath B f Y k) ⁻¹' pathCyl B b g = Set.univ := by
        ext Y
        simp only [Set.mem_preimage, pathCyl, Set.mem_setOf_eq, Set.mem_univ, iff_true]
        intro i hi
        exact (if_pos (hi.trans hb)).trans (hc i hi)
      rw [hleft, hright, measure_univ, mul_one]
    · obtain ⟨i, hi⟩ := not_forall.mp hc
      have hi' : i ≤ b := by
        by_contra hn
        exact hi (fun h => False.elim (hn h))
      have hne' : f i ≠ g i := fun heq => hi (fun _ => heq)
      have hleft : pathCyl B b g ∩ pathCyl B k f = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro X ⟨hXg, hXf⟩
        exact hne' ((hXf i (hi'.trans hb)).symm.trans (hXg i hi'))
      have hright : (fun Y => ghostSplicePath B f Y k) ⁻¹' pathCyl B b g = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro Y hY
        have h := hY i hi'
        have heq : ghostSplicePath B f Y k i = f i := if_pos (hi'.trans hb)
        exact hne' (heq.symm.trans h)
      simp only [hleft, hright, measure_empty, mul_zero]
  · have hkb : k ≤ b := by omega
    by_cases hc : ∀ i ≤ k, f i = g i
    · have hleft : pathCyl B b g ∩ pathCyl B k f = pathCyl B b g := by
        apply Set.inter_eq_left.mpr
        intro X hX i hi
        exact (hX i (hi.trans hkb)).trans (hc i hi).symm
      have hprefix : pathCyl B k f = pathCyl B k g := by
        ext X
        constructor
        · intro hX i hi
          exact (hX i hi).trans (hc i hi)
        · intro hX i hi
          exact (hX i hi).trans (hc i hi).symm
      have hright :
          walkPathLaw B (f k) ((fun Y => ghostSplicePath B f Y k) ⁻¹' pathCyl B b g) =
            walkPathLaw B (f k) (pathCyl B (b - k) (fun i => g (i + k))) := by
        apply measure_congr
        filter_upwards [walkPathLaw_ae_start B (f k)] with Y hY
        apply propext
        constructor
        · intro hX i hi
          by_cases hi0 : i = 0
          · subst i
            simpa only [zero_add] using hY.trans (hc k le_rfl)
          · have hik : ¬ i + k ≤ k := by omega
            have h := hX (i + k) (by omega)
            simpa only [ghostSplicePath, if_neg hik, Nat.add_sub_cancel_right] using h
        · intro hX i hi
          by_cases hik : i ≤ k
          · exact (if_pos hik).trans (hc i hik)
          · have h := hX (i - k) (by omega)
            simpa only [ghostSplicePath, if_neg hik, Nat.sub_add_cancel (by omega : k ≤ i)] using h
      rw [hleft, hright, hprefix, walkPathLaw_pathCyl, walkPathLaw_pathCyl,
        walkPathLaw_pathCyl]
      simp only [zero_add, if_pos (hc k le_rfl).symm, one_mul]
      have hw := ghost_pathWeight_add B k (b - k) g
      rw [Nat.add_sub_of_le hkb] at hw
      rw [hw]
      ring
    · obtain ⟨i, hi⟩ := not_forall.mp hc
      have hi' : i ≤ k := by
        by_contra hn
        exact hi (fun h => False.elim (hn h))
      have hne : f i ≠ g i := fun heq => hi (fun _ => heq)
      have hleft : pathCyl B b g ∩ pathCyl B k f = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro X ⟨hXg, hXf⟩
        exact hne ((hXf i hi').symm.trans (hXg i (hi'.trans hkb)))
      have hright : (fun Y => ghostSplicePath B f Y k) ⁻¹' pathCyl B b g = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro Y hY
        have h := hY i (hi'.trans hkb)
        have heq : ghostSplicePath B f Y k i = f i := if_pos hi'
        exact hne (heq.symm.trans h)
      simp only [hleft, hright, measure_empty, mul_zero]

private def ghostExitContinuationKernel (B : Base) (S : Set (Site B)) :
    Kernel (ℕ → Site B) (ℕ → Site B) where
  toFun X := walkPathLaw B (exitSite' B S X)
  measurable' := (measurable_of_countable (walkPathLaw B)).comp (measurable_exitSite' B S)

private instance ghostExitContinuationKernel_isMarkov (B : Base) (S : Set (Site B)) :
    IsMarkovKernel (ghostExitContinuationKernel B S) :=
  ⟨fun X => walkPathLaw_isProbability B (exitSite' B S X)⟩

private theorem measurable_ghostExitRefreshMap (B : Base) (S : Set (Site B)) :
    Measurable (fun p : (ℕ → Site B) × (ℕ → Site B) =>
      ghostSplicePath B p.1 p.2 (WithTop.untopA (exitTime' B S p.1))) := by
  have hk : Measurable (fun p : (ℕ → Site B) × (ℕ → Site B) =>
      WithTop.untopA (exitTime' B S p.1)) :=
    (measurable_ghostExitIndex B S).comp measurable_fst
  exact (measurable_ghostSplicePath B).comp
    ((measurable_fst.prodMk measurable_snd).prodMk hk)

/-- Refresh one walk's tail at its first exit from a deterministic region. -/
def ghostExitRefreshKernel (B : Base) (S : Set (Site B)) :
    Kernel (ℕ → Site B) (ℕ → Site B) :=
  (Kernel.id.prod (ghostExitContinuationKernel B S)).map
    (fun p => ghostSplicePath B p.1 p.2 (WithTop.untopA (exitTime' B S p.1)))

/-- The refreshing kernel has mass one even on exceptional inputs. -/
instance ghostExitRefreshKernel_isMarkov (B : Base) (S : Set (Site B)) :
    IsMarkovKernel (ghostExitRefreshKernel B S) :=
  Kernel.IsMarkovKernel.map _ (measurable_ghostExitRefreshMap B S)

/-- Evaluation of the refresh kernel as a prescribed fresh continuation. -/
theorem ghostExitRefreshKernel_apply (B : Base) (S : Set (Site B)) (X : ℕ → Site B) :
    ghostExitRefreshKernel B S X =
      (walkPathLaw B (exitSite' B S X)).map
        (fun Y => ghostSplicePath B X Y (WithTop.untopA (exitTime' B S X))) := by
  rw [ghostExitRefreshKernel, Kernel.map_apply _ (measurable_ghostExitRefreshMap B S),
    Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map (measurable_ghostExitRefreshMap B S) measurable_prodMk_left]
  rfl

/-- A finite first-exit time is determined by the path through that exit. -/
theorem ghostExitTime_eq_of_prefix (B : Base) (S : Set (Site B))
    (k : ℕ) (f X : ℕ → Site B) (hcut : exitTime' B S f = (k : ℕ∞))
    (hX : X ∈ pathCyl B k f) : exitTime' B S X = (k : ℕ∞) := by
  have hf := (exitTime'_eq_coe_iff B S f k).mp hcut
  exact (exitTime'_eq_coe_iff B S X k).mpr
    ⟨by rw [hX k le_rfl]; exact hf.1,
      fun n hn => by rw [hX n hn.le]; exact hf.2 n hn⟩

private theorem ghostExitRefreshKernel_eq_on_prefix (B : Base) (S : Set (Site B))
    (k : ℕ) (f X : ℕ → Site B) (hcut : exitTime' B S f = (k : ℕ∞))
    (hX : X ∈ pathCyl B k f) :
    ghostExitRefreshKernel B S X =
      (walkPathLaw B (f k)).map (fun Y => ghostSplicePath B f Y k) := by
  have hXcut := ghostExitTime_eq_of_prefix B S k f X hcut hX
  have hsite : exitSite' B S X = f k := by
    change X (WithTop.untopA (exitTime' B S X)) = f k
    rw [hXcut, untopA_natCast]
    exact hX k le_rfl
  rw [ghostExitRefreshKernel_apply, hsite, hXcut, untopA_natCast]
  congr 1
  funext Y n
  unfold ghostSplicePath
  split_ifs with hn
  · exact hX n hn
  · rfl

/-- Refreshing preserves the law restricted to any valid stopped prefix cylinder. -/
theorem walkPathLaw_restrict_bind_ghostExitRefresh (B : Base) (p : Site B)
    (S : Set (Site B)) (k : ℕ) (f : ℕ → Site B)
    (hcut : exitTime' B S f = (k : ℕ∞)) :
    ((walkPathLaw B p).restrict (pathCyl B k f)).bind (ghostExitRefreshKernel B S) =
      (walkPathLaw B p).restrict (pathCyl B k f) := by
  have hconst : (ghostExitRefreshKernel B S : (ℕ → Site B) → Measure (ℕ → Site B))
      =ᵐ[(walkPathLaw B p).restrict (pathCyl B k f)]
      (fun _ => (walkPathLaw B (f k)).map (fun Y => ghostSplicePath B f Y k)) := by
    filter_upwards [ae_restrict_mem (measurableSet_pathCyl B k f)] with X hX
    exact ghostExitRefreshKernel_eq_on_prefix B S k f X hcut hX
  rw [Measure.bind_congr_right hconst, Measure.bind_const,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact (walkPathLaw_restrict_pathCyl_splice B p k f).symm

/-- A finite exit index and the complete prefix through that exit. -/
abbrev GhostStoppedPrefix (B : Base) := Σ k : ℕ, (Finset.Iic k → Site B)

/-- The cylinder belonging to a valid stopped prefix, and the empty event for an invalid prefix. -/
def ghostStoppedPrefixEvent (B : Base) (S : Set (Site B))
    (c : GhostStoppedPrefix B) : Set (ℕ → Site B) :=
  if exitTime' B S (ofPrefix B c.1 c.2) = (c.1 : ℕ∞) then
    pathCyl B c.1 (ofPrefix B c.1 c.2) else ∅

/-- An a.e. finite exit partitions the walk law into its countably many stopped prefixes. -/
theorem walkPathLaw_eq_sum_ghostStoppedPrefix (B : Base) (p : Site B) (S : Set (Site B))
    (hfin : ∀ᵐ X ∂walkPathLaw B p, exitTime' B S X ≠ ⊤) :
    Measure.sum (fun c : GhostStoppedPrefix B =>
      (walkPathLaw B p).restrict (ghostStoppedPrefixEvent B S c)) = walkPathLaw B p := by
  let C := GhostStoppedPrefix B
  let E : C → Set (ℕ → Site B) := ghostStoppedPrefixEvent B S
  have hEm (c : C) : MeasurableSet (E c) := by
    dsimp only [E, ghostStoppedPrefixEvent]
    split_ifs
    · exact measurableSet_pathCyl B _ _
    · exact MeasurableSet.empty
  have hEc (c : C) {X : ℕ → Site B} (hX : X ∈ E c) :
      X ∈ pathCyl B c.1 (ofPrefix B c.1 c.2) ∧ exitTime' B S X = (c.1 : ℕ∞) := by
    dsimp only [E, ghostStoppedPrefixEvent] at hX
    split_ifs at hX with hc
    · exact ⟨hX, ghostExitTime_eq_of_prefix B S c.1 (ofPrefix B c.1 c.2) X hc hX⟩
    · exact False.elim hX
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro c d hcd
    apply Set.disjoint_left.mpr
    intro X hXc hXd
    obtain ⟨hc, hct⟩ := hEc c hXc
    obtain ⟨hd, hdt⟩ := hEc d hXd
    rcases c with ⟨k, f⟩
    rcases d with ⟨l, g⟩
    have hkl : k = l := ENat.coe_inj.mp (hct.symm.trans hdt)
    subst l
    apply hcd
    congr 1
    funext i
    have h1 := hc i.val (Finset.mem_Iic.mp i.property)
    have h2 := hd i.val (Finset.mem_Iic.mp i.property)
    rw [ofPrefix_apply_coe] at h1 h2
    exact h1.symm.trans h2
  have hcover : ∀ᵐ X ∂walkPathLaw B p, X ∈ ⋃ c, E c := by
    filter_upwards [hfin] with X hX
    let k := (exitTime' B S X).toNat
    have hk : exitTime' B S X = (k : ℕ∞) := (ENat.coe_toNat hX).symm
    let f : Finset.Iic k → Site B := Preorder.frestrictLe k X
    have hprefix : ofPrefix B k f ∈ pathCyl B k X := by
      intro n hn
      simp only [ofPrefix, f, Preorder.frestrictLe_apply, min_eq_left hn]
    have hcut : exitTime' B S (ofPrefix B k f) = (k : ℕ∞) :=
      ghostExitTime_eq_of_prefix B S k X _ hk hprefix
    apply Set.mem_iUnion.mpr
    refine ⟨⟨k, f⟩, ?_⟩
    dsimp only [E, ghostStoppedPrefixEvent]
    rw [if_pos hcut]
    intro n hn
    exact (hprefix n hn).symm
  have hsum : Measure.sum (fun c => (walkPathLaw B p).restrict (E c)) = walkPathLaw B p := by
    rw [← Measure.restrict_iUnion hdisj hEm]
    exact Measure.restrict_eq_self_of_ae_mem hcover
  exact hsum

/-- The first-exit refresh preserves the walk law whenever that exit is a.e. finite.
The stopping argument is proved by a countable partition into finite prefixes. -/
theorem walkPathLaw_bind_ghostExitRefresh (B : Base) (p : Site B) (S : Set (Site B))
    (hfin : ∀ᵐ X ∂walkPathLaw B p, exitTime' B S X ≠ ⊤) :
    (walkPathLaw B p).bind (ghostExitRefreshKernel B S) = walkPathLaw B p := by
  let C := GhostStoppedPrefix B
  let E : C → Set (ℕ → Site B) := ghostStoppedPrefixEvent B S
  have hsum := walkPathLaw_eq_sum_ghostStoppedPrefix B p S hfin
  calc
    (walkPathLaw B p).bind (ghostExitRefreshKernel B S) =
        (Measure.sum fun c => (walkPathLaw B p).restrict (E c)).bind (ghostExitRefreshKernel B S) :=
      congrArg (fun μ => μ.bind (ghostExitRefreshKernel B S)) hsum.symm
    _ = Measure.sum (fun c => ((walkPathLaw B p).restrict (E c)).bind (ghostExitRefreshKernel B S)) :=
      Measure.bind_sum _ _ (ghostExitRefreshKernel B S).measurable.aemeasurable
    _ = Measure.sum (fun c => (walkPathLaw B p).restrict (E c)) := by
      congr 1
      funext c
      dsimp only [E, ghostStoppedPrefixEvent]
      split_ifs with hc
      · exact walkPathLaw_restrict_bind_ghostExitRefresh B p S c.1 (ofPrefix B c.1 c.2) hc
      · rw [Measure.restrict_empty, Measure.bind_zero_left]
    _ = walkPathLaw B p := hsum

/-- A height cap supplies finite exit from recurrence, with no finiteness or Markov binder. -/
theorem walkPathLaw_bind_ghostExitRefresh_of_subset (B : Base) (p : Site B)
    (S : Set (Site B)) (h : ℤ) (hS : S ⊆ R B ((h : ℝ) - 1)) :
    (walkPathLaw B p).bind (ghostExitRefreshKernel B S) = walkPathLaw B p := by
  apply walkPathLaw_bind_ghostExitRefresh B p S
  filter_upwards [ae_exists_ver_eq External.lazyRwRecurrent_holds B p h] with X hX
  obtain ⟨n, hn⟩ := hX
  exact exitTime'_ne_top_of_height B hS hn.ge

example (B : Base) (p : Site B) :
    (walkPathLaw B p).bind (ghostExitRefreshKernel B ∅) = walkPathLaw B p :=
  walkPathLaw_bind_ghostExitRefresh_of_subset B p ∅ 1 (Set.empty_subset _)

end
end IdlaCyl
