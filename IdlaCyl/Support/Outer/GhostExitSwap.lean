/-
Preservation of the walk/site-ghost product law by a stopped tail exchange.
Source: paper/idla-cylinder-gff.tex, tex:1271-1280.

The original continuation is saved in the selected ghost coordinate. This
exchange preserves the whole product law and can therefore be repeated.
-/
import IdlaCyl.Support.Outer.StoppedBookkeeping
import IdlaCyl.Support.Outer.GhostSwap

attribute [local instance] Classical.propDecidable

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section

/-- Exchange a path's post-exit continuation with its exit site's ghost, when that site is interior. -/
def ghostExitSwap (B : Base) (h : ℤ) (S : Set (Site B))
    (p : (ℕ → Site B) × GhostDriver B h) : (ℕ → Site B) × GhostDriver B h :=
  if hz : exitSite' B S p.1 ∈ outerInterior B h then
    let z : ↥(outerInterior B h) := ⟨exitSite' B S p.1, hz⟩
    let k := WithTop.untopA (exitTime' B S p.1)
    (ghostSplicePath B p.1 (p.2 z) k, Function.update p.2 z (fun n => p.1 (n + k)))
  else p

private theorem measurable_ghostFixedSwap (B : Base) (h : ℤ) (z : ↥(outerInterior B h)) (k : ℕ) :
    Measurable (fun p : (ℕ → Site B) × GhostDriver B h =>
      (ghostSplicePath B p.1 (p.2 z) k, Function.update p.2 z (fun n => p.1 (n + k)))) := by
  apply Measurable.prodMk
  · have hX : Measurable (fun p : (ℕ → Site B) × GhostDriver B h => p.1) := measurable_fst
    have hY : Measurable (fun p : (ℕ → Site B) × GhostDriver B h => p.2 z) :=
      (measurable_pi_apply z).comp measurable_snd
    have hk : Measurable (fun _ : (ℕ → Site B) × GhostDriver B h => k) := measurable_const
    exact (measurable_ghostSplicePath B).comp ((hX.prodMk hY).prodMk hk)
  · apply measurable_pi_iff.mpr
    intro w
    by_cases hw : w = z
    · subst w
      simp only [Function.update_self]
      exact measurable_pi_iff.mpr fun n => (measurable_pi_apply (n + k)).comp measurable_fst
    · simp only [Function.update_of_ne hw]
      exact (measurable_pi_apply w).comp measurable_snd

/-- All index selection and path concatenation in the exchange are measurable. -/
theorem measurable_ghostExitSwap (B : Base) (h : ℤ) (S : Set (Site B)) :
    Measurable (ghostExitSwap B h S) := by
  let F : (Site B × ℕ) × ((ℕ → Site B) × GhostDriver B h) →
      (ℕ → Site B) × GhostDriver B h := fun q =>
    if hz : q.1.1 ∈ outerInterior B h then
      (ghostSplicePath B q.2.1 (q.2.2 ⟨q.1.1, hz⟩) q.1.2,
        Function.update q.2.2 ⟨q.1.1, hz⟩ (fun n => q.2.1 (n + q.1.2)))
    else q.2
  have hF : Measurable F := by
    apply measurable_from_prod_countable_right
    rintro ⟨z, k⟩
    dsimp only [F]
    by_cases hz : z ∈ outerInterior B h
    · simp only [dif_pos hz]
      exact measurable_ghostFixedSwap B h ⟨z, hz⟩ k
    · simp only [dif_neg hz]
      exact measurable_id
  have hz : Measurable (fun p : (ℕ → Site B) × GhostDriver B h => exitSite' B S p.1) :=
    (measurable_exitSite' B S).comp measurable_fst
  have hk : Measurable (fun p : (ℕ → Site B) × GhostDriver B h =>
      WithTop.untopA (exitTime' B S p.1)) :=
    (measurable_ghostExitIndex B S).comp measurable_fst
  exact hF.comp ((hz.prodMk hk).prodMk measurable_id)

private theorem ghostExitSwap_prepend (B : Base) (h : ℤ) (S : Set (Site B))
    (k : ℕ) (f Y : ℕ → Site B) (U : GhostDriver B h)
    (hcut : exitTime' B S f = (k : ℕ∞)) (hz : f k ∈ outerInterior B h) (hY : Y 0 = f k) :
    ghostExitSwap B h S (ghostSplicePath B f Y k, U) =
      (ghostSplicePath B f (U ⟨f k, hz⟩) k, Function.update U ⟨f k, hz⟩ Y) := by
  have hp : ghostSplicePath B f Y k ∈ pathCyl B k f := by
    intro n hn
    exact if_pos hn
  have ht := ghostExitTime_eq_of_prefix B S k f _ hcut hp
  have hsite : exitSite' B S (ghostSplicePath B f Y k) = f k := by
    change ghostSplicePath B f Y k (WithTop.untopA (exitTime' B S _)) = f k
    rw [ht, untopA_natCast]
    exact if_pos le_rfl
  unfold ghostExitSwap
  simp only [hsite, dif_pos hz, ht, untopA_natCast]
  apply Prod.ext
  · change ghostSplicePath B (ghostSplicePath B f Y k) (U ⟨f k, hz⟩) k =
      ghostSplicePath B f (U ⟨f k, hz⟩) k
    funext n
    unfold ghostSplicePath
    split_ifs <;> rfl
  · change Function.update U ⟨f k, hz⟩ (fun n => ghostSplicePath B f Y k (n + k)) =
      Function.update U ⟨f k, hz⟩ Y
    congr 1
    funext n
    by_cases hn : n = 0
    · subst n
      simpa only [zero_add, ghostSplicePath, if_pos le_rfl] using hY.symm
    · simp only [ghostSplicePath, if_neg (by omega : ¬ n + k ≤ k), Nat.add_sub_cancel_right]

private theorem ghostExitSwap_prefix_law (B : Base) (h : ℤ) (S : Set (Site B))
    (p : Site B) (k : ℕ) (f : ℕ → Site B) (hcut : exitTime' B S f = (k : ℕ∞)) :
    (((walkPathLaw B p).restrict (pathCyl B k f)).prod (ghostLaw B h)).map (ghostExitSwap B h S) =
      ((walkPathLaw B p).restrict (pathCyl B k f)).prod (ghostLaw B h) := by
  by_cases hz : f k ∈ outerInterior B h
  · let z : ↥(outerInterior B h) := ⟨f k, hz⟩
    let P : (ℕ → Site B) × GhostDriver B h → (ℕ → Site B) × GhostDriver B h :=
      fun q => (ghostSplicePath B f q.1 k, q.2)
    have hP : Measurable P :=
      ((measurable_ghostSplicePath B).comp
        ((measurable_const.prodMk measurable_fst).prodMk measurable_const)).prodMk measurable_snd
    have hp : Measurable (fun Y => ghostSplicePath B f Y k) :=
      (measurable_ghostSplicePath B).comp
        ((measurable_const.prodMk measurable_id).prodMk measurable_const)
    have hprod : ((walkPathLaw B (f k)).map (fun Y => ghostSplicePath B f Y k)).prod (ghostLaw B h) =
        ((walkPathLaw B (f k)).prod (ghostLaw B h)).map P := by
      have H := Measure.map_prod_map (walkPathLaw B (f k)) (ghostLaw B h) hp measurable_id
      rw [Measure.map_id] at H
      exact H
    rw [walkPathLaw_restrict_pathCyl_splice B p k f, Measure.prod_smul_left, hprod,
      Measure.map_smul, Measure.map_map (measurable_ghostExitSwap B h S) hP]
    congr 1
    have heq : ghostExitSwap B h S ∘ P =ᵐ[(walkPathLaw B (f k)).prod (ghostLaw B h)]
        P ∘ ghostCoordinateSwap z := by
      have hstart := (measurePreserving_fst (μ := walkPathLaw B (f k)) (ν := ghostLaw B h)).quasiMeasurePreserving.ae
        (walkPathLaw_ae_start B (f k))
      filter_upwards [hstart] with q hq
      exact ghostExitSwap_prepend B h S k f q.1 q.2 hcut hz hq
    have hswap : MeasurePreserving (ghostCoordinateSwap z)
        ((walkPathLaw B (f k)).prod (ghostLaw B h)) ((walkPathLaw B (f k)).prod (ghostLaw B h)) :=
      measurePreserving_ghostCoordinateSwap (fun w : ↥(outerInterior B h) => walkPathLaw B w.val) z
    rw [Measure.map_congr heq, ← Measure.map_map hP hswap.measurable, hswap.map_eq]
  · have heq : ghostExitSwap B h S =ᵐ[
        ((walkPathLaw B p).restrict (pathCyl B k f)).prod (ghostLaw B h)] id := by
      have hprefix := (measurePreserving_fst
        (μ := (walkPathLaw B p).restrict (pathCyl B k f)) (ν := ghostLaw B h)).quasiMeasurePreserving.ae
        (ae_restrict_mem (measurableSet_pathCyl B k f))
      filter_upwards [hprefix] with q hq
      have ht := ghostExitTime_eq_of_prefix B S k f q.1 hcut hq
      have hsite : exitSite' B S q.1 = f k := by
        change q.1 (WithTop.untopA (exitTime' B S q.1)) = f k
        rw [ht, untopA_natCast]
        exact hq k le_rfl
      simp only [ghostExitSwap, hsite, dif_neg hz, id_eq]
    rw [Measure.map_congr heq, Measure.map_id]

/-- A first-exit exchange preserves the walk/site-ghost product law, with finite exit explicit. -/
theorem ghostExitSwap_map_walkPathLaw (B : Base) (h : ℤ) (S : Set (Site B)) (p : Site B)
    (hfin : ∀ᵐ X ∂walkPathLaw B p, exitTime' B S X ≠ ⊤) :
    ((walkPathLaw B p).prod (ghostLaw B h)).map (ghostExitSwap B h S) =
      (walkPathLaw B p).prod (ghostLaw B h) := by
  let Q : GhostStoppedPrefix B → Measure ((ℕ → Site B) × GhostDriver B h) := fun c =>
    ((walkPathLaw B p).restrict (ghostStoppedPrefixEvent B S c)).prod (ghostLaw B h)
  have hsum : Measure.sum Q = (walkPathLaw B p).prod (ghostLaw B h) := by
    rw [← Measure.prod_sum_left]
    exact congrArg (fun μ => μ.prod (ghostLaw B h)) (walkPathLaw_eq_sum_ghostStoppedPrefix B p S hfin)
  calc
    ((walkPathLaw B p).prod (ghostLaw B h)).map (ghostExitSwap B h S) =
        (Measure.sum Q).map (ghostExitSwap B h S) :=
      congrArg (fun μ => μ.map (ghostExitSwap B h S)) hsum.symm
    _ = Measure.sum (fun c => (Q c).map (ghostExitSwap B h S)) :=
      Measure.map_sum (measurable_ghostExitSwap B h S).aemeasurable
    _ = Measure.sum Q := by
      congr 1
      funext c
      dsimp only [Q, ghostStoppedPrefixEvent]
      split_ifs with hc
      · exact ghostExitSwap_prefix_law B h S p c.1 (ofPrefix B c.1 c.2) hc
      · simp only [Measure.restrict_empty, Measure.zero_prod, Measure.map_zero]
    _ = (walkPathLaw B p).prod (ghostLaw B h) := hsum

/-- A deterministic height cap discharges finite exit in the exchange law. -/
theorem ghostExitSwap_map_walkPathLaw_of_subset (B : Base) (h : ℤ) (S : Set (Site B))
    (p : Site B) (hS : S ⊆ R B ((h : ℝ) - 1)) :
    ((walkPathLaw B p).prod (ghostLaw B h)).map (ghostExitSwap B h S) =
      (walkPathLaw B p).prod (ghostLaw B h) := by
  apply ghostExitSwap_map_walkPathLaw B h S p
  filter_upwards [ae_exists_ver_eq External.lazyRwRecurrent_holds B p h] with X hX
  obtain ⟨n, hn⟩ := hX
  exact exitTime'_ne_top_of_height B hS hn.ge

/-- The stopped exchange also preserves the uniformly started walk/site-ghost product law. -/
theorem measurePreserving_ghostExitSwap_uniform (B : Base) (h : ℤ) (S : Set (Site B))
    (hS : S ⊆ R B ((h : ℝ) - 1)) :
    MeasurePreserving (ghostExitSwap B h S) ((walkLawUniform B).prod (ghostLaw B h))
      ((walkLawUniform B).prod (ghostLaw B h)) := by
  refine ⟨measurable_ghostExitSwap B h S, ?_⟩
  ext A hA
  have hpre := (measurable_ghostExitSwap B h S) hA
  rw [Measure.map_apply (measurable_ghostExitSwap B h S) hA,
    Measure.prod_apply hpre, Measure.prod_apply hA]
  simp_rw [walkLawUniform, walkLawUniformAt_eq_bind]
  rw [Measure.lintegral_bind (measurable_of_countable (walkPathLaw B)).aemeasurable
      (measurable_measure_prodMk_left hpre).aemeasurable,
    Measure.lintegral_bind (measurable_of_countable (walkPathLaw B)).aemeasurable
      (measurable_measure_prodMk_left hA).aemeasurable]
  apply lintegral_congr
  intro p
  have hp := congrArg (fun μ : Measure ((ℕ → Site B) × GhostDriver B h) => μ A)
    (ghostExitSwap_map_walkPathLaw_of_subset B h S p hS)
  rw [Measure.map_apply (measurable_ghostExitSwap B h S) hA,
    Measure.prod_apply hpre, Measure.prod_apply hA] at hp
  exact hp

example : MeasurePreserving (ghostExitSwap PrInnerTail.K2 2 (R PrInnerTail.K2 0))
    ((walkLawUniform PrInnerTail.K2).prod (ghostLaw PrInnerTail.K2 2))
    ((walkLawUniform PrInnerTail.K2).prod (ghostLaw PrInnerTail.K2 2)) :=
  measurePreserving_ghostExitSwap_uniform PrInnerTail.K2 2 (R PrInnerTail.K2 0)
    (R_mono (by norm_num))

end
end IdlaCyl
