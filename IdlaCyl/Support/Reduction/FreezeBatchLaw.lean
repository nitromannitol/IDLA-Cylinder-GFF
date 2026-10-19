/-
Independent canonical walks realize the literal layer-freezing batch law.
Source: paper/idla-cylinder-gff.tex, tex:246-265,595-610,1440-1453.
Coupon filling for the ACTUAL settle-first/freeze-duplicate rule.
-/
import IdlaCyl.Support.Reduction.FreezeFinish

namespace IdlaCyl.Reduction

open MeasureTheory ProbabilityTheory

/-- The visible batch state after the first n independent entrance coupons. -/
noncomputable def freezeGrow (B : Base) (j : ℤ) (s : ResumeState B) (ω : TrajSeq B) :
    ℕ → ResumeState B
  | 0 => s
  | n + 1 => freezeCoupon B (freezeGrow B j s ω n) (firstHitSite B j (ω n))

/-- The whole finite batch state is a measurable function of its released walks. -/
theorem measurable_freezeGrow (B : Base) (j : ℤ) (s : ResumeState B) (n : ℕ) :
    Measurable (fun ω => freezeGrow B j s ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hu : Measurable (fun sX : ResumeState B × (ℕ → Site B) =>
          freezeCoupon B sX.1 (firstHitSite B j sX.2)) := by
        apply measurable_from_prod_countable_right
        intro t
        exact (measurable_of_countable (freezeCoupon B t)).comp (measurable_firstHitSite B j)
      exact hu.comp (ih.prodMk (measurable_pi_apply n))

/-- No future walk or start enters the finite batch state. -/
theorem freezeGrow_congr (B : Base) (j : ℤ) (s : ResumeState B) (ω η : TrajSeq B)
    (n : ℕ) (hn : ∀ i < n, ω i = η i) : freezeGrow B j s ω n = freezeGrow B j s η n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change freezeCoupon B (freezeGrow B j s ω n) (firstHitSite B j (ω n)) = _
      rw [ih (fun i hi => hn i (by omega)), hn n (by omega)]
      rfl

/-- The finite independent-walk construction has the prescribed fresh-step transition. -/
theorem freezeGrow_law_succ (B : Base) (j : ℤ) (s : ResumeState B) (n : ℕ) :
    (idlaMeasure B).map (fun ω => freezeGrow B j s ω (n + 1)) =
      ((idlaMeasure B).map (fun ω => freezeGrow B j s ω n)).bind (freezeLayerStep B j) := by
  let step := fun sX : ResumeState B × (ℕ → Site B) =>
    freezeCoupon B sX.1 (firstHitSite B j sX.2)
  have hs : Measurable step := by
    apply measurable_from_prod_countable_right
    intro t
    exact (measurable_of_countable (freezeCoupon B t)).comp (measurable_firstHitSite B j)
  have hj := IndepFun.map_prod_eq_prod_map_map
    (measurable_freezeGrow B j s n).aemeasurable (measurable_pi_apply n).aemeasurable
    (resume_indep_past B (fun _ => walkLawUniform B) n _ (measurable_freezeGrow B j s n)
      (fun ω η h => freezeGrow_congr B j s ω η n h))
  rw [Measure.infinitePi_map_eval] at hj
  change (idlaMeasure B).map (fun ω => (freezeGrow B j s ω n, ω n)) =
    ((idlaMeasure B).map (fun ω => freezeGrow B j s ω n)).prod (walkLawUniform B) at hj
  calc
    _ = ((idlaMeasure B).map (fun ω => (freezeGrow B j s ω n, ω n))).map step :=
      (Measure.map_map hs ((measurable_freezeGrow B j s n).prodMk
        (measurable_pi_apply n))).symm
    _ = (((idlaMeasure B).map (fun ω => freezeGrow B j s ω n)).prod
        (walkLawUniform B)).map step := by rw [hj]
    _ = _ := resume_prod_map _ _ step hs

/-- The first-step recursion also admits an independent last-step recursion. -/
theorem freezeBatch_succ_right (B : Base) (j : ℤ) (M : ℕ) (s : ResumeState B) :
    (freezeBatch B j M s).bind (freezeLayerStep B j) = freezeBatch B j (M + 1) s := by
  induction M generalizing s with
  | zero =>
      change (Measure.dirac s).bind (freezeLayerStep B j) =
        (freezeLayerStep B j s).bind Measure.dirac
      rw [Measure.dirac_bind (measurable_of_countable _), Measure.bind_dirac]
  | succ M ih =>
      change ((freezeLayerStep B j s).bind (freezeBatch B j M)).bind (freezeLayerStep B j) =
        (freezeLayerStep B j s).bind (freezeBatch B j (M + 1))
      rw [Measure.bind_bind (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable]
      congr 1
      funext t
      exact ih t

/-- The batch kernel is exactly the pushforward of independently released canonical walks. -/
theorem freezeBatch_law (B : Base) (j : ℤ) (M : ℕ) (s : ResumeState B) :
    (idlaMeasure B).map (fun ω => freezeGrow B j s ω M) = freezeBatch B j M s := by
  induction M with
  | zero => simp only [freezeGrow, Measure.map_const, measure_univ, one_smul, freezeBatch]
  | succ M ih => rw [freezeGrow_law_succ, ih, freezeBatch_succ_right]

/-- A batch never removes an occupied site, on every input including exceptional paths. -/
theorem seed_subset_freezeGrow (B : Base) (j : ℤ) (s : ResumeState B) (ω : TrajSeq B)
    (M : ℕ) : resumeSeed B s.1 ⊆ resumeSeed B (freezeGrow B j s ω M).1 := by
  induction M with
  | zero => exact Set.Subset.rfl
  | succ M ih => exact ih.trans (freezeCoupon_seed_mono B _ _)

/-- All coupons already seen are occupied, including coupons whose particles were frozen. -/
theorem freezeGrow_coupon_mem (B : Base) (j : ℤ) (s : ResumeState B) (ω : TrajSeq B)
    (M i : ℕ) (hi : i < M) :
    firstHitSite B j (ω i) ∈ resumeSeed B (freezeGrow B j s ω M).1 := by
  induction M with
  | zero => omega
  | succ M ih =>
      by_cases him : i < M
      · exact freezeCoupon_seed_mono B _ _ (ih him)
      · have heq : i = M := by omega
        subst i
        exact freezeCoupon_mem B _ _

/-- Covering all entrance coupons fills the layer in the actual frozen batch. -/
theorem freezeGrow_filled_of_coupons (B : Base) (j : ℤ) (s : ResumeState B)
    (hF : R B ((j : ℝ) - 1) ⊆ resumeSeed B s.1) (ω : TrajSeq B) (M : ℕ)
    (hc : ω ∉ missingCoupons B j M) :
    R B (j : ℝ) ⊆ resumeSeed B (freezeGrow B j s ω M).1 := by
  intro z hz
  have hzj : z.2 ≤ j := by exact_mod_cast (mem_R.mp hz)
  by_cases hlow : z.2 ≤ j - 1
  · exact seed_subset_freezeGrow B j s ω M (hF (mem_R.mpr (by exact_mod_cast hlow)))
  · have heq : z.2 = j := by omega
    have hex : ∃ i < M, firstHitSite B j (ω i) = (z.1, j) := by
      by_contra hno
      exact hc ⟨z.1, fun i hi he => hno ⟨i, hi, he⟩⟩
    obtain ⟨i, hi, he⟩ := hex
    have hm := freezeGrow_coupon_mem B j s ω M i hi
    have hsite : (z.1, j) = z := Prod.ext rfl heq.symm
    rwa [he, hsite] at hm

/-- The exact settle-first/freeze-duplicates batch satisfies the coupon bound. -/
theorem freezeBatch_fill (B : Base) (j : ℤ) (s : ResumeState B)
    (hF : R B ((j : ℝ) - 1) ⊆ resumeSeed B s.1) (M : ℕ) (q : ℝ)
    (hM : (q + 1) * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (M : ℝ)) :
    freezeBatch B j M s {t | R B (j : ℝ) ⊆ resumeSeed B t.1}ᶜ ≤
      ENNReal.ofReal ((B.card : ℝ) ^ (-q)) := by
  rw [← freezeBatch_law, Measure.map_apply (measurable_freezeGrow B j s M)
    (Set.to_countable _).measurableSet]
  apply (measure_mono (show (fun ω => freezeGrow B j s ω M) ⁻¹'
      {t | R B (j : ℝ) ⊆ resumeSeed B t.1}ᶜ ⊆ missingCoupons B j M from ?_)).trans
  · exact missing_coupons_poly B 0 j M q hM
  · intro ω hbad
    by_contra hc
    exact hbad (freezeGrow_filled_of_coupons B j s hF ω M hc)

end IdlaCyl.Reduction
