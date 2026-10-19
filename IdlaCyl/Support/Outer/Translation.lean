/-
Vertical translation for the prescribed walks and clusters in the outer bound.
Source: paper/idla-cylinder-gff.tex, tex:1427-1431.

These identities move the entire trajectory together with its seed. They do
not reorder particles or identify a paused labelled path with ordinary growth.
-/
import IdlaCyl.Support.FirstHit
import IdlaCyl.Support.PrInnerTail.Nonvacuity

namespace IdlaCyl

open MeasureTheory ProbabilityTheory

/-- Vertical translation by an integer height. -/
def outerShift (B : Base) (h : ℤ) : Site B ≃ Site B where
  toFun p := (p.1, p.2 + h)
  invFun p := (p.1, p.2 - h)
  left_inv p := by
    apply Prod.ext
    · rfl
    · change p.2 + h - h = p.2
      omega
  right_inv p := by
    apply Prod.ext
    · rfl
    · change p.2 - h + h = p.2
      omega

/-- Translate every site of a walk, without changing its time parameter. -/
def outerShiftPath (B : Base) (h : ℤ) (X : ℕ → Site B) : ℕ → Site B :=
  fun n => outerShift B h (X n)

/-- Translate all prescribed walks, without changing their release order. -/
def outerShiftTraj (B : Base) (h : ℤ) (ω : TrajSeq B) : TrajSeq B :=
  fun j => outerShiftPath B h (ω j)

/-- The actual cylinder transition kernel is invariant under vertical shifts. -/
theorem cylKernel_outerShift (B : Base) (h : ℤ) (p q : Site B) :
    cylKernel B (outerShift B h p) (outerShift B h q) = cylKernel B p q := by
  simp only [cylKernel, outerShift, Equiv.coe_fn_mk, add_sub_add_right_eq_sub,
    add_left_inj]

/-- The shift of a prescribed walk has precisely the shifted prescribed law. -/
theorem walkPathLaw_map_outerShift (B : Base) (h : ℤ) (p : Site B) :
    (walkPathLaw B p).map (outerShiftPath B h) = walkPathLaw B (outerShift B h p) :=
  walkPathLaw_map_siteEquiv B (outerShift B h) (cylKernel_outerShift B h) p

/-- A translated path is a measurable function of the original path. -/
theorem measurable_outerShiftPath (B : Base) (h : ℤ) :
    Measurable (outerShiftPath B h) :=
  measurable_pi_iff.mpr (fun n =>
    (measurable_of_countable (outerShift B h)).comp (measurable_pi_apply n))

/-- Measurability of simultaneous translation of all release trajectories. -/
theorem measurable_outerShiftTraj (B : Base) (h : ℤ) :
    Measurable (outerShiftTraj B h) :=
  measurable_pi_iff.mpr (fun j =>
    (measurable_outerShiftPath B h).comp (measurable_pi_apply j))

/-- The entire independent prescribed release law transports under translation. -/
theorem prescribedMeasure_map_outerShift (B : Base) (h : ℤ) (start : ℕ → Site B) :
    (prescribedMeasure B start).map (outerShiftTraj B h) =
      prescribedMeasure B (fun j => outerShift B h (start j)) := by
  unfold prescribedMeasure outerShiftTraj
  rw [Measure.infinitePi_map_pi (fun j => walkPathLaw B (start j))
    (fun _ => measurable_outerShiftPath B h)]
  simp only [walkPathLaw_map_outerShift]

/-- Translating a half-cylinder shifts its real boundary height by h. -/
theorem outerShift_image_R (B : Base) (h : ℤ) (r : ℝ) :
    outerShift B h '' R B r = R B (r + (h : ℝ)) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hq' := mem_R.mp hq
    apply mem_R.mpr
    change ((q.2 + h : ℤ) : ℝ) ≤ r + (h : ℝ)
    push_cast
    linarith
  · intro hp
    refine ⟨(p.1, p.2 - h), ?_, ?_⟩
    · apply mem_R.mpr
      have hp' := mem_R.mp hp
      push_cast
      linarith
    · exact Prod.ext rfl (by change p.2 - h + h = p.2; omega)

/-- Translating both a set and a path preserves the exit time, including ⊤. -/
theorem exitTime'_outerShift (B : Base) (h : ℤ) (A : Set (Site B)) (X : ℕ → Site B) :
    exitTime' B (outerShift B h '' A) (outerShiftPath B h X) = exitTime' B A X := by
  apply enat_eq_of_le_iff
  intro n
  rw [exitTime'_le_iff, exitTime'_le_iff]
  apply exists_congr
  intro j
  apply and_congr_right
  intro _
  have hmem : outerShift B h (X j) ∈ outerShift B h '' A ↔ X j ∈ A := by
    constructor
    · rintro ⟨p, hp, heq⟩
      exact (outerShift B h).injective heq ▸ hp
    · intro hp
      exact ⟨X j, hp, rfl⟩
  exact not_congr hmem

/-- The exit site transports even before a finite-exit hypothesis is imposed. -/
theorem exitSite'_outerShift (B : Base) (h : ℤ) (A : Set (Site B)) (X : ℕ → Site B) :
    exitSite' B (outerShift B h '' A) (outerShiftPath B h X) =
      outerShift B h (exitSite' B A X) := by
  change outerShift B h (X (WithTop.untopA
    (exitTime' B (outerShift B h '' A) (outerShiftPath B h X)))) = _
  rw [exitTime'_outerShift]
  rfl

/-- The whole constructed recursion commutes with translating seed and paths. -/
theorem clusterFrom_outerShift (B : Base) (h : ℤ) (A : Set (Site B)) (ω : TrajSeq B)
    (k : ℕ) :
    clusterFrom B (outerShift B h '' A) (outerShiftTraj B h ω) k =
      outerShift B h '' clusterFrom B A ω k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [clusterFrom_succ, clusterFrom_succ, ih]
      change (outerShift B h '' clusterFrom B A ω k) ∪
        {exitSite' B (outerShift B h '' clusterFrom B A ω k) (outerShiftPath B h (ω k))} = _
      rw [exitSite'_outerShift, Set.image_union, Set.image_singleton]

/-- Height containment is exactly equivalent before and after translating down. -/
theorem outerShift_subset_R_iff (B : Base) (h : ℤ) (A : Set (Site B)) (r : ℝ) :
    outerShift B h '' A ⊆ R B (r + (h : ℝ)) ↔ A ⊆ R B r := by
  rw [← outerShift_image_R B h r]
  exact Set.image_subset_image_iff (outerShift B h).injective

/- Nonvacuity: a genuine one-level shift changes the boundary and the prescribed
start. The two-vertex cylinder is a legitimate base with positive walk laws. -/
example : outerShift PrInnerTail.K2 3 (PrInnerTail.K2.pt, (2 : ℤ)) =
    (PrInnerTail.K2.pt, (5 : ℤ)) := rfl

example : outerShift PrInnerTail.K2 3 '' R PrInnerTail.K2 0 = R PrInnerTail.K2 3 := by
  convert outerShift_image_R PrInnerTail.K2 3 0 using 1
  norm_num

example : (walkPathLaw PrInnerTail.K2 (PrInnerTail.K2.pt, (0 : ℤ))).map
    (outerShiftPath PrInnerTail.K2 3) =
      walkPathLaw PrInnerTail.K2 (PrInnerTail.K2.pt, (3 : ℤ)) :=
  walkPathLaw_map_outerShift PrInnerTail.K2 3 (PrInnerTail.K2.pt, (0 : ℤ))

end IdlaCyl
