module

/-
The exit map and its monotonicity engine.

`exitTime'`/`exitSite'` are the canonical replacements for the hand-rolled
`IdlaCyl.exitTime`/`exitSite` of `IdlaCyl/Support/Idla.lean`, whose junk value
`ENat.toNat ⊤ = 0` silently returns the walk's *start* point.  `stoppedValue`
uses `WithTop.untopA = untopD (Classical.arbitrary _)`, which is opaque, so no
use of the never-exiting branch is exploitable.

`exitSite'_mem_of_subset` (`tex:1417-1424`) is the single most leveraged lemma
of the shape branch: it discharges `le-mono-init`, `eq:monotone_stop` and
`Ā_h(t) ⊆ A(t)` pathwise, with no coupling and no abelian property.
-/
public import IdlaCyl.Support.Cylinder
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Probability.Process.Stopping

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IdlaCyl

variable (B : Base)

/-- `τ_S = inf{k ≥ 0 : X_k ∉ S}`, `⊤` if the walk never leaves. -/
noncomputable def exitTime' (B : Base) (S : Set (Site B)) : (ℕ → Site B) → ℕ∞ :=
  MeasureTheory.hittingAfter (fun (k : ℕ) (X : ℕ → Site B) => X k) Sᶜ 0

/-- The exit location, the paper's `(X_t, Y_t)` (`tex:265`). -/
noncomputable def exitSite' (B : Base) (S : Set (Site B)) : (ℕ → Site B) → Site B :=
  MeasureTheory.stoppedValue (fun (k : ℕ) (X : ℕ → Site B) => X k) (exitTime' B S)

theorem exitSite'_mem_compl (B : Base) (S : Set (Site B)) {X : ℕ → Site B}
    (h : exitTime' B S X ≠ ⊤) : exitSite' B S X ∉ S :=
  MeasureTheory.hittingAfter_mem_set_of_ne_top h

theorem exitTime'_mono (B : Base) {S S' : Set (Site B)} (hss : S ⊆ S') (X : ℕ → Site B) :
    exitTime' B S X ≤ exitTime' B S' X :=
  MeasureTheory.hittingAfter_anti (fun (k : ℕ) (X : ℕ → Site B) => X k) 0
    (Set.compl_subset_compl.mpr hss) X

/-- **The monotonicity engine.**  One lemma; it yields `le:mono-init`
(`tex:1412-1425`), `eq:monotone_stop` (`tex:1156`) and `Ā_h(t) ⊆ A(t)`
(`tex:1153-1155`) — all three *pathwise*, with no coupling and no appeal to the
abelian property. -/
theorem exitSite'_mem_of_subset (B : Base) {S S' : Set (Site B)} (hss : S ⊆ S')
    {X : ℕ → Site B} (hfin : exitTime' B S' X ≠ ⊤) :
    exitSite' B S X ∈ S' ∪ {exitSite' B S' X} := by
  have hmono : exitTime' B S X ≤ exitTime' B S' X := exitTime'_mono B hss X
  by_cases hp1 : exitSite' B S X ∈ S'
  · exact Set.mem_union_left _ hp1
  · refine Set.mem_union_right S' (Set.mem_singleton_iff.mpr ?_)
    have hmem : X (WithTop.untopA (exitTime' B S X)) ∈ S'ᶜ := hp1
    have hle_t2_t1 : exitTime' B S' X ≤ WithTop.untopA (exitTime' B S X) :=
      MeasureTheory.hittingAfter_le_of_mem
        (u := fun (k : ℕ) (Y : ℕ → Site B) => Y k) (s := S'ᶜ) (n := (0 : ℕ))
        (i := WithTop.untopA (exitTime' B S X)) (ω := X)
        (Nat.zero_le _) hmem
    have ht2_le_t1 : WithTop.untopA (exitTime' B S' X) ≤ WithTop.untopA (exitTime' B S X) :=
      WithTop.untopA_le hle_t2_t1
    have ht1_le_t2 : WithTop.untopA (exitTime' B S X) ≤ WithTop.untopA (exitTime' B S' X) :=
      WithTop.untopA_mono hfin hmono
    have heq : WithTop.untopA (exitTime' B S X) = WithTop.untopA (exitTime' B S' X) :=
      le_antisymm ht1_le_t2 ht2_le_t1
    show X (WithTop.untopA (exitTime' B S X)) = X (WithTop.untopA (exitTime' B S' X))
    exact congrArg X heq

theorem measurable_exitSite' (B : Base) (S : Set (Site B)) : Measurable (exitSite' B S) := by
  have hS : MeasurableSet S := (Set.to_countable S).measurableSet
  have hSc : MeasurableSet (Sᶜ : Set (Site B)) := hS.compl
  have hu : MeasureTheory.Adapted
      (⊤ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Site B)))
      (fun (k : ℕ) (Y : ℕ → Site B) => Y k) := fun k => measurable_pi_apply k
  have hτ : MeasureTheory.IsStoppingTime
      (⊤ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace (ℕ → Site B)))
      (exitTime' B S) :=
    hu.isStoppingTime_hittingAfter hSc
  have hτ_sing : ∀ n : ℕ, MeasurableSet {X : ℕ → Site B | exitTime' B S X = (n : ℕ∞)} :=
    fun n => hτ.measurableSet_eq n
  have hτ_top : MeasurableSet {X : ℕ → Site B | exitTime' B S X = (⊤ : ℕ∞)} := by
    have hset : {X : ℕ → Site B | exitTime' B S X = (⊤ : ℕ∞)}
        = ⋂ j : ℕ, (fun X : ℕ → Site B => X j) ⁻¹' S := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
      constructor
      · intro h j
        exact not_not.mp (MeasureTheory.hittingAfter_eq_top_iff.mp h j (Nat.zero_le j))
      · intro h
        exact MeasureTheory.hittingAfter_eq_top_iff.mpr (fun j _ => not_not.mpr (h j))
    rw [hset]
    exact MeasurableSet.iInter (fun j => measurable_pi_apply j hS)
  refine measurable_to_countable' (fun p => ?_)
  have key : exitSite' B S ⁻¹' {p}
      = ⋃ t : ℕ∞, {X : ℕ → Site B | exitTime' B S X = t} ∩
          (fun X : ℕ → Site B => X (WithTop.untopA t)) ⁻¹' {p} := by
    ext X
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    constructor
    · intro hX
      exact ⟨exitTime' B S X, rfl, hX⟩
    · rintro ⟨t, ht, hXt⟩
      show X (WithTop.untopA (exitTime' B S X)) = p
      rw [ht]
      exact hXt
  rw [key]
  refine MeasurableSet.iUnion (fun t => ?_)
  refine MeasurableSet.inter ?_ (measurable_pi_apply (WithTop.untopA t) (measurableSet_singleton p))
  cases t with
  | top => exact hτ_top
  | coe n => exact hτ_sing n

end IdlaCyl
