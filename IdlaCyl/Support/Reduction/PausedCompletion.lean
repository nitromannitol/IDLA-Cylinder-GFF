/-
The literal deep/shallow resumption order and its unconditional completion law.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396,1440-1453;
Failed histories retain their actual completion kernel.
-/
import IdlaCyl.Support.Reduction.QueueSplit
import IdlaCyl.Support.Reduction.LayeredFinish
import IdlaCyl.Support.Reduction.ShiftFinite
import IdlaCyl.Support.Outer.QueueDomination

attribute [local instance] Classical.propDecidable

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Every copy at or below the deep cutoff, in its original relative order. -/
noncomputable def deepQueue (B : Base) (β ℓ : ℕ) (s : ResumeState B × ℕ) : List (Site B) :=
  s.1.2.filter (fun z => z.2 ≤ ((ℓ - β : ℕ) : ℤ))

/-- Every copy above the deep cutoff, in its original relative order. -/
noncomputable def shallowQueue (B : Base) (β ℓ : ℕ) (s : ResumeState B × ℕ) : List (Site B) :=
  s.1.2.filter (fun z => ((ℓ - β : ℕ) : ℤ) < z.2)

/-- Reordering the actual queue into two groups changes no completion law. -/
theorem finishUniform_split (B : Base) (M β ℓ ρ : ℕ) (hβ : β ≤ ℓ)
    (s : ResumeState B × ℕ) (hs : s ∈ goodPaused B M ℓ ρ) :
    finishUniform B s.1 s.2 =
      (resumeRun B s.1.1 (deepQueue B β ℓ s)).bind
        (fun C => (resumeRun B C (shallowQueue B β ℓ s)).bind
          (fun D => layerGrowthLaw B D 0 ρ)) := by
  have hp := (goodPaused_split_counts B M β ℓ ρ hβ s hs).2.2
  unfold finishUniform
  rw [hs.2.1, outerRun_perm B hp s.1.1, resumeRun_append,
    Measure.bind_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
  rfl

/-- A successful actual seed equals the canonical finite code of the raw rectangle. -/
theorem goodPaused_seed_eq (B : Base) (M ℓ ρ : ℕ) (s : ResumeState B × ℕ)
    (hs : s ∈ goodPaused B M ℓ ρ) :
    s.1.1 = shiftFinite B ℓ (resumeEmpty B) := by
  apply resumeSeed_injective B
  rw [hs.1, resumeSeed_shiftFinite_empty]

end IdlaCyl.Reduction
