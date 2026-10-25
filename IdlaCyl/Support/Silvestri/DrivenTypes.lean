module

public import IdlaCyl.Support.FirstHit
public import IdlaCyl.Support.Recurrence.Discharge
public import IdlaCyl.Support.Obligation.ExitAeFinite

@[expose] public section

/-!
# Upward hitting of the cylinder walk and the type law of the driven walk

Source: `paper/idla-cylinder-gff.tex` `tex:598-604`. The vertical increment of
the cylinder walk is `+1`, `-1`, `0` with probabilities `1/4`, `1/4`, `1/2`, so
the vertical coordinate is the lazy symmetric walk on `ℤ`, which is recurrent
(`ext-lazy-rw-recurrent`).

The file proves two facts about the cylinder walk.

1. `walkPathLaw_ae_hits_all`, `walkPathLaw_ae_eq_all`: almost surely the
   canonical cylinder walk from any start visits every height `k : ℤ`, either
   weakly above `k` or exactly at `k`. The almost-sure statement for one height
   is `External.lazyRwRecurrent_holds`; the countable family of heights is
   handled by `ae_all_iff`.

2. `drivenType_law`: the driver of one walk, `walkDriverLaw`, pushed forward by
   the vertical-type map `inc` applied at every time, is the infinite product
   of the one-step type law `typeLaw`. The type law is the explicit law
   `1/4 δ_{-1} + 1/4 δ_{1} + 1/2 δ_{0}` of the vertical increment.
-/

namespace IdlaCyl.Silvestri

open MeasureTheory Filter
open scoped ENNReal
open IdlaCyl.Obligation.ExitAeFinite (inc inc_law measurable_inc)

/-- The uniform law on `[0,1)` is a probability measure. -/
instance stepLaw_isProbability : IsProbabilityMeasure stepLaw := by
  constructor
  norm_num [stepLaw, Measure.restrict_apply_univ]

/-- Almost surely the canonical cylinder walk from `p` reaches every height
`k : ℤ` weakly from above: for every `k` there is a time `n` with
`k ≤ (X n).2`. This is `External.LazyRwRecurrent` lifted over the countable
family of heights `k : ℤ`. -/
theorem walkPathLaw_ae_hits_all (B : Base) (p : Site B) :
    ∀ᵐ X ∂walkPathLaw B p, ∀ k : ℤ, ∃ n, k ≤ (X n).2 :=
  ae_all_iff.mpr fun k => External.lazyRwRecurrent_holds B p k

/-- Almost surely the canonical cylinder walk from `p` visits every height
`k : ℤ` exactly: for every `k` there is a time `n` with `(X n).2 = k`. -/
theorem walkPathLaw_ae_eq_all (B : Base) (p : Site B) :
    ∀ᵐ X ∂walkPathLaw B p, ∀ k : ℤ, ∃ n, (X n).2 = k :=
  ae_all_iff.mpr fun k => ae_exists_ver_eq External.lazyRwRecurrent_holds B p k

/-- Almost surely the canonical cylinder walk from `p` rises above every level:
for every `M : ℤ` there is a time `n` with `M < (X n).2`. -/
theorem walkPathLaw_ae_above (B : Base) (p : Site B) :
    ∀ᵐ X ∂walkPathLaw B p, ∀ M : ℤ, ∃ n, M < (X n).2 := by
  filter_upwards [walkPathLaw_ae_hits_all B p] with X hX M
  obtain ⟨n, hn⟩ := hX (M + 1)
  exact ⟨n, by omega⟩

/-- The law of one step's vertical type: the vertical increment of one cylinder
step takes the value `-1` with probability `1/4`, `1` with probability `1/4`,
and `0` with probability `1/2` (`tex:598-599`). -/
noncomputable def typeLaw : Measure ℤ :=
  (1/4 : ℝ≥0∞) • Measure.dirac (-1 : ℤ) +
    (1/4 : ℝ≥0∞) • Measure.dirac (1 : ℤ) +
    (1/2 : ℝ≥0∞) • Measure.dirac (0 : ℤ)

/-- The type law is the image of one step's pair of uniforms under `inc`. -/
theorem typeLaw_eq : typeLaw = (stepLaw.prod stepLaw).map inc :=
  inc_law.symm

/-- The type law is a probability measure, so `Measure.infinitePi` of it is the
genuine product and not its junk value. -/
instance typeLaw_isProbability : IsProbabilityMeasure typeLaw := by
  rw [typeLaw_eq]
  exact Measure.isProbabilityMeasure_map measurable_inc.aemeasurable

/-- The vertical types of the driven walk are i.i.d.: pushing the driver
`walkDriverLaw` forward by `w ↦ (n ↦ inc (w n))` gives the infinite product of
the type law `typeLaw`. -/
theorem drivenType_law :
    walkDriverLaw.map (fun w n => inc (w n)) = Measure.infinitePi (fun _ : ℕ => typeLaw) := by
  have h := Measure.infinitePi_map_pi (fun _ : ℕ => stepLaw.prod stepLaw)
    (f := fun _ : ℕ => inc) (fun _ => measurable_inc)
  unfold walkDriverLaw
  rw [typeLaw_eq]
  exact h

end IdlaCyl.Silvestri
