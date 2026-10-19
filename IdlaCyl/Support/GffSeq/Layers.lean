/-
Source: paper/idla-cylinder-gff.tex, tex:931-938,990-998.
Finite consecutive height layers cover the bad event almost surely. The
largest layer uses the canonical almost-sure cap, rather than arbitrary paths.
-/
import IdlaCyl.Support.QOnEc.Layers
import IdlaCyl.Support.QOnEc.Mass
import IdlaCyl.Support.GffSeq.Mass
import IdlaCyl.Support.Torus.Sequence

namespace IdlaCyl.GffSeq.QOnEc

open IdlaCyl.Defs MeasureTheory
open scoped BigOperators

/-- The literal shape event is measurable. -/
theorem measurableSet_shape (U : SequenceSetup) (C y₀ : ℝ) (N : ℕ) :
    MeasurableSet (SequenceSetup.shape U C y₀ N) :=
  measurableSet_shapeTraj (U.B N) (SequenceSetup.time U y₀ N)
    ((⌊(SequenceSetup.time U y₀ N : ℝ) / ((U.B N).card : ℝ) - SequenceSetup.width U C y₀ N⌋ : ℤ) : ℝ)
    ((SequenceSetup.time U y₀ N : ℝ) / ((U.B N).card : ℝ) + SequenceSetup.width U C y₀ N)

end IdlaCyl.GffSeq.QOnEc
