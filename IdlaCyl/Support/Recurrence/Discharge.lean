/-
Discharge of `External.LazyRwRecurrent` (`tex:600-604`): the cylinder walk
reaches every height almost surely.

The probability `f(p)` that the walk from `p` never reaches height `k` vanishes
at height `≥ k` and is harmonic below it (`FirstStep.lean`). It depends only on
the height (`HorizontalInvariance.lean`), so as a function of the height it is a
bounded harmonic function of the lazy symmetric walk on `(-∞, k]` that vanishes
at `k`. Such a function is linear, hence zero (`BoundedHarmonic.lean`).
`Assembly.lean` combines the three facts.
-/
import IdlaCyl.Support.Recurrence.FirstStep
import IdlaCyl.Support.Recurrence.HorizontalInvariance
import IdlaCyl.Support.Recurrence.BoundedHarmonic
import IdlaCyl.Support.Recurrence.Assembly

namespace IdlaCyl.External

/-- The lazy cylinder walk reaches every height almost surely: the hypothesis
`LazyRwRecurrent` carried by the first-hit results of `FirstHit.lean` holds. -/
theorem lazyRwRecurrent_holds : LazyRwRecurrent :=
  Recurrence.lazyRwRecurrent_of
    (fun B k p hp => Recurrence.neverReach_of_le B k p hp)
    (fun B k p hp => Recurrence.neverReach_harmonic B k p hp)
    Recurrence.neverReach_hor Recurrence.bounded_harmonic_halfline

end IdlaCyl.External
