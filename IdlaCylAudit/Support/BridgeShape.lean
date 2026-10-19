import IdlaCylAudit.Support.BridgeBase
import IdlaCyl.Definitions.ShapeEvent

/-!
# The bridge for the shape event

Each declaration of the vocabulary that enters the shape event of the maximal fluctuation
bound is identified with the library's definition at the library base `Bridge.base B`: the
half-cylinder `R`, the `t`-step base kernel `basePow`, the total variation distance
`tvToUniform`, the mixing time, `logPlus`, the threshold `T^♯`, the width `Δ_N`, and the event
`eventAt`. The base kernel is compared by induction on the number of steps; the remaining
equalities are unfolded and rewritten from it.
-/

namespace IdlaCylAudit.Bridge

/-- The half-cylinder `R_k` of the vocabulary is the library's. -/
theorem R_eq (B : IdlaCylAudit.Base) (k : ℝ) :
    IdlaCylAudit.R B k = IdlaCyl.R (base B) k := rfl

/-- The number of vertices of the vocabulary base is the library's. -/
theorem card_eq (B : IdlaCylAudit.Base) :
    IdlaCylAudit.Base.card B = IdlaCyl.Base.card (base B) := rfl

/-- The lazy walk kernel `P_N` of the vocabulary is the library's. -/
theorem P_eq (B : IdlaCylAudit.Base) (x x' : B.V) :
    IdlaCylAudit.Base.P B x x' = IdlaCyl.Base.P (base B) x x' := rfl

/-- The `t`-step base kernel `P_N^t` of the vocabulary is the library's. -/
theorem basePow_eq (B : IdlaCylAudit.Base) (t : ℕ) :
    IdlaCylAudit.basePow B t = IdlaCyl.basePow (base B) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      funext x x'
      simp only [IdlaCylAudit.basePow, IdlaCyl.basePow, ih, P_eq]
      rfl

/-- The total variation distance `‖P_N^t(x,·) - π_N‖_TV` is the library's. -/
theorem tvToUniform_eq (B : IdlaCylAudit.Base) (t : ℕ) (x : B.V) :
    IdlaCylAudit.tvToUniform B t x = IdlaCyl.tvToUniform (base B) t x := by
  simp only [IdlaCylAudit.tvToUniform, IdlaCyl.tvToUniform, basePow_eq, card_eq]
  rfl

/-- The total variation mixing time `τ_mix` of the vocabulary is the library's. -/
theorem mixingTime_eq (B : IdlaCylAudit.Base) :
    IdlaCylAudit.mixingTime B = IdlaCyl.mixingTime (base B) := by
  simp only [IdlaCylAudit.mixingTime, IdlaCyl.mixingTime, tvToUniform_eq]
  rfl

/-- The truncated logarithm `log₊` of the vocabulary is the library's. -/
theorem logPlus_eq (s : ℝ) : IdlaCylAudit.logPlus s = IdlaCyl.logPlus s := rfl

/-- The threshold `T^♯` of the vocabulary is the library's. -/
theorem sharp_eq (B : IdlaCylAudit.Base) :
    IdlaCylAudit.Defs.sharp B = IdlaCyl.Defs.sharp (base B) := by
  simp only [IdlaCylAudit.Defs.sharp, IdlaCyl.Defs.sharp, mixingTime_eq, card_eq]

/-- The width `Δ_N` of the vocabulary is the library's. -/
theorem delta_eq (B : IdlaCylAudit.Base) (C : ℝ) (T : ℕ) :
    IdlaCylAudit.Defs.delta B C T = IdlaCyl.Defs.delta (base B) C T := by
  simp only [IdlaCylAudit.Defs.delta, IdlaCyl.Defs.delta, sharp_eq, card_eq, logPlus_eq]

/-- The event `R_{⌊T/N - d⌋} ⊆ A(T) ⊆ R_{T/N + d}` of the vocabulary is the library's. -/
theorem eventAt_eq (B : IdlaCylAudit.Base) (T : ℕ) (d : ℝ) :
    IdlaCylAudit.Defs.eventAt B T d = IdlaCyl.Defs.eventAt (base B) T d := by
  ext ω
  simp only [IdlaCylAudit.Defs.eventAt, IdlaCyl.Defs.eventAt, Set.mem_setOf_eq, R_eq,
    clusterTraj_eq, card_eq]
  exact Iff.rfl

end IdlaCylAudit.Bridge
