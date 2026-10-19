/-
The threshold `T^♯`, the width `Δ_N`, the event of `eq:fluct`, and the quadratic
mass `Q_N` at the paper's time (`paper/idla-cylinder-gff.tex:273`, `:275-277`,
`:335`, `:908-909`, `:1005-1007`).

Each declaration is the printed formula.  The paper's `N` is `(U.B N).card`, and
the time `T = N ⌊y₀ a_N⌋` (`tex:335`) enters through `IdlaCyl.Defs.time` of
`RectangularMass.lean`.
-/
import IdlaCyl.Definitions.RectangularMass
import IdlaCyl.Support.ClmQWAnalytic

namespace IdlaCyl.Defs

/-- The threshold `T^♯ = N √τ_mix (log N)²` (`tex:273`). -/
noncomputable def sharp (B : Base) : ℝ :=
  (B.card : ℝ) * Real.sqrt (mixingTime B) * (Real.log (B.card : ℝ)) ^ 2

/-- The width `Δ_N = C max{log N, √((T ∧ T^♯)/N · (log N + log₊(T/N)))}` at time
`T` (`tex:273`), with `T ∧ T^♯` read as `min T (sharp B)`. -/
noncomputable def delta (B : Base) (C : ℝ) (T : ℕ) : ℝ :=
  C * max (Real.log (B.card : ℝ))
    (Real.sqrt ((min (T : ℝ) (sharp B) / (B.card : ℝ)) *
      (Real.log (B.card : ℝ) + logPlus ((T : ℝ) / (B.card : ℝ)))))

/-- The event of `eq:fluct` (`tex:275-277`), `R_{⌊T/N - d⌋} ⊆ A(T) ⊆ R_{T/N + d}`,
with the floor kept as printed. -/
noncomputable def eventAt (B : Base) (T : ℕ) (d : ℝ) : Set (TrajSeq B) :=
  {ω | R B ((Int.floor ((T : ℝ) / (B.card : ℝ) - d) : ℤ) : ℝ)
      ⊆ clusterTraj B ω T ∧
    clusterTraj B ω T ⊆ R B ((T : ℝ) / (B.card : ℝ) + d)}

/-- The width `Δ_N = delta` at the paper's time `T = N ⌊y₀ a_N⌋` (`tex:273`, `tex:335`). -/
noncomputable def width (U : Setup) (C y₀ : ℝ) (N : ℕ) : ℝ :=
  delta (U.B N) C (time U y₀ N)

/-- The good event `E` of `clm:Q-W` (`tex:908-909`): the event of `eq:fluct` at
the paper's time with width `Δ_N` (`tex:1017`). -/
noncomputable def shape (U : Setup) (C y₀ : ℝ) (N : ℕ) :
    Set (TrajSeq (U.B N)) :=
  eventAt (U.B N) (time U y₀ N) (width U C y₀ N)

/-- The quadratic mass `Q_N = (1/(N a_N)) ∑_{p ∈ A_+(T)} |ψ(p)|²` at the paper's
time `T = N ⌊y₀ a_N⌋` (`tex:1005-1007`), with `ψ = psi U K α y₀ N`. -/
noncomputable def qmass (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ)
    (y₀ : ℝ) (N : ℕ) (ω : TrajSeq (U.B N)) : ℝ :=
  QN (U.B N) U.a (time U y₀ N) (psi U K α y₀ N) ω

end IdlaCyl.Defs
