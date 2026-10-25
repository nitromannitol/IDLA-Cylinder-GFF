module

/-
The optional-stopping core of `le:martingale`.

`paper/idla-cylinder-gff.tex:694-705`: conditionally on `𝓕_k = σ(A(0),…,A(k))`,
the next settling site `(X_{k+1},Y_{k+1})` is an independent uniform-start
cylinder walk's exit from the current cluster, so for a discrete-harmonic,
zero-horizontal-average `ψ` the martingale increment has zero conditional
expectation:
  `E[ψ(z_k) | 𝓕_k] = 0`.

`IdlaCyl.condExp_settleSite_eq_integral` (`Support/CondDistrib.lean`) turns the
conditional expectation into the integral `∫ w, ψ (exitSite' B (clusterTraj B ω k) w) ∂(walkLawUniform B)`.
Since `R_0 ⊆ clusterTraj B ω k` always, the hypothesis `hint_zero` — the
`tex:698` averaging statement, discharged in the paper from discrete harmonicity
and exponential decay — makes that integral vanish almost everywhere.

The zero-integral hypothesis is needed only to identify the conditional
expectation with the integral.  When `ψ (settleSite B · k)` is *not* integrable,
`condExp` is `0` by definition (`condExp_of_not_integrable`), so the identity
holds trivially; the case split below records this.
-/
public import IdlaCyl.Support.CondDistrib
public import IdlaCyl.Support.Idla

@[expose] public section

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable (B : Base)

/-- **The optional-stopping core.**  If the exit-site integral of `ψ` vanishes
for every set `S ⊇ R_0`, then the conditional expectation of `ψ` at the `k`-th
settling site given `𝓕_k` is almost surely zero. -/
theorem condExp_settleSite_eq_zero (B : Base) (ψ : Site B → ℝ)
    (hzero : ZeroHorizontalAverage B ψ)
    (hint_zero : ∀ S : Set (Site B), R B 0 ⊆ S →
      ∫ w, ψ (exitSite' B S w) ∂(walkLawUniform B) = 0)
    (k : ℕ) :
    (idlaMeasure B)[fun ω : TrajSeq B => ψ (settleSite B ω k) | idlaFiltration B k]
      =ᵐ[idlaMeasure B] 0 := by
  classical
  -- `hzero` is the paper's own zero-horizontal-average hypothesis; here
  -- its consequences are already packaged in `hint_zero`, but it is kept in the
  -- signature for interface stability with `le:martingale`.
  have _hzero : ZeroHorizontalAverage B ψ := hzero
  by_cases hint : Integrable (fun ω : TrajSeq B => ψ (settleSite B ω k)) (idlaMeasure B)
  · -- integrable case: use the conditional-expectation form and `hint_zero`
    have hψ : StronglyMeasurable ψ := (measurable_of_countable ψ).stronglyMeasurable
    refine (condExp_settleSite_eq_integral B k ψ hψ hint).trans ?_
    filter_upwards with ω
    exact hint_zero (clusterTraj B ω k)
      (clusterFrom_mono B (R B 0) ω (Nat.zero_le k))
  · -- non-integrable case: `condExp` is zero by definition
    rw [condExp_of_not_integrable hint]

end IdlaCyl
