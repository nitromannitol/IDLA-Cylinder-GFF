module

/-
External propositions carried as explicit binders.

Each is a `def … : Prop`, never a `theorem`, so that it is a legitimate
hypothesis carrier rather than a claimed result about a fixed predicate.  The
shape branch consumes these; the Gaussian branch consumes a subset.  Each is
discharged in `IdlaCyl/External/Discharge/`.

Nothing in this file asserts a result about the actual IDLA process.  The
propositions are the *statements* of the cited inputs, and each consumer takes
the ones it needs as a binder.

The cluster-level propositions (`AbelianPerm`, `AbelianMono`,
`AbelianTwoStage`, `prescribedMeasure`) live in `IdlaCyl/External/Abelian.lean`,
because they mention `clusterFrom`/`TrajSeq`, which are built in
`IdlaCyl/Support/CanonicalIdla.lean`.
-/
public import IdlaCyl.Support.Canonical

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IdlaCyl.External

-- FROZEN-STATEMENT-BEGIN
/-- `ext-lazy-rw-recurrent` (`tex:600-604`): the lazy symmetric
nearest-neighbour walk on `ℤ` is recurrent, hence an admissible cylinder walk
almost surely reaches every level above its start. -/
def LazyRwRecurrent : Prop :=
  ∀ (B : Base) (p : Site B) (k : ℤ), ∀ᵐ X ∂walkPathLaw B p, ∃ n, k ≤ (X n).2

/-- `ext-freedman` (`tex:1209-1216`, Freedman 1975 eq. (1.5)), in the form
`lem:M lower tail` consumes. -/
def Freedman : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)) (M : ℕ → Ω → ℝ) (n : ℕ)
    (b v r : ℝ),
    Martingale M ℱ P → M 0 = 0 → (∀ t, Integrable (M t) P) → 0 < b → 0 ≤ v → 0 ≤ r →
    (∀ i < n, ∀ ω, |M (i + 1) ω - M i ω| ≤ b) →
    (∀ᵐ ω ∂P, ∑ i ∈ Finset.range n,
        (P[fun ω' => (M (i + 1) ω' - M i ω') ^ 2 | ℱ i]) ω ≤ v) →
    P {ω | M n ω ≤ -r} ≤ ENNReal.ofReal (Real.exp (-(r ^ 2 / (2 * (v + b * r / 3)))))

/-- `ext-bernstein` (`tex:1314-1320`): a two-sided deviation bound for a sum of
independent indicators with variance proxy `∑ pᵢ`. -/
def Bernstein : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (p : Fin n → ℝ) (X : Fin n → Ω → ℝ) (ε : ℝ),
    (∀ i, 0 ≤ p i) → (∀ i, p i ≤ 1) → 0 ≤ ε →
    iIndepFun X P → (∀ i ω, X i ω = 0 ∨ X i ω = 1) →
    (∀ i, ∫ ω, X i ω ∂P = p i) →
    P {ω | ε ≤ |(∑ i, X i ω) - ∑ i, p i|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(ε ^ 2 / 2) / (∑ i, p i + ε / 3)))

/-- `ext-chernoff` (`tex:1341-1343`): the multiplicative lower tail of a sum of
independent indicators, `ℙ(S < (1-δ)μ) ≤ exp(−δ²μ/2)`. -/
def Chernoff : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (p δ : ℝ) (X : Fin n → Ω → ℝ),
    0 ≤ p → p ≤ 1 → 0 ≤ δ → δ ≤ 1 →
    iIndepFun X P → (∀ i ω, X i ω = 0 ∨ X i ω = 1) →
    (∀ i, ∫ ω, X i ω ∂P = p) →
    P {ω | (∑ i, X i ω) < (1 - δ) * (n * p)}
      ≤ ENNReal.ofReal (Real.exp (-(δ ^ 2 * n * p / 4)))
-- FROZEN-STATEMENT-END

/-! ### Obligations, not citations

`LazyRwRecurrent` is a statement about *our own* `walkPathLaw`, not a literature
import.  It is an obligation of this development, discharged in
`IdlaCyl/External/Discharge/LazyRw.lean`.

The former `OptionalStopping` (a `Prop` with an everywhere-finite `τ : Ω → ℕ`,
inapplicable to the a.s.-finite `exitTime'`) has been deleted;
the replacement is the *theorem* `IdlaCyl.integral_stoppedValue_of_ae_finite` in
`IdlaCyl/Support/Stopping.lean`.  `StrongMarkov` likewise stated only the
one-step property and has been moved to
`IdlaCyl/Support/StrongMarkov.lean`, restated for random stopping times.

`External.Chernoff`'s exponent is `−(δ²np/4)`, not `−(δ²np/2)`: the latter is not
reachable from `LatticeProb.bernstein_one_sided` or `adaptive_lower_tail`; the `∃ K₁` in `le_released` absorbs the
factor.  `External.Bernstein` carries the standard factor 2 (erratum E15):
`LatticeProb.bernstein` yields `2 · exp(−(ε²/2)/(B² + Mε/3))` and the factor 2
cannot be removed, but `le_released`'s `∃ K₁` absorbs it as well. -/

end IdlaCyl.External
