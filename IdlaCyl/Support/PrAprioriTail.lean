/-
The occupation-recurrence / binomial-tail reduction behind `pr:apriori`
(`tex:583-619`), on the **canonical** carrier (`TrajSeq`/`idlaMeasure`).

`layerMean B t m` is the paper's `μ_m(t) = 𝔼 Z_m(t)`, the expected number of
occupied sites at vertical level `m` at time `t`, written as a sum of
`idlaMeasure`-probabilities so that a failure of measurability cannot silently
produce `0`.

The paper's argument is

  `μ_m(t+1) − μ_m(t) ≤ (1/N) μ_{m-1}(t)`   (`eq:mu-recurrence`, `tex:590`),

and then `cylinder_binomial_recurrence` (`Support/BinomialBound.lean`) turns it
into `μ_m(t) ≤ N^{-(m-1)} C(t,m)`.  This file lands the reduction and leaves the
one-step recurrence `hstep` as the explicit remaining input.  That recurrence is
the only place where the uniformity of the first hit of a level (`tex:595-610`)
enters; its canonical one-step form is
`IdlaCyl.condExp_settleSite_level_le_layerCount` (`Support/PrAprioriSupport.lean`).

Nothing here mentions the retired `Driver`/`driverLaw`/`cluster` carrier.
-/
import IdlaCyl.Support.CanonicalIdla
import IdlaCyl.Support.BinomialBound

namespace IdlaCyl

open MeasureTheory Filter
open scoped BigOperators ENNReal

/-- `μ_m(t) = 𝔼 Z_m(t)`, the expected occupation of vertical level `m` at time
`t` under the canonical IDLA law (`tex:583`).  Written as
`∑_x ℙ((x,m) ∈ A(t))`, so it is an expectation by construction. -/
noncomputable def layerMean (B : Base) (t : ℕ) (m : ℤ) : ℝ :=
  ∑ x : B.V, (idlaMeasure B {ω : TrajSeq B | (x, m) ∈ clusterTraj B ω t}).toReal

theorem layerMean_nonneg (B : Base) (t : ℕ) (m : ℤ) : 0 ≤ layerMean B t m :=
  Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

/-- `μ_m(0) = 0` for `m ≥ 1` (`tex:628`): the flat configuration `R_0` has no
site above level `0`, and `clusterTraj B · 0 = R_0`. -/
theorem layerMean_zero (B : Base) (m : ℤ) (hm : 1 ≤ m) : layerMean B 0 m = 0 := by
  unfold layerMean
  refine Finset.sum_eq_zero fun x _ => ?_
  have hempty : {ω : TrajSeq B | (x, m) ∈ clusterTraj B ω 0} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rw [show clusterTraj B ω 0 = R B 0 from rfl, mem_R]
    intro h
    have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  rw [hempty, measure_empty, ENNReal.toReal_zero]

/-- **`LBG_up` from the recurrence** (`tex:585-619`).  The paper's one-step
recurrence `μ_{m+1}(t+1) ≤ μ_{m+1}(t) + (1/N) μ_m(t)`, together with the two base
cases, gives `μ_{m+1}(t) ≤ N^{-m} C(t, m+1)`. -/
theorem layerMean_le_binom_of_recurrence (B : Base) (hN : 0 < B.card)
    (hzero : ∀ m : ℕ, layerMean B 0 ((m : ℤ) + 1) ≤ 0)
    (hbase : ∀ t, layerMean B t 1 ≤ (t : ℝ))
    (hstep : ∀ m t, layerMean B (t + 1) ((m : ℤ) + 2) ≤
      layerMean B t ((m : ℤ) + 2) + (1 / (B.card : ℝ)) * layerMean B t ((m : ℤ) + 1)) :
    ∀ m t : ℕ, layerMean B t ((m : ℤ) + 1) ≤
      (1 / (B.card : ℝ)) ^ m * (Nat.choose t (m + 1) : ℝ) := by
  have h := cylinder_binomial_recurrence (fun m t => layerMean B t ((m : ℤ) + 1)) B.card hN
    hzero hbase ?_
  · exact h
  · intro m t
    have h' := hstep m t
    have hidx : ((m : ℤ) + 2) = (((m + 1 : ℕ) : ℤ) + 1) := by push_cast; ring
    rwa [hidx] at h'

end IdlaCyl
