module

/-
The honest zero-conditional-mean statement.

`Support/CondExpZero.lean` states `condExp_settleSite_eq_zero` with the
zero-integral hypothesis

  `hint_zero : ∀ S, R B 0 ⊆ S → ∫ w, ψ (exitSite' B S w) ∂(walkLawUniform B) = 0`,

which quantifies over *all* sets containing `R_0`, unbounded ones included.
This is the wrong interface:
the walk optional stopping `integral_exitSite_uniform_eq_zero_of_expDecayBelow`
proves the vanishing only under the height cap `S ⊆ R B h`, and the unbounded-`S`
instances of `hint_zero` can only be satisfied through the `integral_undef` junk
value (the exit site is unbounded above and `ψ` at the exit is not integrable),
and no declaration in the library discharges `hint_zero`.

This file supplies the honest form.  The only sets actually used by the proof of
`condExp_settleSite_eq_zero` are the clusters `clusterTraj B ω k`, and those are
always contained in a half-cylinder:

* `IdlaCyl.clusterTraj_subset_R B ω k` (`Support/ClusterHeight.lean`) gives an
  explicit height `H` with `clusterTraj B ω k ⊆ R B H`;
* `IdlaCyl.clusterTraj_plus_ncard_of_seed_subset` gives the seed inclusion
  `R B 0 ⊆ clusterTraj B ω k`;
* `IdlaCyl.exitTraj_ae_finite_hits_all_levels` / `exitTraj_ae_finite_of_hits_all`
  give the a.s. finiteness of the exit from the cluster.

So `condExp_settleSite_eq_zero_of_expDecayBelow` derives the conditional mean
vanishing with the honest integrability hypothesis
`hint : ∀ k, Integrable (ψ ∘ settleSite B · k) (idlaMeasure B)` and no
zero-integral hypothesis at all.  Feeding it to
`harmonicMartingale_isMartingale` gives the unconditional martingale
`harmonicMartingale_isMartingale_of_expDecayBelow` (still carrying the
integrability of the statistic, which is the separate `pr:apriori` input).
-/
public import IdlaCyl.Support.CondDistrib
public import IdlaCyl.Support.ExitIntegral
public import IdlaCyl.Support.ClusterHeight
public import IdlaCyl.Support.MartingaleProperty

@[expose] public section

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable (B : Base)

/-- **The honest zero-conditional-mean statement.**  For a discrete harmonic,
zero-horizontal-average, exponentially decaying `ψ`, the conditional expectation
of `ψ` at the `k`-th settling site given `𝓕_k` vanishes almost surely.

Unlike `condExp_settleSite_eq_zero`, this takes the integrability of the summand
as a hypothesis (the honest one: no `hint_zero` over unbounded sets) and supplies
the zero exit integral from `integral_exitSite_uniform_eq_zero_of_expDecayBelow`
at the actual cluster `clusterTraj B ω k`. -/
theorem condExp_settleSite_eq_zero_of_expDecayBelow (B : Base) (ψ : Site B → ℝ)
    (hharm : DiscreteHarmonic B ψ) (hzero : ZeroHorizontalAverage B ψ)
    (hd : ExpDecayBelow B ψ)
    (hint : ∀ k, Integrable (fun ω : TrajSeq B => ψ (settleSite B ω k)) (idlaMeasure B))
    (k : ℕ) :
    (idlaMeasure B)[fun ω : TrajSeq B => ψ (settleSite B ω k) | idlaFiltration B k]
      =ᵐ[idlaMeasure B] 0 := by
  have hf : StronglyMeasurable ψ := (measurable_of_countable ψ).stronglyMeasurable
  refine (condExp_settleSite_eq_integral B k ψ hf (hint k)).trans ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  obtain ⟨H, hH⟩ := clusterTraj_subset_R B ω k
  have hS0 : R B 0 ⊆ clusterTraj B ω k := clusterTraj_plus_ncard_of_seed_subset B ω k
  have hae : ∀ᵐ X ∂(walkLawUniform B), exitTime' B (clusterTraj B ω k) X ≠ ⊤ := by
    filter_upwards [exitTraj_ae_finite_hits_all_levels B] with X hX
    exact exitTraj_ae_finite_of_hits_all B ω k hX
  exact integral_exitSite_uniform_eq_zero_of_expDecayBelow B ψ hharm hzero hd
    (clusterTraj B ω k) H hH hS0 hae

/-- **The unconditional martingale.**  `harmonicMartingale_isMartingale` with its
`hcond` hypothesis discharged by `condExp_settleSite_eq_zero_of_expDecayBelow`.
The remaining hypothesis is the integrability of the statistic `M(t)`, the
`pr:apriori` input; the per-summand integrability needed by the discharge is
derived from it by `harmonicMartingale_succ`. -/
theorem harmonicMartingale_isMartingale_of_expDecayBelow (B : Base) (ψ : Site B → ℝ)
    (hharm : DiscreteHarmonic B ψ) (hzero : ZeroHorizontalAverage B ψ)
    (hd : ExpDecayBelow B ψ)
    (hint : ∀ t, Integrable (harmonicMartingale B ψ t) (idlaMeasure B)) :
    Martingale (harmonicMartingale B ψ) (idlaFiltration B) (idlaMeasure B) := by
  have hcard : (B.card : ℝ) ≠ 0 := by
    have h2 : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
    positivity
  have hZint : ∀ k, Integrable (fun ω : TrajSeq B => ψ (settleSite B ω k)) (idlaMeasure B) := by
    intro k
    have hEq : (fun ω : TrajSeq B => ψ (settleSite B ω k))
        = fun ω => (B.card : ℝ) *
            (harmonicMartingale B ψ (k + 1) ω - harmonicMartingale B ψ k ω) := by
      funext ω
      rw [harmonicMartingale_succ B ψ k ω]
      field_simp
    rw [hEq]
    exact ((hint (k + 1)).sub (hint k)).const_mul _
  exact harmonicMartingale_isMartingale B ψ hharm hzero hd hint
    (fun k => condExp_settleSite_eq_zero_of_expDecayBelow B ψ hharm hzero hd hZint k)

end IdlaCyl
