/-
The martingale property of the harmonic statistic `M(t) = (1/N)⟪D_t, ψ⟫`.

`paper/idla-cylinder-gff.tex:687-691` (Lemma `le:martingale`):

  "Let `ψ : 𝔾_N → ℝ` be a discrete harmonic function with the zero horizontal
   average property and exponential decay as `y → -∞`, let `(A(t))_{t ≥ 0}` be an
   IDLA process on `𝔾_N` with `A(0) = R_0`, and let
   `M(t) := (1/N)⟪D_t, ψ⟫ = (1/N)∑_{(x,y) ∈ A_+(t)} ψ(x,y)`. Then `(M(t))_{t ≥ 0}`
   is a martingale with respect to the natural filtration of the IDLA process."

The canonical statistic `harmonicMartingale B ψ t = (1/N)∑_{k<t} ψ(z_k)` is a
`Finset.range` sum over the settling sites `z_k = settleSite B · k`
(`Support/Martingale.lean`), and the natural filtration is `idlaFiltration B`
(`Support/Filtration.lean`: `𝓕_k = σ(z_0,…,z_{k-1})`).

The paper's proof has two halves:

* the probabilistic half, `𝔼[ψ(z_k) | 𝓕_k] = 0`, obtained from discrete
  harmonicity, the zero horizontal average and the exponential decay by optional
  stopping (the paper's `tex:693-707`); this is the source of the three
  hypotheses `hharm`, `hzero`, `hdecay`, and it is taken here as the explicit
  hypothesis `hcond`, proved as `condExp_settleSite_eq_zero`;
* the algebraic half proved *here*: the one-step conditional-mean identity
  upgrades to the martingale property for all `i ≤ j`, by the tower property of
  the conditional expectation (`Filtration.condExp_condExp`), linearity over the
  finite sum (`condExp_finsetSum`, `condExp_add`, `condExp_smul`), and the
  adaptedness of the statistic.

`hint` records the integrability of `M(t)`, which is what makes `Martingale`'s
`condExp` identity meaningful (Mathlib's `Martingale` derives `Integrable` from
it, but the statistic must be integrable for the tower argument to apply).

Note `Measurable ψ` is *not* an extra hypothesis: `Site B = V_N × ℤ` is countable
with the discrete σ-algebra (`V_N` discrete, `ℤ` measurable singletons), so every
`ψ` is measurable and every sample value `ψ (settleSite B · k)` is
`𝓕_k`-measurable.
-/
import IdlaCyl.Support.Harmonic
import IdlaCyl.Support.Filtration
import IdlaCyl.Support.Martingale
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

namespace IdlaCyl

open MeasureTheory Filter
open scoped BigOperators

/-- **`le:martingale` (`tex:687-691`), algebraic half.**

Given the one-step conditional-mean vanishing `hcond`
(`(idlaMeasure B)[ψ ∘ settleSite B · k | 𝓕_k] =ᵐ 0`) and integrability of the
statistic, the harmonic statistic `M(t) = (1/N)∑_{k<t} ψ(z_k)` is a martingale
for the natural filtration `idlaFiltration B`. The hypotheses `hharm`, `hzero`,
`hdecay` are the paper's inputs to `hcond` and are recorded for fidelity. -/
theorem harmonicMartingale_isMartingale (B : Base) (ψ : Site B → ℝ)
    (hharm : DiscreteHarmonic B ψ) (hzero : ZeroHorizontalAverage B ψ)
    (hdecay : ExpDecayBelow B ψ)
    (hint : ∀ t, Integrable (harmonicMartingale B ψ t) (idlaMeasure B))
    (hcond : ∀ k, (idlaMeasure B)[fun ω : TrajSeq B => ψ (settleSite B ω k) | idlaFiltration B k] =ᵐ[idlaMeasure B] 0) :
    Martingale (harmonicMartingale B ψ) (idlaFiltration B) (idlaMeasure B) := by
  classical
  have _ := hharm
  have _ := hzero
  have _ := hdecay
  have hψmeas : Measurable ψ := measurable_of_countable ψ
  -- Adaptedness: every summand is `𝓕_t`-measurable for `k < t`, and the finite
  -- sum inherits measurability.
  have hstrong : StronglyAdapted (idlaFiltration B) (harmonicMartingale B ψ) := by
    intro t
    refine Measurable.stronglyMeasurable ?_
    unfold harmonicMartingale
    refine Measurable.const_mul ?_ _
    exact Finset.measurable_sum (Finset.range t) (fun k hk =>
      hψmeas.comp (measurable_settleSite_filtration_of_lt B (Finset.mem_range.mp hk)))
  refine ⟨hstrong, ?_⟩
  intro i j hij
  have hcard : (B.card : ℝ) ≠ 0 := by
    have h2 : (2 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast B.nontrivial
    positivity
  -- Integrability of each summand, from the one-step difference of the
  -- integrable statistic: `ψ ∘ settleSite B · k = N · (M(k+1) - M(k))`.
  have hZint : ∀ k, Integrable (fun ω : TrajSeq B => ψ (settleSite B ω k)) (idlaMeasure B) := by
    intro k
    have hEq : (fun ω : TrajSeq B => ψ (settleSite B ω k))
        = fun ω => (B.card : ℝ) *
            (harmonicMartingale B ψ (k + 1) ω - harmonicMartingale B ψ k ω) := by
      funext ω
      rw [harmonicMartingale_succ B ψ k ω]
      field_simp
    rw [hEq]
    exact ((hint (k+1)).sub (hint k)).const_mul _
  have hTint : Integrable (fun ω : TrajSeq B => ∑ k ∈ Finset.Ico i j, ψ (settleSite B ω k)) (idlaMeasure B) :=
    integrable_finsetSum _ (fun k _ => hZint k)
  have hMi : (idlaMeasure B)[harmonicMartingale B ψ i | idlaFiltration B i] = harmonicMartingale B ψ i :=
    condExp_of_stronglyMeasurable ((idlaFiltration B).le i) (hstrong i) (hint i)
  -- `𝔼[∑_{i ≤ k < j} ψ(z_k) | 𝓕_i] = 0`, by the tower property and `hcond`.
  have hTcond : (idlaMeasure B)[fun ω : TrajSeq B => ∑ k ∈ Finset.Ico i j, ψ (settleSite B ω k) | idlaFiltration B i] =ᵐ[idlaMeasure B] 0 := by
    have hbase := condExp_finsetSum (s := Finset.Ico i j)
      (f := fun k (ω : TrajSeq B) => ψ (settleSite B ω k)) (fun k _ => hZint k) (idlaFiltration B i)
    rw [show (∑ k ∈ Finset.Ico i j, fun ω : TrajSeq B => ψ (settleSite B ω k))
        = (fun ω : TrajSeq B => ∑ k ∈ Finset.Ico i j, ψ (settleSite B ω k)) from by
          ext ω; rw [Finset.sum_apply]] at hbase
    refine hbase.trans ?_
    have hper : ∀ k ∈ Finset.Ico i j,
        (idlaMeasure B)[fun ω : TrajSeq B => ψ (settleSite B ω k) | idlaFiltration B i] =ᵐ[idlaMeasure B] 0 := by
      intro k hk
      have hik : i ≤ k := (Finset.mem_Ico.mp hk).1
      have h1 : (idlaMeasure B)[(idlaMeasure B)[fun ω : TrajSeq B => ψ (settleSite B ω k) | idlaFiltration B k] | idlaFiltration B i]
          =ᵐ[idlaMeasure B] (idlaMeasure B)[fun ω : TrajSeq B => ψ (settleSite B ω k) | idlaFiltration B i] :=
        Filtration.condExp_condExp (fun ω : TrajSeq B => ψ (settleSite B ω k)) (idlaFiltration B) hik
      have h2 : (idlaMeasure B)[(idlaMeasure B)[fun ω : TrajSeq B => ψ (settleSite B ω k) | idlaFiltration B k] | idlaFiltration B i]
          =ᵐ[idlaMeasure B] (idlaMeasure B)[(0 : TrajSeq B → ℝ) | idlaFiltration B i] :=
        condExp_congr_ae (hcond k)
      rw [condExp_zero] at h2
      exact h1.symm.trans h2
    refine (eventuallyEq_sum hper).trans ?_
    simp
  have hscaled : (idlaMeasure B)[fun ω : TrajSeq B => (1 / (B.card : ℝ)) * ∑ k ∈ Finset.Ico i j, ψ (settleSite B ω k) | idlaFiltration B i]
      =ᵐ[idlaMeasure B] fun ω => (1 / (B.card : ℝ)) * ((idlaMeasure B)[fun ω : TrajSeq B => ∑ k ∈ Finset.Ico i j, ψ (settleSite B ω k) | idlaFiltration B i]) ω := by
    have h : (idlaMeasure B)[(1 / (B.card : ℝ)) • (fun ω : TrajSeq B => ∑ k ∈ Finset.Ico i j, ψ (settleSite B ω k)) | idlaFiltration B i]
        =ᵐ[idlaMeasure B] (1 / (B.card : ℝ)) • (idlaMeasure B)[fun ω : TrajSeq B => ∑ k ∈ Finset.Ico i j, ψ (settleSite B ω k) | idlaFiltration B i] :=
      condExp_smul (1 / (B.card : ℝ)) (fun ω : TrajSeq B => ∑ k ∈ Finset.Ico i j, ψ (settleSite B ω k)) (idlaFiltration B i)
    have hconv1 : ((1 / (B.card : ℝ)) • (fun ω : TrajSeq B => ∑ k ∈ Finset.Ico i j, ψ (settleSite B ω k)))
        = (fun ω : TrajSeq B => (1 / (B.card : ℝ)) * ∑ k ∈ Finset.Ico i j, ψ (settleSite B ω k)) := by
      ext ω; rw [Pi.smul_apply, smul_eq_mul]
    have hconv2 : ((1 / (B.card : ℝ)) • (idlaMeasure B)[fun ω : TrajSeq B => ∑ k ∈ Finset.Ico i j, ψ (settleSite B ω k) | idlaFiltration B i])
        = (fun ω : TrajSeq B => (1 / (B.card : ℝ)) * ((idlaMeasure B)[fun ω : TrajSeq B => ∑ k ∈ Finset.Ico i j, ψ (settleSite B ω k) | idlaFiltration B i]) ω) := by
      ext ω; rw [Pi.smul_apply, smul_eq_mul]
    rw [hconv1, hconv2] at h
    exact h
  -- `M(j)` splits as `M(i)` plus the `Ico i j` part.
  have hsplit : harmonicMartingale B ψ j
      = harmonicMartingale B ψ i + fun ω : TrajSeq B => (1 / (B.card : ℝ)) * ∑ k ∈ Finset.Ico i j, ψ (settleSite B ω k) := by
    funext ω
    simp only [Pi.add_apply]
    unfold harmonicMartingale
    rw [← Finset.sum_range_add_sum_Ico (fun k => ψ (settleSite B ω k)) hij]
    ring
  have hconst : (fun ω : TrajSeq B => (1 / (B.card : ℝ)) * ((idlaMeasure B)[fun ω : TrajSeq B => ∑ k ∈ Finset.Ico i j, ψ (settleSite B ω k) | idlaFiltration B i]) ω)
      =ᵐ[idlaMeasure B] (fun ω : TrajSeq B => (1 / (B.card : ℝ)) * (0 : TrajSeq B → ℝ) ω) := by
    filter_upwards [hTcond] with ω hω
    rw [hω]
  calc
    (idlaMeasure B)[harmonicMartingale B ψ j | idlaFiltration B i]
        =ᵐ[idlaMeasure B] (idlaMeasure B)[harmonicMartingale B ψ i + fun ω : TrajSeq B => (1 / (B.card : ℝ)) * ∑ k ∈ Finset.Ico i j, ψ (settleSite B ω k)
            | idlaFiltration B i] := condExp_congr_ae (by rw [hsplit])
    _ =ᵐ[idlaMeasure B] (idlaMeasure B)[harmonicMartingale B ψ i | idlaFiltration B i]
          + (idlaMeasure B)[fun ω : TrajSeq B => (1 / (B.card : ℝ)) * ∑ k ∈ Finset.Ico i j, ψ (settleSite B ω k) | idlaFiltration B i] :=
        condExp_add (hint i) (hTint.const_mul _) (idlaFiltration B i)
    _ =ᵐ[idlaMeasure B] harmonicMartingale B ψ i
          + fun ω : TrajSeq B => (1 / (B.card : ℝ)) * ((idlaMeasure B)[fun ω : TrajSeq B => ∑ k ∈ Finset.Ico i j, ψ (settleSite B ω k) | idlaFiltration B i]) ω := by
        rw [hMi]
        filter_upwards [hscaled] with ω hω
        simp only [Pi.add_apply]
        rw [hω]
    _ =ᵐ[idlaMeasure B] harmonicMartingale B ψ i + fun ω : TrajSeq B => (1 / (B.card : ℝ)) * (0 : TrajSeq B → ℝ) ω := by
        filter_upwards [hconst] with ω hω
        simp only [Pi.add_apply]
        rw [hω]
    _ =ᵐ[idlaMeasure B] harmonicMartingale B ψ i := by
        filter_upwards with ω
        simp

end IdlaCyl
