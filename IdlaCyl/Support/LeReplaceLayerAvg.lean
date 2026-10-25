module

/-
The `eq:layeravg` inputs of `le:replace` (`paper/idla-cylinder-gff.tex:836-841`).

`layerMean B t m = 𝔼 Z_m(t) = Σ_x ℙ((x,m) ∈ A(t))` is the expected number of
occupied sites of the canonical cluster `A(t) = clusterTraj B · t` at height `m`
(`Support/PrAprioriTail.lean`, `Support/LayerRecurrence.lean`).

This file proves the two layer facts the layer-averaging estimate
`eq:layeravg` consumes:

1. **Layer constancy** (`tex:836`): for fixed `y`, the probability
   `ℙ((x,y) ∈ A(T))` is independent of `x`.  This is vertex-transitivity of the
   base `V_N` (`Base.vertexTransitive`) pushed through the *measure-level*
   horizontal invariance of `idlaMeasure` (`idlaMeasure_map_transportTraj`,
   `Support/Transitive.lean`).  Consequently
   `layerMean B T y = N · ℙ((x,y) ∈ A(T))` for every `x`.

2. **Mass bound** (`clusterTraj_plus_ncard`): `A_+(T) = A(T) ∩ {y ≥ 1}` has
   exactly `T` sites almost surely, so the total layer mass over any finite slab
   of heights is at most `T`:
   `Σ_{y ∈ Icc 1 M} layerMean B T y ≤ T`, and for each `x`,
   `Σ_{y ∈ Icc 1 M} N · ℙ((x,y) ∈ A(T)) ≤ T`.

## Relation to the paper's `≤ 2`

The paper's `eq:layeravg` mass bound is `Σ_y N r_j(y) ≤ 2`, where
`r_j(y) = ℙ((x,y) ∈ D_j)` and `D_j = A_+(T; ω) △ A_+(T; ω̃)` is the *resampled
difference* — the `|D_j| ≤ 2` is `pr:exchange` (`tex:830-833`).  It is **not** a
bound on the mass of `A(T)` itself: `A_+(T)` has `T` sites, so the mass of
`A(T)` in a slab is `T`, not `2`.  The `≤ 2` discrepancy form needs the
resampling pair `(ω, ω̃)` and a *canonical* `pr:exchange` over `TrajSeq`
(the frozen `Frozen.pr_exchange` is stated over the retired `Driver` carrier);
the canonical resampling layer is not yet in the tree.  This file therefore
proves the `A_+`-mass bound with the named lemmas (`clusterTraj_plus_ncard`,
`layerMean`) and records the discrepancy-mass form as a separate obligation.
-/
public import IdlaCyl.Support.CanonicalGrowth
public import IdlaCyl.Support.LayerRecurrence
public import IdlaCyl.Support.Transitive
public import IdlaCyl.Support.Discrepancy

@[expose] public section

namespace IdlaCyl

open MeasureTheory
open scoped BigOperators ENNReal

variable (B : Base)

/-- **(1) Layer constancy** (`tex:836`): for fixed `y`, the probability that
`(x,y)` lies in the cluster `A(T)` does not depend on the horizontal coordinate
`x`. -/
theorem layer_constancy (T : ℕ) (x x' : B.V) (y : ℤ) :
    (idlaMeasure B).real {w : TrajSeq B | (x, y) ∈ clusterTraj B w T}
      = (idlaMeasure B).real {w : TrajSeq B | (x', y) ∈ clusterTraj B w T} := by
  obtain ⟨σ, hσ⟩ := B.vertexTransitive x x'
  exact idlaMeasure_real_clusterTraj_orbit B σ x x' T hσ y

/-- `layerMean` is `N` times the (`x`-independent) layer probability. -/
theorem layerMean_eq_card_mul_layerProb (T : ℕ) (x : B.V) (y : ℤ) :
    layerMean B T y
      = (B.card : ℝ)
        * (idlaMeasure B).real {w : TrajSeq B | (x, y) ∈ clusterTraj B w T} := by
  unfold layerMean
  change ∑ x' : B.V, (idlaMeasure B).real {ω | (x', y) ∈ clusterTraj B ω T}
      = (B.card : ℝ) * (idlaMeasure B).real {ω | (x, y) ∈ clusterTraj B ω T}
  rw [Finset.sum_congr rfl (fun x' _ => layer_constancy B T x' x y)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rfl

/-- The number of occupied sites in a finite slab of layers is at most the
total number of occupied sites above level `0`. -/
theorem layerCount_sum_Icc_le_clusterPlusFinset (T : ℕ) (M : ℤ) (ω : TrajSeq B) :
    ∑ y ∈ Finset.Icc 1 M, layerCount B ω T y ≤ (clusterPlusFinset B ω T).card := by
  classical
  have hcount : ∀ y : ℤ, layerCount B ω T y
      = ∑ x : B.V, if (x, y) ∈ clusterTraj B ω T then 1 else 0 := by
    intro y
    rw [layerCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hprod : (((Finset.univ : Finset B.V).product (Finset.Icc 1 M)).filter
        (fun p : Site B => p ∈ clusterTraj B ω T)).card
      = ∑ x : B.V, ∑ y ∈ Finset.Icc 1 M,
          (if (x, y) ∈ clusterTraj B ω T then 1 else 0) := by
    rw [Finset.card_filter]
    exact Finset.sum_product _ _ _
  calc
    ∑ y ∈ Finset.Icc 1 M, layerCount B ω T y
        = ∑ x : B.V, ∑ y ∈ Finset.Icc 1 M,
            (if (x, y) ∈ clusterTraj B ω T then 1 else 0) := by
          rw [Finset.sum_congr rfl (fun y _ => hcount y)]
          exact Finset.sum_comm
    _ = (((Finset.univ : Finset B.V).product (Finset.Icc 1 M)).filter
            (fun p : Site B => p ∈ clusterTraj B ω T)).card := hprod.symm
    _ ≤ (clusterPlusFinset B ω T).card := by
          apply Finset.card_le_card
          intro p hp
          rw [Finset.mem_filter] at hp
          obtain ⟨hpmem, hpcl⟩ := hp
          have hp2 : 1 ≤ p.2 := by
            have h2 := (Finset.mem_product.mp hpmem).2
            exact (Finset.mem_Icc.mp h2).1
          exact (mem_clusterPlusFinset_iff_cluster B ω T hp2).mpr hpcl

/-- The slab mass is at most `|A_+(T)|`. -/
theorem layerCount_sum_Icc_le_ncard (T : ℕ) (M : ℤ) (ω : TrajSeq B) :
    ∑ y ∈ Finset.Icc 1 M, layerCount B ω T y
      ≤ (clusterTraj B ω T ∩ {p : Site B | 1 ≤ p.2}).ncard := by
  rw [show clusterTraj B ω T ∩ {p : Site B | 1 ≤ p.2}
        = (clusterPlusFinset B ω T : Set (Site B)) from
      (coe_clusterPlusFinset B ω T).symm]
  rw [Set.ncard_coe_finset]
  exact layerCount_sum_Icc_le_clusterPlusFinset B T M ω

/-- Deterministic slab mass bound: at most `T` sites. -/
theorem layerCount_sum_Icc_le_card (T : ℕ) (M : ℤ) (ω : TrajSeq B) :
    ∑ y ∈ Finset.Icc 1 M, layerCount B ω T y ≤ T := by
  refine (layerCount_sum_Icc_le_clusterPlusFinset B T M ω).trans ?_
  unfold clusterPlusFinset
  calc (Finset.filter (fun p => 1 ≤ p.2) ((Finset.range T).image (settleSite B ω))).card
      ≤ ((Finset.range T).image (settleSite B ω)).card := Finset.card_filter_le _ _
    _ ≤ (Finset.range T).card := Finset.card_image_le
    _ = T := Finset.card_range T

/-- **(2) Mass bound** (`clusterTraj_plus_ncard`, `tex:265`, `tex:340`): the
total expected layer mass of `A(T)` over any finite slab of heights is at most
`T`, because `A_+(T)` has exactly `T` sites almost surely. -/
theorem layerMean_sum_Icc_le (T : ℕ) (M : ℤ) :
    ∑ y ∈ Finset.Icc 1 M, layerMean B T y ≤ (T : ℝ) := by
  have hint : ∀ y ∈ Finset.Icc 1 M, Integrable (fun ω : TrajSeq B =>
      (layerCount B ω T y : ℝ)) (idlaMeasure B) :=
    fun y _ => integrable_layerCount B T y
  rw [Finset.sum_congr rfl (fun y _ => layerMean_eq_integral B T y)]
  rw [← integral_finsetSum _ hint]
  have hbound : ∀ᵐ ω ∂idlaMeasure B,
      ∑ y ∈ Finset.Icc 1 M, (layerCount B ω T y : ℝ) ≤ (T : ℝ) := by
    filter_upwards [clusterTraj_plus_ncard B T] with ω hω
    exact_mod_cast (layerCount_sum_Icc_le_ncard B T M ω).trans (le_of_eq hω)
  have hint2 : Integrable (fun ω : TrajSeq B =>
      ∑ y ∈ Finset.Icc 1 M, (layerCount B ω T y : ℝ)) (idlaMeasure B) :=
    integrable_finsetSum _ (fun y _ => integrable_layerCount B T y)
  calc ∫ ω, ∑ y ∈ Finset.Icc 1 M, (layerCount B ω T y : ℝ) ∂idlaMeasure B
      ≤ ∫ ω, (T : ℝ) ∂idlaMeasure B := integral_mono_ae hint2 (integrable_const _) hbound
    _ = (T : ℝ) := by rw [integral_const, probReal_univ, smul_eq_mul, one_mul]

/-- The mass bound in the form `eq:layeravg` reads it: for any fixed `x` and any
finite slab of heights `Icc 1 M`, `Σ_y N · ℙ((x,y) ∈ A(T)) ≤ T`. -/
theorem layerProb_slab_mass_le (T : ℕ) (x : B.V) (M : ℤ) :
    ∑ y ∈ Finset.Icc 1 M,
        (B.card : ℝ)
          * (idlaMeasure B).real {w : TrajSeq B | (x, y) ∈ clusterTraj B w T}
      ≤ (T : ℝ) := by
  rw [← Finset.sum_congr rfl (fun y _ => layerMean_eq_card_mul_layerProb B T x y)]
  exact layerMean_sum_Icc_le B T M

end IdlaCyl
