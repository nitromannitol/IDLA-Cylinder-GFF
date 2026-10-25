module

/-
Canonical discrepancy function and pairing.

`tex:348-353` (Definition of the discrepancy), `tex:356-361` (`def:zero`) and
`tex:363-366` (the pairing).

  `D_t(x,y) := 1_{A(t)}(x,y) - 1_{R_{t/N}}(x,y)`,
  `⟪D_t, f⟫ := ∑_{(x,y) ∈ G_N} D_t(x,y) f(x,y)`.

The sum is written as a `finsum`, which is the paper's "absolutely convergent
finite sum" exactly when `D_t` has finite support.  That support fact is the
rule-5 guard that keeps the definition from silently collapsing to `0`:
`discrepancyTraj_support_finite` below proves it for *every* trajectory, not
merely almost every one.

The key structural observation, used by every later identity, is that below
level `0` the two indicators cancel: `A(t) ⊇ R_0` and `R_{t/N} ⊇ R_0` because
`t/N ≥ 0`.  Hence `D_t` vanishes on `{y ≤ 0}` and the pairing is a difference of
two *finite* sums, one over `A_+(t) = A(t) ∩ {y ≥ 1}` and one over the finite
rectangle `V_N × {1, …, ⌊t/N⌋}`:

  `⟪D_t, f⟫ = ∑_{A_+(t)} f - ∑_{V_N × Icc 1 ⌊t/N⌋} f`.

For a zero-horizontal-average `f` the second sum vanishes layer by layer
(`def:zero`), recovering `⟪D_t, f⟫ = ∑_{A_+(t)} f`, the form used at
`tex:845-847` and `tex:897-900`.
-/
public import IdlaCyl.Support.CanonicalGrowth
public import IdlaCyl.Support.CanonicalShape
public import IdlaCyl.Support.Idla

@[expose] public section

namespace IdlaCyl

open MeasureTheory
open scoped BigOperators

variable (B : Base)

/-- `A_+(t) = A(t) ∩ {y ≥ 1}`, the part of the cluster strictly above level
zero (`tex:265`, `tex:340`). -/
noncomputable def clusterPlusTraj (ω : TrajSeq B) (t : ℕ) : Set (Site B) :=
  clusterTraj B ω t ∩ {p : Site B | 1 ≤ p.2}

/-- `A_+(t)` as a `Finset`: the distinct settling sites up to time `t` that sit
above level `0`.  This is the carrier for the finite sum below; it is equal to
`clusterPlusTraj` (`coe_clusterPlusFinset`), because the cluster is `R_0`
together with the settling sites (`clusterTraj_eq_union`) and `R_0` lies below
level `0`. -/
noncomputable def clusterPlusFinset (ω : TrajSeq B) (t : ℕ) : Finset (Site B) :=
  ((Finset.range t).image (settleSite B ω)).filter (fun p => 1 ≤ p.2)

/-- The finite rectangle `V_N × {1, …, ⌊t/N⌋}`: the part of `R_{t/N}` above
level `0`, and the second half of the pairing identity. -/
noncomputable def rectangleFinset (B : Base) (t : ℕ) : Finset (Site B) :=
  Finset.univ.product (Finset.Icc (1 : ℤ) ⌊(t : ℝ) / (B.card : ℝ)⌋)

/-- The discrepancy function `D_t = 1_{A(t)} - 1_{R_{t/N}}` (`tex:348-351`). -/
noncomputable def discrepancyTraj (ω : TrajSeq B) (t : ℕ) (p : Site B) : ℝ :=
  (clusterTraj B ω t).indicator (fun _ => (1 : ℝ)) p
    - (R B ((t : ℝ) / B.card)).indicator (fun _ => (1 : ℝ)) p

/-- The pairing `⟪D_t, f⟫ = ∑_{(x,y)} D_t(x,y) f(x,y)` (`tex:363-366`).  Written
as a `finsum`; `discrepancyTraj_support_finite` makes it the paper's finite
sum.  Downstream code must define the martingale `M(t)` by a `Finset.range`
sum, never by this `finsum`; `pairingTraj_eq_sum` converts between them. -/
noncomputable def pairingTraj (ω : TrajSeq B) (t : ℕ) (f : Site B → ℝ) : ℝ :=
  ∑ᶠ p : Site B, discrepancyTraj B ω t p * f p

/-! ### The support of the discrepancy -/

/-- The `Finset` form of `A_+(t)` is exactly the set form (`tex:263-265`). -/
theorem coe_clusterPlusFinset (ω : TrajSeq B) (t : ℕ) :
    (clusterPlusFinset B ω t : Set (Site B)) = clusterPlusTraj B ω t := by
  unfold clusterPlusFinset clusterPlusTraj
  rw [clusterTraj_eq_union]
  ext p
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_union,
    Finset.mem_coe, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hp1⟩
    exact ⟨Or.inr ⟨i, hi, rfl⟩, hp1⟩
  · rintro ⟨h | ⟨i, hi, rfl⟩, hp1⟩
    · exfalso
      have h0 : (p.2 : ℝ) ≤ 0 := h
      have h1 : (1 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast hp1
      linarith
    · exact ⟨⟨i, hi, rfl⟩, hp1⟩

/-- Below level `0` the two indicators in `D_t` cancel: both `A(t)` and
`R_{t/N}` contain `R_0` (`tex:261-265`). -/
theorem discrepancyTraj_eq_zero_of_ver_nonpos (ω : TrajSeq B) (t : ℕ) {p : Site B}
    (hp : p.2 ≤ 0) : discrepancyTraj B ω t p = 0 := by
  have hcard : (0 : ℝ) < (B.card : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num) B.nontrivial
  have hR0 : p ∈ R B 0 := by
    simp only [mem_R]
    exact_mod_cast hp
  have hmem : p ∈ clusterTraj B ω t :=
    clusterFrom_mono B (R B 0) ω (Nat.zero_le t) hR0
  have ht : (0 : ℝ) ≤ (t : ℝ) / (B.card : ℝ) :=
    div_nonneg (Nat.cast_nonneg t) (le_of_lt hcard)
  have hRt : p ∈ R B ((t : ℝ) / B.card) := by
    rw [mem_R] at hR0 ⊢
    exact le_trans hR0 ht
  rw [discrepancyTraj, Set.indicator_of_mem hmem, Set.indicator_of_mem hRt]
  norm_num

/-- The support of `D_t` is contained in `A_+(t)` together with the finite
rectangle of `R_{t/N}` above level `0`. -/
theorem support_discrepancyTraj_subset (ω : TrajSeq B) (t : ℕ) :
    Function.support (discrepancyTraj B ω t) ⊆
      (clusterPlusFinset B ω t : Set (Site B)) ∪
        (Set.univ ×ˢ Set.Icc (1 : ℤ) ⌊(t : ℝ) / (B.card : ℝ)⌋) := by
  have hcard : (0 : ℝ) < (B.card : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num) B.nontrivial
  intro p hp
  by_cases hcl : p ∈ clusterTraj B ω t
  · by_cases hR : p ∈ R B ((t : ℝ) / B.card)
    · exfalso
      apply hp
      rw [discrepancyTraj, Set.indicator_of_mem hcl, Set.indicator_of_mem hR]
      norm_num
    · left
      have hp2 : 1 ≤ p.2 := by
        by_contra h
        have hle : p.2 ≤ 0 := by omega
        have h0 : p ∈ R B 0 := by
          simp only [mem_R]
          exact_mod_cast hle
        exact hR (R_mono (div_nonneg (Nat.cast_nonneg t) (le_of_lt hcard)) h0)
      change p ∈ clusterPlusFinset B ω t
      rw [clusterPlusFinset, Finset.mem_filter]
      refine ⟨?_, hp2⟩
      rw [clusterTraj_eq_union] at hcl
      rcases hcl with hcl | hcl
      · exfalso
        have h0 : (p.2 : ℝ) ≤ 0 := hcl
        have h1 : (1 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast hp2
        linarith
      · exact hcl
  · by_cases hR : p ∈ R B ((t : ℝ) / B.card)
    · right
      have hR0 : p ∉ R B 0 := fun h =>
        hcl (clusterFrom_mono B (R B 0) ω (Nat.zero_le t) h)
      have hp1 : 1 ≤ p.2 := by
        have h0 : ¬ p.2 ≤ 0 := fun h =>
          hR0 (by simp only [mem_R]; exact_mod_cast h)
        omega
      have hpM : p.2 ≤ ⌊(t : ℝ) / (B.card : ℝ)⌋ := by
        rw [mem_R] at hR
        exact Int.le_floor.mpr hR
      exact ⟨Set.mem_univ _, hp1, hpM⟩
    · exfalso
      apply hp
      rw [discrepancyTraj, Set.indicator_of_notMem hcl, Set.indicator_of_notMem hR]
      norm_num

/-- The discrepancy has finite support, for *every* trajectory (`tex:352-353`):
sites below level `0` cancel, sites above `t/N` are outside both `A(t)` and
`R_{t/N}`, and the remaining sites lie in `A_+(t)`, which is finite. -/
theorem discrepancyTraj_support_finite (ω : TrajSeq B) (t : ℕ) :
    (Function.support (discrepancyTraj B ω t)).Finite :=
  ((clusterPlusFinset B ω t).finite_toSet.union
    (Set.finite_univ.prod (Set.finite_Icc _ _))).subset
      (support_discrepancyTraj_subset B ω t)

/-! ### The finite decomposition of the pairing -/

/-- The set form of the rectangle `V_N × {1, …, ⌊t/N⌋}`. -/
theorem coe_rectangleFinset (t : ℕ) :
    (rectangleFinset B t : Set (Site B))
      = Set.univ ×ˢ Set.Icc (1 : ℤ) ⌊(t : ℝ) / (B.card : ℝ)⌋ := by
  ext p
  simp [rectangleFinset]

/-- Membership in `A_+(t)` as a `Finset`. -/
theorem mem_clusterPlusFinset_iff (ω : TrajSeq B) (t : ℕ) (p : Site B) :
    p ∈ clusterPlusFinset B ω t ↔
      p ∈ (Finset.range t).image (settleSite B ω) ∧ 1 ≤ p.2 := by
  simp [clusterPlusFinset]

/-- A site of `A_+(t)` lies in the cluster. -/
theorem mem_clusterPlusFinset_cluster (ω : TrajSeq B) (t : ℕ) {p : Site B}
    (hp : p ∈ clusterPlusFinset B ω t) : p ∈ clusterTraj B ω t := by
  rw [mem_clusterPlusFinset_iff] at hp
  rw [clusterTraj_eq_union]
  exact Or.inr hp.1

/-- Membership in the rectangle. -/
theorem mem_rectangleFinset_iff (t : ℕ) (p : Site B) :
    p ∈ rectangleFinset B t ↔ 1 ≤ p.2 ∧ p.2 ≤ ⌊(t : ℝ) / (B.card : ℝ)⌋ := by
  simp [rectangleFinset, Finset.mem_product, Finset.mem_Icc]

/-- Above level `0`, membership in `A_+(t)` is membership in the cluster. -/
theorem mem_clusterPlusFinset_iff_cluster (ω : TrajSeq B) (t : ℕ) {p : Site B}
    (hy : 1 ≤ p.2) : p ∈ clusterPlusFinset B ω t ↔ p ∈ clusterTraj B ω t := by
  constructor
  · exact fun h => mem_clusterPlusFinset_cluster B ω t h
  · intro hcl
    rw [mem_clusterPlusFinset_iff]
    refine ⟨?_, hy⟩
    rw [clusterTraj_eq_union] at hcl
    rcases hcl with hcl | hcl
    · exfalso
      have h0 : (p.2 : ℝ) ≤ 0 := hcl
      have h1 : (1 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast hy
      linarith
    · exact hcl

/-- Above level `0`, membership in the rectangle is membership in `R_{t/N}`. -/
theorem mem_rectangleFinset_iff_R (t : ℕ) {p : Site B} (hy : 1 ≤ p.2) :
    p ∈ rectangleFinset B t ↔ p ∈ R B ((t : ℝ) / B.card) := by
  rw [mem_rectangleFinset_iff, mem_R]
  constructor
  · intro h
    exact le_trans (by exact_mod_cast h.2) (Int.floor_le _)
  · intro h
    exact ⟨hy, Int.le_floor.mpr h⟩

/-- The second sum vanishes for a zero-horizontal-average function (`def:zero`,
`tex:356-361`): the rectangle is a union of complete layers `V_N × {y}`. -/
theorem sum_rectangleFinset_eq_zero (t : ℕ) (f : Site B → ℝ)
    (hf : ZeroHorizontalAverage B f) :
    ∑ p ∈ rectangleFinset B t, f p = 0 := by
  classical
  rw [rectangleFinset]
  have hprod : (∑ p ∈ (Finset.univ : Finset B.V).product
        (Finset.Icc (1 : ℤ) ⌊(t : ℝ) / (B.card : ℝ)⌋), f p)
      = ∑ x : B.V, ∑ y ∈ Finset.Icc (1 : ℤ) ⌊(t : ℝ) / (B.card : ℝ)⌋, f (x, y) :=
    Finset.sum_product _ _ _
  rw [hprod, Finset.sum_comm]
  exact Finset.sum_eq_zero fun y _ => hf y

/-- **The finite decomposition of the pairing.**  For every trajectory,
`⟪D_t, f⟫` is the difference of the finite sum over `A_+(t)` and the finite sum
over the rectangle `V_N × {1, …, ⌊t/N⌋}`. -/
theorem pairingTraj_eq_sum (ω : TrajSeq B) (t : ℕ) (f : Site B → ℝ) :
    pairingTraj B ω t f
      = (∑ p ∈ clusterPlusFinset B ω t, f p) - (∑ p ∈ rectangleFinset B t, f p) := by
  classical
  have hsub : Function.support (fun p => discrepancyTraj B ω t p * f p) ⊆
      ((clusterPlusFinset B ω t ∪ rectangleFinset B t : Finset (Site B)) :
        Set (Site B)) := by
    intro p hp
    have hD : p ∈ Function.support (discrepancyTraj B ω t) := by
      by_contra h
      have h0 : discrepancyTraj B ω t p = 0 := Function.notMem_support.mp h
      exact hp (by show discrepancyTraj B ω t p * f p = 0; rw [h0, zero_mul])
    have hmem := support_discrepancyTraj_subset B ω t hD
    rwa [Finset.coe_union, coe_rectangleFinset]
  rw [pairingTraj, finsum_eq_sum_of_support_subset _ hsub]
  have hpoint : ∀ p ∈ (clusterPlusFinset B ω t ∪ rectangleFinset B t : Finset (Site B)),
      discrepancyTraj B ω t p * f p
        = (if p ∈ clusterPlusFinset B ω t then f p else 0)
          - (if p ∈ rectangleFinset B t then f p else 0) := by
    intro p hp
    have hp_cases : p ∈ clusterPlusFinset B ω t ∨ p ∈ rectangleFinset B t := by
      simpa only [Finset.mem_union] using hp
    have hver : 1 ≤ p.2 := by
      rcases hp_cases with h | h
      · exact (mem_clusterPlusFinset_iff B ω t p).mp h |>.2
      · exact (mem_rectangleFinset_iff B t p).mp h |>.1
    have h1 := mem_clusterPlusFinset_iff_cluster B ω t hver
    have h2 := mem_rectangleFinset_iff_R B t hver
    by_cases hcp : p ∈ clusterPlusFinset B ω t <;>
      by_cases hrect : p ∈ rectangleFinset B t
    · have hcl : p ∈ clusterTraj B ω t := h1.mp hcp
      have hR : p ∈ R B ((t : ℝ) / B.card) := h2.mp hrect
      rw [discrepancyTraj, Set.indicator_of_mem hcl, Set.indicator_of_mem hR,
        if_pos hcp, if_pos hrect]
      ring
    · have hcl : p ∈ clusterTraj B ω t := h1.mp hcp
      have hR : p ∉ R B ((t : ℝ) / B.card) := fun h => hrect (h2.mpr h)
      rw [discrepancyTraj, Set.indicator_of_mem hcl, Set.indicator_of_notMem hR,
        if_pos hcp, if_neg hrect]
      ring
    · have hcl : p ∉ clusterTraj B ω t := fun h => hcp (h1.mpr h)
      have hR : p ∈ R B ((t : ℝ) / B.card) := h2.mp hrect
      rw [discrepancyTraj, Set.indicator_of_notMem hcl, Set.indicator_of_mem hR,
        if_neg hcp, if_pos hrect]
      ring
    · exact absurd hp_cases (by tauto)
  rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_ite_mem]
    congr 1
    exact Finset.inter_eq_right.mpr Finset.subset_union_left
  · rw [Finset.sum_ite_mem]
    congr 1
    exact Finset.inter_eq_right.mpr Finset.subset_union_right

/-- **`tex:845-847`.**  For a zero-horizontal-average test function the pairing
is the sum over `A_+(t)` alone. -/
theorem pairingTraj_eq_sum_clusterPlus (ω : TrajSeq B) (t : ℕ) (f : Site B → ℝ)
    (hf : ZeroHorizontalAverage B f) :
    pairingTraj B ω t f = ∑ p ∈ clusterPlusFinset B ω t, f p := by
  rw [pairingTraj_eq_sum B ω t f, sum_rectangleFinset_eq_zero B t f hf, sub_zero]

/-! ### Measurability of the pairing -/

/-- The sum over the image of the settling-site map is measurable.  The image
may collapse repeated sites, but `Finset.sum_image'` rewrites the image sum as a
fixed finite sum that weights each distinct site exactly once; the
first-occurrence indicator is a finite Boolean combination of measurable
events. -/
theorem measurable_sum_image (t : ℕ) (f : Site B → ℝ) :
    Measurable (fun ω : TrajSeq B =>
      ∑ p ∈ (Finset.range t).image (settleSite B ω), f p) := by
  have heq : ∀ ω : TrajSeq B,
      (∑ p ∈ (Finset.range t).image (settleSite B ω), f p)
        = ∑ i ∈ Finset.range t,
            if (∀ j ∈ Finset.range t, j < i → settleSite B ω j ≠ settleSite B ω i)
              then f (settleSite B ω i) else 0 := by
    intro ω
    refine Finset.sum_image' (f := f) (g := settleSite B ω) (s := Finset.range t)
      (h := fun i => if (∀ j ∈ Finset.range t, j < i → settleSite B ω j ≠ settleSite B ω i)
        then f (settleSite B ω i) else 0) ?_
    intro i hi
    set Fib := (Finset.range t).filter (fun j => settleSite B ω j = settleSite B ω i) with hFib
    have hFib_ne : Fib.Nonempty :=
      ⟨i, by rw [hFib, Finset.mem_filter]; exact ⟨hi, rfl⟩⟩
    set i₀ := Fib.min' hFib_ne with hi₀
    have hi₀_mem : i₀ ∈ Fib := Finset.min'_mem _ _
    have hi₀_range : i₀ ∈ Finset.range t := by
      have h := Finset.mem_filter.mp (hFib ▸ hi₀_mem)
      exact h.1
    have hi₀_eq : settleSite B ω i₀ = settleSite B ω i := by
      have h := Finset.mem_filter.mp (hFib ▸ hi₀_mem)
      exact h.2
    have hcond₀ : ∀ j ∈ Finset.range t, j < i₀ → settleSite B ω j ≠ settleSite B ω i₀ := by
      intro j hj hlt hij
      have hjFib : j ∈ Fib := by
        rw [hFib, Finset.mem_filter]
        exact ⟨hj, hij.trans hi₀_eq⟩
      have hle : i₀ ≤ j := Finset.min'_le _ j hjFib
      omega
    have hzero : ∀ j ∈ Fib, j ≠ i₀ →
        (if (∀ k ∈ Finset.range t, k < j → settleSite B ω k ≠ settleSite B ω j)
          then f (settleSite B ω j) else 0) = 0 := by
      intro j hjFib hjne
      have hji : settleSite B ω j = settleSite B ω i := by
        have h := Finset.mem_filter.mp (hFib ▸ hjFib)
        exact h.2
      have hlt : i₀ < j := by
        have hle : i₀ ≤ j := Finset.min'_le _ j hjFib
        omega
      have hfalse : ¬ (∀ k ∈ Finset.range t, k < j → settleSite B ω k ≠ settleSite B ω j) := by
        intro hcon
        exact hcon i₀ hi₀_range hlt (by rw [hji, hi₀_eq])
      rw [if_neg hfalse]
    rw [Finset.sum_eq_single_of_mem i₀ hi₀_mem hzero]
    rw [if_pos hcond₀, hi₀_eq]
  rw [show (fun ω : TrajSeq B => ∑ p ∈ (Finset.range t).image (settleSite B ω), f p)
      = fun ω => ∑ i ∈ Finset.range t,
          if (∀ j ∈ Finset.range t, j < i → settleSite B ω j ≠ settleSite B ω i)
            then f (settleSite B ω i) else 0 from funext heq]
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.ite ?_ ?_ measurable_const
  · have hset : {ω : TrajSeq B |
          ∀ j ∈ Finset.range t, j < i → settleSite B ω j ≠ settleSite B ω i}
        = ⋂ j ∈ Finset.range t,
            {ω : TrajSeq B | j < i → settleSite B ω j ≠ settleSite B ω i} := by
      ext ω; simp
    rw [hset]
    refine MeasurableSet.biInter (Finset.range t).countable_toSet fun j _ => ?_
    by_cases hj : j < i
    · simp only [hj, true_implies]
      have hdiag : MeasurableSet {p : Site B × Site B | p.1 = p.2} :=
        (Set.to_countable _).measurableSet
      have hpair : Measurable
          (fun ω : TrajSeq B => (settleSite B ω j, settleSite B ω i)) :=
        (measurable_settleSite B j).prod (measurable_settleSite B i)
      exact (hpair hdiag).compl
    · simp only [hj, false_implies]
      exact MeasurableSet.univ
  · exact (measurable_of_countable f).comp (measurable_settleSite B i)

/-- `pairingTraj` is measurable in the driving trajectories (`tex:363-366`), so
its law and expectation are the paper's.  Immediate from
`pairingTraj_eq_sum` and `measurable_sum_image`. -/
theorem measurable_pairingTraj (t : ℕ) (f : Site B → ℝ) :
    Measurable (fun ω : TrajSeq B => pairingTraj B ω t f) := by
  have heq : (fun ω : TrajSeq B => pairingTraj B ω t f)
      = fun ω => (∑ p ∈ clusterPlusFinset B ω t, f p)
          - (∑ p ∈ rectangleFinset B t, f p) :=
    funext fun ω => pairingTraj_eq_sum B ω t f
  rw [heq]
  refine Measurable.sub ?_ measurable_const
  have hfilter : (fun ω : TrajSeq B => ∑ p ∈ clusterPlusFinset B ω t, f p)
      = fun ω => ∑ p ∈ (Finset.range t).image (settleSite B ω),
          if 1 ≤ p.2 then f p else 0 := by
    funext ω
    rw [clusterPlusFinset, Finset.sum_filter]
  rw [hfilter]
  exact measurable_sum_image B t fun p => if 1 ≤ p.2 then f p else 0

/-! ### The symmetric-difference bound of `clm:Q-W` -/

/-- **The deterministic bound of `clm:Q-W`** (`tex:1011-1015`): for a
non-negative `g` and finite sets `A, B`,
`|∑_A g − ∑_B g| ≤ ∑_{A △ B} g`, where `A △ B = (A \ B) ∪ (B \ A)`. -/
theorem abs_sum_sub_sum_le_sum_symmDiff (s t : Finset (Site B)) (g : Site B → ℝ)
    (hg : 0 ≤ g) :
    |∑ p ∈ s, g p - ∑ p ∈ t, g p| ≤ ∑ p ∈ (s \ t) ∪ (t \ s), g p := by
  classical
  have hA := Finset.sum_sdiff (s₁ := s ∩ t) (s₂ := s) (f := g) Finset.inter_subset_left
  have hB := Finset.sum_sdiff (s₁ := s ∩ t) (s₂ := t) (f := g) Finset.inter_subset_right
  have hAs : s \ (s ∩ t) = s \ t := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hBs : t \ (s ∩ t) = t \ s := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [hAs] at hA
  rw [hBs] at hB
  have hdisj : Disjoint (s \ t) (t \ s) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_sdiff.mp hq).1
  have hunion := Finset.sum_union hdisj (f := g)
  rw [← hA, ← hB, hunion, add_sub_add_right_eq_sub]
  have hSA : 0 ≤ ∑ p ∈ s \ t, g p := Finset.sum_nonneg fun p _ => hg p
  have hSB : 0 ≤ ∑ p ∈ t \ s, g p := Finset.sum_nonneg fun p _ => hg p
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

end IdlaCyl
