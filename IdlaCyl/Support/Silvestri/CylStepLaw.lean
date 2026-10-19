import IdlaCyl.Support.Silvestri.NeighbourFibre
import IdlaCyl.Support.Idla
import IdlaCyl.Support.Canonical

/-!
# The one-step law of the driven walk is the cylinder kernel

For a site `p` of the cylinder, the image of two independent uniforms under the driven step
`cylStep B p` (`IdlaCyl/Support/Idla.lean`) has the law `cylMeasure B p` of the canonical
one-step walk (`IdlaCyl/Support/Canonical.lean`).

The two measures are compared on singletons. A singleton `{q}` is the image of a box in the
unit square for each of the four kinds of move (vertical up, vertical down, staying, a
horizontal move to a neighbour). A horizontal move to a neighbour `y` of `p.1` has preimage
a product whose second factor is the neighbour fibre of
`IdlaCyl.Silvestri.horizontalFibre_volume` (`IdlaCyl/Support/Silvestri/NeighbourFibre.lean`),
transported from `s = 2u - 1` to `u ∈ [1/2, 1)`. Every other site has kernel weight `0`, and
no uniform reaches it.
-/

namespace IdlaCyl.Silvestri

open MeasureTheory
open scoped ENNReal

/-- The driven step is jointly measurable in the site and the two uniforms. -/
private theorem measurable_cylStep_joint (B : Base) :
    Measurable (fun z : Site B × (ℝ × ℝ) => cylStep B z.1 z.2) := by
  let values : B.V × ℕ → B.V := fun z =>
    (B.graph.neighborFinset z.1).toList.getD z.2 z.1
  have hvalues : Measurable values := measurable_of_countable values
  have hx : Measurable (fun z : Site B × (ℝ × ℝ) => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hs : Measurable (fun z : Site B × (ℝ × ℝ) => 2 * z.2.2 - 1) := by
    fun_prop
  have hbase : Measurable (fun z : Site B × (ℝ × ℝ) =>
      values (z.1.1, ⌊(B.deg : ℝ) * (2 * z.2.2 - 1)⌋₊)) :=
    hvalues.comp (hx.prodMk (by fun_prop))
  have hcond₁ : MeasurableSet {z : Site B × (ℝ × ℝ) | z.2.1 < 1 / 2} := by
    exact measurableSet_lt (by fun_prop) measurable_const
  have hcond₂ : MeasurableSet {z : Site B × (ℝ × ℝ) | z.2.2 < 1 / 2} := by
    exact measurableSet_lt (by fun_prop) measurable_const
  have hdown : Measurable (fun z : Site B × (ℝ × ℝ) => (z.1.1, z.1.2 - 1)) := by
    fun_prop
  have hup : Measurable (fun z : Site B × (ℝ × ℝ) => (z.1.1, z.1.2 + 1)) := by
    fun_prop
  have hhold : Measurable (fun z : Site B × (ℝ × ℝ) => z.1) := measurable_fst
  have hvertical : Measurable (fun z : Site B × (ℝ × ℝ) =>
      if z.2.2 < 1 / 2 then (z.1.1, z.1.2 - 1) else (z.1.1, z.1.2 + 1)) :=
    Measurable.ite hcond₂ hdown hup
  unfold cylStep baseNeighbor
  dsimp only [values] at hbase
  change Measurable (fun z : Site B × (ℝ × ℝ) =>
    if z.2.1 < 1 / 2 then
      if z.2.2 < 1 / 2 then (z.1.1, z.1.2 - 1) else (z.1.1, z.1.2 + 1)
    else if z.2.2 < 1 / 2 then z.1 else
      ((B.graph.neighborFinset z.1.1).toList.getD
        ⌊(B.deg : ℝ) * (2 * z.2.2 - 1)⌋₊ z.1.1, z.1.2))
  exact Measurable.ite hcond₁ hvertical
    (Measurable.ite hcond₂ hhold (hbase.prodMk (by fun_prop)))

/-- For a fixed site, the driven step is measurable in its two uniforms. -/
theorem measurable_cylStep (B : Base) (p : Site B) : Measurable (cylStep B p) :=
  (measurable_cylStep_joint B).comp (measurable_const.prodMk measurable_id)

/-- The image of the uniform square under the driven step, at a singleton, is the product
of the Lebesgue measures of the two sections of the preimage. -/
theorem map_cylStep_singleton_eq_mul (B : Base) (p q : Site B) (A C : Set ℝ)
    (hrect : cylStep B p ⁻¹' {q} ∩ (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) = A ×ˢ C) :
    ((stepLaw.prod stepLaw).map (cylStep B p)) {q} = volume A * volume C := by
  rw [Measure.map_apply (measurable_cylStep B p) (measurableSet_singleton q)]
  have hprod : stepLaw.prod stepLaw =
      (volume.prod volume).restrict (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    unfold stepLaw
    exact Measure.prod_restrict _ _
  rw [hprod, Measure.restrict_apply ((measurableSet_singleton q).preimage
    (measurable_cylStep B p)), hrect, Measure.prod_prod]

/-- The canonical one-step measure charges each site with its kernel weight. -/
theorem cylMeasure_singleton (B : Base) (p q : Site B) :
    cylMeasure B p {q} = ENNReal.ofReal (cylKernel B p q) := by
  unfold cylMeasure
  rw [Measure.sum_apply _ (measurableSet_singleton q), tsum_eq_single q]
  · rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_singleton q), smul_eq_mul,
      mul_one]
  · intro b hb
    rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_singleton q)]
    simp [hb]

/-- Every site reached by one driven step from `p` from a uniform pair in the unit square has
a nonzero kernel weight from `p`. -/
theorem cylKernel_cylStep_ne_zero (B : Base) (p : Site B) (u : ℝ × ℝ)
    (hu : u ∈ Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) :
    cylKernel B p (cylStep B p u) ≠ 0 := by
  obtain ⟨a, b⟩ := u
  obtain ⟨⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩ := hu
  by_cases h1 : a < 1 / 2 <;> by_cases h2 : b < 1 / 2
  · norm_num [cylStep, cylKernel, h1, h2]
  · norm_num [cylStep, cylKernel, h1, h2]
  · norm_num [cylStep, cylKernel, Base.P, h1, h2]
  · have hs₀ : 0 ≤ 2 * b - 1 := by linarith [not_lt.mp h2]
    have hs₁ : 2 * b - 1 < 1 := by linarith
    have hadj : B.graph.Adj p.1 (baseNeighbor B p.1 (2 * b - 1)) :=
      horizontalChoice_adj B p.1 hs₀ hs₁
    have hd : (0 : ℝ) < (B.deg : ℝ) := by exact_mod_cast B.deg_pos
    have hc : cylStep B p (a, b) = (baseNeighbor B p.1 (2 * b - 1), p.2) := by
      simp only [cylStep, h1, h2, ↓reduceIte]
    rw [hc]
    simp [cylKernel, Base.P, hadj, B.graph.ne_of_adj hadj, hd.ne']

/-- The neighbour fibre in the horizontal uniform `u ∈ [1/2, 1)`. The substitution `s = 2u - 1`
maps `[1/2, 1)` onto `[0, 1)` and halves the measure, so the fibre of a neighbour `y` of `x`
has measure `1 / (2 deg)`. -/
theorem horizontalFibre_volume_half (B : Base) (x y : B.V) (hy : B.graph.Adj x y) :
    volume {u : ℝ | u ∈ Set.Ico (1 / 2 : ℝ) 1 ∧ baseNeighbor B x (2 * u - 1) = y}
      = ENNReal.ofReal (1 / (2 * (B.deg : ℝ))) := by
  have hS := horizontalFibre_volume B x y hy
  set S : Set ℝ := {s : ℝ | s ∈ Set.Ico (0 : ℝ) 1 ∧
    (B.graph.neighborFinset x).toList.getD ⌊(B.deg : ℝ) * s⌋₊ x = y} with hSdef
  have hset : {u : ℝ | u ∈ Set.Ico (1 / 2 : ℝ) 1 ∧ baseNeighbor B x (2 * u - 1) = y}
      = (fun u : ℝ => 2 * u) ⁻¹' ((fun t : ℝ => t - 1) ⁻¹' S) := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hSdef, Set.mem_Ico]
    constructor
    · rintro ⟨⟨h0, h1⟩, h⟩
      exact ⟨⟨by linarith, by linarith⟩, h⟩
    · rintro ⟨⟨h0, h1⟩, h⟩
      exact ⟨⟨by linarith, by linarith⟩, h⟩
  have hW : volume ((fun t : ℝ => t - 1) ⁻¹' S) = volume S := by
    simpa only [sub_eq_add_neg] using measure_preimage_add_right volume (-1 : ℝ) S
  rw [hset, Real.volume_preimage_mul_left (by norm_num : (2 : ℝ) ≠ 0), hW, hS]
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_inv, abs_two]
  ring

/-- The preimage of the vertical-down site `(p.1, p.2 - 1)` in the unit square. -/
theorem cylStep_preimage_down (B : Base) (p : Site B) :
    cylStep B p ⁻¹' {(p.1, p.2 - 1)} ∩ (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) =
      Set.Ico (0 : ℝ) (1 / 2) ×ˢ Set.Ico (0 : ℝ) (1 / 2) := by
  ext ⟨a, b⟩
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod,
    Set.mem_Ico]
  unfold cylStep
  split_ifs <;> grind

/-- The preimage of the vertical-up site `(p.1, p.2 + 1)` in the unit square. -/
theorem cylStep_preimage_up (B : Base) (p : Site B) :
    cylStep B p ⁻¹' {(p.1, p.2 + 1)} ∩ (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) =
      Set.Ico (0 : ℝ) (1 / 2) ×ˢ Set.Ico (1 / 2 : ℝ) 1 := by
  ext ⟨a, b⟩
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod,
    Set.mem_Ico]
  unfold cylStep
  split_ifs <;> grind

/-- The preimage of the staying site `p` in the unit square. -/
theorem cylStep_preimage_stay (B : Base) (p : Site B) :
    cylStep B p ⁻¹' {(p.1, p.2)} ∩ (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) =
      Set.Ico (1 / 2 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) (1 / 2) := by
  ext ⟨a, b⟩
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod,
    Set.mem_Ico]
  unfold cylStep
  split_ifs <;> try grind
  rename_i h1 h2
  dsimp only at h1 h2 ⊢
  constructor
  · rintro ⟨h, -, hb0, hb1⟩
    exfalso
    exact horizontalChoice_ne_self B p.1 (s := 2 * b - 1) (by linarith [not_lt.mp h2])
      (by linarith) (congrArg Prod.fst h)
  · rintro ⟨-, -, hb⟩
    exact absurd hb h2

/-- The preimage of a horizontal site `(q₁, p.2)`, with `q₁` a neighbour of `p.1`, in the
unit square: the vertical uniform is in `[1/2, 1)`, the stay bit is off, and the horizontal
uniform lies in the neighbour fibre of `q₁`. -/
theorem cylStep_preimage_horizontal (B : Base) (p : Site B) (q₁ : B.V)
    (hadj : B.graph.Adj p.1 q₁) :
    cylStep B p ⁻¹' {(q₁, p.2)} ∩ (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) =
      Set.Ico (1 / 2 : ℝ) 1 ×ˢ {u : ℝ | u ∈ Set.Ico (1 / 2 : ℝ) 1 ∧
        baseNeighbor B p.1 (2 * u - 1) = q₁} := by
  have hne : p.1 ≠ q₁ := B.graph.ne_of_adj hadj
  ext ⟨a, b⟩
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod,
    Set.mem_Ico, Set.mem_setOf_eq]
  unfold cylStep
  split_ifs <;> grind

/-- A site of zero kernel weight is not reached by the driven step: every site reached from
the unit square has nonzero weight. -/
theorem map_cylStep_singleton_of_kernel_zero (B : Base) (p q : Site B)
    (hk : cylKernel B p q = 0) :
    ((stepLaw.prod stepLaw).map (cylStep B p)) {q} = ENNReal.ofReal (cylKernel B p q) := by
  have hempty : cylStep B p ⁻¹' {q} ∩ (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) = ∅ ×ˢ ∅ := by
    rw [Set.empty_prod]
    ext ⟨a, b⟩
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro hq hbox
    exact cylKernel_cylStep_ne_zero B p (a, b) hbox (by rw [hq]; exact hk)
  rw [map_cylStep_singleton_eq_mul B p q ∅ ∅ hempty, hk]
  simp

/-- The one-step law of the driven step at a singleton is the cylinder kernel weight. -/
theorem stepLaw_map_cylStep_singleton (B : Base) (p q : Site B) :
    ((stepLaw.prod stepLaw).map (cylStep B p)) {q} = ENNReal.ofReal (cylKernel B p q) := by
  obtain ⟨q₁, q₂⟩ := q
  by_cases hv : p.1 = q₁ ∧ (p.2 - q₂).natAbs = 1
  · have hy : q₂ = p.2 - 1 ∨ q₂ = p.2 + 1 := by
      have h := Int.natAbs_eq (p.2 - q₂)
      rw [hv.2] at h
      omega
    obtain rfl := hv.1
    rcases hy with rfl | rfl
    · rw [map_cylStep_singleton_eq_mul B p _ _ _ (cylStep_preimage_down B p)]
      simp only [Real.volume_Ico]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2 - 0)]
      congr 1
      norm_num [cylKernel]
    · rw [map_cylStep_singleton_eq_mul B p _ _ _ (cylStep_preimage_up B p)]
      simp only [Real.volume_Ico]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2 - 0)]
      congr 1
      norm_num [cylKernel]
  · by_cases hy : q₂ = p.2
    · subst hy
      by_cases hx : p.1 = q₁
      · obtain rfl := hx
        rw [map_cylStep_singleton_eq_mul B p _ _ _ (cylStep_preimage_stay B p)]
        simp only [Real.volume_Ico]
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2)]
        congr 1
        norm_num [cylKernel, Base.P]
      · by_cases hadj : B.graph.Adj p.1 q₁
        · rw [map_cylStep_singleton_eq_mul B p _ _ _ (cylStep_preimage_horizontal B p q₁ hadj),
            horizontalFibre_volume_half B p.1 q₁ hadj]
          simp only [Real.volume_Ico]
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2)]
          congr 1
          norm_num [cylKernel, Base.P, hadj, hx]
        · apply map_cylStep_singleton_of_kernel_zero
          norm_num [cylKernel, Base.P, hadj, hx]
    · apply map_cylStep_singleton_of_kernel_zero
      simp only [cylKernel]
      rw [if_neg hv, if_neg (fun h => hy h.symm)]

/-- The driven one-step law of the walk from `p` is the canonical one-step law `cylMeasure B p`:
the image of two independent uniforms under `cylStep B p` is the cylinder kernel
(`tex:246-255`). -/
theorem cylStep_map_eq (B : Base) (p : Site B) :
    (stepLaw.prod stepLaw).map (cylStep B p) = cylMeasure B p :=
  Measure.ext_iff_singleton.mpr fun q => by
    rw [stepLaw_map_cylStep_singleton, cylMeasure_singleton]

end IdlaCyl.Silvestri
