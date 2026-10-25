module

/-
The obligations the model layer owes.

A junk-value risk that is named in prose and nowhere else is not tracked:
nothing fails when it goes unmet.  These obligations are therefore stated and
proved as declarations, so that `#print axioms` sees them.

Each is stated once and cited from the header of the file whose definition
depends on it.
-/
public import IdlaCyl.Support.Idla
public import IdlaCyl.Support.Obligation.ExitAeFinite
public import IdlaCyl.Support.Obligation.ClusterPlusCard
public import IdlaCyl.Support.Spectral
public import IdlaCyl.Support.Obligation.DiscrepancySupport
public import IdlaCyl.Support.Obligation.BasePowPos
public import IdlaCyl.Support.Obligation.MixingContraction
public import IdlaCyl.Support.Obligation.SpectralQuadratic
public import IdlaCyl.Support.Obligation.SpectralConstruction

@[expose] public section

namespace IdlaCyl

open MeasureTheory Filter
open scoped BigOperators ENNReal

variable {B : Base}

private theorem measurable_cylStep_stepLaw (B : Base) :
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

private theorem baseNeighbor_adj_of_range (B : Base) (x : B.V) (s : ℝ)
    (hs₀ : 0 ≤ s) (hs₁ : s < 1) :
    B.graph.Adj x (baseNeighbor B x s) := by
  let L := (B.graph.neighborFinset x).toList
  have hlen : L.length = B.deg := by
    dsimp [L]
    rw [Finset.length_toList, SimpleGraph.card_neighborFinset_eq_degree, B.degree_eq x]
  have hd : (0 : ℝ) < (B.deg : ℝ) := by exact_mod_cast B.deg_pos
  have hprod₀ : 0 ≤ (B.deg : ℝ) * s := mul_nonneg (by positivity) hs₀
  have hprod₁ : (B.deg : ℝ) * s < (B.deg : ℝ) := by nlinarith
  have hn : ⌊(B.deg : ℝ) * s⌋₊ < B.deg := by
    rw [Nat.floor_lt hprod₀]
    exact_mod_cast hprod₁
  have hnL : ⌊(B.deg : ℝ) * s⌋₊ < L.length := by rw [hlen]; exact hn
  have hmem : L.getD ⌊(B.deg : ℝ) * s⌋₊ x ∈ B.graph.neighborFinset x := by
    rw [List.getD_eq_getElem L x hnL]
    exact Finset.mem_toList.mp (List.getElem_mem _)
  have hmem' : L.getD ⌊(B.deg : ℝ) * s⌋₊ x ∈ B.graph.neighborFinset x := hmem
  simpa only [baseNeighbor, L] using
    (SimpleGraph.mem_neighborFinset (G := B.graph) x (baseNeighbor B x s)).mp hmem'

private theorem baseNeighbor_ne_self_of_range (B : Base) (x : B.V) (s : ℝ)
    (hs₀ : 0 ≤ s) (hs₁ : s < 1) : baseNeighbor B x s ≠ x := by
  intro h
  have hadj := baseNeighbor_adj_of_range B x s hs₀ hs₁
  exact B.graph.irrefl (h ▸ hadj)

private theorem baseNeighbor_eq_iff_interval (B : Base) (x y : B.V) (i : ℕ)
    (hi : i < (B.graph.neighborFinset x).toList.length)
    (hidx : (B.graph.neighborFinset x).toList.getD i x = y)
    {u : ℝ} (hu : u ∈ Set.Ico (1 / 2 : ℝ) 1) :
    baseNeighbor B x (2 * u - 1) = y ↔
      u ∈ Set.Ico (1 / 2 + (i : ℝ) / (2 * (B.deg : ℝ)))
        (1 / 2 + ((i : ℝ) + 1) / (2 * (B.deg : ℝ))) := by
  let L := (B.graph.neighborFinset x).toList
  have hlen : L.length = B.deg := by
    dsimp [L]
    rw [Finset.length_toList, SimpleGraph.card_neighborFinset_eq_degree, B.degree_eq x]
  have hd : (0 : ℝ) < (B.deg : ℝ) := by exact_mod_cast B.deg_pos
  have hD₀ : 0 ≤ (B.deg : ℝ) := le_of_lt hd
  have hu₀ : 0 ≤ 2 * u - 1 := by
    rcases Set.mem_Ico.mp hu with ⟨huL, _⟩
    nlinarith
  have hu₁ : 2 * u - 1 < 1 := by
    rcases Set.mem_Ico.mp hu with ⟨_, huR⟩
    nlinarith
  have hprod₀ : 0 ≤ (B.deg : ℝ) * (2 * u - 1) := mul_nonneg hD₀ hu₀
  have hprod₁ : (B.deg : ℝ) * (2 * u - 1) < (B.deg : ℝ) := by nlinarith
  have hn : ⌊(B.deg : ℝ) * (2 * u - 1)⌋₊ < B.deg := by
    rw [Nat.floor_lt hprod₀]
    exact_mod_cast hprod₁
  have hnL : ⌊(B.deg : ℝ) * (2 * u - 1)⌋₊ < L.length := by rw [hlen]; exact hn
  have hnodup : L.Nodup := by dsimp [L]; exact Finset.nodup_toList _
  have hinj : Function.Injective L.get := List.nodup_iff_injective_get.mp hnodup
  have hidxValid : i < L.length := by simpa only [L] using hi
  have hlow : 2 * (1 / 2 + (i : ℝ) / (2 * (B.deg : ℝ))) - 1 =
      (i : ℝ) / (B.deg : ℝ) := by field_simp [hd.ne']; ring
  have hupp : 2 * (1 / 2 + ((i : ℝ) + 1) / (2 * (B.deg : ℝ))) - 1 =
      ((i : ℝ) + 1) / (B.deg : ℝ) := by field_simp [hd.ne']; ring
  constructor
  · intro hbase
    have hq : L.getD ⌊(B.deg : ℝ) * (2 * u - 1)⌋₊ x = y := by
      simpa only [baseNeighbor, L] using hbase
    have hni : ⌊(B.deg : ℝ) * (2 * u - 1)⌋₊ = i := by
      have hget : L.get ⟨⌊(B.deg : ℝ) * (2 * u - 1)⌋₊, hnL⟩ = L.get ⟨i, hidxValid⟩ := by
        change L[⌊(B.deg : ℝ) * (2 * u - 1)⌋₊] = L[i]
        rw [← List.getD_eq_getElem L x hnL, ← List.getD_eq_getElem L x hidxValid]
        exact hq.trans hidx.symm
      exact congrArg Fin.val (hinj hget)
    have hfloor : ⌊(B.deg : ℝ) * (2 * u - 1)⌋₊ = i := hni
    have hineq := (Nat.floor_eq_iff hprod₀).mp hfloor
    have hlo : (i : ℝ) / (B.deg : ℝ) ≤ 2 * u - 1 := by
      apply (div_le_iff₀ hd).2
      nlinarith [hineq.1]
    have hhi : 2 * u - 1 < ((i : ℝ) + 1) / (B.deg : ℝ) := by
      apply (lt_div_iff₀ hd).2
      nlinarith [hineq.2]
    exact ⟨by linarith [hlow], by linarith [hupp]⟩
  · intro hui
    rcases Set.mem_Ico.mp hui with ⟨huiL, huiR⟩
    have hlow' : (i : ℝ) / (B.deg : ℝ) ≤ 2 * u - 1 := by
      linarith [hlow, huiL]
    have hupp' : 2 * u - 1 < ((i : ℝ) + 1) / (B.deg : ℝ) := by
      linarith [hupp, huiR]
    have hineq₁ : (i : ℝ) ≤ (B.deg : ℝ) * (2 * u - 1) := by
      have h := (div_le_iff₀ hd).mp hlow'
      nlinarith [h]
    have hineq₂ : (B.deg : ℝ) * (2 * u - 1) < (i : ℝ) + 1 := by
      have h := (lt_div_iff₀ hd).mp hupp'
      nlinarith [h]
    have hfloor : ⌊(B.deg : ℝ) * (2 * u - 1)⌋₊ = i :=
      (Nat.floor_eq_iff hprod₀).mpr ⟨hineq₁, hineq₂⟩
    change L.getD (⌊(B.deg : ℝ) * (2 * u - 1)⌋₊) x = y
    rw [hfloor, hidx]

private theorem cylStep_level_down_iff (B : Base) (p : Site B) (u : ℝ × ℝ) :
    (cylStep B p u).2 = p.2 - 1 ↔ u.1 < 1 / 2 ∧ u.2 < 1 / 2 := by
  by_cases h1 : u.1 < 1 / 2 <;> by_cases h2 : u.2 < 1 / 2
  · have h1' : u.1 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h1
    have h2' : u.2 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h2
    simp [cylStep, h1', h2']
  · have h1' : u.1 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h1
    have h2' : ¬ u.2 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h2
    simp [cylStep, h1', h2']; omega
  · have h1' : ¬ u.1 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h1
    have h2' : u.2 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h2
    simp [cylStep, h1', h2']; omega
  · have h1' : ¬ u.1 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h1
    have h2' : ¬ u.2 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h2
    simp [cylStep, h1', h2']; omega

private theorem cylStep_level_up_iff (B : Base) (p : Site B) (u : ℝ × ℝ) :
    (cylStep B p u).2 = p.2 + 1 ↔ u.1 < 1 / 2 ∧ ¬ u.2 < 1 / 2 := by
  by_cases h1 : u.1 < 1 / 2 <;> by_cases h2 : u.2 < 1 / 2
  · have h1' : u.1 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h1
    have h2' : u.2 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h2
    simp [cylStep, h1', h2']; omega
  · have h1' : u.1 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h1
    have h2' : ¬ u.2 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h2
    simp [cylStep, h1', h2']
  · have h1' : ¬ u.1 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h1
    have h2' : u.2 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h2
    simp [cylStep, h1', h2']
  · have h1' : ¬ u.1 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h1
    have h2' : ¬ u.2 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h2
    simp [cylStep, h1', h2']

private theorem cylStep_level_same_iff (B : Base) (p : Site B) (u : ℝ × ℝ) :
    (cylStep B p u).2 = p.2 ↔ ¬ u.1 < 1 / 2 := by
  by_cases h1 : u.1 < 1 / 2 <;> by_cases h2 : u.2 < 1 / 2
  · have h1' : u.1 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h1
    have h2' : u.2 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h2
    simp [cylStep, h1', h2']
  · have h1' : u.1 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h1
    have h2' : ¬ u.2 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h2
    simp [cylStep, h1', h2']
  · have h1' : ¬ u.1 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h1
    have h2' : u.2 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h2
    simp [cylStep, h1', h2']
  · have h1' : ¬ u.1 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h1
    have h2' : ¬ u.2 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h2
    simp [cylStep, h1', h2']

private theorem cylStep_level_cases (B : Base) (p : Site B) (u : ℝ × ℝ) :
    (cylStep B p u).2 = p.2 - 1 ∨ (cylStep B p u).2 = p.2 ∨
      (cylStep B p u).2 = p.2 + 1 := by
  by_cases h1 : u.1 < 1 / 2 <;> by_cases h2 : u.2 < 1 / 2
  · have h1' : u.1 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h1
    have h2' : u.2 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h2
    simp [cylStep, h1', h2']
  · have h1' : u.1 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h1
    have h2' : ¬ u.2 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h2
    simp [cylStep, h1', h2']
  · have h1' : ¬ u.1 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h1
    have h2' : u.2 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h2
    simp [cylStep, h1', h2']
  · have h1' : ¬ u.1 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h1
    have h2' : ¬ u.2 < (2 : ℝ)⁻¹ := by simpa only [one_div] using h2
    simp [cylStep, h1', h2']

private theorem stepLaw_map_cylStep_rect (B : Base) (p q : Site B)
    (A C : Set ℝ) (hmeas : Measurable (cylStep B p))
    (hrect : (cylStep B p) ⁻¹' {q} ∩
      (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) = A ×ˢ C) :
    ((stepLaw.prod stepLaw).map (cylStep B p)) {q} = volume A * volume C := by
  rw [Measure.map_apply hmeas (measurableSet_singleton q)]
  have hprod : stepLaw.prod stepLaw =
      (volume.prod volume).restrict (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    unfold stepLaw
    exact Measure.prod_restrict _ _
  rw [hprod, Measure.restrict_apply ((measurableSet_singleton q).preimage hmeas),
    hrect, Measure.prod_prod]

/-! ### The walk -/

/-- The driven step realises the paper's kernel (`tex:246-255`, `def:SRW`):
for a fixed source `p`, the law of `cylStep B p ·` under a pair of independent
uniforms is `cylKernel B p ·`.

Without this, `cylStep` is an unrelated recursion and the model has no
connection to the paper's `𝒫_N`. -/
theorem step_law_eq_cylKernel (B : Base) (p q : Site B) :
    ((stepLaw.prod stepLaw).map (cylStep B p)) {q} =
      ENNReal.ofReal (cylKernel B p q) := by
  classical
  have hm : Measurable (cylStep B p) := by
    have hpair : Measurable (fun u : ℝ × ℝ => (p, u)) :=
      measurable_const.prodMk measurable_id
    have hcomp := (measurable_cylStep_stepLaw B).comp hpair
    change Measurable (fun u : ℝ × ℝ =>
      (fun z : Site B × (ℝ × ℝ) => cylStep B z.1 z.2) (p, u))
    exact hcomp
  by_cases hy : q.2 = p.2
  · by_cases hx : q.1 = p.1
    · have hqp : q = p := Prod.ext hx hy
      subst q
      have hrect : (cylStep B p) ⁻¹' {p} ∩
          (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) =
          Set.Ico (1 / 2 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) (1 / 2) := by
        ext z
        rcases z with ⟨a, b⟩
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
          Set.mem_prod, Set.mem_Ico]
        constructor
        · rintro ⟨hz, ⟨⟨ha₀, ha₁⟩, ⟨hb₀, hb₁⟩⟩⟩
          have hz' : cylStep B p (a, b) = p := by simpa only [eq_comm] using hz
          have ha : ¬ a < 1 / 2 :=
            (cylStep_level_same_iff B p (a, b)).mp (congrArg Prod.snd hz')
          by_cases hb : b < 1 / 2
          · exact ⟨⟨le_of_not_gt ha, ha₁⟩, ⟨hb₀, hb⟩⟩
          · have hs₀ : 0 ≤ 2 * b - 1 := by nlinarith [hb₀, hb]
            have hs₁ : 2 * b - 1 < 1 := by nlinarith [hb₁]
            have hne := baseNeighbor_ne_self_of_range B p.1 (2 * b - 1) hs₀ hs₁
            simp only [cylStep, if_neg ha, if_neg hb] at hz'
            exact False.elim (hne (Prod.mk.inj hz').1)
        · rintro ⟨⟨ha₀, ha₁⟩, ⟨hb₀, hb₁⟩⟩
          have ha : ¬ a < 1 / 2 := not_lt.mpr ha₀
          have hb : b < 1 / 2 := hb₁
          refine ⟨?_, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩⟩
          · unfold cylStep
            split_ifs <;> (simp_all; try linarith)
          · linarith
          · exact ha₁
          · exact hb₀
          · linarith
      have hvol : volume (Set.Ico (1 / 2 : ℝ) 1) *
          volume (Set.Ico (0 : ℝ) (1 / 2)) = ENNReal.ofReal (1 / 4 : ℝ) := by
        rw [Real.volume_Ico, Real.volume_Ico]
        rw [show (1 : ℝ) - 1 / 2 = (1 / 2 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        simp only [sub_zero]
        norm_num
      have hker : cylKernel B p p = (1 / 4 : ℝ) := by
        norm_num [cylKernel, Base.P]
      rw [stepLaw_map_cylStep_rect B p p _ _ hm hrect, hvol, hker]
    · by_cases hadj : B.graph.Adj p.1 q.1
      · let L := (B.graph.neighborFinset p.1).toList
        have hlen : L.length = B.deg := by
          dsimp [L]
          rw [Finset.length_toList, SimpleGraph.card_neighborFinset_eq_degree,
            B.degree_eq p.1]
        have hmem : q.1 ∈ B.graph.neighborFinset p.1 :=
          (SimpleGraph.mem_neighborFinset (G := B.graph) p.1 q.1).mpr hadj
        have hmemL : q.1 ∈ L := by
          change q.1 ∈ (B.graph.neighborFinset p.1).toList
          exact Finset.mem_toList.mpr hmem
        rcases List.mem_iff_getElem.mp hmemL with ⟨i, hi, hget⟩
        have hidx : L.getD i p.1 = q.1 := by
          rw [List.getD_eq_getElem L p.1 hi]
          exact hget
        have hi' : i < (B.graph.neighborFinset p.1).toList.length := by
          simpa only [L] using hi
        have hidx' : (B.graph.neighborFinset p.1).toList.getD i p.1 = q.1 := by
          simpa only [L] using hidx
        have hiDeg : i < B.deg := by rw [← hlen]; exact hi
        have hJsub : Set.Ico (1 / 2 + (i : ℝ) / (2 * (B.deg : ℝ)))
            (1 / 2 + ((i : ℝ) + 1) / (2 * (B.deg : ℝ))) ⊆
              Set.Ico (1 / 2 : ℝ) 1 := by
          intro b hb
          have hd : (0 : ℝ) < (B.deg : ℝ) := by exact_mod_cast B.deg_pos
          have hiNat : i + 1 ≤ B.deg := Nat.succ_le_of_lt hiDeg
          have hiReal : (i : ℝ) + 1 ≤ (B.deg : ℝ) := by exact_mod_cast hiNat
          have hfrac : ((i : ℝ) + 1) / (2 * (B.deg : ℝ)) ≤ (1 : ℝ) / 2 := by
            apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (B.deg : ℝ))).2
            nlinarith
          rcases Set.mem_Ico.mp hb with ⟨hbL, hbR⟩
          apply Set.mem_Ico.mpr
          constructor
          · have : 0 ≤ (i : ℝ) / (2 * (B.deg : ℝ)) := by positivity
            linarith [hbL]
          · linarith [hbR]
        have hrect : (cylStep B p) ⁻¹' {q} ∩
            (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) =
            Set.Ico (1 / 2 : ℝ) 1 ×ˢ
              Set.Ico (1 / 2 + (i : ℝ) / (2 * (B.deg : ℝ)))
                (1 / 2 + ((i : ℝ) + 1) / (2 * (B.deg : ℝ))) := by
          ext z
          rcases z with ⟨a, b⟩
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_prod, Set.mem_Ico]
          constructor
          · rintro ⟨hz, ⟨⟨ha₀, ha₁⟩, ⟨hb₀, hb₁⟩⟩⟩
            have hz' : cylStep B p (a, b) = q := by simpa only [eq_comm] using hz
            have hlevel : (cylStep B p (a, b)).2 = q.2 := congrArg Prod.snd hz'
            have ha : ¬ a < 1 / 2 :=
              (cylStep_level_same_iff B p (a, b)).mp (hlevel.trans hy)
            by_cases hb : b < 1 / 2
            · simp only [cylStep, if_neg ha, if_pos hb] at hz'
              exact False.elim (hx ((Prod.mk.inj hz').1.symm))
            · have hbase : baseNeighbor B p.1 (2 * b - 1) = q.1 := by
                simp only [cylStep, if_neg ha, if_neg hb] at hz'
                exact (Prod.mk.inj hz').1
              have hbRange : b ∈ Set.Ico (1 / 2 : ℝ) 1 := ⟨le_of_not_gt hb, hb₁⟩
              have hbJ := (baseNeighbor_eq_iff_interval B p.1 q.1 i hi' hidx' hbRange).mp hbase
              exact ⟨⟨le_of_not_gt ha, ha₁⟩, hbJ⟩
          · rintro ⟨⟨ha₀, ha₁⟩, hbJ⟩
            have haRange : a ∈ Set.Ico (0 : ℝ) 1 := by
              exact ⟨by linarith [ha₀], ha₁⟩
            have hbRange : b ∈ Set.Ico (1 / 2 : ℝ) 1 := hJsub hbJ
            have hb₀ : ¬ b < 1 / 2 := not_lt.mpr hbRange.1
            have hbUnit : b ∈ Set.Ico (0 : ℝ) 1 :=
              ⟨by linarith [hbRange.1], hbRange.2⟩
            have hbase := (baseNeighbor_eq_iff_interval B p.1 q.1 i hi' hidx' hbRange).mpr hbJ
            refine ⟨?_, ⟨haRange, hbUnit⟩⟩
            have hA : ¬ (a, b).1 < 1 / 2 := by
              simpa using (not_lt.mpr ha₀)
            have hB : ¬ (a, b).2 < 1 / 2 := by
              simpa using (not_lt.mpr hbRange.1)
            simp only [cylStep, if_neg hA, if_neg hB]
            exact Prod.ext hbase hy.symm
        have hvol : volume (Set.Ico (1 / 2 : ℝ) 1) *
            volume (Set.Ico (1 / 2 + (i : ℝ) / (2 * (B.deg : ℝ)))
              (1 / 2 + ((i : ℝ) + 1) / (2 * (B.deg : ℝ)))) =
              ENNReal.ofReal ((1 / 2 : ℝ) * (1 / (2 * (B.deg : ℝ)))) := by
          rw [Real.volume_Ico, Real.volume_Ico]
          have hwidth :
              (1 / 2 + ((i : ℝ) + 1) / (2 * (B.deg : ℝ))) -
                  (1 / 2 + (i : ℝ) / (2 * (B.deg : ℝ))) =
                1 / (2 * (B.deg : ℝ)) := by
            have hd : (0 : ℝ) < (B.deg : ℝ) := by exact_mod_cast B.deg_pos
            field_simp [hd.ne']
            ring
          rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, hwidth,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        have hpx : p.1 ≠ q.1 := Ne.symm hx
        have hker : cylKernel B p q = (1 / 2 : ℝ) * (1 / (2 * (B.deg : ℝ))) := by
          simp [cylKernel, Base.P, hpx, hy, hadj]
        rw [stepLaw_map_cylStep_rect B p q _ _ hm hrect, hvol, hker]
      · have hrect : (cylStep B p) ⁻¹' {q} ∩
            (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) =
            (∅ : Set ℝ) ×ˢ (∅ : Set ℝ) := by
          ext z
          rcases z with ⟨a, b⟩
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_prod, Set.mem_Ico, Set.mem_empty_iff_false]
          constructor
          · rintro ⟨hz, ⟨⟨_, _⟩, ⟨hb₀, hb₁⟩⟩⟩
            have hz' : cylStep B p (a, b) = q := by simpa only [eq_comm] using hz
            have hlevel : (cylStep B p (a, b)).2 = q.2 := congrArg Prod.snd hz'
            have ha : ¬ a < 1 / 2 :=
              (cylStep_level_same_iff B p (a, b)).mp (hlevel.trans hy)
            by_cases hb : b < 1 / 2
            · simp only [cylStep, if_neg ha, if_pos hb] at hz'
              exact False.elim (hx ((Prod.mk.inj hz').1.symm))
            · have hs₀ : 0 ≤ 2 * b - 1 := by nlinarith [hb₀, hb]
              have hs₁ : 2 * b - 1 < 1 := by nlinarith [hb₁]
              have hadjBase := baseNeighbor_adj_of_range B p.1 (2 * b - 1) hs₀ hs₁
              have hz' : baseNeighbor B p.1 (2 * b - 1) = q.1 := by
                simp only [cylStep, if_neg ha, if_neg hb] at hz'
                exact (Prod.mk.inj hz').1
              rw [hz'] at hadjBase
              exact False.elim (hadj hadjBase)
          · intro h
            simp at h
        have hker : cylKernel B p q = 0 := by
          simp [cylKernel, Base.P, Ne.symm hx, hy, hadj]
        rw [stepLaw_map_cylStep_rect B p q _ _ hm hrect, hker]
        simp
  · by_cases hdown : q.2 = p.2 - 1
    · by_cases hx : q.1 = p.1
      · have hqp : q = (p.1, p.2 - 1) := Prod.ext hx hdown
        subst q
        have hrect : (cylStep B p) ⁻¹' {(p.1, p.2 - 1)} ∩
            (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) =
            Set.Ico (0 : ℝ) (1 / 2) ×ˢ Set.Ico (0 : ℝ) (1 / 2) := by
          ext z
          rcases z with ⟨a, b⟩
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_prod, Set.mem_Ico]
          constructor
          · rintro ⟨hz, ⟨⟨ha₀, ha₁⟩, ⟨hb₀, hb₁⟩⟩⟩
            have hz' : cylStep B p (a, b) = (p.1, p.2 - 1) := by
              simpa only [eq_comm] using hz
            have hlevel : (cylStep B p (a, b)).2 = p.2 - 1 := congrArg Prod.snd hz'
            have hbranch := (cylStep_level_down_iff B p (a, b)).mp hlevel
            exact ⟨⟨ha₀, hbranch.1⟩, ⟨hb₀, hbranch.2⟩⟩
          · rintro ⟨⟨ha₀, ha₁⟩, ⟨hb₀, hb₁⟩⟩
            refine ⟨?_, ⟨⟨ha₀, ?_⟩, ⟨hb₀, ?_⟩⟩⟩
            · unfold cylStep
              split_ifs <;> simp_all
            · linarith
            · linarith
        have hvol : volume (Set.Ico (0 : ℝ) (1 / 2)) *
            volume (Set.Ico (0 : ℝ) (1 / 2)) = ENNReal.ofReal (1 / 4 : ℝ) := by
          rw [Real.volume_Ico]
          simp only [sub_zero]
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          norm_num
        have hker : cylKernel B p (p.1, p.2 - 1) = (1 / 4 : ℝ) := by
          simp [cylKernel]
        rw [stepLaw_map_cylStep_rect B p (p.1, p.2 - 1) _ _ hm hrect, hvol, hker]
      · have hrect : (cylStep B p) ⁻¹' {q} ∩
            (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) =
            (∅ : Set ℝ) ×ˢ (∅ : Set ℝ) := by
          ext z
          rcases z with ⟨a, b⟩
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_prod, Set.mem_Ico, Set.mem_empty_iff_false]
          constructor
          · rintro ⟨hz, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩
            have hz' : cylStep B p (a, b) = q := by simpa only [eq_comm] using hz
            have hlevel : (cylStep B p (a, b)).2 = q.2 := congrArg Prod.snd hz'
            have hbranch := (cylStep_level_down_iff B p (a, b)).mp (hlevel.trans hdown)
            have hfirst : (cylStep B p (a, b)).1 = p.1 := by
              unfold cylStep
              split_ifs <;> simp_all
            exact False.elim (hx ((congrArg Prod.fst hz').symm.trans hfirst))
          · intro h
            simp at h
        have hneqY : p.2 ≠ q.2 := by
          intro heq
          rw [heq] at hdown
          omega
        have hker : cylKernel B p q = 0 := by
          simp [cylKernel, Ne.symm hx, hneqY]
        rw [stepLaw_map_cylStep_rect B p q _ _ hm hrect, hker]
        simp
    · by_cases hup : q.2 = p.2 + 1
      · by_cases hx : q.1 = p.1
        · have hqp : q = (p.1, p.2 + 1) := Prod.ext hx hup
          subst q
          have hrect : (cylStep B p) ⁻¹' {(p.1, p.2 + 1)} ∩
              (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) =
              Set.Ico (0 : ℝ) (1 / 2) ×ˢ Set.Ico (1 / 2 : ℝ) 1 := by
            ext z
            rcases z with ⟨a, b⟩
            simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
              Set.mem_prod, Set.mem_Ico]
            constructor
            · rintro ⟨hz, ⟨⟨ha₀, ha₁⟩, ⟨hb₀, hb₁⟩⟩⟩
              have hz' : cylStep B p (a, b) = (p.1, p.2 + 1) := by
                simpa only [eq_comm] using hz
              have hlevel : (cylStep B p (a, b)).2 = p.2 + 1 := congrArg Prod.snd hz'
              have hbranch := (cylStep_level_up_iff B p (a, b)).mp hlevel
              exact ⟨⟨ha₀, hbranch.1⟩, ⟨le_of_not_gt hbranch.2, hb₁⟩⟩
            · rintro ⟨⟨ha₀, ha₁⟩, ⟨hb₀, hb₁⟩⟩
              have hb : ¬ b < 1 / 2 := not_lt.mpr hb₀
              refine ⟨?_, ⟨⟨ha₀, ?_⟩, ⟨by linarith [hb₀], hb₁⟩⟩⟩
              · unfold cylStep
                split_ifs <;> simp_all
              · linarith
          have hvol : volume (Set.Ico (0 : ℝ) (1 / 2)) *
              volume (Set.Ico (1 / 2 : ℝ) 1) = ENNReal.ofReal (1 / 4 : ℝ) := by
            rw [Real.volume_Ico, Real.volume_Ico]
            rw [show (1 : ℝ) - 1 / 2 = (1 / 2 : ℝ) by norm_num]
            simp only [sub_zero]
            rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
            norm_num
          have hker : cylKernel B p (p.1, p.2 + 1) = (1 / 4 : ℝ) := by
            simp [cylKernel]
          rw [stepLaw_map_cylStep_rect B p (p.1, p.2 + 1) _ _ hm hrect, hvol, hker]
        · have hrect : (cylStep B p) ⁻¹' {q} ∩
              (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) =
              (∅ : Set ℝ) ×ˢ (∅ : Set ℝ) := by
            ext z
            rcases z with ⟨a, b⟩
            simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
              Set.mem_prod, Set.mem_Ico, Set.mem_empty_iff_false]
            constructor
            · rintro ⟨hz, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩
              have hz' : cylStep B p (a, b) = q := by simpa only [eq_comm] using hz
              have hlevel : (cylStep B p (a, b)).2 = q.2 := congrArg Prod.snd hz'
              have hbranch := (cylStep_level_up_iff B p (a, b)).mp (hlevel.trans hup)
              have hfirst : (cylStep B p (a, b)).1 = p.1 := by
                unfold cylStep
                split_ifs <;> simp_all
              exact False.elim (hx ((congrArg Prod.fst hz').symm.trans hfirst))
            · intro h
              simp at h
          have hneqY : p.2 ≠ q.2 := by
            intro heq
            rw [heq] at hup
            omega
          have hker : cylKernel B p q = 0 := by
            simp [cylKernel, Ne.symm hx, hneqY]
          rw [stepLaw_map_cylStep_rect B p q _ _ hm hrect, hker]
          simp
      · have hrect : (cylStep B p) ⁻¹' {q} ∩
            (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) =
            (∅ : Set ℝ) ×ˢ (∅ : Set ℝ) := by
          ext z
          rcases z with ⟨a, b⟩
          simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
            Set.mem_prod, Set.mem_Ico, Set.mem_empty_iff_false]
          constructor
          · rintro ⟨hz, ⟨⟨_, _⟩, ⟨_, _⟩⟩⟩
            have hz' : cylStep B p (a, b) = q := by simpa only [eq_comm] using hz
            have hlevel : (cylStep B p (a, b)).2 = q.2 := congrArg Prod.snd hz'
            rcases cylStep_level_cases B p (a, b) with hcase | hcase | hcase
            · exact False.elim (hdown (hlevel.symm.trans hcase))
            · exact False.elim (hy (hlevel.symm.trans hcase))
            · exact False.elim (hup (hlevel.symm.trans hcase))
          · intro h
            simp at h
        have hnatAbs : (p.2 - q.2).natAbs ≠ 1 := by
          intro habs
          have habs' : (p.2 - q.2).natAbs = (1 : ℤ).natAbs := by simpa using habs
          rcases Int.natAbs_eq_iff.mp habs' with hpos | hneg
          · exact hdown (by omega)
          · exact hup (by omega)
        have hker : cylKernel B p q = 0 := by
          have hneqY : p.2 ≠ q.2 := by intro heq; exact hy heq.symm
          simp [cylKernel, hneqY, hnatAbs]
        rw [stepLaw_map_cylStep_rect B p q _ _ hm hrect, hker]
        simp

/-- The walk leaves any cluster almost surely: the exit time is finite off a
null set (`tex:265` takes the exit location for granted).

`exitSite` reads the trajectory at `ENat.toNat ⊤ = 0` when the walk never
exits, which returns the walk's own starting point; this lemma is what makes
that branch negligible. -/
theorem exit_ae_finite (B : Base) (t : ℕ) :
    ∀ᵐ ω ∂driverLaw, exitTime B (cluster B ω t) (stepWalk B (ω t)) ≠ ⊤ := by
  exact Obligation.exit_ae_finite B t

/-- The cluster grows by exactly one site per step, off the null set of
`exit_ae_finite`: the paper's `|A_+(t)| = t` (`tex:265`, `tex:340`).

This is the paper's only sanity check on the growth rule, and the whole
normalisation `T = N⌊y₀ a_N⌋` depends on it. -/
theorem clusterPlus_ncard (B : Base) (t : ℕ) :
    ∀ᵐ ω ∂driverLaw, (clusterPlus B ω t).ncard = t := by
  exact Obligation.clusterPlus_ncard_legacy B t

/-! ### The discrepancy -/

/-- `D_t` has finite support, so the `finsum` in `pairing` is the paper's
"absolutely convergent finite sum" (`tex:352-353`) and not the junk value
`finsum` returns on an infinite support.

This holds for *every* driver, not merely almost every one: the cluster always
contains `R_0` and exceeds it by finitely many sites. -/
theorem discrepancy_support_finite (B : Base) (ω : Driver) (t : ℕ) :
    (Function.support (discrepancy B ω t)).Finite := by
  exact Obligation.discrepancy_support_finite B ω t

private theorem measurable_startVertex_legacy (B : Base) :
    Measurable (startVertex B) := by
  unfold startVertex
  let values : ℕ → B.V := fun n => (Finset.univ : Finset B.V).toList.getD n B.pt
  have hvalues : Measurable values := measurable_of_countable values
  have hindex : Measurable (fun r : ℝ => ⌊(B.card : ℝ) * r⌋₊) := by fun_prop
  exact hvalues.comp hindex

private theorem measurable_cylStep_legacy (B : Base) :
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

private theorem measurable_stepWalk_eval_legacy (B : Base) (n : ℕ) :
    Measurable (fun d : StepDriver => stepWalk B d n) := by
  induction n with
  | zero =>
      unfold stepWalk
      change Measurable (fun d : StepDriver => (startVertex B d.1, 0))
      exact ((measurable_startVertex_legacy B).comp measurable_fst).prodMk measurable_const
  | succ n ih =>
      unfold stepWalk at *
      change Measurable (fun d : StepDriver =>
        cylStep B (cylPath B (startVertex B d.1, 0) d.2 n) (d.2 n))
      exact (measurable_cylStep_legacy B).comp (ih.prodMk (by fun_prop))

private theorem exitTime_eq_nat_iff_legacy (B : Base) (S : Set (Site B))
    (X : ℕ → Site B) (n : ℕ) :
    exitTime B S X = (n : ℕ∞) ↔ X n ∉ S ∧ ∀ m < n, X m ∈ S := by
  classical
  unfold exitTime
  let E : Set ℕ∞ := {k : ℕ∞ | ∃ m : ℕ, k = (m : ℕ∞) ∧ X m ∉ S}
  change sInf E = (n : ℕ∞) ↔ X n ∉ S ∧ ∀ m < n, X m ∈ S
  by_cases hE : E.Nonempty
  · rw [csInf_eq_iff hE]
    constructor
    · rintro ⟨hn, hmin⟩
      have hn' : X n ∉ S := by
        change ∃ m : ℕ, (n : ℕ∞) = (m : ℕ∞) ∧ X m ∉ S at hn
        rcases hn with ⟨m, hmn, hnot⟩
        have : n = m := by exact_mod_cast hmn
        subst m
        exact hnot
      refine ⟨hn', ?_⟩
      intro m hmn
      by_contra hnot
      have hle : (n : ℕ∞) ≤ (m : ℕ∞) := hmin (m : ℕ∞) ⟨m, rfl, hnot⟩
      have : n ≤ m := by exact_mod_cast hle
      omega
    · rintro ⟨hn, hbefore⟩
      refine ⟨⟨n, rfl, hn⟩, ?_⟩
      intro a ha
      change ∃ m : ℕ, a = (m : ℕ∞) ∧ X m ∉ S at ha
      rcases ha with ⟨m, rfl, hnot⟩
      by_contra hnm
      have hnm' : ¬ n ≤ m := by
        intro hnm'
        exact hnm (by exact_mod_cast hnm')
      have hm : m < n := Nat.lt_of_not_ge hnm'
      exact hnot (hbefore m hm)
  · have hEmpty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hE
    rw [hEmpty, sInf_empty]
    constructor
    · intro h
      simp at h
    · rintro ⟨hn, _⟩
      exfalso
      exact hE ⟨(n : ℕ∞), by dsimp [E]; exact ⟨n, rfl, hn⟩⟩

private theorem exitTime_eq_top_iff_legacy (B : Base) (S : Set (Site B))
    (X : ℕ → Site B) :
    exitTime B S X = ⊤ ↔ ∀ n : ℕ, X n ∈ S := by
  classical
  unfold exitTime
  constructor
  · intro h n
    by_contra hnot
    have hle : sInf {k : ℕ∞ | ∃ m : ℕ, k = (m : ℕ∞) ∧ X m ∉ S} ≤ (n : ℕ∞) :=
      sInf_le ⟨n, rfl, hnot⟩
    rw [h] at hle
    simp at hle
  · intro h
    have hEmpty : {k : ℕ∞ | ∃ m : ℕ, k = (m : ℕ∞) ∧ X m ∉ S} = ∅ := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨m, rfl, hnot⟩
      exact hnot (h m)
    rw [hEmpty, sInf_empty]

private noncomputable def legacySettleSite (B : Base) (ω : Driver) (t : ℕ) : Site B :=
  exitSite B (cluster B ω t) (ω t)

private theorem cluster_eq_image_legacy (B : Base) (ω : Driver) (t : ℕ) :
    cluster B ω t = R B 0 ∪ (Finset.range t).image (legacySettleSite B ω) := by
  induction t with
  | zero => simp
  | succ n ih =>
      rw [cluster_succ, ih, Finset.range_add_one, Finset.image_insert]
      ext p
      simp only [Set.mem_union, Set.mem_singleton_iff, Finset.coe_insert,
        Set.mem_insert_iff]
      have hs : exitSite B (R B 0 ∪ ↑(Finset.image (legacySettleSite B ω) (Finset.range n)))
          (ω n) = legacySettleSite B ω n := by
        calc
          _ = exitSite B (cluster B ω n) (ω n) := by rw [← ih]
          _ = legacySettleSite B ω n := rfl
      rw [hs]
      tauto

private theorem cluster_eq_range_of_history_legacy (B : Base) {t : ℕ}
    {ω : Driver} {s : Fin t → Site B}
    (h : ∀ j : Fin t, legacySettleSite B ω j.1 = s j) :
    cluster B ω t = R B 0 ∪ Set.range s := by
  rw [cluster_eq_image_legacy]
  congr 1
  ext p
  simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio, Set.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, hj⟩, (h ⟨j, hj⟩).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j.1, j.2, h j⟩

private theorem measurable_exitSite_driver_legacy (B : Base) (S : Set (Site B)) :
    Measurable (fun d : StepDriver => exitSite B S d) := by
  classical
  have htop_set : {d : StepDriver | exitTime B S (stepWalk B d) = ⊤} =
      ⋂ n : ℕ, (fun d : StepDriver => stepWalk B d n) ⁻¹' S := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    exact exitTime_eq_top_iff_legacy B S (stepWalk B d)
  have htop_meas : MeasurableSet {d : StepDriver | exitTime B S (stepWalk B d) = ⊤} := by
    rw [htop_set]
    exact MeasurableSet.iInter fun n =>
      (measurable_stepWalk_eval_legacy B n) ((Set.to_countable S).measurableSet)
  have hfinite_set (n : ℕ) :
      {d : StepDriver | exitTime B S (stepWalk B d) = (n : ℕ∞)} =
        (fun d : StepDriver => stepWalk B d n) ⁻¹' Sᶜ ∩
          ⋂ m ∈ Set.Iio n, (fun d : StepDriver => stepWalk B d m) ⁻¹' S := by
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter₂, Set.mem_preimage,
      Set.mem_compl_iff, Set.mem_Iio]
    exact exitTime_eq_nat_iff_legacy B S (stepWalk B d) n
  have hfinite_meas (n : ℕ) :
      MeasurableSet {d : StepDriver | exitTime B S (stepWalk B d) = (n : ℕ∞)} := by
    rw [hfinite_set]
    exact ((measurable_stepWalk_eval_legacy B n) ((Set.to_countable Sᶜ).measurableSet)).inter
      (MeasurableSet.biInter (Set.to_countable (Set.Iio n)) fun m _ =>
        (measurable_stepWalk_eval_legacy B m) ((Set.to_countable S).measurableSet))
  refine measurable_to_countable' fun q => ?_
  have hkey : (fun d : StepDriver => exitSite B S d) ⁻¹' {q} =
      ⋃ t : ℕ∞, {d : StepDriver | exitTime B S (stepWalk B d) = t} ∩
        (fun d : StepDriver => stepWalk B d t.toNat) ⁻¹' {q} := by
    ext d
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_setOf_eq, exitSite]
    constructor
    · intro hq
      exact ⟨exitTime B S (stepWalk B d), rfl, hq⟩
    · rintro ⟨t, ht, hq⟩
      show stepWalk B d (exitTime B S (stepWalk B d)).toNat = q
      rw [ht]
      exact hq
  rw [hkey]
  refine MeasurableSet.iUnion fun t => MeasurableSet.inter ?_ ?_
  · cases t with
    | top => exact htop_meas
    | coe n => exact hfinite_meas n
  · exact (measurable_stepWalk_eval_legacy B t.toNat) (measurableSet_singleton q)

private theorem measurable_legacySettleSite (B : Base) (t : ℕ) :
    Measurable (fun ω : Driver => legacySettleSite B ω t) := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
      refine measurable_to_countable' fun q => ?_
      have hset : (fun ω : Driver => legacySettleSite B ω t) ⁻¹' {q} =
          ⋃ s : Fin t → Site B,
            ({ω : Driver | ∀ j : Fin t, legacySettleSite B ω j.1 = s j} ∩
              {ω : Driver | exitSite B (R B 0 ∪ Set.range s) (ω t) = q}) := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
          Set.mem_setOf_eq]
        constructor
        · intro hq
          refine ⟨fun j => legacySettleSite B ω j.1, fun j => rfl, ?_⟩
          rw [← cluster_eq_range_of_history_legacy B (fun _ => rfl)]
          exact hq
        · rintro ⟨s, hs, hq⟩
          have hc := cluster_eq_range_of_history_legacy B hs
          show exitSite B (cluster B ω t) (ω t) = q
          rw [hc]
          exact hq
      rw [hset]
      refine MeasurableSet.iUnion fun s => MeasurableSet.inter ?_ ?_
      · have hhistory : {ω : Driver | ∀ j : Fin t, legacySettleSite B ω j.1 = s j} =
            ⋂ j : Fin t, (fun ω : Driver => legacySettleSite B ω j.1) ⁻¹' {s j} := by
          ext ω
          simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
        rw [hhistory]
        exact MeasurableSet.iInter fun j => ih j.1 j.2 (measurableSet_singleton (s j))
      · exact ((measurable_exitSite_driver_legacy B (R B 0 ∪ Set.range s)).comp
          (measurable_pi_apply t)) (measurableSet_singleton q)

private theorem measurableSet_mem_cluster_legacy (B : Base) (t : ℕ) (p : Site B) :
    MeasurableSet {ω : Driver | p ∈ cluster B ω t} := by
  have hset : {ω : Driver | p ∈ cluster B ω t} =
      {ω : Driver | p ∈ R B 0} ∪
        ⋃ j ∈ Finset.range t, (fun ω : Driver => legacySettleSite B ω j) ⁻¹' {p} := by
    ext ω
    simp only [cluster_eq_image_legacy, Set.mem_setOf_eq, Set.mem_union, Finset.coe_image,
      Finset.coe_range, Set.mem_image, Set.mem_Iio, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_singleton_iff, Finset.mem_range, exists_prop]
  rw [hset]
  refine MeasurableSet.union (MeasurableSet.const _) ?_
  exact MeasurableSet.biUnion (Finset.range t).countable_toSet fun j _ =>
    measurable_legacySettleSite B j (measurableSet_singleton p)

/-- The event in `max_fluct` is measurable, so `driverLaw` applied to it is a
probability and not merely an outer measure.  The containments are countable
conditions over the countable set `Site B`. -/
theorem measurableSet_shape (B : Base) (t : ℕ) (j k : ℝ) :
    MeasurableSet {ω : Driver | R B j ⊆ cluster B ω t ∧ cluster B ω t ⊆ R B k} := by
  have hset : {ω : Driver | R B j ⊆ cluster B ω t ∧ cluster B ω t ⊆ R B k}
      = (⋂ p ∈ R B j, {ω : Driver | p ∈ cluster B ω t}) ∩
        (⋂ p ∈ (R B k)ᶜ, {ω : Driver | p ∈ cluster B ω t}ᶜ) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter₂, Set.mem_compl_iff,
      Set.subset_def]
    refine and_congr Iff.rfl ⟨fun h p hp hpc => hp (h p hpc), fun h p hpc => ?_⟩
    by_contra hp
    exact h p hp hpc
  rw [hset]
  exact (MeasurableSet.biInter (Set.to_countable _) fun p _ =>
      measurableSet_mem_cluster_legacy B t p).inter
    (MeasurableSet.biInter (Set.to_countable _) fun p _ =>
      (measurableSet_mem_cluster_legacy B t p).compl)

/-- A sum over the distinct sites visited by finitely many settlements is
measurable, even when the settlement map repeats a site. -/
private theorem measurable_sum_legacy_image (B : Base) (t : ℕ) (f : Site B → ℝ) :
    Measurable (fun ω : Driver =>
      ∑ p ∈ (Finset.range t).image (legacySettleSite B ω), f p) := by
  classical
  have heq : ∀ ω : Driver,
      (∑ p ∈ (Finset.range t).image (legacySettleSite B ω), f p) =
        ∑ i ∈ Finset.range t,
          if (∀ j ∈ Finset.range t, j < i →
              legacySettleSite B ω j ≠ legacySettleSite B ω i)
          then f (legacySettleSite B ω i) else 0 := by
    intro ω
    refine Finset.sum_image' (f := f) (g := legacySettleSite B ω)
      (s := Finset.range t) (h := fun i =>
        if (∀ j ∈ Finset.range t, j < i →
            legacySettleSite B ω j ≠ legacySettleSite B ω i)
        then f (legacySettleSite B ω i) else 0) ?_
    intro i hi
    set Fib := (Finset.range t).filter
      (fun j => legacySettleSite B ω j = legacySettleSite B ω i) with hFib
    have hFib_ne : Fib.Nonempty :=
      ⟨i, by rw [hFib, Finset.mem_filter]; exact ⟨hi, rfl⟩⟩
    set i₀ := Fib.min' hFib_ne with hi₀
    have hi₀_mem : i₀ ∈ Fib := Finset.min'_mem _ _
    have hi₀_mem' : i₀ ∈ (Finset.range t).filter
        (fun j => legacySettleSite B ω j = legacySettleSite B ω i) := by
      simpa [Fib] using hi₀_mem
    have hi₀_range : i₀ ∈ Finset.range t := by
      exact (Finset.mem_filter.mp hi₀_mem').1
    have hi₀_eq : legacySettleSite B ω i₀ = legacySettleSite B ω i := by
      exact (Finset.mem_filter.mp hi₀_mem').2
    have hcond₀ : ∀ j ∈ Finset.range t, j < i₀ →
        legacySettleSite B ω j ≠ legacySettleSite B ω i₀ := by
      intro j hj hlt hij
      have hjFib : j ∈ Fib := by
        rw [hFib, Finset.mem_filter]
        exact ⟨hj, hij.trans hi₀_eq⟩
      have hle : i₀ ≤ j := Finset.min'_le _ j hjFib
      omega
    have hzero : ∀ j ∈ Fib, j ≠ i₀ →
        (if (∀ k ∈ Finset.range t, k < j →
            legacySettleSite B ω k ≠ legacySettleSite B ω j)
          then f (legacySettleSite B ω j) else 0) = 0 := by
      intro j hjFib hjne
      have hjFib' : j ∈ (Finset.range t).filter
          (fun k => legacySettleSite B ω k = legacySettleSite B ω i) := by
        simpa [Fib] using hjFib
      have hji : legacySettleSite B ω j = legacySettleSite B ω i :=
        (Finset.mem_filter.mp hjFib').2
      have hlt : i₀ < j := by
        have hle : i₀ ≤ j := Finset.min'_le _ j hjFib
        omega
      have hfalse : ¬ (∀ k ∈ Finset.range t, k < j →
          legacySettleSite B ω k ≠ legacySettleSite B ω j) := by
        intro hcon
        exact hcon i₀ hi₀_range hlt (by rw [hji, hi₀_eq])
      rw [if_neg hfalse]
    rw [Finset.sum_eq_single_of_mem i₀ hi₀_mem hzero]
    rw [if_pos hcond₀, hi₀_eq]
  rw [show (fun ω : Driver =>
      ∑ p ∈ (Finset.range t).image (legacySettleSite B ω), f p) =
      fun ω => ∑ i ∈ Finset.range t,
        if (∀ j ∈ Finset.range t, j < i →
            legacySettleSite B ω j ≠ legacySettleSite B ω i)
        then f (legacySettleSite B ω i) else 0 from funext heq]
  refine Finset.measurable_sum _ fun i _ => ?_
  refine Measurable.ite ?_ ?_ measurable_const
  · have hset : {ω : Driver |
        ∀ j ∈ Finset.range t, j < i →
          legacySettleSite B ω j ≠ legacySettleSite B ω i} =
      ⋂ j ∈ Finset.range t,
        {ω : Driver | j < i →
          legacySettleSite B ω j ≠ legacySettleSite B ω i} := by
      ext ω
      simp
    rw [hset]
    refine MeasurableSet.biInter (Finset.range t).countable_toSet fun j _ => ?_
    by_cases hj : j < i
    · simp only [hj, true_implies]
      have hdiag : MeasurableSet {p : Site B × Site B | p.1 = p.2} :=
        (Set.to_countable _).measurableSet
      have hpair : Measurable
          (fun ω : Driver => (legacySettleSite B ω j, legacySettleSite B ω i)) :=
        (measurable_legacySettleSite B j).prod (measurable_legacySettleSite B i)
      exact (hpair hdiag).compl
    · simp only [hj, false_implies]
      exact MeasurableSet.univ
  · exact (measurable_of_countable f).comp (measurable_legacySettleSite B i)

/-- The legacy pairing is measurable in the driver. Integrability for a given
test function is a separate obligation. -/
theorem measurable_pairing (B : Base) (t : ℕ) (f : Site B → ℝ) :
    Measurable (fun ω : Driver => pairing B ω t f) := by
  classical
  let plus (ω : Driver) : Finset (Site B) :=
    ((Finset.range t).image (legacySettleSite B ω)).filter (fun p => 1 ≤ p.2)
  let rect : Finset (Site B) :=
    Finset.univ.product (Finset.Icc (1 : ℤ) ⌊(t : ℝ) / (B.card : ℝ)⌋)
  have hplus (ω : Driver) (p : Site B) :
      p ∈ plus ω ↔ p ∈ cluster B ω t ∧ 1 ≤ p.2 := by
    change p ∈ ((Finset.range t).image (legacySettleSite B ω)).filter _ ↔ _
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨himage, hy⟩
      have hcluster : p ∈ cluster B ω t := by
        rw [cluster_eq_image_legacy]
        exact Or.inr himage
      exact ⟨hcluster, hy⟩
    · rintro ⟨hcluster, hy⟩
      rw [cluster_eq_image_legacy] at hcluster
      rcases hcluster with hp0 | hpimage
      · have hp0' : (p.2 : ℝ) ≤ 0 := by simpa only [mem_R] using hp0
        have hy' : (1 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast hy
        linarith
      · exact ⟨hpimage, hy⟩
  have hrect (p : Site B) :
      p ∈ rect ↔ 1 ≤ p.2 ∧ p.2 ≤ ⌊(t : ℝ) / (B.card : ℝ)⌋ := by
    simp [rect, Finset.mem_product, Finset.mem_Icc]
  have hcard : (0 : ℝ) < (B.card : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num) B.nontrivial
  have ht : (0 : ℝ) ≤ (t : ℝ) / B.card :=
    div_nonneg (Nat.cast_nonneg t) hcard.le
  have hrect_R (p : Site B) (hp : 1 ≤ p.2) :
      p ∈ rect ↔ p ∈ R B ((t : ℝ) / B.card) := by
    rw [hrect]
    simp only [mem_R]
    constructor
    · rintro ⟨_, hfloor⟩
      exact Int.le_floor.mp hfloor
    · intro hR
      exact ⟨hp, Int.le_floor.mpr hR⟩
  have hpair_eq (ω : Driver) :
      pairing B ω t f = (∑ p ∈ plus ω, f p) - (∑ p ∈ rect, f p) := by
    have hsub : Function.support (fun p => discrepancy B ω t p * f p) ⊆
        ((plus ω ∪ rect : Finset (Site B)) : Set (Site B)) := by
      intro p hp
      have hD : discrepancy B ω t p ≠ 0 := by
        intro hzero
        exact hp (by
          show discrepancy B ω t p * f p = 0
          rw [hzero, zero_mul])
      rcases Obligation.discrepancy_support_finite_mem_or B ω t p hD with
        ⟨hcluster, hnotR⟩ | ⟨hnotcluster, hR⟩
      · have hR0 : p ∉ R B 0 := fun hp0 => hnotR
          (R_mono ht hp0)
        have hp0 : ¬ p.2 ≤ 0 := by
          intro hle
          apply hR0
          simp only [mem_R]
          exact_mod_cast hle
        have hy : 1 ≤ p.2 := by omega
        exact Finset.mem_union.mpr (Or.inl ((hplus ω p).mpr ⟨hcluster, hy⟩))
      · have hR0 : p ∉ R B 0 := fun hp0 => hnotcluster
          (cluster_mono B ω (Nat.zero_le t) hp0)
        have hp0 : ¬ p.2 ≤ 0 := by
          intro hle
          apply hR0
          simp only [mem_R]
          exact_mod_cast hle
        have hy : 1 ≤ p.2 := by omega
        have hupper_real : (p.2 : ℝ) ≤ (t : ℝ) / B.card := by
          simpa only [mem_R] using hR
        exact Finset.mem_union.mpr
          (Or.inr ((hrect p).mpr ⟨hy, Int.le_floor.mpr hupper_real⟩))
    rw [pairing, finsum_eq_sum_of_support_subset _ hsub]
    have hpoint : ∀ p ∈ (plus ω ∪ rect : Finset (Site B)),
        discrepancy B ω t p * f p =
          (if p ∈ plus ω then f p else 0) - (if p ∈ rect then f p else 0) := by
      intro p hp
      have hcases : p ∈ plus ω ∨ p ∈ rect := Finset.mem_union.mp hp
      have hy : 1 ≤ p.2 := by
        rcases hcases with hplus' | hrect'
        · exact (hplus ω p).mp hplus' |>.2
        · exact (hrect p).mp hrect' |>.1
      have hcluster : p ∈ plus ω ↔ p ∈ cluster B ω t := by
        constructor
        · exact fun h => (hplus ω p).mp h |>.1
        · exact fun h => (hplus ω p).mpr ⟨h, hy⟩
      have hR : p ∈ rect ↔ p ∈ R B ((t : ℝ) / B.card) := hrect_R p hy
      by_cases hplus' : p ∈ plus ω <;> by_cases hrect' : p ∈ rect
      · have hcl := hcluster.mp hplus'
        have hRt := hR.mp hrect'
        rw [discrepancy, Set.indicator_of_mem hcl, Set.indicator_of_mem hRt,
          if_pos hplus', if_pos hrect']
        ring
      · have hcl := hcluster.mp hplus'
        have hRt : p ∉ R B ((t : ℝ) / B.card) := fun h => hrect' (hR.mpr h)
        rw [discrepancy, Set.indicator_of_mem hcl, Set.indicator_of_notMem hRt,
          if_pos hplus', if_neg hrect']
        ring
      · have hcl : p ∉ cluster B ω t := fun h => hplus' (hcluster.mpr h)
        have hRt := hR.mp hrect'
        rw [discrepancy, Set.indicator_of_notMem hcl, Set.indicator_of_mem hRt,
          if_neg hplus', if_pos hrect']
        ring
      · exact (hcases.elim hplus' hrect').elim
    rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_ite_mem]
      congr 1
      exact Finset.inter_eq_right.mpr Finset.subset_union_left
    · rw [Finset.sum_ite_mem]
      congr 1
      exact Finset.inter_eq_right.mpr Finset.subset_union_right
  have hsum (g : Site B → ℝ) :
      Measurable (fun ω : Driver => ∑ p ∈ plus ω, g p) := by
    have hfilter : (fun ω : Driver => ∑ p ∈ plus ω, g p) =
        fun ω => ∑ p ∈ (Finset.range t).image (legacySettleSite B ω),
          if 1 ≤ p.2 then g p else 0 := by
      funext ω
      simp [plus, Finset.sum_filter]
    rw [hfilter]
    exact measurable_sum_legacy_image B t (fun p => if 1 ≤ p.2 then g p else 0)
  have hfun : (fun ω : Driver => pairing B ω t f) =
      fun ω => (∑ p ∈ plus ω, f p) - (∑ p ∈ rect, f p) := funext hpair_eq
  rw [hfun]
  exact Measurable.sub (hsum f) measurable_const

/-! ### The spectrum and the mixing time -/

/-- The mixing-time defining set is non-empty, so `mixingTime = sInf …` is the
paper's `τ_mix` (`tex:269`) and not `sInf ∅ = 0`.

This one is load-bearing on the *truth value* of `max_fluct`: with `τ_mix = 0`
one gets `T^♯ = 0`, hence `Δ_N = C log N`, which is strictly stronger than the
paper's bound and false for large `T`. -/
theorem mixingTime_spec (B : Base) :
    {t : ℕ | ∀ x : B.V, tvToUniform B t x ≤ 1 / 4}.Nonempty := by
  exact Obligation.mixingTime_spec_of_pos B (Obligation.basePow_pos_uniform B)

/-- Every base admits the diagonalisation the paper asserts at `tex:301-311`:
`P_N` is symmetric, hence orthogonally diagonalisable, with `λ_1 = 1` and
`f_1 ≡ 1` by stochasticity, `λ_N ≥ 0` by laziness and `λ_2 < 1` by
irreducibility. -/
theorem spectralData_exists (B : Base) : Nonempty (SpectralData B) := by
  exact Obligation.spectralData_exists_of B (Obligation.P_quadratic_nonneg B)
    (Obligation.P_quadratic_le B) (fun v hv x y => Obligation.P_fixed_const B v hv x y)

end IdlaCyl
