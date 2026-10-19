import IdlaCyl.Support.Silvestri.DrivenLaw
import IdlaCyl.Support.Silvestri.TailBounds

/-!
# The holding count of a first-passage segment of the canonical walk

For the canonical cylinder walk `walkPathLaw B p` and a level `ℓ : ℤ`, the first exit from the
region `{q | q.2 < ℓ}` is the first arrival at height `ℓ`. The holding count `holdCount B ℓ X` is the
number of steps before that exit on which the height does not change.

The vertical increments of the walk are i.i.d. with the one-step type law `typeLaw`
(`walkPathLaw_incr_law`). If the start lies at distance at least `h ≥ 0` below `ℓ`, then the
probability that the holding count is below `m ≥ 1` is at most
`exp (-h ^ 2 / (4 m)) + exp (-m / 2)`. The proof splits on whether the walk climbs by `h` within
the first `4 m` steps, which the climb bound controls, and otherwise on whether fewer than `m` of
the first `4 m` increments vanish, which the holding bound controls.
-/

namespace IdlaCyl.Silvestri

open MeasureTheory Filter
open scoped ENNReal
open IdlaCyl.Obligation.ExitAeFinite (inc)

/-- One step of the driven cylinder walk changes the height by the vertical type `inc` of its
driver entry. -/
theorem cylPath_incr (B : Base) (x : Site B) (w : WalkDriver) (i : ℕ) :
    (cylPath B x w (i + 1)).2 - (cylPath B x w i).2 = inc (w i) := by
  rw [cylPath_succ]
  unfold cylStep inc
  split_ifs <;> simp

/-- The vertical increment map on paths is measurable. -/
theorem measurable_incr (B : Base) :
    Measurable (fun (X : ℕ → Site B) (i : ℕ) => (X (i + 1)).2 - (X i).2) := by
  refine measurable_pi_lambda _ fun i => ?_
  exact (measurable_snd.comp (measurable_pi_apply (i + 1))).sub
    (measurable_snd.comp (measurable_pi_apply i))

/-- The vertical increments of the canonical walk are i.i.d. with the one-step type law
`typeLaw`: pushing `walkPathLaw B p` forward by the increment map gives the infinite product of
`typeLaw`. -/
theorem walkPathLaw_incr_law (B : Base) (p : Site B) :
    (walkPathLaw B p).map (fun X i => (X (i + 1)).2 - (X i).2) =
      Measure.infinitePi (fun _ : ℕ => typeLaw) := by
  have hcomp : ((fun (X : ℕ → Site B) (i : ℕ) => (X (i + 1)).2 - (X i).2) ∘
      fun w : WalkDriver => cylPath B p w) = fun w n => inc (w n) := by
    funext w i
    exact cylPath_incr B p w i
  rw [← drivenPath_law B p, Measure.map_map (measurable_incr B) (measurable_cylPath B p), hcomp,
    drivenType_law]

/-- The holding count of the first-passage segment of `X` at level `ℓ`: the number of steps
`i < τ` before the first exit `τ` from `{q | q.2 < ℓ}` on which the height does not change. -/
noncomputable def holdCount (B : Base) (ℓ : ℤ) (X : ℕ → Site B) : ℕ :=
  ((Finset.range (WithTop.untopA (exitTime' B {q : Site B | q.2 < ℓ} X))).filter
    fun i => (X (i + 1)).2 = (X i).2).card

/-- Holding-count tail. If `p` lies at distance at least `h ≥ 0` below level `ℓ`, then for `m ≥ 1`
the probability that the holding count of the first-passage segment is below `m` is at most
`exp (-h ^ 2 / (4 m)) + exp (-m / 2)`. -/
theorem walkPathLaw_holdCount_lt (B : Base) (ℓ : ℤ) (p : Site B) (h : ℝ) (hh : 0 ≤ h)
    (hℓ : (p.2 : ℝ) + h ≤ ℓ) (m : ℕ) (hm : 0 < m) :
    walkPathLaw B p {X | holdCount B ℓ X < m} ≤
      ENNReal.ofReal (Real.exp (-h ^ 2 / (4 * m)) + Real.exp (-(m : ℝ) / 2)) := by
  -- The pushforward of a set of increment sequences has mass at most its i.i.d. mass.
  have hA : ∀ E : Set (ℕ → ℤ), walkPathLaw B p ((fun (X : ℕ → Site B) (i : ℕ) =>
      (X (i + 1)).2 - (X i).2) ⁻¹' E) ≤
      ENNReal.ofReal ((Measure.infinitePi fun _ : ℕ => typeLaw).real E) := by
    intro E
    calc walkPathLaw B p _ ≤ (walkPathLaw B p).map (fun (X : ℕ → Site B) (i : ℕ) =>
          (X (i + 1)).2 - (X i).2) E := Measure.le_map_apply (measurable_incr B).aemeasurable E
      _ = (Measure.infinitePi fun _ : ℕ => typeLaw) E := by rw [walkPathLaw_incr_law]
      _ = ENNReal.ofReal ((Measure.infinitePi fun _ : ℕ => typeLaw).real E) := by
          rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hae : ∀ᵐ X ∂walkPathLaw B p, X 0 = p ∧ ∀ M : ℤ, ∃ n, M < (X n).2 :=
    (walkPathLaw_ae_start B p).and (walkPathLaw_ae_above B p)
  have hsub : ∀ᵐ X ∂walkPathLaw B p, X ∈ {X | holdCount B ℓ X < m} →
      X ∈ (fun (X : ℕ → Site B) (i : ℕ) => (X (i + 1)).2 - (X i).2) ⁻¹'
          {ω : ℕ → ℤ | ∃ t ≤ 4 * m, h ≤ ∑ i ∈ Finset.range t, (ω i : ℝ)} ∪
        (fun (X : ℕ → Site B) (i : ℕ) => (X (i + 1)).2 - (X i).2) ⁻¹'
          {ω : ℕ → ℤ | (Finset.filter (fun i => ω i = 0) (Finset.range (4 * m))).card < m} := by
    filter_upwards [hae] with X hX hcount
    obtain ⟨hX0, hX⟩ := hX
    have hcount' : holdCount B ℓ X < m := hcount
    -- The walk reaches level `ℓ`, so the exit time is finite.
    obtain ⟨n, hn⟩ := hX (ℓ - 1)
    have hn' : X n ∈ ({q : Site B | q.2 < ℓ})ᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
      omega
    have hle : exitTime' B {q : Site B | q.2 < ℓ} X ≤ (n : ℕ∞) := by
      unfold exitTime'
      exact MeasureTheory.hittingAfter_le_iff.mpr ⟨n, ⟨Nat.zero_le n, le_rfl⟩, hn'⟩
    have hne : exitTime' B {q : Site B | q.2 < ℓ} X ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.coe_ne_top n) hle
    obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hne
    obtain ⟨hXt, -⟩ := (exitTime'_eq_coe_iff B {q : Site B | q.2 < ℓ} X t).mp ht.symm
    have hhold : holdCount B ℓ X =
        ((Finset.range t).filter fun i => (X (i + 1)).2 = (X i).2).card := by
      unfold holdCount
      rw [← ht, untopA_natCast]
    have hXt' : ℓ ≤ (X t).2 := by
      simp only [Set.mem_setOf_eq, not_lt] at hXt
      exact hXt
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_setOf_eq]
    rcases lt_or_ge t (4 * m) with htm | htm
    · -- The walk climbs by `h` within `4 m` steps.
      left
      have hsumZ : ∑ i ∈ Finset.range t, ((X (i + 1)).2 - (X i).2) = (X t).2 - (X 0).2 :=
        Finset.sum_range_sub (fun i => (X i).2) t
      have hR : ((∑ i ∈ Finset.range t, ((X (i + 1)).2 - (X i).2) : ℤ) : ℝ) =
          (((X t).2 - (X 0).2 : ℤ) : ℝ) := by
        rw [hsumZ]
      push_cast at hR
      have hlt : (ℓ : ℝ) ≤ ((X t).2 : ℝ) := by exact_mod_cast hXt'
      have h0 : ((X 0).2 : ℝ) = (p.2 : ℝ) := by rw [hX0]
      refine ⟨t, htm.le, ?_⟩
      push_cast
      linarith
    · -- Otherwise the holding count is at most the number of zero increments in `4 m` steps.
      right
      have hsub' : Finset.filter (fun i => (X (i + 1)).2 - (X i).2 = 0) (Finset.range (4 * m)) ⊆
          Finset.filter (fun i => (X (i + 1)).2 = (X i).2) (Finset.range t) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
        exact ⟨by omega, by omega⟩
      have hcard := Finset.card_le_card hsub'
      omega
  have hb1 := climb_small (4 * m) (by omega) h hh
  have hb2 := hor_small m hm
  have hcast : ((4 * m : ℕ) : ℝ) = 4 * (m : ℝ) := by push_cast; ring
  rw [hcast] at hb1
  calc walkPathLaw B p {X | holdCount B ℓ X < m}
      ≤ walkPathLaw B p (((fun (X : ℕ → Site B) (i : ℕ) => (X (i + 1)).2 - (X i).2) ⁻¹'
          {ω : ℕ → ℤ | ∃ t ≤ 4 * m, h ≤ ∑ i ∈ Finset.range t, (ω i : ℝ)}) ∪
        ((fun (X : ℕ → Site B) (i : ℕ) => (X (i + 1)).2 - (X i).2) ⁻¹'
          {ω : ℕ → ℤ | (Finset.filter (fun i => ω i = 0) (Finset.range (4 * m))).card < m})) :=
        measure_mono_ae hsub
    _ ≤ walkPathLaw B p (((fun (X : ℕ → Site B) (i : ℕ) => (X (i + 1)).2 - (X i).2) ⁻¹'
          {ω : ℕ → ℤ | ∃ t ≤ 4 * m, h ≤ ∑ i ∈ Finset.range t, (ω i : ℝ)})) +
        walkPathLaw B p (((fun (X : ℕ → Site B) (i : ℕ) => (X (i + 1)).2 - (X i).2) ⁻¹'
          {ω : ℕ → ℤ | (Finset.filter (fun i => ω i = 0) (Finset.range (4 * m))).card < m})) :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-h ^ 2 / (4 * m))) +
        ENNReal.ofReal (Real.exp (-(m : ℝ) / 2)) :=
        add_le_add ((hA _).trans (ENNReal.ofReal_le_ofReal hb1))
          ((hA _).trans (ENNReal.ofReal_le_ofReal hb2))
    _ = ENNReal.ofReal (Real.exp (-h ^ 2 / (4 * m)) + Real.exp (-(m : ℝ) / 2)) :=
        (ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le).symm

end IdlaCyl.Silvestri
