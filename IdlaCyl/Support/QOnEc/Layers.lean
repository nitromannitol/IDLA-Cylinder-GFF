module

/-
Source: paper/idla-cylinder-gff.tex, tex:931-938,990-998.
Finite consecutive height layers cover the bad event almost surely. The
largest layer uses the canonical almost-sure cap, rather than arbitrary paths.
-/
public import IdlaCyl.Support.QOnEc.Mass

@[expose] public section

namespace IdlaCyl.QOnEc

open IdlaCyl.Defs MeasureTheory
open scoped BigOperators

/-- The event that the cluster is not contained below a specified height. -/
def aboveHeight (B : Base) (T h : ℕ) : Set (TrajSeq B) :=
  {ω | ¬ clusterTraj B ω T ⊆ R B (h : ℝ)}

/-- The height failure event is measurable. -/
theorem measurableSet_aboveHeight (B : Base) (T h : ℕ) :
    MeasurableSet (aboveHeight B T h) := by
  have heq : aboveHeight B T h =
      ⋃ p : Site B, {ω : TrajSeq B | p ∈ clusterTraj B ω T ∧ p ∉ R B (h : ℝ)} := by
    ext ω
    simp only [aboveHeight, Set.mem_setOf_eq, Set.mem_iUnion, Set.not_subset]
  rw [heq]
  exact MeasurableSet.iUnion fun p =>
    (measurableSet_mem_clusterTraj B T p).inter (MeasurableSet.const _)

/-- The literal shape event is measurable. -/
theorem measurableSet_shape (U : Setup) (C y₀ : ℝ) (N : ℕ) :
    MeasurableSet (shape U C y₀ N) :=
  measurableSet_shapeTraj (U.B N) (time U y₀ N)
    ((⌊(time U y₀ N : ℝ) / ((U.B N).card : ℝ) - width U C y₀ N⌋ : ℤ) : ℝ)
    ((time U y₀ N : ℝ) / ((U.B N).card : ℝ) + width U C y₀ N)

private theorem pointwise_layer_cover (B : Base) (T H : ℕ)
    (f : TrajSeq B → ℝ) (E : Set (TrajSeq B)) (M : ℝ) (hM : 0 ≤ M)
    (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hf0 : ∀ ω, clusterTraj B ω T ⊆ R B (H : ℝ) → f ω ≤ M)
    (hf : ∀ j ω, clusterTraj B ω T ⊆ R B ((H + j + 1 : ℕ) : ℝ) → f ω ≤ w j)
    (ω : TrajSeq B) (hcap : clusterTraj B ω T ⊆ R B (T : ℝ)) :
    f ω * Eᶜ.indicator (fun _ => (1 : ℝ)) ω ≤
      M * Eᶜ.indicator (fun _ => (1 : ℝ)) ω +
        ∑ j ∈ Finset.range T, w j * (aboveHeight B T (H + j)).indicator (fun _ => (1 : ℝ)) ω := by
  classical
  have hnn : ∀ j, 0 ≤ w j * (aboveHeight B T (H + j)).indicator (fun _ => (1 : ℝ)) ω :=
    fun j => mul_nonneg (hw j) (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
  have hsum0 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range T) => hnn j)
  by_cases hE : ω ∈ Eᶜ
  · rw [Set.indicator_of_mem hE, mul_one, mul_one]
    have hex : ∃ j : ℕ, clusterTraj B ω T ⊆ R B ((H + j : ℕ) : ℝ) :=
      ⟨T, hcap.trans (R_mono (by exact_mod_cast Nat.le_add_left T H))⟩
    let j := Nat.find hex
    have hjmem : clusterTraj B ω T ⊆ R B ((H + j : ℕ) : ℝ) := Nat.find_spec hex
    have hjT : j ≤ T := Nat.find_min' hex
      (hcap.trans (R_mono (by exact_mod_cast Nat.le_add_left T H)))
    by_cases hj0 : j = 0
    · have h0 : clusterTraj B ω T ⊆ R B (H : ℝ) := by simpa only [hj0, Nat.add_zero] using hjmem
      exact (hf0 ω h0).trans (le_add_of_nonneg_right hsum0)
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hprev : ω ∈ aboveHeight B T (H + (j - 1)) :=
        Nat.find_min hex (by omega)
      have hbound : f ω ≤ w (j - 1) := by
        apply hf (j - 1) ω
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j), Nat.add_assoc] using hjmem
      have hsingle : w (j - 1) ≤
          ∑ i ∈ Finset.range T, w i * (aboveHeight B T (H + i)).indicator (fun _ => (1 : ℝ)) ω := by
        have hle := Finset.single_le_sum (fun i (_ : i ∈ Finset.range T) => hnn i)
          (show j - 1 ∈ Finset.range T from Finset.mem_range.mpr (by omega))
        simpa only [Set.indicator_of_mem hprev, mul_one] using hle
      exact hbound.trans (hsingle.trans (le_add_of_nonneg_left hM))
  · rw [Set.indicator_of_notMem hE, mul_zero, mul_zero, zero_add]
    exact hsum0

/-- Integrating a finite height cover gives the weighted height-probability
sum. The hypotheses here are deterministic bounds on each height event. -/
theorem integral_le_height_layers (B : Base) (T H : ℕ)
    (f : TrajSeq B → ℝ) (hfint : Integrable f (idlaMeasure B))
    (E : Set (TrajSeq B)) (hE : MeasurableSet E) (M : ℝ) (hM : 0 ≤ M)
    (w : ℕ → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hf0 : ∀ ω, clusterTraj B ω T ⊆ R B (H : ℝ) → f ω ≤ M)
    (hf : ∀ j ω, clusterTraj B ω T ⊆ R B ((H + j + 1 : ℕ) : ℝ) → f ω ≤ w j) :
    ∫ ω, f ω * Eᶜ.indicator (fun _ => (1 : ℝ)) ω ∂idlaMeasure B ≤
      M * (idlaMeasure B Eᶜ).toReal +
        ∑ j ∈ Finset.range T, w j * (idlaMeasure B (aboveHeight B T (H + j))).toReal := by
  have hprod : (fun ω => f ω * Eᶜ.indicator (fun _ => (1 : ℝ)) ω) = Eᶜ.indicator f := by
    funext ω
    by_cases hω : ω ∈ Eᶜ <;> simp only [Set.indicator, hω, ↓reduceIte, mul_one, mul_zero]
  have hfi : Integrable (fun ω => f ω * Eᶜ.indicator (fun _ => (1 : ℝ)) ω) (idlaMeasure B) := by
    rw [hprod]
    exact hfint.indicator hE.compl
  have hMi : Integrable (fun ω : TrajSeq B => M * Eᶜ.indicator (fun _ => (1 : ℝ)) ω)
      (idlaMeasure B) := ((integrable_const (1 : ℝ)).indicator hE.compl).const_mul M
  have hwi : ∀ j : ℕ, Integrable
      (fun ω : TrajSeq B => w j * (aboveHeight B T (H + j)).indicator (fun _ => (1 : ℝ)) ω)
      (idlaMeasure B) := fun j =>
    ((integrable_const (1 : ℝ)).indicator (measurableSet_aboveHeight B T (H + j))).const_mul (w j)
  have hgi := hMi.add (integrable_finsetSum (Finset.range T) (fun j _ => hwi j))
  have hle := integral_mono_ae hfi hgi
    ((clusterTraj_ae_subset_R_time B T).mono fun ω hcap =>
      pointwise_layer_cover B T H f E M hM w hw hf0 hf ω hcap)
  refine hle.trans_eq ?_
  simp only [Pi.add_apply]
  rw [integral_add hMi (integrable_finsetSum (Finset.range T) (fun j _ => hwi j)),
    integral_const_mul, integral_indicator_const (1 : ℝ) hE.compl,
    integral_finsetSum _ (fun j _ => hwi j)]
  simp only [smul_eq_mul, mul_one, Measure.real]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_indicator_const (1 : ℝ) (measurableSet_aboveHeight B T (H + j))]
  simp only [smul_eq_mul, mul_one, Measure.real]

end IdlaCyl.QOnEc
