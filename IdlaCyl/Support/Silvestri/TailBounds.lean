module

public import LatticeProb.Prob.SubGaussianMaximal
public import IdlaCyl.Support.Silvestri.DrivenTypes
public import Mathlib

@[expose] public section

/-!
# Tail bounds for the i.i.d. vertical types

The vertical types of the cylinder walk are i.i.d. with the law `typeLaw`, which takes the values
`-1`, `1` and `0` with probabilities `1/4`, `1/4` and `1/2`. On the sequence space `ℕ → ℤ` with the
product law `Measure.infinitePi (fun _ => typeLaw)`, this file proves two exponential tail bounds.

* `climb_small`: the probability that some partial sum of the first `W` types reaches a level
  `h ≥ 0` is at most `exp (-h ^ 2 / W)`.
* `hor_small`: the probability that fewer than `m` of the first `4 m` types are `0` is at most
  `exp (-m / 2)`.

The type law has moment generating function at most `exp (t ^ 2 / 4)`, so each coordinate is
sub-Gaussian with variance proxy `1/2` (`typeLaw_hasSubgaussianMGF`). The first bound is the
maximal sub-Gaussian inequality of `LatticeProb`. The second is the Hoeffding lower tail for sums
of independent Bernoulli variables, applied to the indicators of the zero type.
-/

namespace IdlaCyl.Silvestri

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The moment generating function of the vertical type `Z ∼ typeLaw` is
`E e^{t Z} = (1/4) e^t + (1/4) e^{-t} + 1/2`. -/
theorem typeLaw_mgf (t : ℝ) :
    mgf (fun z : ℤ => (z : ℝ)) typeLaw t =
      (1 / 4) * Real.exp t + (1 / 4) * Real.exp (-t) + 1 / 2 := by
  have hi : ∀ a : ℤ, Integrable (fun z : ℤ => Real.exp (t * z)) (Measure.dirac a) :=
    fun a => integrable_dirac (by simp)
  have h1 : Integrable (fun z : ℤ => Real.exp (t * z)) ((1 / 4 : ℝ≥0∞) • Measure.dirac (-1 : ℤ)) :=
    (hi (-1)).smul_measure (by simp)
  have h2 : Integrable (fun z : ℤ => Real.exp (t * z)) ((1 / 4 : ℝ≥0∞) • Measure.dirac (1 : ℤ)) :=
    (hi 1).smul_measure (by simp)
  have h3 : Integrable (fun z : ℤ => Real.exp (t * z)) ((1 / 2 : ℝ≥0∞) • Measure.dirac (0 : ℤ)) :=
    (hi 0).smul_measure (by simp)
  rw [mgf, typeLaw, integral_add_measure ((h1.add_measure h2)) h3,
    integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac, integral_dirac]
  norm_num [ENNReal.toReal_div]
  ring

/-- The vertical type `Z ∼ typeLaw` has exponential moments of every order. -/
theorem typeLaw_integrable_exp (t : ℝ) :
    Integrable (fun z : ℤ => Real.exp (t * (z : ℝ))) typeLaw := by
  have hi : ∀ a : ℤ, Integrable (fun z : ℤ => Real.exp (t * z)) (Measure.dirac a) :=
    fun a => integrable_dirac (by simp)
  unfold typeLaw
  exact (((hi (-1)).smul_measure (by simp)).add_measure
    ((hi 1).smul_measure (by simp))).add_measure ((hi 0).smul_measure (by simp))

/-- The vertical type `Z ∼ typeLaw` is sub-Gaussian with variance proxy `1/2`, since its moment
generating function is at most `exp (t ^ 2 / 4)` (`LatticeProb.lazySign_mgf_le`). -/
theorem typeLaw_hasSubgaussianMGF : HasSubgaussianMGF (fun z : ℤ => (z : ℝ)) (1 / 2) typeLaw := by
  refine ⟨fun t => typeLaw_integrable_exp t, fun t => ?_⟩
  have hc : ((1 / 2 : ℝ≥0) : ℝ) * t ^ 2 / 2 = t ^ 2 / 4 := by
    norm_num
    ring
  rw [typeLaw_mgf, hc]
  exact LatticeProb.lazySign_mgf_le t

/-- Each coordinate `ω ↦ ω i` of the type sequence, read as a real number, is sub-Gaussian with
variance proxy `1/2` under `Measure.infinitePi (fun _ => typeLaw)`. -/
theorem coord_hasSubgaussianMGF (i : ℕ) :
    HasSubgaussianMGF (fun ω : ℕ → ℤ => (ω i : ℝ)) (1 / 2)
      (Measure.infinitePi fun _ : ℕ => typeLaw) := by
  have h : HasSubgaussianMGF (fun z : ℤ => (z : ℝ)) (1 / 2)
      ((Measure.infinitePi fun _ : ℕ => typeLaw).map (fun ω : ℕ → ℤ => ω i)) := by
    rw [Measure.infinitePi_map_eval]
    exact typeLaw_hasSubgaussianMGF
  exact HasSubgaussianMGF.of_map (measurable_pi_apply i).aemeasurable h

/-- The coordinates of the type sequence, read as real numbers, are independent under
`Measure.infinitePi (fun _ => typeLaw)`. -/
theorem coord_iIndepFun :
    iIndepFun (fun (i : ℕ) (ω : ℕ → ℤ) => (ω i : ℝ))
      (Measure.infinitePi fun _ : ℕ => typeLaw) :=
  iIndepFun_infinitePi (X := fun _ (z : ℤ) => (z : ℝ)) (fun _ => measurable_of_countable _)

/-- Climb bound. For `W ≥ 1` and `h ≥ 0`, the probability under the i.i.d. type law that some
partial sum of the first `t ≤ W` types reaches `h` is at most `exp (-h ^ 2 / W)`. -/
theorem climb_small (W : ℕ) (hW : 0 < W) (h : ℝ) (hh : 0 ≤ h) :
    (Measure.infinitePi fun _ : ℕ => typeLaw).real
        {ω : ℕ → ℤ | ∃ t ≤ W, h ≤ ∑ i ∈ Finset.range t, (ω i : ℝ)} ≤
      Real.exp (-(h ^ 2) / W) := by
  refine (LatticeProb.measure_exists_partialSum_ge_le (fun i (ω : ℕ → ℤ) => (ω i : ℝ))
    coord_iIndepFun (fun i => (measurable_of_countable _).comp (measurable_pi_apply i))
    (1 / 2) coord_hasSubgaussianMGF W hW hh).trans (le_of_eq ?_)
  have hW' : (W : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hW.ne'
  have h2 : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  congr 1
  rw [h2]
  field_simp

/-- Holding-count bound. For `m ≥ 1`, the probability under the i.i.d. type law that fewer than
`m` of the first `4 m` types equal `0` is at most `exp (-m / 2)`. -/
theorem hor_small (m : ℕ) (hm : 0 < m) :
    (Measure.infinitePi fun _ : ℕ => typeLaw).real
        {ω : ℕ → ℤ | (Finset.filter (fun i => ω i = 0) (Finset.range (4 * m))).card < m} ≤
      Real.exp (-(m : ℝ) / 2) := by
  set g : ℤ → ℝ := fun z => if z = 0 then 1 else 0 with hg_def
  have hind : iIndepFun (fun (i : ℕ) (ω : ℕ → ℤ) => g (ω i))
      (Measure.infinitePi fun _ : ℕ => typeLaw) :=
    iIndepFun_infinitePi (X := fun _ => g) (fun _ => measurable_of_countable _)
  have hmeas : ∀ i, Measurable (fun ω : ℕ → ℤ => g (ω i)) :=
    fun i => (measurable_of_countable g).comp (measurable_pi_apply i)
  have hβ : ∀ i, ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => typeLaw),
      g (ω i) = 0 ∨ g (ω i) = 1 :=
    fun i => ae_of_all _ fun ω => by
      simp only [hg_def]
      split_ifs <;> simp
  have hmean : ∀ i, (Measure.infinitePi fun _ : ℕ => typeLaw)[fun ω : ℕ → ℤ => g (ω i)] = 1 / 2 := by
    intro i
    have hgi : g = Set.indicator {0} 1 := by
      ext z
      by_cases h : z = 0 <;> simp [hg_def, h]
    have hmap := integral_map (μ := Measure.infinitePi fun _ : ℕ => typeLaw)
      (φ := fun ω : ℕ → ℤ => ω i) (f := g) (measurable_pi_apply i).aemeasurable
      (measurable_of_countable g).aestronglyMeasurable
    rw [Measure.infinitePi_map_eval] at hmap
    rw [← hmap, hgi, integral_indicator_one (measurableSet_singleton 0), measureReal_def]
    simp [typeLaw, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply']
  have hLP := LatticeProb.measure_sum_bernoulli_le (fun i (ω : ℕ → ℤ) => g (ω i)) hind hmeas hβ
    hmean (4 * m) (r := (m : ℝ)) (Nat.cast_nonneg m)
  have hsub : {ω : ℕ → ℤ | (Finset.filter (fun i => ω i = 0) (Finset.range (4 * m))).card < m} ⊆
      {ω : ℕ → ℤ | ∑ i ∈ Finset.range (4 * m), g (ω i) ≤ ((4 * m : ℕ) : ℝ) / 2 - m} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hsum : ∑ i ∈ Finset.range (4 * m), g (ω i) =
        ((Finset.filter (fun i => ω i = 0) (Finset.range (4 * m))).card : ℝ) := by
      simp [hg_def, Finset.sum_boole]
    rw [hsum]
    have hle : ((Finset.filter (fun i => ω i = 0) (Finset.range (4 * m))).card : ℝ) ≤ m := by
      exact_mod_cast hω.le
    push_cast
    linarith
  refine (measureReal_mono hsub).trans (hLP.trans (le_of_eq ?_))
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  congr 1
  push_cast
  field_simp
  ring

end IdlaCyl.Silvestri
