/-
The canonical construction of the cylinder walk.

The model layer in `IdlaCyl/Support/Idla.lean` drives the walk with an explicit
pair of uniforms per step.  That realises the paper's kernel, but it is a
*definition* of a different process, and the bridge back to `cylKernel`
(`tex:246-255`) is the obligation `step_law_eq_cylKernel`.  This file instead
takes the canonical route that Mathlib already provides: the transition kernel
is the object, and the law of the whole trajectory is Ionescu-Tulcea
(`ProbabilityTheory.Kernel.trajMeasure`,
`Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean`).

Why this is the right construction:

* `cylKernel` (`tex:246-255`) *is* the transition kernel, so no law-matching
  lemma is needed at the level of one step.  What remains is the paper's own
  observation that each row sums to one, which is `cylMeasure_isProbability`
  below.
* `walkPathLaw x` is then the law of the entire walk from `x`, produced by
  Mathlib's Ionescu-Tulcea theorem; the Markov property is available as
  `Kernel.map_traj_succ_self` and the conditional law as
  `Kernel.condDistrib_trajMeasure`.
* The state space `Site B = B.V × ℤ` is countable with measurable singletons,
  so a kernel is just a family of measures and `Kernel.ofFunOfCountable`
  applies; there is no measurability obligation to discharge.

Junk values.  `cylMeasure` is a `Measure.sum` of Dirac masses weighted by
`ENNReal.ofReal (cylKernel …)`; it is a probability measure exactly when the
row sum is, and that is `cylMeasure_isProbability`.  Because a `Measure.sum` of
finite measures is always defined, there is no junk branch: a failure here is a
failure to prove, not a silent `0`.

Status.  `cylMeasure_isProbability` is proved below; it is the canonical form of
`step_law_eq_cylKernel` and the reason neither `walkLawUniform` nor `idlaMeasure`
falls into the `Measure.infinitePi` zero branch.
-/
import IdlaCyl.Support.Cylinder
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IdlaCyl

variable (B : Base)

/-- The one-step law of the cylinder walk from `p`, as a measure on sites: the
weights are the paper's kernel `cylKernel` (`tex:246-255`). -/
noncomputable def cylMeasure (p : Site B) : Measure (Site B) :=
  Measure.sum (fun q : Site B => ENNReal.ofReal (cylKernel B p q) • Measure.dirac q)

/-- The cylinder walk as a Markov kernel on the cylinder.  This is the
canonical replacement for the driven `cylStep` of `IdlaCyl/Support/Idla.lean`
and the model of the paper's `𝒫_N` (`def:SRW`, `tex:246-255`). -/
noncomputable def cylTransitionKernel : Kernel (Site B) (Site B) :=
  Kernel.ofFunOfCountable (cylMeasure B)

/-- Each row of `cylKernel` sums to one (`tex:246-255`): the vertical branch
contributes `1/4 + 1/4 = 1/2`, and the horizontal branch contributes
`(1/2) ∑_{x'} P_N(x,x') = 1/2` by `Base.P_row_sum`.  Equivalently, `cylMeasure`
is a probability measure.

This is the canonical form of the obligation `step_law_eq_cylKernel`: it says
the object defined here *is* the paper's kernel, so no separate law-matching
lemma is needed at the level of one step. -/
theorem cylMeasure_isProbability (p : Site B) : IsProbabilityMeasure (cylMeasure B p) := by
  constructor
  have hstep : cylMeasure B p Set.univ = ∑' q : Site B, ENNReal.ofReal (cylKernel B p q) := by
    unfold cylMeasure
    rw [Measure.sum_apply _ MeasurableSet.univ]
    simp
  rw [hstep]
  have hzero : ∀ q ∉ (Finset.univ ×ˢ ({p.2 - 1, p.2, p.2 + 1} : Finset ℤ) : Finset (Site B)),
      ENNReal.ofReal (cylKernel B p q) = 0 := by
    intro q hq
    simp only [Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hq
    obtain ⟨hq1, hq2, hq3⟩ := hq
    have hk0 : cylKernel B p q = 0 := by
      unfold cylKernel
      split_ifs with h1 h2
      · exfalso
        obtain ⟨-, h1'⟩ := h1
        rcases Int.natAbs_eq (p.2 - q.2) with hd | hd <;> rw [h1'] at hd <;> omega
      · exact absurd h2.symm hq2
      · rfl
    rw [hk0, ENNReal.ofReal_zero]
  have hrow : ∑ q ∈ (Finset.univ ×ˢ ({p.2 - 1, p.2, p.2 + 1} : Finset ℤ) : Finset (Site B)),
      cylKernel B p q = 1 := by
    rw [Finset.sum_product]
    have hT : ∀ x : B.V, ∑ y ∈ ({p.2 - 1, p.2, p.2 + 1} : Finset ℤ), cylKernel B p (x, y)
        = cylKernel B p (x, p.2 - 1) + cylKernel B p (x, p.2) + cylKernel B p (x, p.2 + 1) := by
      intro x
      have h1 : p.2 - 1 ∉ ({p.2, p.2 + 1} : Finset ℤ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have h2 : p.2 ∉ ({p.2 + 1} : Finset ℤ) := by
        simp only [Finset.mem_singleton]
        omega
      rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
      ring
    have hbot : ∀ x : B.V, cylKernel B p (x, p.2 - 1) = if p.1 = x then (1 / 4 : ℝ) else 0 := by
      intro x
      unfold cylKernel
      have hne : p.2 ≠ p.2 - 1 := by omega
      simp [hne]
    have hmid : ∀ x : B.V, cylKernel B p (x, p.2) = (1 / 2) * B.P p.1 x := by
      intro x
      unfold cylKernel
      simp
    have htop : ∀ x : B.V, cylKernel B p (x, p.2 + 1) = if p.1 = x then (1 / 4 : ℝ) else 0 := by
      intro x
      unfold cylKernel
      have hne : p.2 ≠ p.2 + 1 := by omega
      simp [hne]
    simp_rw [hT, hbot, hmid, htop]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp
    rw [← Finset.mul_sum, B.P_row_sum p.1]
    norm_num
  calc ∑' q : Site B, ENNReal.ofReal (cylKernel B p q)
      = ∑ q ∈ (Finset.univ ×ˢ ({p.2 - 1, p.2, p.2 + 1} : Finset ℤ) : Finset (Site B)),
          ENNReal.ofReal (cylKernel B p q) := tsum_eq_sum hzero
    _ = ENNReal.ofReal (∑ q ∈ (Finset.univ ×ˢ ({p.2 - 1, p.2, p.2 + 1} : Finset ℤ) : Finset (Site B)),
          cylKernel B p q) := (ENNReal.ofReal_sum_of_nonneg (fun q _ => cylKernel_nonneg p q)).symm
    _ = ENNReal.ofReal 1 := by rw [hrow]
    _ = 1 := ENNReal.ofReal_one

instance cylTransitionKernel_isMarkov : IsMarkovKernel (cylTransitionKernel B) :=
  ⟨cylMeasure_isProbability B⟩

/-! ### The law of the whole trajectory

`Kernel.trajMeasure` wants the transition at time `n` as a kernel on the
*past* `Π _ : Finset.Iic n, Site B`.  The walk is time-homogeneous, so that
kernel reads the last coordinate and applies `cylMeasure`. -/

/-- The Ionescu-Tulcea transition family of the homogeneous cylinder walk: the
kernel at time `n` reads the position at time `n` from the past. -/
noncomputable def cylITKernel :
    (n : ℕ) → Kernel (Π _ : Finset.Iic n, Site B) (Site B) :=
  fun n => Kernel.ofFunOfCountable
    (fun x => cylMeasure B (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩))

instance cylITKernel_isMarkov : ∀ n, IsMarkovKernel (cylITKernel B n) :=
  fun n => ⟨fun x => cylMeasure_isProbability B (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)⟩

/-- The law of the entire cylinder walk started at `x`, a probability measure
on path space `ℕ → Site B`.  This is the paper's law of one cylinder walk
(`tex:265`, "an independent cylinder walk"), built by Ionescu-Tulcea. -/
noncomputable def walkPathLaw (x : Site B) : Measure (ℕ → Site B) :=
  Kernel.trajMeasure (Measure.dirac x) (cylITKernel B)

instance walkPathLaw_isProbability (x : Site B) : IsProbabilityMeasure (walkPathLaw B x) := by
  rw [walkPathLaw]
  haveI : IsProbabilityMeasure (Measure.dirac x : Measure (Site B)) := inferInstance
  infer_instance

end IdlaCyl
