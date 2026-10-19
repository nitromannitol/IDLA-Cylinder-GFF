/-
Source: paper/idla-cylinder-gff.tex, tex:893-903,1069-1070.
The martingale differences are square integrable because their settling sites
have a deterministic almost-sure finite height cap. Orthogonality gives
E[M(T)²] = E[Q_N], including when the limiting variance vanishes.
-/
import IdlaCyl.Support.Gff.Product
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import IdlaCyl.Support.GffSeq.Product
import IdlaCyl.Support.Torus.Sequence

namespace IdlaCyl.GffSeq.Gff

open IdlaCyl.Defs Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- Each increment is square integrable, without an asymptotic hypothesis. -/
theorem memLp_increment (U : SequenceSetup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (N k : ℕ) :
    MemLp (gffIncrement U K α y₀ N k) 2 (idlaMeasure (U.B N)) := by
  apply (memLp_two_iff_integrable_sq (measurable_increment U K α y₀ N k).aestronglyMeasurable).mpr
  simpa only [gffIncrement, mul_pow] using
    (integrable_psi_settleSite (U.B N) (fun p => SequenceSetup.psi U K α y₀ N p ^ 2) k).const_mul
      ((Real.sqrt (((U.B N).card : ℝ) * U.a N))⁻¹ ^ 2)

/-- Finite partial sums of the array are square integrable. -/
theorem memLp_sum (U : SequenceSetup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ) (N t : ℕ) :
    MemLp (fun ω => ∑ k ∈ Finset.range t, gffIncrement U K α y₀ N k ω) 2
      (idlaMeasure (U.B N)) := by
  exact memLp_finsetSum (Finset.range t) (fun k _ => memLp_increment U K α y₀ N k)

/-- An increment is orthogonal to the preceding partial sum (`tex:1069`). -/
theorem integral_sum_mul_increment (U : SequenceSetup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ)
    (N t : ℕ) (hK : K ≤ (U.B N).card) :
    (∫ ω, (∑ k ∈ Finset.range t, gffIncrement U K α y₀ N k ω) *
      gffIncrement U K α y₀ N t ω ∂idlaMeasure (U.B N)) = 0 := by
  let P := idlaMeasure (U.B N)
  let ℱ := idlaFiltration (U.B N)
  let M := fun t ω => ∑ k ∈ Finset.range t, gffIncrement U K α y₀ N k ω
  let X := gffIncrement U K α y₀ N t
  have hM : Martingale M ℱ P := gffIncrement_martingale U K α y₀ N hK
  have hX : Integrable X P := (memLp_increment U K α y₀ N t).integrable (by norm_num)
  have hMX : Integrable (M t * X) P :=
    (memLp_sum U K α y₀ N t).integrable_mul (memLp_increment U K α y₀ N t)
  have hdiff : X = M (t + 1) - M t := by
    funext ω
    simp only [M, X, Finset.sum_range_succ, Pi.sub_apply, add_sub_cancel_left]
  have hcond : P[X | ℱ t] =ᵐ[P] 0 := by
    rw [hdiff]
    have hs := condExp_sub (hM.integrable (t + 1)) (hM.integrable t) (ℱ t)
    have hnext := hM.condExp_ae_eq (Nat.le_succ t)
    have hprev := hM.condExp_ae_eq (le_refl t)
    filter_upwards [hs, hnext, hprev] with ω hsω hnω hpω
    simp only [Pi.sub_apply, Pi.zero_apply] at *
    rw [hsω, hnω, hpω, sub_self]
  have hpull := condExp_mul_of_stronglyMeasurable_left (hM.stronglyMeasurable t) hMX hX
  have hzero : P[M t * X | ℱ t] =ᵐ[P] 0 := by
    filter_upwards [hpull, hcond] with ω hp hc
    simpa only [Pi.mul_apply, Pi.zero_apply, hc, mul_zero] using hp
  calc
    (∫ ω, M t ω * X ω ∂P) = ∫ ω, P[M t * X | ℱ t] ω ∂P :=
      (integral_condExp (ℱ.le t)).symm
    _ = 0 := by simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae hzero

/-- Orthogonality identifies the second moment with the sum of squared
increments at every finite time (`tex:1069`). -/
theorem integral_sum_sq (U : SequenceSetup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ)
    (N t : ℕ) (hK : K ≤ (U.B N).card) :
    (∫ ω, (∑ k ∈ Finset.range t, gffIncrement U K α y₀ N k ω) ^ 2 ∂idlaMeasure (U.B N)) =
      ∫ ω, ∑ k ∈ Finset.range t, gffIncrement U K α y₀ N k ω ^ 2 ∂idlaMeasure (U.B N) := by
  induction t with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, integral_zero]
  | succ t ih =>
    have hsum := (memLp_sum U K α y₀ N t).integrable_sq
    have hinc := (memLp_increment U K α y₀ N t).integrable_sq
    have hprod := (memLp_sum U K α y₀ N t).integrable_mul (memLp_increment U K α y₀ N t)
    have hsquares : Integrable (fun ω => ∑ k ∈ Finset.range t,
        gffIncrement U K α y₀ N k ω ^ 2) (idlaMeasure (U.B N)) :=
      integrable_finsetSum _ (fun k _ => (memLp_increment U K α y₀ N k).integrable_sq)
    have heq : (fun ω : TrajSeq (U.B N) =>
        (∑ k ∈ Finset.range (t + 1), gffIncrement U K α y₀ N k ω) ^ 2) =
        fun ω => (∑ k ∈ Finset.range t, gffIncrement U K α y₀ N k ω) ^ 2 +
          2 * ((∑ k ∈ Finset.range t, gffIncrement U K α y₀ N k ω) *
            gffIncrement U K α y₀ N t ω) + gffIncrement U K α y₀ N t ω ^ 2 := by
      funext ω
      rw [Finset.sum_range_succ]
      ring
    have hprod2 : Integrable (fun ω => 2 *
        ((∑ k ∈ Finset.range t, gffIncrement U K α y₀ N k ω) *
          gffIncrement U K α y₀ N t ω)) (idlaMeasure (U.B N)) := hprod.const_mul 2
    have hfirst : Integrable (fun ω =>
        (∑ k ∈ Finset.range t, gffIncrement U K α y₀ N k ω) ^ 2 +
          2 * ((∑ k ∈ Finset.range t, gffIncrement U K α y₀ N k ω) *
            gffIncrement U K α y₀ N t ω)) (idlaMeasure (U.B N)) := hsum.add hprod2
    rw [heq, integral_add hfirst hinc,
      integral_add hsum hprod2, integral_const_mul,
      integral_sum_mul_increment U K α y₀ N t hK, mul_zero, add_zero, ih]
    simp only [Finset.sum_range_succ, integral_add hsquares hinc]

/-- At the paper's observation time, `E[M(T)²] = E[Q_N]`. -/
theorem integral_sum_sq_eq_qmass (U : SequenceSetup) (K : ℕ) (α : ℕ → ℝ → ℝ) (y₀ : ℝ)
    (N : ℕ) (hK : K ≤ (U.B N).card) :
    (∫ ω, (∑ k ∈ Finset.range (SequenceSetup.time U y₀ N), gffIncrement U K α y₀ N k ω) ^ 2
      ∂idlaMeasure (U.B N)) = ∫ ω, SequenceSetup.qmass U K α y₀ N ω ∂idlaMeasure (U.B N) := by
  rw [integral_sum_sq U K α y₀ N (SequenceSetup.time U y₀ N) hK]
  exact integral_congr_ae (gffIncrement_sq_sum_eq_qmass U K α y₀ N)

end IdlaCyl.GffSeq.Gff
