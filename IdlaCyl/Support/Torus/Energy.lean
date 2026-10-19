/-
Exact rescaled energies and fixed-frequency limits for the torus.
Source: tex:502-507, `paper/idla-cylinder-gff.tex`.
-/
import IdlaCyl.Support.Torus.Spectrum
import IdlaCyl.Support.Torus.Shells
import IdlaCyl.Support.Cycle.Limit

namespace IdlaCyl.TorusSpectrum
open Filter
open scoped BigOperators Topology

/-- Reduction of an integer frequency modulo the side length. -/
def frequency (d n : ℕ) (m : Fin d → ℤ) : Fin d → ZMod n := fun i => (m i : ZMod n)

/-- The squared rescaled spectral parameter at an integer frequency. -/
noncomputable def energy (d n : ℕ) (m : Fin d → ℤ) : ℝ :=
  (2 / (d : ℝ)) * ∑ i, (Real.pi * (m i : ℝ) * Real.sinc (Real.pi * (m i : ℝ) / n)) ^ 2

lemma cos_cast (n : ℕ) [NeZero n] (a : ℤ) :
    Real.cos (2 * Real.pi * ((a : ZMod n).val : ℝ) / n) =
      Real.cos (2 * Real.pi * (a : ℝ) / n) := by
  have hi : ZMod.stdAddChar (a : ZMod n) =
      Complex.exp ((2 * Real.pi * (a : ℝ) / n : ℝ) * Complex.I) := by
    rw [ZMod.stdAddChar_coe]
    push_cast
    congr 1
    ring
  have h := congrArg Complex.re ((character_exp n (a : ZMod n)).symm.trans hi)
  simpa only [Complex.exp_ofReal_mul_I_re] using h

lemma mul_sin_eq_sinc (n : ℕ) [NeZero n] (a : ℤ) :
    (n : ℝ) * Real.sin (Real.pi * (a : ℝ) / n) =
      Real.pi * (a : ℝ) * Real.sinc (Real.pi * (a : ℝ) / n) := by
  rw [← CycleSpectrum.mul_sinc (Real.pi * (a : ℝ) / n)]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp

lemma energy_sin (d n : ℕ) [NeZero n] (m : Fin d → ℤ) :
    energy d n m = (2 / (d : ℝ)) * ∑ i, ((n : ℝ) * Real.sin (Real.pi * (m i : ℝ) / n)) ^ 2 := by
  simp only [energy, mul_sin_eq_sinc]

lemma energy_value (d n : ℕ) [NeZero n] (hd : 1 ≤ d) (m : Fin d → ℤ) :
    energy d n m = (n : ℝ) ^ 2 * (2 * (1 - value d n (frequency d n m))) := by
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcos (a : ℤ) : Real.cos (2 * Real.pi * (a : ℝ) / n) =
      1 - 2 * Real.sin (Real.pi * (a : ℝ) / n) ^ 2 := by
    rw [show 2 * Real.pi * (a : ℝ) / n = 2 * (Real.pi * (a : ℝ) / n) by ring,
      Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * (a : ℝ) / n)]
  rw [energy_sin]
  simp only [value, frequency, cos_cast, hcos, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    ← Finset.mul_sum, mul_pow]
  field_simp
  ring

lemma normSq_cast (d : ℕ) (m : Fin d → ℤ) :
    (normSq d m : ℝ) = ∑ i, (m i : ℝ) ^ 2 := by
  simp only [normSq, Nat.cast_sum, Nat.cast_pow, Nat.cast_natAbs, Int.cast_abs, sq_abs]

/-- The fixed-frequency squared spectral limit, before sorting. -/
theorem energy_limit (d : ℕ) (m : Fin d → ℤ) :
    Tendsto (fun n : ℕ => energy d (n + 3) m) atTop
      (𝓝 ((2 * Real.pi ^ 2 / d) * normSq d m)) := by
  have hN : Tendsto (fun n : ℕ => ((n + 3 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 3)
  have hi (i : Fin d) : Tendsto
      (fun n : ℕ => (Real.pi * (m i : ℝ) * Real.sinc (Real.pi * (m i : ℝ) / ((n + 3 : ℕ) : ℝ))) ^ 2)
      atTop (𝓝 ((Real.pi * (m i : ℝ)) ^ 2)) := by
    have hx := hN.const_div_atTop (Real.pi * (m i : ℝ))
    have hs := Real.continuous_sinc.continuousAt.tendsto.comp hx
    simpa only [Function.comp_apply, Real.sinc_zero, mul_one] using
      (hs.const_mul (Real.pi * (m i : ℝ))).pow 2
  have hsum := (tendsto_finsetSum Finset.univ (fun i _ => hi i)).const_mul (2 / (d : ℝ))
  have heq : (2 / (d : ℝ)) * ∑ i, (Real.pi * (m i : ℝ)) ^ 2 =
      (2 * Real.pi ^ 2 / d) * normSq d m := by
    rw [normSq_cast]
    simp only [mul_pow, ← Finset.mul_sum]
    ring
  rw [heq] at hsum
  exact hsum

lemma sine_sq_natAbs (n : ℕ) (a : ℤ) :
    Real.sin (Real.pi * (a : ℝ) / n) ^ 2 =
      Real.sin (Real.pi * (a.natAbs : ℝ) / n) ^ 2 := by
  have habs : (a.natAbs : ℝ) = |(a : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [habs]
  by_cases ha : 0 ≤ (a : ℝ)
  · rw [abs_of_nonneg ha]
  · rw [abs_of_neg (lt_of_not_ge ha), mul_neg, neg_div, Real.sin_neg, neg_sq]

lemma coordinate_energy_lower (n : ℕ) [NeZero n] (a : ℤ)
    (ha : 2 * a.natAbs ≤ n) :
    4 * (a.natAbs : ℝ) ^ 2 ≤ ((n : ℝ) * Real.sin (Real.pi * (a : ℝ) / n)) ^ 2 := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have haR : 2 * (a.natAbs : ℝ) ≤ n := by exact_mod_cast ha
  have hx : Real.pi * (a.natAbs : ℝ) / n ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hn).mpr
    nlinarith [mul_le_mul_of_nonneg_left haR Real.pi_pos.le]
  have hs := Real.mul_le_sin (by positivity : 0 ≤ Real.pi * (a.natAbs : ℝ) / n) hx
  have hs' : 2 * (a.natAbs : ℝ) ≤ (n : ℝ) * Real.sin (Real.pi * (a.natAbs : ℝ) / n) := by
    have heq : 2 / Real.pi * (Real.pi * (a.natAbs : ℝ) / n) =
        2 * (a.natAbs : ℝ) / n := by field_simp
    rw [heq, div_le_iff₀ hn] at hs
    simpa only [mul_comm] using hs
  rw [mul_pow, sine_sq_natAbs]
  nlinarith [sq_nonneg ((n : ℝ) * Real.sin (Real.pi * (a.natAbs : ℝ) / n) - 2 * (a.natAbs : ℝ)),
    sq_nonneg ((n : ℝ) * Real.sin (Real.pi * (a.natAbs : ℝ) / n) + 2 * (a.natAbs : ℝ))]

/-- A global confinement estimate on centered torus frequencies. -/
theorem energy_lower (d n : ℕ) [NeZero n] (hd : 1 ≤ d) (m : Fin d → ℤ)
    (hm : ∀ i, 2 * (m i).natAbs ≤ n) :
    (8 / (d : ℝ)) * normSq d m ≤ energy d n m := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
    coordinate_energy_lower n (m i) (hm i))
  rw [← Finset.mul_sum] at hs
  have h := mul_le_mul_of_nonneg_left hs (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hdR.le)
  rw [energy_sin]
  have hnorm : (normSq d m : ℝ) = ∑ i, ((m i).natAbs : ℝ) ^ 2 := by
    simp only [normSq, Nat.cast_sum, Nat.cast_pow]
  rw [hnorm]
  calc
    (8 / (d : ℝ)) * (∑ i, ((m i).natAbs : ℝ) ^ 2) =
        (2 / (d : ℝ)) * (4 * ∑ i, ((m i).natAbs : ℝ) ^ 2) := by ring
    _ ≤ _ := h

/-- The canonical centered representative of a torus frequency. -/
def centered (d n : ℕ) (m : Fin d → ZMod n) : Fin d → ℤ := fun i => (m i).valMinAbs

lemma frequency_centered (d n : ℕ) (m : Fin d → ZMod n) :
    frequency d n (centered d n m) = m := by
  funext i
  exact ZMod.coe_valMinAbs (m i)

lemma centered_injective (d n : ℕ) : Function.Injective (centered d n) := by
  intro m l h
  have heq := congrArg (frequency d n) h
  simpa only [frequency_centered] using heq

lemma centered_bound (d n : ℕ) [NeZero n] (m : Fin d → ZMod n) (i : Fin d) :
    2 * (centered d n m i).natAbs ≤ n := by
  have h := ZMod.natAbs_valMinAbs_le (m i)
  change 2 * (m i).valMinAbs.natAbs ≤ n
  omega

lemma centered_frequency (d n R : ℕ) [NeZero n] (hn : 2 * R < n)
    (m : Fin d → ℤ) (hm : m ∈ latticeBall d R) :
    centered d n (frequency d n m) = m := by
  funext i
  apply (ZMod.valMinAbs_spec _ _).mpr
  refine ⟨rfl, ?_⟩
  have hi := coord_natAbs_le d R m ((mem_latticeBall d R m).mp hm) i
  have habs : |m i| ≤ (R : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hi
  have hnR : 2 * (R : ℤ) < n := by exact_mod_cast hn
  rcases abs_le.mp habs with ⟨hlo, hhi⟩
  constructor <;> linarith

lemma frequency_injOn_ball (d n R : ℕ) [NeZero n] (hn : 2 * R < n) :
    Set.InjOn (frequency d n) (latticeBall d R) := by
  intro m hm l hl h
  have heq := congrArg (centered d n) h
  rwa [centered_frequency d n R hn m hm, centered_frequency d n R hn l hl] at heq

lemma gamma_pos (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : 2 ≤ k) :
    0 < Real.pi * Real.sqrt (2 / (d : ℝ)) * Real.sqrt (shell d hd k) := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  exact mul_pos (mul_pos Real.pi_pos (Real.sqrt_pos.mpr (div_pos (by norm_num) hdR)))
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (shell_pos d hd k hk)))

end IdlaCyl.TorusSpectrum
