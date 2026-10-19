/-
Uniform parameters and finite iteration of the raw-layer reduction.
Source: paper/idla-cylinder-gff.tex, tex:270-282,1119-1136,1440-1453;
The finite coefficient and cutoff precede the base and time.
-/
import IdlaCyl.Support.Reduction.RoundAssembly
import IdlaCyl.Support.Reduction.ReductionTrace
import IdlaCyl.Support.Reduction.TraceVolume
import IdlaCyl.Support.Reduction.TraceErrorBudget
import IdlaCyl.Support.Reduction.TraceGlue
import IdlaCyl.Support.Reduction.MixingScale

namespace IdlaCyl.Reduction

open MeasureTheory
open scoped BigOperators

/-- The manuscript reduction scale is strictly positive for every legitimate base. -/
theorem reduction_sharp_pos (B : Base) : 0 < Defs.sharp B := by
  have hN : (0 : ℝ) < B.card := card_real_pos B
  have hτ : (0 : ℝ) < mixingTime B := by exact_mod_cast manuscript_mixing_pos B
  have hlog : 0 < Real.log (B.card : ℝ) :=
    Real.log_pos (by exact_mod_cast ((by decide : 1 < 2).trans_le B.nontrivial))
  unfold Defs.sharp
  positivity

/-- The iterated endpoint coupling has a finite uniform coefficient and the final error budget. -/
theorem reduced_cluster_coupling (hsil : External.silvestri_prop2)
    (ν m : ℝ) (hν : 0 < ν) (hm : 1 ≤ m) :
    ∃ α : ℝ, 0 < α ∧ ∃ N₀ : ℕ, ∀ B : Base,
      N₀ ≤ B.card → ∀ T : ℕ, 0 < T → (T : ℝ) ≤ (B.card : ℝ) ^ m →
        ∃ T' k : ℕ, 1 ≤ T' ∧ (T' : ℝ) ≤ α * Defs.sharp B ∧
          T' + B.card * k = T ∧
          ClusterCoupling B (flatClusterLaw B T) (flatClusterLaw B T') k
            ((B.card : ℝ) ^ (-(ν + 1))) := by
  let r := ⌈m⌉₊
  have hmr : m ≤ (r : ℝ) := Nat.le_ceil m
  have hrR : (1 : ℝ) ≤ r := hm.trans hmr
  have hr : 1 ≤ r := by exact_mod_cast hrR
  let p := ν + (r : ℝ) + 2
  let q := ν + 2 * (r : ℝ) + 1
  let a := q + 1
  have hp : 0 < p := by dsimp only [p]; linarith
  have ha : 2 ≤ a := by dsimp only [a, q]; linarith
  obtain ⟨b, hb, N₁, hround⟩ := one_round hsil r p hp
  let α := 3 * (a + 1) * (b + 1)
  have hα : 0 < α := by dsimp only [α]; positivity
  refine ⟨α, hα, max N₁ ⌈Real.exp 1⌉₊, ?_⟩
  intro B hN T hT hTm
  have hcard : 0 < B.card := lt_of_lt_of_le (by decide : 0 < 2) B.nontrivial
  have hcardR : (0 : ℝ) < B.card := card_real_pos B
  have hcardOne : (1 : ℝ) ≤ B.card := by exact_mod_cast ((by decide : 1 ≤ 2).trans B.nontrivial)
  have hcut : ⌈Real.exp 1⌉₊ ≤ B.card := (le_max_right _ _).trans hN
  have hlog : 1 ≤ Real.log (B.card : ℝ) :=
    (Real.le_log_iff_exp_le hcardR).mpr ((Nat.le_ceil _).trans (by exact_mod_cast hcut))
  have hτ : (1 : ℝ) ≤ mixingTime B := by exact_mod_cast manuscript_mixing_pos B
  have hsqrt : 1 ≤ Real.sqrt (mixingTime B) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hτ
  let M := ⌈a * (B.card : ℝ) * Real.log (B.card : ℝ)⌉₊
  let β := ⌈b * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ)⌉₊
  have hMcast : 2 * (B.card : ℝ) ≤ (M : ℝ) := by
    calc
      _ ≤ a * (B.card : ℝ) := mul_le_mul_of_nonneg_right ha hcardR.le
      _ ≤ a * (B.card : ℝ) * Real.log (B.card : ℝ) :=
        le_mul_of_one_le_right (by positivity) hlog
      _ ≤ (M : ℝ) := Nat.le_ceil _
  have hM : 2 * B.card ≤ M := by exact_mod_cast hMcast
  have hβcast : (1 : ℝ) ≤ β :=
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hb hsqrt) hlog).trans (Nat.le_ceil _)
  have hβ : 0 < β := by
    have : 1 ≤ β := by exact_mod_cast hβcast
    omega
  have hbuf : b * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ) ≤ (β : ℝ) := Nat.le_ceil _
  have hcoupon : (q + 1) * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (M : ℝ) := Nat.le_ceil _
  have hscale := rounded_scale B a b ha hb hlog
  change ((3 * β * M : ℕ) : ℝ) ≤ α * Defs.sharp B at hscale
  have hTr : T ≤ B.card ^ r := by
    have hh := hTm.trans (Real.rpow_le_rpow_of_exponent_le hcardOne hmr)
    rw [Real.rpow_natCast] at hh
    exact_mod_cast hh
  obtain ⟨R, t, ℓ, hzero, htimes, hsteps, hterm, hR⟩ :=
    reduction_trace B.card M β T hcard (by omega) hβ hT
  let ε := fun i : Fin R => roundError B p q (ℓ i) β
  have hε (i : Fin R) : 0 ≤ ε i := by dsimp only [ε, roundError]; positivity
  have hc (i : Fin R) : ClusterCoupling B
      (flatClusterLaw B (t i.castSucc)) (flatClusterLaw B (t i.succ)) (ℓ i) (ε i) := by
    have hi := hsteps i
    have hgo : 3 * β ≤ t i.castSucc / M := by rw [← hi.2.1]; exact hi.1
    have hh := hround B ((le_max_left _ _).trans hN) M β (t i.castSucc) q hM hβ hbuf
      hcoupon (htimes i.castSucc).1 ((htimes i.castSucc).2.trans hTr) hgo
    have hnext : t i.succ = t i.castSucc - B.card * (t i.castSucc / M) := by
      rw [← hi.2.1]
      omega
    rw [← hnext] at hh
    simpa only [← hi.2.1] using hh
  have hglue := glue_flat_trace B R t ℓ ε hε hc
  have hbudget := trace_error_budget B M β T R r t ℓ ν (by omega) hr hTr
    (fun i => (htimes i).2) (fun i => ⟨(hsteps i).2.1, (hsteps i).1⟩) hR
  have hvol := trace_volume B.card R t ℓ (fun i => (hsteps i).2.2)
  rw [hzero] at hvol
  have hterminal : t (Fin.last R) < 3 * β * M :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < M)).mp hterm
  refine ⟨t (Fin.last R), ∑ i, ℓ i, (htimes (Fin.last R)).1,
    (show (t (Fin.last R) : ℝ) ≤ ((3 * β * M : ℕ) : ℝ) by exact_mod_cast hterminal.le).trans
      hscale, hvol, ?_⟩
  have hh := clusterCoupling_mono B (flatClusterLaw B (t 0))
    (flatClusterLaw B (t (Fin.last R))) (∑ i, ℓ i) (∑ i, ε i)
    ((B.card : ℝ) ^ (-(ν + 1))) hbudget hglue
  simpa only [hzero] using hh

end IdlaCyl.Reduction
