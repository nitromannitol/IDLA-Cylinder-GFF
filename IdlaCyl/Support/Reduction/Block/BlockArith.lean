module

public import IdlaCyl.Support.Reduction.ReductionTrace
public import IdlaCyl.Support.Reduction.TraceGlue
public import IdlaCyl.Definitions.ShapeEvent

@[expose] public section

/-!
Arithmetic of the block reduction. The restart of `reduction_trace` at block
size `N * H` and step `2 * (N * H)` gives a finite trace whose steps are at least
three blocks long, whose last time is below `6 * (N * H)`, and whose total volume
is `T`. For the block height `H = ⌈B₀ √τ log N⌉₊` the summed errors are at most
`N ^ (-p)`, the per-block tail is at most `N ^ (-γ)` when `N * H ≤ N ^ q`, and the
block time is at most `α` times the sharp threshold `N √τ (log N)²` once
`log N ≥ 6 (B₀ + 1) / α`. Pure real and natural arithmetic, no probability.
-/

namespace IdlaCyl.Reduction

/-- Telescoping of a trace with block size `N`: the last time plus `N` times the
total length equals the first time. -/
theorem block_telescope (N : ℕ) : ∀ (R : ℕ) (t : Fin (R + 1) → ℕ) (ℓ : Fin R → ℕ),
    (∀ i : Fin R, t i.succ + N * ℓ i = t i.castSucc) →
    t (Fin.last R) + N * ∑ i, ℓ i = t 0
  | 0, t, ℓ, _ => by simp
  | R + 1, t, ℓ, h => by
    have ih := block_telescope N R (fun i => t i.succ) (fun i => ℓ i.succ)
      (fun i => h i.succ)
    have h0 := h 0
    simp only [Fin.succ_last, Fin.castSucc_zero, Nat.succ_eq_add_one] at ih h0 ⊢
    rw [Fin.sum_univ_succ, mul_add]
    omega

/-- The block trace: `reduction_trace` at block size `N * H`, step `2 * (N * H)`
and `β = 1`, with the consequences used by the block gluing. -/
theorem block_trace (N H T : ℕ) (hN : 0 < N) (hH : 0 < H) (hT : 0 < T) :
    ∃ R : ℕ, ∃ t : Fin (R + 1) → ℕ, ∃ ℓ : Fin R → ℕ,
      t 0 = T ∧ (∀ i, 0 < t i ∧ t i ≤ T) ∧
      (∀ i : Fin R, 3 ≤ ℓ i ∧ ℓ i = t i.castSucc / (2 * (N * H)) ∧
        t i.succ + (N * H) * ℓ i = t i.castSucc) ∧
      1 ≤ t (Fin.last R) ∧ t (Fin.last R) < 6 * (N * H) ∧
      t (Fin.last R) + (N * H) * ∑ i, ℓ i = T ∧
      ∑ i, ℓ i ≤ T / (N * H) ∧ R ≤ T / (N * H) := by
  have hNH : 0 < N * H := Nat.mul_pos hN hH
  obtain ⟨R, t, ℓ, h0, htimes, hsteps, hterm, hR⟩ :=
    reduction_trace (N * H) (2 * (N * H)) 1 T hNH (by omega) one_pos hT
  have hlast : t (Fin.last R) < 6 * (N * H) := by
    have h := (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * (N * H))).mp hterm
    omega
  have hvol := block_telescope (N * H) R t ℓ (fun i => (hsteps i).2.2)
  rw [h0] at hvol
  have hsum : ∑ i, ℓ i ≤ T / (N * H) := by
    rw [Nat.le_div_iff_mul_le hNH, Nat.mul_comm]
    omega
  refine ⟨R, t, ℓ, h0, htimes, fun i => ⟨by simpa using (hsteps i).1,
    (hsteps i).2.1, (hsteps i).2.2⟩, (htimes _).1, hlast, hvol, hsum, hR⟩

/-- Error sum over a block trace: with per-block errors at most `N ^ (-γ)`,
`γ = p + q + 1`, and total volume at most `N ^ q`, the summed errors are at most
`N ^ (-p)`. -/
theorem block_error_sum {R : ℕ} (ℓ : Fin R → ℕ) (T N H q : ℕ) (p γ f e : ℝ)
    (hN : 2 ≤ N) (hℓ : ∀ i, 3 ≤ ℓ i)
    (hsum : ∑ i, ℓ i ≤ T / (N * H)) (hT : T ≤ N ^ q) (hγ : γ = p + q + 1)
    (hf : f ≤ (N : ℝ) ^ (-γ)) (he : e ≤ (N : ℝ) ^ (-γ)) :
    ∑ i, (((ℓ i : ℝ) + 1) * f + 2 * e) ≤ (N : ℝ) ^ (-p) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set c : ℝ := (N : ℝ) ^ (-γ) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg hNpos.le _
  -- each block contributes at most `(ℓ i + 3) c`
  have hterm : ∀ i, ((ℓ i : ℝ) + 1) * f + 2 * e ≤ ((ℓ i : ℝ) + 3) * c := by
    intro i
    have h1 : ((ℓ i : ℝ) + 1) * f ≤ ((ℓ i : ℝ) + 1) * c :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    have h2 : 2 * e ≤ 2 * c := by linarith
    nlinarith
  have hS : ∑ i, ((ℓ i : ℝ) + 3) * c ≤ 2 * (∑ i, (ℓ i : ℝ)) * c := by
    rw [← Finset.sum_mul]
    apply mul_le_mul_of_nonneg_right _ hc0
    have h3 : ∑ _i : Fin R, (3 : ℝ) ≤ ∑ i, (ℓ i : ℝ) :=
      Finset.sum_le_sum fun i _ => by exact_mod_cast hℓ i
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3 ⊢
    linarith
  have hSN : ∑ i, (ℓ i : ℝ) ≤ (N : ℝ) ^ q := by
    have h1 : ∑ i, ℓ i ≤ T := hsum.trans (Nat.div_le_self _ _)
    have h2 : ((∑ i, ℓ i : ℕ) : ℝ) ≤ ((N ^ q : ℕ) : ℝ) := by
      exact_mod_cast h1.trans hT
    push_cast at h2
    simpa using h2
  have hS0 : 0 ≤ ∑ i, (ℓ i : ℝ) := Finset.sum_nonneg fun i _ => by positivity
  have hfin : 2 * (∑ i, (ℓ i : ℝ)) * c ≤ 2 * (N : ℝ) ^ q * c := by
    apply mul_le_mul_of_nonneg_right _ hc0
    linarith
  -- `N ^ q * N ^ (-γ) = N ^ (-p) / N`
  have hkey : (N : ℝ) ^ q * c = (N : ℝ) ^ (-p) / N := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_add hNpos, ← Real.rpow_sub_one hNpos.ne']
    congr 1
    rw [hγ]
    ring
  have hX : 0 ≤ (N : ℝ) ^ (-p) := Real.rpow_nonneg hNpos.le _
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  calc ∑ i, (((ℓ i : ℝ) + 1) * f + 2 * e)
      ≤ ∑ i, ((ℓ i : ℝ) + 3) * c := Finset.sum_le_sum fun i _ => hterm i
    _ ≤ 2 * (∑ i, (ℓ i : ℝ)) * c := hS
    _ ≤ 2 * (N : ℝ) ^ q * c := hfin
    _ = 2 * ((N : ℝ) ^ (-p) / N) := by rw [mul_assoc, hkey]
    _ ≤ (N : ℝ) ^ (-p) := by
      rw [← mul_div_assoc, div_le_iff₀ hNpos]
      nlinarith

/-- The per-block tail: with `H = ⌈B₀ √τ log N⌉₊`, `τ ≥ 1`, `log N ≥ 1`,
`B₀ ≥ 8 (γ + q)` and `N * H ≤ N ^ q`, one has `N H e^{-H/8} ≤ N^{-γ}`. -/
theorem block_tail_le (N H q : ℕ) (B₀ τ γ : ℝ) (hB₀ : 0 ≤ B₀) (hτ : 1 ≤ τ)
    (hlog : 1 ≤ Real.log N) (hγB : 8 * (γ + q) ≤ B₀)
    (hH : H = ⌈B₀ * Real.sqrt τ * Real.log N⌉₊) (hNH : (N : ℝ) * H ≤ (N : ℝ) ^ q) :
    (N : ℝ) * H * Real.exp (-((H : ℝ) / 8)) ≤ (N : ℝ) ^ (-γ) := by
  have hNpos : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; norm_num at hlog
    · exact_mod_cast h
  have hsq : 1 ≤ Real.sqrt τ := Real.one_le_sqrt.mpr hτ
  have hx : 0 ≤ B₀ * Real.sqrt τ * Real.log N := by
    have : 0 ≤ Real.log N := by linarith
    positivity
  have hHx : B₀ * Real.sqrt τ * Real.log N ≤ (H : ℝ) := by
    rw [hH]
    exact Nat.le_ceil _
  have hB_log : B₀ * Real.log N ≤ (H : ℝ) := by
    have h1 : B₀ * Real.log N * 1 ≤ B₀ * Real.log N * Real.sqrt τ :=
      mul_le_mul_of_nonneg_left hsq (mul_nonneg hB₀ (by linarith))
    nlinarith
  -- `H / 8 ≥ (γ + q) log N`, hence `exp (-H/8) ≤ N ^ (-(γ + q))`
  have hexp : Real.exp (-((H : ℝ) / 8)) ≤ (N : ℝ) ^ (-(γ + q)) := by
    rw [Real.rpow_def_of_pos hNpos]
    apply Real.exp_le_exp.mpr
    nlinarith
  calc (N : ℝ) * H * Real.exp (-((H : ℝ) / 8))
      ≤ (N : ℝ) ^ q * Real.exp (-((H : ℝ) / 8)) :=
        mul_le_mul_of_nonneg_right hNH (Real.exp_nonneg _)
    _ ≤ (N : ℝ) ^ q * (N : ℝ) ^ (-(γ + q)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (N : ℝ) ^ (-γ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hNpos]
        congr 1
        ring

/-- The block time against the sharp threshold: with `H = ⌈B₀ √τ log N⌉₊`,
`6 N H ≤ α · N √τ (log N)²` once `log N ≥ 6 (B₀ + 1) / α`. -/
theorem block_time_le_sharp (N H : ℕ) (B₀ τ α : ℝ) (hB₀ : 0 ≤ B₀) (hτ : 1 ≤ τ)
    (hlog : 1 ≤ Real.log N) (hα : 0 < α) (hlogα : 6 * (B₀ + 1) / α ≤ Real.log N)
    (hH : H = ⌈B₀ * Real.sqrt τ * Real.log N⌉₊) :
    6 * ((N : ℝ) * H) ≤ α * ((N : ℝ) * Real.sqrt τ * (Real.log N) ^ 2) := by
  have hNpos : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; norm_num at hlog
    · exact_mod_cast h
  have hsq : 1 ≤ Real.sqrt τ := Real.one_le_sqrt.mpr hτ
  have hL0 : 0 ≤ Real.log N := by linarith
  have hK : 1 ≤ Real.sqrt τ * Real.log N := by nlinarith
  have hx : 0 ≤ B₀ * Real.sqrt τ * Real.log N := by positivity
  have hHle : (H : ℝ) ≤ (B₀ + 1) * (Real.sqrt τ * Real.log N) := by
    have h1 : (H : ℝ) < B₀ * Real.sqrt τ * Real.log N + 1 := by
      rw [hH]
      exact Nat.ceil_lt_add_one hx
    nlinarith
  have hα6 : 6 * (B₀ + 1) ≤ α * Real.log N := by
    rw [div_le_iff₀ hα] at hlogα
    linarith
  set K : ℝ := (N : ℝ) * Real.sqrt τ * Real.log N with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hHK : 6 * ((N : ℝ) * H) ≤ 6 * (B₀ + 1) * K := by
    have : (N : ℝ) * H ≤ (N : ℝ) * ((B₀ + 1) * (Real.sqrt τ * Real.log N)) :=
      mul_le_mul_of_nonneg_left hHle hNpos.le
    rw [hKdef]
    nlinarith
  have hfin : 6 * (B₀ + 1) * K ≤ α * Real.log N * K :=
    mul_le_mul_of_nonneg_right hα6 hK0
  calc 6 * ((N : ℝ) * H) ≤ 6 * (B₀ + 1) * K := hHK
    _ ≤ α * Real.log N * K := hfin
    _ = α * ((N : ℝ) * Real.sqrt τ * (Real.log N) ^ 2) := by
        rw [hKdef]; ring

/-- The block time against `Defs.sharp B`, for the base `B` with `N = B.card` and
`τ = mixingTime B` (`tex:273`). -/
theorem block_time_le_sharp_base (B : Base) (H : ℕ) (B₀ α : ℝ) (hB₀ : 0 ≤ B₀)
    (hτ : 1 ≤ (mixingTime B : ℝ)) (hlog : 1 ≤ Real.log (B.card : ℝ))
    (hα : 0 < α) (hlogα : 6 * (B₀ + 1) / α ≤ Real.log (B.card : ℝ))
    (hH : H = ⌈B₀ * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ)⌉₊) :
    6 * ((B.card : ℝ) * H) ≤ α * Defs.sharp B := by
  unfold Defs.sharp
  exact block_time_le_sharp B.card H B₀ (mixingTime B) α hB₀ hτ hlog hα hlogα hH

end IdlaCyl.Reduction
