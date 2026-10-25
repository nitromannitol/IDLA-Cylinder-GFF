module

public import IdlaCyl.Support.CanonicalIdla
public import IdlaCyl.Support.Cylinder
public import IdlaCyl.Support.PrInnerStopped.Composition
public import IdlaCyl.Support.PrInnerTail.Nonvacuity
public import IdlaCyl.Support.Spectral
public import IdlaCyl.Support.Stopped

@[expose] public section

/-!
# `pr:inner`: the inner tail bound for the stopped IDLA process

Proposition `pr:inner`, verbatim from *Gaussian fluctuations for Internal DLA on cylinders*
(Bou-Rabee, Silvestri, Yadin), `tex:1160-1166`:

> For every $\n > 0$ there exist constants $C_1 = C_1(\n) < \infty$ and $K_0 = K_0(\n) < \infty$ such that, for every integer $T \geq K_0 N\log N$ and with
> \[ \ell_* \coloneqq C_1 \sqrt{\frac{T}{N}\Big( \log N + \log_+\!\big(T/N\big)\Big)}\,, \qquad h \coloneqq \Big\lfloor \frac{T}{N} - \ell_* \Big\rfloor\,, \]
> the IDLA process $(A(t))_{t \leq T}$ on $V_N \times \bbZ$ starting from $A(0) = R_0$ satisfies $h \geq 1$ and
> \[ \bbP \big( A(T) \not\supseteq R_h \big) \leq \bbP\!\big( \bar A_h(T) \not\supseteq R_h \big) \leq N^{-(\n+1)} \]
> for $N$ large enough.

The Lean statement reads this as: for constants $C_1$ and $K_0$ depending only on $\nu$, and for every family of bases $B_N$ with $N$ vertices for $N \geq 2$, there is a cutoff $N_0$ such that every $N \geq N_0$ and every integer $T \geq K_0 N \log N$ give $h \geq 1$ and the printed chain, with $A(T)$ the cluster `clusterTraj (B N) ω T` and $\bar A_h(T)$ the stopped cluster `stoppedCluster (B N) h ω T`.

The proof takes $C_1 = 2\sqrt{\nu+4}$, $K_0 = 16 C_1^2$ and cutoff $\max\, 2\, \lceil 256 C_1^4 + 1 \rceil_+$, and transports `IdlaCyl.pr_inner_probability_bound` along $|B_N| = N$.
-/

namespace IdlaCyl.Frozen

-- FROZEN-STATEMENT-BEGIN
theorem pr_inner_stopped (ν : ℝ) (hν : 0 < ν) :
    ∃ C₁ K₀ : ℝ, ∀ B : ℕ → Base, (∀ N : ℕ, 2 ≤ N → (B N).card = N) →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ T : ℕ,
        K₀ * (N : ℝ) * Real.log (N : ℝ) ≤ (T : ℝ) →
        (let ℓ : ℝ :=
            C₁ * Real.sqrt (((T : ℝ) / (N : ℝ)) *
              (Real.log (N : ℝ) + logPlus ((T : ℝ) / (N : ℝ))));
         let h : ℤ := Int.floor ((T : ℝ) / (N : ℝ) - ℓ);
         (1 : ℤ) ≤ h ∧
           idlaMeasure (B N) {ω : TrajSeq (B N) | ¬ (R (B N) (h : ℝ) ⊆ clusterTraj (B N) ω T)} ≤
             idlaMeasure (B N)
               {ω : TrajSeq (B N) | ¬ (R (B N) (h : ℝ) ⊆ stoppedCluster (B N) h ω T)} ∧
           idlaMeasure (B N)
               {ω : TrajSeq (B N) | ¬ (R (B N) (h : ℝ) ⊆ stoppedCluster (B N) h ω T)} ≤
             ENNReal.ofReal ((N : ℝ) ^ (-(ν + 1))))
-- FROZEN-STATEMENT-END
:= by
  refine ⟨2 * Real.sqrt (ν + 4), 16 * (2 * Real.sqrt (ν + 4)) ^ 2, ?_⟩
  intro B hcard
  refine ⟨max 2 ⌈256 * (2 * Real.sqrt (ν + 4)) ^ 4 + 1⌉₊, ?_⟩
  intro N hN T hT
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNc : ⌈256 * (2 * Real.sqrt (ν + 4)) ^ 4 + 1⌉₊ ≤ N := (le_max_right _ _).trans hN
  have hNr : 256 * (2 * Real.sqrt (ν + 4)) ^ 4 + 1 ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr hNc)
  have hcardN : ((B N).card : ℝ) = (N : ℝ) := by rw [hcard N hN2]
  have hNr' : 256 * (2 * Real.sqrt (ν + 4)) ^ 4 + 1 ≤ ((B N).card : ℝ) := by
    rw [hcardN]
    exact hNr
  have hT' : 16 * (2 * Real.sqrt (ν + 4)) ^ 2 * ((B N).card : ℝ) * Real.log ((B N).card : ℝ)
      ≤ (T : ℝ) := by
    rw [hcardN]
    exact hT
  dsimp only
  rw [← hcardN]
  exact IdlaCyl.pr_inner_probability_bound (B N) ν hν hNr' T hT' _ rfl

-- Nonvacuity of the family hypothesis: the complete graphs on `max N 2` vertices have `N`
-- vertices for every `N ≥ 2`, so the family is not vacuous.
example : ∃ B : ℕ → Base, ∀ N : ℕ, 2 ≤ N → (B N).card = N :=
  ⟨fun N => IdlaCyl.PrInnerTail.completeBase (max N 2) (le_max_right N 2), fun N hN => by
    show Fintype.card (Fin (max N 2)) = N
    rw [Fintype.card_fin, max_eq_left hN]⟩

end IdlaCyl.Frozen
