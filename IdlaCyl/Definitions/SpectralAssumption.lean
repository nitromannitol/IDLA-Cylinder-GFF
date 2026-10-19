/-
Assumption `a:spectral` from Bou-Rabee, Silvestri, Yadin,
*Gaussian fluctuations for Internal DLA on cylinders*,
`paper/idla-cylinder-gff.tex`, lines 323-326, as printed in the paper:

  "For each fixed integer $k \geq 2$, the $k$-th eigenvalue
   $2a_N^2(1 - \l_k(N))$ of $L_N$ converges to a finite positive limit
   $\g_k^2 \in (0, +\infty)$. Equivalently,
     \[ \lim_{N\to\infty} a_N \sqrt{2(1-\l_k(N))} = \g_k \in (0, +\infty)\,. \]"

This is an assumption of the paper, not a theorem. The results that use it take
it as a hypothesis: `Setup.SpectralAssumption` for the modes `2 ≤ k ≤ K` that a
given result needs, and `a_spectral` below for all modes `k ≥ 2`. It does not
hold for every setup and every `γ`: the zero sequence refutes `a_spectral`
(`not_a_spectral_zero`).
-/

import IdlaCyl.Support.Spectral

namespace IdlaCyl.Defs

/-- Assumption `a:spectral` (tex:323-326), for every mode k ≥ 2. -/
def a_spectral (U : Setup) (γ : ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 2 ≤ k → U.GammaLimit γ k ∧ 0 < γ k

/-- The finite-mode form: `a_spectral` gives `Setup.SpectralAssumption` for each `K`. -/
theorem a_spectral.spectralAssumption {U : Setup} {γ : ℕ → ℝ} (h : a_spectral U γ) (K : ℕ) :
    U.SpectralAssumption γ K := by
  intro k hk _
  exact h k hk

/-- `a_spectral` holds exactly when every finite-mode form holds. -/
theorem a_spectral_iff_forall_spectralAssumption (U : Setup) (γ : ℕ → ℝ) :
    a_spectral U γ ↔ ∀ K, U.SpectralAssumption γ K :=
  ⟨fun h K => a_spectral.spectralAssumption h K, fun h k hk => h k k hk le_rfl⟩

/-- Nonvacuity: the zero sequence refutes `a_spectral` for every setup, since `0 < γ 2` fails. -/
theorem not_a_spectral_zero (U : Setup) : ¬ a_spectral U (fun _ => 0) :=
  fun h => lt_irrefl (0 : ℝ) (h 2 le_rfl).2

/-- Nonvacuity: the restriction at `K = 2` is the normalisation `eq:aN` (tex:318-320). -/
example {U : Setup} {γ : ℕ → ℝ} (h : a_spectral U γ) : U.NormalisedAt γ :=
  a_spectral.spectralAssumption h 2 2 le_rfl le_rfl

end IdlaCyl.Defs
