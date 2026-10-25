module

/-
The rectangular quadratic mass `W_N` and the objects it is built from
(`paper/idla-cylinder-gff.tex:755-758`, `:904`, `:407`, `:401`).

Each declaration is the printed formula.  The paper's symbols are read as
follows: `a_N = U.a N`, `T = N ⌊y₀ a_N⌋`, and `q_k = (U.S N).qk k` is the
un-rescaled rate, so that the paper's `q_k^N = a_N q_k` (`tex:750-752`).
-/
public import IdlaCyl.Support.Spectral
public import IdlaCyl.Support.Discrepancy

@[expose] public section

namespace IdlaCyl.Defs

open scoped Topology BigOperators

/-- The reference height `h = T/N = ⌊y₀ a_N⌋` (`tex:1045`). -/
noncomputable def height (U : Setup) (y₀ : ℝ) (N : ℕ) : ℕ :=
  Nat.floor (y₀ * U.a N)

/-- The time `T = N ⌊y₀ a_N⌋` (`tex:1045`), so that `T/N = height`. -/
noncomputable def time (U : Setup) (y₀ : ℝ) (N : ℕ) : ℕ :=
  (U.B N).card * height U y₀ N

/-- The harmonic extension of the mode sum with coefficients `α_k(h/a)`:
`∑_{k=2}^K α_k(h/a) f_k(x) e^{q_k (y-h)}` (`tex:755-758`).  The coefficient is
`α_k(T/(N a_N))` and the exponent `q_k^N (y - T/N)/a_N` equals `q_k (y - h)`. -/
noncomputable def harmAt (B : Base) (S : SpectralData B) (a : ℝ)
    (h : ℤ) (K : ℕ) (α : ℕ → ℝ → ℝ) (p : Site B) : ℝ :=
  ∑ k ∈ Finset.Icc 2 K,
    α k ((h : ℝ) / a) * S.f k p.1 *
      Real.exp (S.qk k * ((p.2 : ℝ) - (h : ℝ)))

/-- The discrete harmonic extension `ψ` of the test function from the line
`y = T/N`, that is `harmAt` at reference height `⌊y₀ a_N⌋` (`tex:755-758`,
`eq:truepsi`). -/
noncomputable def psi (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ)
    (y₀ : ℝ) (N : ℕ) : Site (U.B N) → ℝ :=
  harmAt (U.B N) (U.S N) (U.a N) (height U y₀ N : ℤ) K α

/-- The rectangular quadratic mass `W_N = (1/(N a_N)) ∑_{R_{T/N} \ R_0} |ψ|²`
(`tex:904`), where the rectangle is `V_N × {1, …, ⌊T/N⌋}`. -/
noncomputable def wmass (U : Setup) (K : ℕ) (α : ℕ → ℝ → ℝ)
    (y₀ : ℝ) (N : ℕ) : ℝ :=
  1 / (((U.B N).card : ℝ) * U.a N) *
    ∑ p ∈ rectangleFinset (U.B N) (time U y₀ N), (psi U K α y₀ N p) ^ 2

/-- The limiting variance `σ²(φ) = ∑_{k=2}^K α_k(y₀)² (1 - e^{-2γ_k y₀})/(2γ_k)`
(`tex:407`, and the limit displayed at `tex:1062`). -/
noncomputable def variance (K : ℕ) (α : ℕ → ℝ → ℝ)
    (γ : ℕ → ℝ) (y₀ : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 K,
    (α k y₀) ^ 2 * (1 - Real.exp (-2 * γ k * y₀)) / (2 * γ k)

/-- The coefficient regularity of `th:GFF`: for `2 ≤ k ≤ K`, `α_k` is
differentiable on a neighbourhood of `y₀` with bounded derivative there
(`tex:401`). -/
def regular (α : ℕ → ℝ → ℝ) (K : ℕ) (y₀ : ℝ) : Prop :=
  ∀ k, 2 ≤ k → k ≤ K → ∃ s ∈ 𝓝 y₀,
    (∀ y ∈ s, DifferentiableAt ℝ (α k) y) ∧
    ∃ M : ℝ, ∀ y ∈ s, |deriv (α k) y| ≤ M

end IdlaCyl.Defs
