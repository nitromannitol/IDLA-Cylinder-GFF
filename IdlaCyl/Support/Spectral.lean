module

/-
The spectrum of the base kernel, the mixing time, and the paper's standing
spectral assumption.

`paper/idla-cylinder-gff.tex:301-311`:

  "`P_N` has `N` real eigenvalues `1 = λ_1(N) > λ_2(N) ≥ ⋯ ≥ λ_N(N) ≥ 0` where
   strict inequality `λ_2(N) < 1` comes from irreducibility and the lower bound
   `λ_N(N) ≥ 0` comes from laziness.  Denote the corresponding real
   eigenvectors by `{f^N_j : 1 ≤ j ≤ N}`.  The eigenvectors can be taken to be
   an orthonormal basis of `ℝ^{V_N}` with respect to the *normalised*
   counting-measure inner product `⟨f,g⟩ := (1/N) ∑_x f(x) g(x)`."

`paper/idla-cylinder-gff.tex:313-321` (the rescaled operator `L_N`, `eq:aN`)
and `tex:323-326` (`Assumption a:spectral`).

## Indexing

The paper indexes eigenvalues and eigenvectors by `1 ≤ k ≤ N`.  That indexing
is kept *literally* here: `lam : ℕ → ℝ` and `f : ℕ → V → ℝ`, with every axiom
of `SpectralData` restricted to `1 ≤ k ≤ N`.  Values outside that range are
unconstrained and no statement in this development may depend on them.  The
alternative, `Fin N`, would shift every index in `Theorem th:GFF` by one and
is exactly the kind of silent reindexing a correspondence audit exists to
catch.

`SpectralData` is a hypothesis, not a construction: the paper asserts the
diagonalisation and then uses it.  That such data exists for every `Base` is
the separate obligation `IdlaCyl.spectralData_exists`.
-/
public import IdlaCyl.Support.Cylinder
public import Mathlib

@[expose] public section

namespace IdlaCyl

open Filter
open scoped BigOperators Topology

/-! ### The spectrum of the base kernel -/

/-- A diagonalisation of the base kernel `P_N` in the paper's own indexing
(`tex:301-311`): eigenvalues `λ_1 … λ_N` in non-increasing order with
`λ_1 = 1` and `λ_N ≥ 0`, and eigenvectors `f_1 … f_N` orthonormal for the
normalised counting-measure inner product `⟨f,g⟩ = (1/N) ∑_x f(x) g(x)`. -/
structure SpectralData (B : Base) where
  /-- The eigenvalues, indexed as in the paper by `1 ≤ k ≤ N`. -/
  lam : ℕ → ℝ
  /-- The eigenvectors, indexed as in the paper by `1 ≤ k ≤ N`. -/
  f : ℕ → B.V → ℝ
  /-- `P_N f_k = λ_k f_k` for `1 ≤ k ≤ N`. -/
  eigen : ∀ k, 1 ≤ k → k ≤ B.card → ∀ x : B.V,
    ∑ x' : B.V, B.P x x' * f k x' = lam k * f k x
  /-- The eigenvectors are orthonormal for `⟨f,g⟩ = (1/N) ∑_x f(x) g(x)`
  (`tex:305-308`, equation `eq:product`). -/
  orthonormal : ∀ j k, 1 ≤ j → j ≤ B.card → 1 ≤ k → k ≤ B.card →
    (1 / (B.card : ℝ)) * ∑ x : B.V, f j x * f k x = if j = k then 1 else 0
  /-- `λ_1 = 1` (`tex:303`). -/
  lam_one : lam 1 = 1
  /-- `f_1 ≡ 1` (`tex:392`, "`f_1^N ≡ 1` is the constant function"). -/
  f_one : ∀ x : B.V, f 1 x = 1
  /-- The eigenvalues are non-increasing (`tex:303`). -/
  antitone : ∀ j k, 1 ≤ j → j ≤ k → k ≤ B.card → lam k ≤ lam j
  /-- `λ_2 < 1`, from irreducibility (`tex:303-304`). -/
  lam_two_lt : 2 ≤ B.card → lam 2 < 1
  /-- `λ_N ≥ 0`, from laziness (`tex:303-304`). -/
  lam_nonneg : ∀ k, 1 ≤ k → k ≤ B.card → 0 ≤ lam k

namespace SpectralData

variable {B : Base} (S : SpectralData B)

/-- The spectral gap `1 - λ_2(N)` (`tex:309`). -/
def gap : ℝ := 1 - S.lam 2

/-- The relaxation time `τ_rel = 1/(1 - λ_2(N))` (`tex:309-311`). -/
noncomputable def relaxTime : ℝ := 1 / S.gap

/-- The rescaled operator `L_N = 2 a_N^2 (I - P_N)` acting on eigenvalues
(`tex:313-316`, `def:LN`): the `k`-th eigenvalue of `L_N` is
`2 a_N^2 (1 - λ_k)`. -/
def rescaledEigenvalue (a : ℝ) (k : ℕ) : ℝ := 2 * a ^ 2 * (1 - S.lam k)

/-- The positive root of `cosh(q_k) = 2 - λ_k` (`def:qk`, `tex:717-721`), via
Mathlib's `Real.arcosh`. -/
noncomputable def qk (k : ℕ) : ℝ := Real.arcosh (2 - S.lam k)

/-- `q_k > 0` for `k ≥ 2` (`tex:718-721`): irreducibility gives `λ_k < 1`, so
`2 - λ_k > 1`. -/
theorem qk_pos {k : ℕ} (hk : 2 ≤ k) (hkN : k ≤ B.card) : 0 < S.qk k := by
  have hlt : S.lam k < 1 := by
    have h2 : S.lam 2 < 1 := S.lam_two_lt (by omega)
    exact lt_of_le_of_lt (S.antitone 2 k (by omega) hk hkN) h2
  exact Real.arcosh_pos (by linarith)

/-- `cosh(q_k) = 2 - λ_k` (`def:qk`), for every `1 ≤ k ≤ N` (where `λ_k ≤ 1`). -/
theorem cosh_qk {k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ B.card) :
    Real.cosh (S.qk k) = 2 - S.lam k := by
  have hle : S.lam k ≤ 1 := by
    calc S.lam k ≤ S.lam 1 := S.antitone 1 k le_rfl hk hkN
      _ = 1 := S.lam_one
  exact Real.cosh_arcosh (by linarith)

end SpectralData

/-! ### The mixing time -/

/-- The `t`-step base kernel `P_N^t`. -/
noncomputable def basePow (B : Base) : ℕ → B.V → B.V → ℝ
  | 0, x, x' => if x = x' then 1 else 0
  | t + 1, x, x' => ∑ z : B.V, basePow B t x z * B.P z x'

/-- The total variation distance from `P_N^t(x, ·)` to the uniform
distribution `π_N`, written `‖P_N^t(x,·) - π_N‖_TV` in the paper. -/
noncomputable def tvToUniform (B : Base) (t : ℕ) (x : B.V) : ℝ :=
  (1 / 2) * ∑ x' : B.V, |basePow B t x x' - 1 / (B.card : ℝ)|

/-- The total variation mixing time of `P_N` at threshold `1/4` (`tex:269`):
"the smallest integer `t ≥ 0` with `max_x ‖P_N^t(x,·) - π_N‖_TV ≤ 1/4`".

`sInf` on `ℕ` returns `0` when the set is empty; that the set is nonempty is
the obligation `mixingTime_spec`. -/
noncomputable def mixingTime (B : Base) : ℕ :=
  sInf {t : ℕ | ∀ x : B.V, tvToUniform B t x ≤ 1 / 4}

/-! ### The sequence of bases and the standing assumption -/

/-- `log_+(s) = max(log s, 0)` (`tex:270`). -/
noncomputable def logPlus (s : ℝ) : ℝ := max (Real.log s) 0

/-- A sequence of bases together with the normalising sequence `a_N` and the
spectral data, as the paper sets them up in `tex:229` and `tex:313-321`.

`a_spec` is the paper's `eq:aN`, `a_N √(2(1-λ_2(N))) → γ_2 ∈ (0,∞)`; the
`Assumption a:spectral` itself is the separate predicate `SpectralAssumption`
below, because `Theorem th:max_fluct` does *not* assume it and only
`Theorem th:GFF` does. -/
structure Setup extends BaseSeq where
  /-- A diagonalisation of each `P_N` (`tex:301-311`). -/
  S : ∀ N, SpectralData (B N)
  /-- The normalising sequence `a_N` (`tex:317`). -/
  a : ℕ → ℝ
  /-- `a_N > 0` (`tex:317`). -/
  a_pos : ∀ N, 0 < a N
  /-- `a_N → ∞` (`tex:317`). -/
  a_tendsto : Tendsto a atTop atTop

namespace Setup

variable (U : Setup)

/-- The paper's `γ_k`, the limit of `a_N √(2(1-λ_k(N)))` (`tex:319`, `tex:325`).
It is a *parameter* of the assumption, not a definition, so it is carried
explicitly wherever it is used. -/
def GammaLimit (γ : ℕ → ℝ) (k : ℕ) : Prop :=
  Tendsto (fun N => U.a N * Real.sqrt (2 * (1 - (U.S N).lam k))) atTop (𝓝 (γ k))

/-- `eq:aN` (`tex:318-320`): `a_N √(2(1-λ_2(N))) → γ_2 ∈ (0,∞)`. -/
def NormalisedAt (γ : ℕ → ℝ) : Prop := U.GammaLimit γ 2 ∧ 0 < γ 2

/-- `Assumption a:spectral` (`tex:323-326`), stated for the modes `2 ≤ k ≤ K`
that a given test function uses:

  "For each fixed integer `k ≥ 2`, the `k`-th eigenvalue `2a_N^2(1 - λ_k(N))`
   of `L_N` converges to a finite positive limit `γ_k^2 ∈ (0,+∞)`.
   Equivalently, `lim_N a_N √(2(1-λ_k(N))) = γ_k ∈ (0,+∞)`."

`Theorem th:GFF` assumes it "for each `2 ≤ k ≤ K`" (`tex:404`), so the range
is a parameter here rather than being baked in as `∀ k ≥ 2`. -/
def SpectralAssumption (γ : ℕ → ℝ) (K : ℕ) : Prop :=
  ∀ k, 2 ≤ k → k ≤ K → U.GammaLimit γ k ∧ 0 < γ k

/-- The growth condition `a_N ≫ log N + log_+ a_N` (`tex:321`, `tex:405`),
read as `(log N + log_+ a_N) / a_N → 0`. -/
def GrowthCondition : Prop :=
  Tendsto (fun N : ℕ => (Real.log N + logPlus (U.a N)) / U.a N) atTop (𝓝 0)

end Setup

end IdlaCyl
