module

/-
The cylinder `G_N = V_N × ℤ`, its walk kernel, and the half-cylinders `R_k`.

`paper/idla-cylinder-gff.tex:239-256`:

  "We construct IDLA on the cylinder graph `G_N := V_N × ℤ = {(x,y) : x ∈ V_N,
   y ∈ ℤ}` ... The cylinder walk on `G_N` is the discrete-time Markov chain
   with transition kernel `P_N((x,y);(x',y')) = 1/4` if `x = x'` and
   `|y - y'| = 1` (vertical step), `= (1/2) P_N(x,x')` if `y = y'` (horizontal
   step), `= 0` otherwise.  The vertical coordinate has zero drift and makes a
   step with probability `1/2`, independently of the horizontal structure."

`paper/idla-cylinder-gff.tex:261-262`:

  "For each real number `k`, let `R_k` denote the infinite half-cylinder of
   height `k` given by `R_k := {(x,y) ∈ G_N : y ≤ k}`."

`R_k` takes a *real* `k` because the paper evaluates it at `T/N`, which is not
an integer.  `Site` is a plain product; the cylinder is not presented as a
`SimpleGraph` because the walk is lazy and a simple graph cannot hold a
holding probability.
-/
public import IdlaCyl.Support.Base

@[expose] public section

namespace IdlaCyl

open scoped BigOperators

variable (B : Base)

/-- A site of the cylinder `G_N = V_N × ℤ` (`tex:241`).  The first coordinate
is the paper's horizontal coordinate `x`, the second its vertical `y`. -/
abbrev Site : Type := B.V × ℤ

/-- The base vertex set is finite, so the discrete σ-algebra is the only
sensible one; it makes every subset of `Site B = V_N × ℤ` measurable. -/
instance instMeasurableSpaceV (B : Base) : MeasurableSpace B.V := ⊤

instance instMeasurableSingletonV (B : Base) : MeasurableSingletonClass B.V :=
  ⟨fun _ => trivial⟩

namespace Site

variable {B}

/-- The horizontal coordinate `x` of a site (`tex:243`). -/
def hor (p : Site B) : B.V := p.1

/-- The vertical coordinate `y` of a site (`tex:243`). -/
def ver (p : Site B) : ℤ := p.2

end Site

/-- The cylinder walk kernel `𝒫_N` (`tex:246-255`, equation `def:SRW`):
`1/4` for a vertical step, `(1/2) P_N(x,x')` for a horizontal one, `0`
otherwise.  The two branches do not overlap: a vertical step changes `y`. -/
noncomputable def cylKernel (p q : Site B) : ℝ :=
  if p.1 = q.1 ∧ (p.2 - q.2).natAbs = 1 then 1 / 4
  else if p.2 = q.2 then (1 / 2) * B.P p.1 q.1
  else 0

/-- The half-cylinder of height `k` (`tex:261-262`):
`R_k = {(x,y) ∈ G_N : y ≤ k}`.  `k` is real, as in the paper. -/
def R (k : ℝ) : Set (Site B) := {p : Site B | (p.2 : ℝ) ≤ k}

variable {B}

@[simp] theorem mem_R {k : ℝ} {p : Site B} : p ∈ R B k ↔ (p.2 : ℝ) ≤ k := Iff.rfl

/-- The half-cylinders increase in their height. -/
theorem R_mono {j k : ℝ} (h : j ≤ k) : R B j ⊆ R B k :=
  fun _ hp => le_trans hp h

/-- Every entry of the cylinder kernel is nonnegative. -/
theorem cylKernel_nonneg (p q : Site B) : 0 ≤ cylKernel B p q := by
  unfold cylKernel
  split_ifs
  · norm_num
  · exact mul_nonneg (by norm_num) (B.P_nonneg _ _)
  · exact le_refl 0

/-- A sequence of base graphs, `V_N` on `N` vertices (`tex:229`).  The
maximal-fluctuation theorem needs only this; the spectral data and the
normalising sequence `a_N` are extra structure carried by `Setup`. -/
structure BaseSeq where
  /-- The base graph on `N` vertices. -/
  B : ℕ → Base
  /-- `V_N` has `N` vertices (`tex:229`). -/
  card_eq : ∀ N, 2 ≤ N → (B N).card = N

end IdlaCyl
