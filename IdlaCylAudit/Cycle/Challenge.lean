module

public import Mathlib

@[expose] public section

/-!
# The cycle example: comparator challenge

Mathlib-only comparator challenge for `thm:cycle` (`paper/idla-cylinder-gff.tex:486-494`), as the library states it in
`IdlaCyl.Frozen.thm_cycle_v3` (`IdlaCyl/Frozen/ThmCycleV3.lean`).

On the cycles `ℤ_N`, with `a_N = N` and `γ_k = √2 π ⌊k/2⌋`, the Gaussian limit of Theorem 1.3
holds for every choice of eigenbases, every `K ≥ 2` and coefficients `α_k` that are
differentiable with bounded derivative.

Only `Mathlib` is imported. The vocabulary between `VOCABULARY-BEGIN` and `VOCABULARY-END`
rebuilds, token for token and under the namespace `IdlaCylAudit` in place of `IdlaCyl`, the
library's model of the paper: the base graph `Base` and its lazy walk `Base.P`, the cylinder
walk kernel `cylKernel` and its law, the canonical IDLA driving law `idlaMeasure` (independent
walks started uniformly on layer `0`), the clusters `clusterTraj`, the half-cylinders `R`, the
mixing time, the spectral data, the test functions and the limiting variance, and the cycle and
torus bases. All four challenges share this block. The sole intentional `sorry` is the proof of
the final theorem.
-/

-- VOCABULARY-BEGIN
/-! ### From `IdlaCyl/Support/Base.lean` -/
namespace IdlaCylAudit
open scoped BigOperators
/-- A finite, connected, vertex-transitive base graph.  The paper's `V_N`;
`N` is `Fintype.card V`.

`vertexTransitive` says the automorphism group acts transitively on vertices,
which is the paper's definition (`tex:229`).  `nontrivial` records `N ≥ 2`,
also from `tex:229`; without it the degree is `0` and the lazy kernel is junk. -/
structure Base where
  /-- The vertex set. -/
  V : Type
  [fintypeV : Fintype V]
  [decEqV : DecidableEq V]
  /-- The adjacency relation, written `∼` in the paper. -/
  graph : SimpleGraph V
  [decRel : DecidableRel graph.Adj]
  /-- `V_N` is connected (`tex:229`). -/
  connected : graph.Connected
  /-- `V_N` is vertex-transitive: `Aut(V_N)` acts transitively (`tex:229`). -/
  vertexTransitive : ∀ x y : V, ∃ σ : graph ≃g graph, σ x = y
  /-- `N ≥ 2` (`tex:229`). -/
  nontrivial : 2 ≤ Fintype.card V

namespace Base
attribute [instance] Base.fintypeV Base.decEqV Base.decRel
variable (B : Base)
instance : Nonempty B.V := by
  have : 0 < Fintype.card B.V := lt_of_lt_of_le (by norm_num) B.nontrivial
  exact Fintype.card_pos_iff.mp this

/-- `N`, the number of vertices (`tex:229`). -/
def card : ℕ := Fintype.card B.V

/-- An arbitrary but fixed base point, used only to name the common degree. -/
noncomputable def pt : B.V := Classical.arbitrary B.V

/-- The paper's common degree `d = d(N)` (`tex:229`).  `degree_eq` shows it is
the degree of every vertex, so the choice of `pt` is immaterial. -/
noncomputable def deg : ℕ := B.graph.degree B.pt

/-- Vertex-transitivity makes the degree common to all vertices: the paper's
"every vertex has a common degree `d`" (`tex:229`). -/
theorem degree_eq (x : B.V) : B.graph.degree x = B.deg := by
  obtain ⟨σ, hσ⟩ := B.vertexTransitive x B.pt
  have h := SimpleGraph.Iso.degree_eq σ x
  rw [hσ] at h
  unfold deg
  omega

/-- The degree is positive: a connected graph on at least two vertices has no
isolated vertex.  Needed before `1/(2d)` is anything but a junk value. -/
theorem deg_pos : 0 < B.deg := by
  have h1 : 1 < Fintype.card B.V := lt_of_lt_of_le (by norm_num) B.nontrivial
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card h1 B.pt
  obtain ⟨w⟩ := B.connected.preconnected B.pt y
  cases w with
  | nil => exact absurd rfl hy
  | cons h _ =>
      have hpos : 0 < B.graph.degree B.pt :=
        (B.graph.degree_pos_iff_exists_adj B.pt).mpr ⟨_, h⟩
      simpa [deg] using hpos

/-- The lazy simple random walk kernel `P_N` on the base (`tex:230-236`,
equation `eq:PN`):
`P x x' = 1/(2d)` if `x ∼ x'`, `1/2` if `x = x'`, and `0` otherwise. -/
noncomputable def P (x x' : B.V) : ℝ :=
  if B.graph.Adj x x' then 1 / (2 * B.deg)
  else if x = x' then 1 / 2
  else 0

/-- Every entry of `P_N` is nonnegative. -/
theorem P_nonneg (x x' : B.V) : 0 ≤ B.P x x' := by
  unfold P
  split_ifs <;> positivity

/-- `P_N` is stochastic: rows sum to one (`tex:237`, "doubly stochastic"). -/
theorem P_row_sum (x : B.V) : ∑ x' : B.V, B.P x x' = 1 := by
  classical
  have hsplit :
      ∑ x' : B.V, B.P x x'
        = ∑ x' ∈ B.graph.neighborFinset x, B.P x x' + B.P x x := by
    rw [← Finset.sum_subset (Finset.subset_univ (insert x (B.graph.neighborFinset x)))]
    · rw [Finset.sum_insert (by simp [SimpleGraph.mem_neighborFinset])]
      ring
    · intro y _ hy
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset, not_or] at hy
      unfold P
      simp [hy.2, Ne.symm hy.1]
  have hnb : ∑ x' ∈ B.graph.neighborFinset x, B.P x x'
      = (B.deg : ℝ) * (1 / (2 * B.deg)) := by
    rw [Finset.sum_congr rfl (fun y hy => ?_), Finset.sum_const, nsmul_eq_mul,
      SimpleGraph.card_neighborFinset_eq_degree, B.degree_eq]
    · simp [SimpleGraph.mem_neighborFinset] at hy
      unfold P
      simp [hy]
  have hd : (B.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr B.deg_pos.ne'
  have hxx : B.P x x = 1 / 2 := by unfold P; simp
  rw [hsplit, hnb, hxx]
  field_simp
  norm_num

end Base
end IdlaCylAudit

/-! ### From `IdlaCyl/Support/CycleBase.lean` -/
namespace IdlaCylAudit
open SimpleGraph
/-- The rotation `x ↦ x + c` of `Fin N` as a graph automorphism of the cycle `cycleGraph N`.
Adjacency is `u - v = 1 ∨ v - u = 1`, and this is invariant under a common translation. -/
def cycleRot {N : ℕ} [NeZero N] (c : Fin N) : cycleGraph N ≃g cycleGraph N where
  toEquiv := Equiv.addRight c
  map_rel_iff' := by
    intro u v
    simp only [Equiv.coe_addRight, cycleGraph_adj', add_sub_add_right_eq_sub]

/-- The cycle base `ℤ_N` for `N ≥ 3` (`tex:474-475`): finite, connected, vertex-transitive, with
`N` vertices. The paper's `N ≥ 2` is narrowed to `N ≥ 3`, as explained in the header. -/
def cycleBase (N : ℕ) (hN : 3 ≤ N) : Base where
  V := Fin N
  graph := cycleGraph N
  connected := by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 3 := ⟨N - 3, by omega⟩
    exact cycleGraph_connected
  vertexTransitive := by
    intro x y
    haveI : NeZero N := ⟨by omega⟩
    refine ⟨cycleRot (y - x), ?_⟩
    show x + (y - x) = y
    simp
  nontrivial := by
    rw [Fintype.card_fin]
    omega

end IdlaCylAudit

/-! ### From `IdlaCyl/Support/Cylinder.lean` -/
namespace IdlaCylAudit
open scoped BigOperators
variable (B : Base)
/-- A site of the cylinder `G_N = V_N × ℤ` (`tex:241`).  The first coordinate
is the paper's horizontal coordinate `x`, the second its vertical `y`. -/
abbrev Site : Type := B.V × ℤ

/-- The base vertex set is finite, so the discrete σ-algebra is the only
sensible one; it makes every subset of `Site B = V_N × ℤ` measurable. -/
instance instMeasurableSpaceV (B : Base) : MeasurableSpace B.V := ⊤

namespace Site
variable {B}
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

end IdlaCylAudit

/-! ### From `IdlaCyl/Support/Canonical.lean` -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace IdlaCylAudit
variable (B : Base)
/-- The one-step law of the cylinder walk from `p`, as a measure on sites: the
weights are the paper's kernel `cylKernel` (`tex:246-255`). -/
noncomputable def cylMeasure (p : Site B) : Measure (Site B) :=
  Measure.sum (fun q : Site B => ENNReal.ofReal (cylKernel B p q) • Measure.dirac q)

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

/-- The Ionescu-Tulcea transition family of the homogeneous cylinder walk: the
kernel at time `n` reads the position at time `n` from the past. -/
noncomputable def cylITKernel :
    (n : ℕ) → Kernel (Π _ : Finset.Iic n, Site B) (Site B) :=
  fun n => Kernel.ofFunOfCountable
    (fun x => cylMeasure B (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩))

instance cylITKernel_isMarkov : ∀ n, IsMarkovKernel (cylITKernel B n) :=
  fun n => ⟨fun x => cylMeasure_isProbability B (x ⟨n, Finset.mem_Iic.mpr le_rfl⟩)⟩

end IdlaCylAudit

/-! ### From `IdlaCyl/Support/Exit.lean` -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace IdlaCylAudit
variable (B : Base)
/-- `τ_S = inf{k ≥ 0 : X_k ∉ S}`, `⊤` if the walk never leaves. -/
noncomputable def exitTime' (B : Base) (S : Set (Site B)) : (ℕ → Site B) → ℕ∞ :=
  MeasureTheory.hittingAfter (fun (k : ℕ) (X : ℕ → Site B) => X k) Sᶜ 0

/-- The exit location, the paper's `(X_t, Y_t)` (`tex:265`). -/
noncomputable def exitSite' (B : Base) (S : Set (Site B)) : (ℕ → Site B) → Site B :=
  MeasureTheory.stoppedValue (fun (k : ℕ) (X : ℕ → Site B) => X k) (exitTime' B S)

end IdlaCylAudit

/-! ### From `IdlaCyl/Support/CanonicalIdla.lean` -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace IdlaCylAudit
/-- A sequence of independent walk trajectories, indexed by the order they are released
(`tex:1402`, "`ω = (ω_1, ω_2, …)`"). -/
abbrev TrajSeq (B : Base) : Type := ℕ → (ℕ → Site B)

/-- The uniform law on layer `k` of the cylinder (`tex:265`, "chosen uniformly from
`V_N × {0}`", generalised to an arbitrary layer so `walkLawUniform` can be obtained by
induction from `walkLawUniformAt`). -/
noncomputable def layerLawAt (B : Base) (k : ℤ) : Measure (Site B) :=
  Measure.sum fun x : B.V => ((B.card : ℝ≥0∞))⁻¹ • Measure.dirac ((x, k) : Site B)

/-- The law of a cylinder walk started uniformly on layer `k` (generalisation of
`walkLawUniform`, needed for the induction underlying `walkLawUniformAt_eq_bind`). -/
noncomputable def walkLawUniformAt (B : Base) (k : ℤ) : Measure (ℕ → Site B) :=
  ProbabilityTheory.Kernel.trajMeasure (layerLawAt B k) (cylITKernel B)

/-- The law of a cylinder walk started uniformly on layer `0` (`tex:265`). -/
noncomputable def walkLawUniform (B : Base) : Measure (ℕ → Site B) := walkLawUniformAt B 0

/-- `idlaMeasure` is the paper's driving law of independent cylinder walks, each started
uniformly on layer `0` (`tex:265`): the law of `Ã^{(m)}` at `m = ∞` before any site is
prescribed. -/
noncomputable def idlaMeasure (B : Base) : Measure (TrajSeq B) :=
  Measure.infinitePi fun _ : ℕ => walkLawUniform B

/-- `Φ_k(𝓑)` (`tex:1406-1410`): the cluster from seed `S` after `k` prescribed walks have
settled. -/
noncomputable def clusterFrom (B : Base) (S : Set (Site B)) (ω : TrajSeq B) :
    ℕ → Set (Site B)
  | 0 => S
  | k + 1 => clusterFrom B S ω k ∪ {exitSite' B (clusterFrom B S ω k) (ω k)}

/-- `A(t)`, the IDLA cluster from the flat configuration (`tex:263-265`). -/
noncomputable def clusterTraj (B : Base) (ω : TrajSeq B) (t : ℕ) : Set (Site B) :=
  clusterFrom B (R B 0) ω t

end IdlaCylAudit

/-! ### From `IdlaCyl/Support/Discrepancy.lean` -/
namespace IdlaCylAudit
open MeasureTheory
open scoped BigOperators
variable (B : Base)
/-- The discrepancy function `D_t = 1_{A(t)} - 1_{R_{t/N}}` (`tex:348-351`). -/
noncomputable def discrepancyTraj (ω : TrajSeq B) (t : ℕ) (p : Site B) : ℝ :=
  (clusterTraj B ω t).indicator (fun _ => (1 : ℝ)) p
    - (R B ((t : ℝ) / B.card)).indicator (fun _ => (1 : ℝ)) p

/-- The pairing `⟪D_t, f⟫ = ∑_{(x,y)} D_t(x,y) f(x,y)` (`tex:363-366`).  Written
as a `finsum`; `discrepancyTraj_support_finite` makes it the paper's finite
sum.  Downstream code must define the martingale `M(t)` by a `Finset.range`
sum, never by this `finsum`; `pairingTraj_eq_sum` converts between them. -/
noncomputable def pairingTraj (ω : TrajSeq B) (t : ℕ) (f : Site B → ℝ) : ℝ :=
  ∑ᶠ p : Site B, discrepancyTraj B ω t p * f p

end IdlaCylAudit

/-! ### From `IdlaCyl/Support/Spectral.lean` -/
namespace IdlaCylAudit
open Filter
open scoped BigOperators Topology
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
end SpectralData
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
end IdlaCylAudit

/-! ### From `IdlaCyl/Definitions/RectangularMass.lean` -/
namespace IdlaCylAudit.Defs
open scoped Topology BigOperators
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

end IdlaCylAudit.Defs

/-! ### From `IdlaCyl/Definitions/ShapeEvent.lean` -/
namespace IdlaCylAudit.Defs
/-- The threshold `T^♯ = N √τ_mix (log N)²` (`tex:273`). -/
noncomputable def sharp (B : Base) : ℝ :=
  (B.card : ℝ) * Real.sqrt (mixingTime B) * (Real.log (B.card : ℝ)) ^ 2

/-- The width `Δ_N = C max{log N, √((T ∧ T^♯)/N · (log N + log₊(T/N)))}` at time
`T` (`tex:273`), with `T ∧ T^♯` read as `min T (sharp B)`. -/
noncomputable def delta (B : Base) (C : ℝ) (T : ℕ) : ℝ :=
  C * max (Real.log (B.card : ℝ))
    (Real.sqrt ((min (T : ℝ) (sharp B) / (B.card : ℝ)) *
      (Real.log (B.card : ℝ) + logPlus ((T : ℝ) / (B.card : ℝ)))))

/-- The event of `eq:fluct` (`tex:275-277`), `R_{⌊T/N - d⌋} ⊆ A(T) ⊆ R_{T/N + d}`,
with the floor kept as printed. -/
noncomputable def eventAt (B : Base) (T : ℕ) (d : ℝ) : Set (TrajSeq B) :=
  {ω | R B ((Int.floor ((T : ℝ) / (B.card : ℝ) - d) : ℤ) : ℝ)
      ⊆ clusterTraj B ω T ∧
    clusterTraj B ω T ⊆ R B ((T : ℝ) / (B.card : ℝ) + d)}

end IdlaCylAudit.Defs

/-! ### From `IdlaCyl/Definitions/TestFunction.lean` -/
namespace IdlaCylAudit.Defs
open scoped BigOperators
/-- The literal rescaled test function `∑_{k=2}^K α_k(y/a_N) f_k^N(x)`
(`tex:787`, `tex:805-810`). -/
noncomputable def testAt (B : Base) (S : SpectralData B) (a : ℝ)
    (K : ℕ) (α : ℕ → ℝ → ℝ) (p : Site B) : ℝ :=
  ∑ k ∈ Finset.Icc 2 K, α k ((p.2 : ℝ) / a) * S.f k p.1

end IdlaCylAudit.Defs

/-! ### From `IdlaCyl/Support/Cycle/Setup.lean` -/
namespace IdlaCylAudit
open Filter
open scoped Topology
namespace CycleSpectrum
/-- The connected two-vertex base used at the finite prefix of `Setup`. -/
def pairBase : Base where
  V := Fin 2
  graph := ⊤
  connected := SimpleGraph.connected_top
  vertexTransitive := by
    intro x y
    refine ⟨{ toEquiv := Equiv.swap x y, map_rel_iff' := ?_ }, ?_⟩
    · intro u v
      simp only [SimpleGraph.top_adj, (Equiv.swap x y).injective.ne_iff]
    · exact Equiv.swap_apply_left x y
  nontrivial := by norm_num

/-- A base with exactly `N` vertices for every `N ≥ 2`, eventually the cycle. -/
def indexedBase (N : ℕ) : Base :=
  if hN : 3 ≤ N then cycleBase N hN else pairBase

end CycleSpectrum
namespace CycleSpectrum
end CycleSpectrum
end IdlaCylAudit

/-! ### From `IdlaCyl/Support/Torus/Shells.lean` -/
namespace IdlaCylAudit.TorusSpectrum
open scoped BigOperators
/-- Squared Euclidean norm on the integer frequency lattice. -/
def normSq (d : ℕ) (m : Fin d → ℤ) : ℕ := ∑ i, (m i).natAbs ^ 2

lemma coord_natAbs_le (d R : ℕ) (m : Fin d → ℤ) (hm : normSq d m ≤ R) (i : Fin d) :
    (m i).natAbs ≤ R := by
  have hi : (m i).natAbs ^ 2 ≤ normSq d m := by
    unfold normSq
    exact Finset.single_le_sum (fun j _ => Nat.zero_le ((m j).natAbs ^ 2)) (Finset.mem_univ i)
  have hsq : (m i).natAbs ≤ (m i).natAbs ^ 2 := Nat.le_self_pow (by omega) _
  exact hsq.trans (hi.trans hm)

/-- The complete finite sublevel set of the lattice norm; the box is only an implementation. -/
noncomputable def latticeBall (d R : ℕ) : Finset (Fin d → ℤ) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(R : ℤ)) R)).filter (fun m => normSq d m ≤ R)

lemma mem_latticeBall (d R : ℕ) (m : Fin d → ℤ) :
    m ∈ latticeBall d R ↔ normSq d m ≤ R := by
  rw [latticeBall, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hm
    refine ⟨Fintype.mem_piFinset.mpr (fun i => ?_), hm⟩
    apply Finset.mem_Icc.mpr
    apply abs_le.mp
    rw [← Int.natCast_natAbs]
    exact_mod_cast coord_natAbs_le d R m hm i

lemma normSq_single (d : ℕ) (i : Fin d) (a : ℤ) :
    normSq d (Pi.single i a) = a.natAbs ^ 2 := by
  simp only [normSq, Pi.single_apply, apply_ite (fun z : ℤ => z.natAbs ^ 2),
    Int.natAbs_zero, zero_pow (by omega : 2 ≠ 0), Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma latticeBall_card_unbounded (d : ℕ) (hd : 1 ≤ d) (k : ℕ) :
    ∃ R, k ≤ (latticeBall d R).card := by
  let i : Fin d := ⟨0, hd⟩
  refine ⟨k ^ 2, ?_⟩
  have hinj : Function.Injective (fun j : ℕ => (Pi.single i (j : ℤ) : Fin d → ℤ)) := by
    intro a b h
    have h' := congrFun h i
    simpa only [Pi.single_eq_same, Int.natCast_inj] using h'
  have hs : (Finset.range k).image (fun j : ℕ => (Pi.single i (j : ℤ) : Fin d → ℤ)) ⊆
      latticeBall d (k ^ 2) := by
    intro m hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
    rw [mem_latticeBall, normSq_single, Int.natAbs_natCast]
    exact Nat.pow_le_pow_left (Finset.mem_range.mp hj).le 2
  have hc := Finset.card_le_card hs
  rwa [Finset.card_image_of_injective _ hinj, Finset.card_range] at hc

/-- The one-based ordered squared norms, with full lattice multiplicity.
The value at index zero is also defined by the same certified minimum. -/
noncomputable def shell (d : ℕ) (hd : 1 ≤ d) (k : ℕ) : ℕ :=
  Nat.find (latticeBall_card_unbounded d hd k)

end IdlaCylAudit.TorusSpectrum

/-! ### From `IdlaCyl/Support/TorusBase.lean` -/
namespace IdlaCylAudit
/-- `1 ≠ 0` in `ℤ/N` for `N ≥ 3`. -/
theorem torus_one_ne_zero {N : ℕ} (hN : 3 ≤ N) : (1 : ZMod N) ≠ 0 := by
  intro h
  have h' : ((1 : ℕ) : ZMod N) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have := Nat.le_of_dvd Nat.one_pos h'
  omega

/-- Nearest-neighbour adjacency on `(ℤ/N)^d`, the torus `ℤ_n^d` of `tex:502-514`:
`x ∼ y` iff some coordinate `i` has `y i = x i ± 1` and all other coordinates agree. -/
def torusAdj (d N : ℕ) (x y : Fin d → ZMod N) : Prop :=
  ∃ i : Fin d, (∀ j, j ≠ i → x j = y j) ∧ (y i = x i + 1 ∨ y i = x i - 1)

instance torusAdj_decidable (d N : ℕ) (x y : Fin d → ZMod N) : Decidable (torusAdj d N x y) := by
  unfold torusAdj
  infer_instance

/-- The torus adjacency is symmetric. -/
theorem torusAdj_symm {d N : ℕ} {x y : Fin d → ZMod N} (h : torusAdj d N x y) :
    torusAdj d N y x := by
  unfold torusAdj at h ⊢
  obtain ⟨i, h1, h2⟩ := h
  refine ⟨i, fun j hj => (h1 j hj).symm, ?_⟩
  rcases h2 with h2 | h2
  · exact Or.inr (by linear_combination -h2)
  · exact Or.inl (by linear_combination -h2)

/-- No vertex of the torus is adjacent to itself, since `1 ≠ 0` in `ℤ/N`. -/
theorem torusAdj_irrefl {d N : ℕ} (hN : 3 ≤ N) (x : Fin d → ZMod N) : ¬ torusAdj d N x x := by
  unfold torusAdj
  rintro ⟨i, -, h⟩
  rcases h with h | h
  · exact torus_one_ne_zero hN (by linear_combination -h)
  · exact torus_one_ne_zero hN (by linear_combination h)

/-- The torus adjacency is invariant under translation. -/
theorem torusAdj_add {d N : ℕ} (c x y : Fin d → ZMod N) :
    torusAdj d N (x + c) (y + c) ↔ torusAdj d N x y := by
  simp only [torusAdj, Pi.add_apply]
  constructor
  · rintro ⟨i, h1, h2⟩
    refine ⟨i, fun j hj => ?_, ?_⟩
    · linear_combination h1 j hj
    · rcases h2 with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
  · rintro ⟨i, h1, h2⟩
    refine ⟨i, fun j hj => ?_, ?_⟩
    · linear_combination h1 j hj
    · rcases h2 with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)

/-- The torus graph on `(ℤ/N)^d` (`tex:502-514`), with the nearest-neighbour adjacency. -/
def torusGraph (d N : ℕ) (hN : 3 ≤ N) : SimpleGraph (Fin d → ZMod N) where
  Adj := torusAdj d N
  symm := ⟨fun _ _ h => torusAdj_symm h⟩
  loopless := ⟨fun x => torusAdj_irrefl hN x⟩

instance torusGraph_decRel (d N : ℕ) (hN : 3 ≤ N) : DecidableRel (torusGraph d N hN).Adj :=
  fun x y => torusAdj_decidable d N x y

/-- Translation by `c` is an automorphism of the torus graph. -/
def torusTranslate (d N : ℕ) (hN : 3 ≤ N) (c : Fin d → ZMod N) :
    torusGraph d N hN ≃g torusGraph d N hN where
  toEquiv := Equiv.addRight c
  map_rel_iff' := fun {a b} => torusAdj_add c a b

/-- The torus graph is vertex-transitive: translations act transitively (`tex:229`). -/
theorem torusGraph_transitive (d N : ℕ) (hN : 3 ≤ N) (x y : Fin d → ZMod N) :
    ∃ σ : torusGraph d N hN ≃g torusGraph d N hN, σ x = y :=
  ⟨torusTranslate d N hN (y - x), by
    show x + (y - x) = y
    abel⟩

/-- The torus graph is connected: any vertex is reached from `0` by moving one coordinate at a
time, one unit step at a time (`tex:502-514`). -/
theorem torusGraph_connected (d N : ℕ) (hN : 3 ≤ N) : (torusGraph d N hN).Connected := by
  haveI : NeZero N := ⟨by omega⟩
  -- Moving coordinate `i` up by `n` unit steps, one edge at a time.
  have step : ∀ (x : Fin d → ZMod N) (i : Fin d) (n : ℕ),
      (torusGraph d N hN).Reachable x (x + Pi.single i (n : ZMod N)) := by
    intro x i n
    induction n with
    | zero => simp
    | succ n ih =>
      have hadj : torusAdj d N (x + Pi.single i (n : ZMod N))
          (x + Pi.single i ((n + 1 : ℕ) : ZMod N)) := by
        unfold torusAdj
        refine ⟨i, fun j hj => ?_, Or.inl ?_⟩
        · simp [Pi.single_eq_of_ne hj]
        · simp only [Pi.add_apply, Pi.single_eq_same]
          push_cast
          ring
      exact ih.trans (SimpleGraph.Adj.reachable (G := torusGraph d N hN) hadj)
  -- Any displacement in a single coordinate.
  have stepAll : ∀ (x : Fin d → ZMod N) (i : Fin d) (c : ZMod N),
      (torusGraph d N hN).Reachable x (x + Pi.single i c) := by
    intro x i c
    have h := step x i c.val
    rwa [ZMod.natCast_zmod_val] at h
  -- Every vertex is reached from `0` by summing its coordinates one at a time.
  have reach0 : ∀ x : Fin d → ZMod N, (torusGraph d N hN).Reachable 0 x := by
    intro x
    have hs : ∀ s : Finset (Fin d),
        (torusGraph d N hN).Reachable 0 (∑ i ∈ s, Pi.single i (x i)) := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simp
      · intro a s ha ih
        rw [Finset.sum_insert ha, add_comm]
        exact ih.trans (stepAll _ a (x a))
    have hx : ∑ i : Fin d, Pi.single i (x i) = x := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    have h := hs Finset.univ
    rwa [hx] at h
  exact { preconnected := fun x y => (reach0 x).symm.trans (reach0 y) }

/-- The vertex count of `(ℤ/N)^d` is `N ^ d`, the paper's `N = n^d` (`tex:502-514`). -/
theorem torus_card (d N : ℕ) [NeZero N] : Fintype.card (Fin d → ZMod N) = N ^ d := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

/-- The torus has at least two vertices when `d ≥ 1` and `N ≥ 3`. -/
theorem torus_two_le (d N : ℕ) (hd : 1 ≤ d) (hN : 3 ≤ N) [NeZero N] :
    2 ≤ Fintype.card (Fin d → ZMod N) := by
  rw [torus_card]
  exact le_trans (show 2 ≤ N by omega) (Nat.le_self_pow (by omega) N)

/-- The discrete torus `(ℤ/N)^d` as a `Base` (`tex:229`, torus examples `tex:502-514`).
Here `d ≥ 1` is the dimension and `N ≥ 3` the side length (the paper's `n`), so the vertex
count is `N ^ d`, the paper's `N = n^d`. -/
def torusBase (d N : ℕ) (hd : 1 ≤ d) (hN : 3 ≤ N) : Base := by
  haveI : NeZero N := ⟨by omega⟩
  exact
    { V := Fin d → ZMod N
      graph := torusGraph d N hN
      connected := torusGraph_connected d N hN
      vertexTransitive := torusGraph_transitive d N hN
      nontrivial := torus_two_le d N hd hN }

end IdlaCylAudit

/-! ### From `IdlaCyl/Support/Torus/Setup.lean` -/
namespace IdlaCylAudit
open Filter
open scoped Topology
/-- The torus sequence with the finite inadmissible prefix removed. -/
abbrev torusSeq (d : ℕ) (hd : 1 ≤ d) (n : ℕ) : Base :=
  torusBase d (n + 3) hd (by omega)

end IdlaCylAudit
-- VOCABULARY-END

namespace IdlaCylAudit

open IdlaCylAudit.Defs Filter MeasureTheory ProbabilityTheory
open scoped Topology

theorem thm_cycle
    (S : (N : ℕ) → SpectralData (CycleSpectrum.indexedBase N))
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ)
    (hd : ∀ k ∈ Finset.Icc 2 K, Differentiable ℝ (α k))
    (hb : ∀ k ∈ Finset.Icc 2 K, ∃ M : ℝ, ∀ y, |deriv (α k) y| ≤ M)
    (y₀ : ℝ) (hy₀ : 0 < y₀) :
    ∀ g : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun N : ℕ => ∫ ω : TrajSeq (CycleSpectrum.indexedBase N),
        g ((1 / (N : ℝ)) *
          pairingTraj (CycleSpectrum.indexedBase N) ω (N * Nat.floor (y₀ * (N : ℝ)))
            (testAt (CycleSpectrum.indexedBase N) (S N) (N : ℝ) K α))
          ∂idlaMeasure (CycleSpectrum.indexedBase N))
        atTop (𝓝 (∫ z : ℝ, g z ∂gaussianReal 0
          (Real.toNNReal (variance K α (fun k => Real.sqrt 2 * Real.pi * ((k / 2 : ℕ) : ℝ)) y₀)))) := by
  sorry

end IdlaCylAudit
