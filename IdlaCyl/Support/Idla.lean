/-
The IDLA process on the cylinder, and the discrepancy function.

`paper/idla-cylinder-gff.tex:263-265`:

  "We define the IDLA process `(A(t))_{t ≥ 0}` on `G_N` starting from the flat
   configuration `R_0` inductively.  Set `A(0) := R_0`.  For each integer
   `t ≥ 1`, set `A(t) := A(t-1) ∪ {(X_t, Y_t)}`, where `(X_t, Y_t)` is the exit
   location from `A(t-1)` of an independent cylinder walk started at a site
   chosen uniformly from `V_N × {0}` ... setting `A_+(t) := A(t) ∩ {y ≥ 1}` we
   have `|A_+(t)| = t` for every `t ≥ 0`."

`paper/idla-cylinder-gff.tex:348-351` (Definition, discrepancy function):

  "For `t ≥ 0`, the discrepancy function `D_t : V_N × ℤ → {-1,0,+1}` is defined
   by `D_t(x,y) := 1_{A(t)}(x,y) - 1_{R_{t/N}}(x,y)`."

`paper/idla-cylinder-gff.tex:353` (the pairing) and `tex:356-361` (Definition
`def:zero`, the zero horizontal average property).

## How the randomness is carried

Rather than invoke Ionescu--Tulcea, the process is *driven*: each aggregation
step `t` consumes one `StepDriver`, namely a uniform `[0,1)` variable choosing
the starting vertex in the layer `V_N × {0}` and a sequence of uniform pairs
driving the walk.  `driverLaw` is the product of countably many independent
copies, so the walks are independent, as the paper requires.  This is the same
device `LatticeProb.Graph.walkLaw` uses.

`cylStep` splits one step exactly the way the paper describes the kernel
(`tex:256`, "the vertical coordinate ... makes a step with probability 1/2,
independently of the horizontal structure"): the first uniform decides
vertical against horizontal, the second decides which way.  That this realises
`cylKernel` is the obligation `step_law_eq_cylKernel`, not a definition.

## Junk values

`exitTime` is valued in `ℕ∞`, so a trajectory that never leaves the cluster
gets `⊤` rather than a junk finite time; `exitSite` then reads the trajectory
at `ENat.toNat ⊤ = 0`, i.e. at its starting point.  Those trajectories form a
null set (obligation `exit_ae_finite`), which is why the statements are
probabilistic.  The pairing is a `finsum`, which is the honest sum here
because `D_t` has finite support (obligation `discrepancy_support_finite`);
without that lemma the pairing would silently be `0`.
-/
import IdlaCyl.Support.Cylinder
import Mathlib

namespace IdlaCyl

open MeasureTheory
open scoped BigOperators

/-! ### The driving randomness -/

/-- The law of one uniform instruction on `[0,1)`. -/
noncomputable def stepLaw : Measure ℝ := volume.restrict (Set.Ico (0 : ℝ) 1)

/-- The instructions driving one cylinder walk: at each time a pair of
uniforms, the first choosing vertical against horizontal and the second
choosing the direction. -/
abbrev WalkDriver : Type := ℕ → ℝ × ℝ

/-- The randomness consumed by one aggregation step: the uniform choosing the
starting vertex in `V_N × {0}`, and the walk instructions. -/
abbrev StepDriver : Type := ℝ × WalkDriver

/-- The randomness driving the whole IDLA process: one `StepDriver` per
aggregated particle, independent across particles. -/
abbrev Driver : Type := ℕ → StepDriver

/-- The law of one walk's instructions. -/
noncomputable def walkDriverLaw : Measure WalkDriver :=
  Measure.infinitePi fun _ : ℕ => stepLaw.prod stepLaw

/-- The law of one aggregation step's randomness. -/
noncomputable def stepDriverLaw : Measure StepDriver := stepLaw.prod walkDriverLaw

/-- The law of the whole driving sequence: independent steps (`tex:265`,
"an independent cylinder walk"). -/
noncomputable def driverLaw : Measure Driver :=
  Measure.infinitePi fun _ : ℕ => stepDriverLaw

/-! ### One step of the cylinder walk -/

variable (B : Base)

/-- The vertex of `V_N` selected by a uniform `r ∈ [0,1)`; uniform on `V_N`
because `|V_N| = N`.  This is the paper's "a site chosen uniformly from
`V_N × {0}`" (`tex:265`). -/
noncomputable def startVertex (r : ℝ) : B.V :=
  (Finset.univ : Finset B.V).toList.getD ⌊(B.card : ℝ) * r⌋₊ B.pt

/-- The neighbour of `x` in the base graph selected by `s ∈ [0,1)`; uniform on
the `d` neighbours of `x`. -/
noncomputable def baseNeighbor (x : B.V) (s : ℝ) : B.V :=
  (B.graph.neighborFinset x).toList.getD ⌊(B.deg : ℝ) * s⌋₊ x

/-- One step of the cylinder walk, driven by a pair of uniforms.  The first
coordinate chooses vertical (probability `1/2`) against horizontal; inside the
vertical branch the second coordinate chooses the sign, and inside the
horizontal branch it chooses laziness (probability `1/2`) against a uniform
neighbour.  Compare `cylKernel` (`tex:246-255`). -/
noncomputable def cylStep (p : Site B) (u : ℝ × ℝ) : Site B :=
  if u.1 < 1 / 2 then
    (if u.2 < 1 / 2 then (p.1, p.2 - 1) else (p.1, p.2 + 1))
  else
    (if u.2 < 1 / 2 then p else (baseNeighbor B p.1 (2 * u.2 - 1), p.2))

/-- The cylinder-walk trajectory started at `p` and driven by `w`. -/
noncomputable def cylPath (p : Site B) (w : WalkDriver) : ℕ → Site B
  | 0 => p
  | k + 1 => cylStep B (cylPath p w k) (w k)

@[simp] theorem cylPath_zero (p : Site B) (w : WalkDriver) : cylPath B p w 0 = p := rfl

theorem cylPath_succ (p : Site B) (w : WalkDriver) (k : ℕ) :
    cylPath B p w (k + 1) = cylStep B (cylPath B p w k) (w k) := rfl

/-- The exit time `τ_S = inf{k ≥ 0 : X_k ∉ S}`, in `ℕ∞`, so that a trajectory
which never leaves `S` has the value `⊤` and not a junk finite time. -/
noncomputable def exitTime (S : Set (Site B)) (X : ℕ → Site B) : ℕ∞ :=
  sInf {k : ℕ∞ | ∃ n : ℕ, (k : ℕ∞) = n ∧ X n ∉ S}

/-- The trajectory of the walk launched by one aggregation step: started
uniformly on the layer `V_N × {0}` (`tex:265`). -/
noncomputable def stepWalk (d : StepDriver) : ℕ → Site B :=
  cylPath B (startVertex B d.1, 0) d.2

/-- The exit location from `S` of the walk launched by `d`, the paper's
`(X_t, Y_t)` (`tex:265`).  A trajectory that never exits reads its own
starting point, through `ENat.toNat ⊤ = 0`; such trajectories are null. -/
noncomputable def exitSite (S : Set (Site B)) (d : StepDriver) : Site B :=
  stepWalk B d (exitTime B S (stepWalk B d)).toNat

/-! ### The IDLA cluster -/

/-- The IDLA cluster `A(t)` on the cylinder, started from the flat
configuration `A(0) = R_0` (`tex:263-265`). -/
noncomputable def cluster (ω : Driver) : ℕ → Set (Site B)
  | 0 => R B 0
  | t + 1 => cluster ω t ∪ {exitSite B (cluster ω t) (ω t)}

@[simp] theorem cluster_zero (ω : Driver) : cluster B ω 0 = R B 0 := rfl

theorem cluster_succ (ω : Driver) (t : ℕ) :
    cluster B ω (t + 1) = cluster B ω t ∪ {exitSite B (cluster B ω t) (ω t)} := rfl

/-- The clusters increase (`tex:265`, "the aggregates are increasing"). -/
theorem cluster_mono (ω : Driver) {s t : ℕ} (h : s ≤ t) :
    cluster B ω s ⊆ cluster B ω t := by
  induction t with
  | zero => simpa using (le_antisymm h (Nat.zero_le _) ▸ Set.Subset.refl _)
  | succ n ih =>
      rcases Nat.lt_or_ge s (n + 1) with hs | hs
      · exact (ih (Nat.lt_succ_iff.mp hs)).trans (by rw [cluster_succ]; exact Set.subset_union_left)
      · have : s = n + 1 := le_antisymm h hs
        subst this; exact Set.Subset.refl _

/-- `A_+(t) = A(t) ∩ {y ≥ 1}`, the part of the cluster strictly above level
zero (`tex:265`, `tex:339`). -/
def clusterPlus (ω : Driver) (t : ℕ) : Set (Site B) :=
  cluster B ω t ∩ {p : Site B | 1 ≤ p.2}

/-! ### The discrepancy function -/

/-- The discrepancy function `D_t = 1_{A(t)} - 1_{R_{t/N}}` (`tex:348-351`). -/
noncomputable def discrepancy (ω : Driver) (t : ℕ) (p : Site B) : ℝ :=
  (cluster B ω t).indicator (fun _ => (1 : ℝ)) p
    - (R B ((t : ℝ) / B.card)).indicator (fun _ => (1 : ℝ)) p

/-- The pairing `⟪D_t, f⟫ = ∑_{(x,y)} D_t(x,y) f(x,y)` (`tex:353`).  Written as
a `finsum`, which is the paper's "absolutely convergent finite sum" exactly
when `D_t` has finite support; see `discrepancy_support_finite`. -/
noncomputable def pairing (ω : Driver) (t : ℕ) (f : Site B → ℝ) : ℝ :=
  ∑ᶠ p : Site B, discrepancy B ω t p * f p

/-- A function has the zero horizontal average property when every complete
horizontal layer sums to zero (`tex:356-361`, Definition `def:zero`). -/
def ZeroHorizontalAverage (f : Site B → ℝ) : Prop :=
  ∀ y : ℤ, ∑ x : B.V, f (x, y) = 0

end IdlaCyl
