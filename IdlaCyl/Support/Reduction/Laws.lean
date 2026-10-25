module

/-
Probability laws and events used by the layer-by-layer reduction.
Source: paper/idla-cylinder-gff.tex, tex:246-265,595-610,1440-1453.
These definitions do not assert the stochastic conclusions of the reduction.
All measures below are literal canonical pushforwards.
-/
public import IdlaCyl.Support.Outer.ResumeGrowth
public import IdlaCyl.Support.Outer.Translation

@[expose] public section

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Independent canonical walks released uniformly at an arbitrary fixed layer. -/
noncomputable def layerDrivingLaw (B : Base) (h : ℤ) : Measure (TrajSeq B) :=
  Measure.infinitePi (fun _ : ℕ => walkLawUniformAt B h)

instance layerDrivingLaw_isProbability (B : Base) (h : ℤ) :
    IsProbabilityMeasure (layerDrivingLaw B h) := by
  unfold layerDrivingLaw
  infer_instance

/-- Growth from a fixed finite extension with releases on a fixed layer. -/
noncomputable def layerGrowthLaw (B : Base) (F : ResumeFinite B) (h : ℤ) (n : ℕ) :
    Measure (ResumeFinite B) :=
  (layerDrivingLaw B h).map (fun ω => resumeGrow B F ω n)

instance layerGrowthLaw_isProbability (B : Base) (F : ResumeFinite B) (h : ℤ) (n : ℕ) :
    IsProbabilityMeasure (layerGrowthLaw B F h n) :=
  Measure.isProbabilityMeasure_map (measurable_resumeGrow B F n).aemeasurable

/-- The canonical flat-start finite-cluster distribution. -/
noncomputable def flatClusterLaw (B : Base) (n : ℕ) : Measure (ResumeFinite B) :=
  layerGrowthLaw B (resumeEmpty B) 0 n

/-- All sites of the indicated rectangle are occupied. -/
def filled (B : Base) (j : ℤ) : Set (ResumeFinite B) :=
  {F | R B (j : ℝ) ⊆ resumeSeed B F}

/-- A fixed layer has at least one missing first-entrance coupon. -/
def missingCoupons (B : Base) (j : ℤ) (M : ℕ) : Set (TrajSeq B) :=
  {ω | ∃ x : B.V, ∀ i < M, firstHitSite B j (ω i) ≠ (x, j)}

/-- Equality of actual occupied sets after shifting the second finite cluster. -/
def matchShift (B : Base) (k : ℕ) : Set (ResumeFinite B × ResumeFinite B) :=
  {p | resumeSeed B p.1 = outerShift B (k : ℤ) '' resumeSeed B p.2}

/-- A finite-cluster coupling with both literal marginals and a failure allowance. -/
def ClusterCoupling (B : Base) (P Q : Measure (ResumeFinite B))
    (k : ℕ) (ε : ℝ) : Prop :=
  ∃ μ : Measure (ResumeFinite B × ResumeFinite B),
    μ.map Prod.fst = P ∧ μ.map Prod.snd = Q ∧
      μ (matchShift B k)ᶜ ≤ ENNReal.ofReal ε

/-- The explicit four-term allowance of one valid round. -/
noncomputable def roundError (B : Base) (p q : ℝ) (ℓ β : ℕ) : ℝ :=
  ((ℓ + β : ℕ) : ℝ) * (B.card : ℝ) ^ (-q) + 2 * (B.card : ℝ) ^ (-p)

end IdlaCyl.Reduction
