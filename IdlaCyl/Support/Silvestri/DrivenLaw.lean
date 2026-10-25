module

public import IdlaCyl.Support.Silvestri.CylStepLaw
public import IdlaCyl.Support.Silvestri.DrivenBase

@[expose] public section

/-!
# The driven walk has the canonical walk law

The driven path `cylPath B x w` of `IdlaCyl/Support/Idla.lean`, with the driver `w`
drawn from `walkDriverLaw`, has the finite-dimensional marginals of the canonical walk
`walkPathLaw x` of `IdlaCyl/Support/Canonical.lean`: on each initial segment `Π i : Iic n`,
the law is the time-`n` partial trajectory of the kernel family `cylITKernel B`.

The proof is by induction on `n`. The base case is the Dirac mass at the starting site. The
induction step splits off the last driver entry `w n`, which is independent of the path up to
time `n` and drives the one new coordinate with the one-step law `cylStep_map_eq`. The two
marginal statements are `cylPath_fdd` and `drivenPath_law`. The head-tail decomposition
`walkDriverLaw_eq_consNat` is a standalone fact about the driver law.
-/

namespace IdlaCyl.Silvestri

open MeasureTheory ProbabilityTheory

/-- The driver law is the first driver entry followed by an independent copy of itself. -/
theorem walkDriverLaw_eq_consNat :
    walkDriverLaw = ((stepLaw.prod stepLaw).prod walkDriverLaw).map
      (fun q : (ℝ × ℝ) × WalkDriver => LatticeProb.consNat q.1 q.2) := by
  haveI : IsProbabilityMeasure stepLaw := ⟨by norm_num [stepLaw, Measure.restrict_apply_univ]⟩
  unfold walkDriverLaw
  exact (LatticeProb.map_consNat (stepLaw.prod stepLaw)).symm

/-- The time-zero finite-dimensional marginal of the driven path is the Dirac mass at the
starting site. -/
theorem cylPath_fdd_zero (B : Base) (x : Site B) :
    walkDriverLaw.map (fun w : WalkDriver => fun i : Finset.Iic 0 => cylPath B x w i.1)
      = (Kernel.partialTraj (X := fun _ : ℕ => Site B) (cylITKernel B) 0 0) (fun _ => x) := by
  haveI : IsProbabilityMeasure stepLaw := ⟨by norm_num [stepLaw, Measure.restrict_apply_univ]⟩
  haveI : IsProbabilityMeasure walkDriverLaw := by unfold walkDriverLaw; infer_instance
  have hconst : (fun w : WalkDriver => fun i : Finset.Iic 0 => cylPath B x w i.1)
      = fun _ => (fun _ : Finset.Iic 0 => x) := by
    funext w i
    have h0 : i.1 = 0 := Nat.le_zero.mp (Finset.mem_Iic.mp i.2)
    rw [h0, cylPath_zero]
  rw [hconst, Measure.map_const, Kernel.partialTraj_self, Kernel.id_apply, measure_univ,
    one_smul]

/-- The driven path up to time `n` depends only on the driver entries below time `n`. -/
theorem cylPath_eq_of_eq_below (B : Base) (x : Site B) (w w' : WalkDriver) (n : ℕ)
    (h : ∀ k < n, w k = w' k) : ∀ i ≤ n, cylPath B x w i = cylPath B x w' i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    change cylStep B (cylPath B x w i) (w i) = cylStep B (cylPath B x w' i) (w' i)
    rw [ih (by omega), h i (by omega)]

/-- The driven path up to time `n`, as a function of the driver entries `w 0, …, w (n-1)`
(the other entries are set to `(0, 0)`, and are never read). -/
noncomputable def pathOfPrefix (B : Base) (x : Site B) (n : ℕ)
    (v : Finset.range n → ℝ × ℝ) : Finset.Iic n → Site B :=
  fun j => cylPath B x (fun k => if h : k < n then v ⟨k, Finset.mem_range.2 h⟩ else (0, 0)) j.1

/-- The prefix path map is measurable. -/
theorem measurable_pathOfPrefix (B : Base) (x : Site B) (n : ℕ) :
    Measurable (pathOfPrefix B x n) := by
  refine measurable_pi_lambda _ fun j => ?_
  have hext : Measurable (fun v : Finset.range n → ℝ × ℝ =>
      fun k : ℕ => if h : k < n then v ⟨k, Finset.mem_range.2 h⟩ else (0, 0)) := by
    refine measurable_pi_lambda _ fun k => ?_
    by_cases h : k < n
    · simp only [dif_pos h]
      exact measurable_pi_apply _
    · simp only [dif_neg h]
      exact measurable_const
  exact (measurable_pi_apply j.1).comp ((measurable_cylPath B x).comp hext)

/-- The prefix path map applied to the restricted driver is the driven path. -/
theorem pathOfPrefix_restrict (B : Base) (x : Site B) (n : ℕ) (w : WalkDriver) :
    pathOfPrefix B x n (fun i : Finset.range n => w i)
      = fun j : Finset.Iic n => cylPath B x w j.1 := by
  funext j
  have hj : j.1 ≤ n := Finset.mem_Iic.mp j.2
  exact cylPath_eq_of_eq_below B x _ w n (fun k hk => by simp [hk]) j.1 hj

/-- The coordinate `w n` of the driver is independent of the driven path up to time `n`, and
has the one-step law. -/
theorem indepFun_cylPath_prefix_last (B : Base) (x : Site B) (n : ℕ) :
    IndepFun (fun w : WalkDriver => fun i : Finset.Iic n => cylPath B x w i.1)
      (fun w : WalkDriver => w n) walkDriverLaw := by
  haveI : IsProbabilityMeasure stepLaw := ⟨by norm_num [stepLaw, Measure.restrict_apply_univ]⟩
  have hind : iIndepFun (fun (i : ℕ) (w : WalkDriver) => w i) walkDriverLaw := by
    unfold walkDriverLaw
    exact iIndepFun_infinitePi (P := fun _ : ℕ => stepLaw.prod stepLaw)
      (X := fun _ : ℕ => id) (fun _ => measurable_id)
  have hsplit := hind.indepFun_finset (Finset.range n) {n} (by simp)
    (fun i => measurable_pi_apply i)
  have hev : Measurable (fun v : ({n} : Finset ℕ) → ℝ × ℝ => v ⟨n, Finset.mem_singleton_self n⟩) :=
    measurable_pi_apply _
  have hlast := hsplit.comp measurable_id hev
  have hF : (fun w : WalkDriver => fun i : Finset.Iic n => cylPath B x w i.1)
      = pathOfPrefix B x n ∘ (fun w : WalkDriver => fun i : Finset.range n => w i) := by
    funext w
    rw [Function.comp_apply, pathOfPrefix_restrict]
  rw [hF]
  exact hlast.comp (measurable_pathOfPrefix B x n) measurable_id

/-- The coordinates of the driven path up to time `n + 1` are those up to time `n`, with the
new coordinate `cylStep` applied to the last one and the last driver entry. -/
theorem cylPath_fdd_succ (B : Base) (n : ℕ) (x : Site B)
    (ih : walkDriverLaw.map (fun w : WalkDriver => fun i : Finset.Iic n => cylPath B x w i.1)
      = (Kernel.partialTraj (X := fun _ : ℕ => Site B) (cylITKernel B) 0 n) (fun _ => x)) :
    walkDriverLaw.map (fun w : WalkDriver => fun i : Finset.Iic (n + 1) => cylPath B x w i.1)
      = (Kernel.partialTraj (X := fun _ : ℕ => Site B) (cylITKernel B) 0 (n + 1)) (fun _ => x) := by
  haveI : IsProbabilityMeasure stepLaw := ⟨by norm_num [stepLaw, Measure.restrict_apply_univ]⟩
  haveI : IsProbabilityMeasure walkDriverLaw := by unfold walkDriverLaw; infer_instance
  have hpath : Measurable (fun w : WalkDriver => fun i : Finset.Iic n => cylPath B x w i.1) :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply i.1).comp (measurable_cylPath B x)
  have hpair : Measurable (fun w : WalkDriver =>
      ((fun i : Finset.Iic n => cylPath B x w i.1), w n)) :=
    hpath.prodMk (measurable_pi_apply n)
  have hcs : Measurable (fun q : (Finset.Iic n → Site B) × (ℝ × ℝ) =>
      cylStep B (q.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩) q.2) := by
    have h1 : Measurable (fun q : (Finset.Iic n → Site B) × (ℝ × ℝ) =>
        (q.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩, q.2)) :=
      ((measurable_pi_apply (⟨n, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic n)).comp
        measurable_fst).prodMk measurable_snd
    exact (measurable_cylStep_pair B).comp h1
  let G : (Finset.Iic n → Site B) × (ℝ × ℝ) → (Finset.Iic (n + 1) → Site B) := fun q =>
    IicProdIoc (X := fun _ : ℕ => Site B) n (n + 1) (q.1, MeasurableEquiv.piSingleton (X := fun _ : ℕ => Site B) n
      (cylStep B (q.1 ⟨n, Finset.mem_Iic.2 le_rfl⟩) q.2))
  have hG : Measurable G :=
    (measurable_IicProdIoc (X := fun _ : ℕ => Site B)).comp
      (measurable_fst.prodMk ((MeasurableEquiv.piSingleton (X := fun _ : ℕ => Site B) n).measurable.comp hcs))
  have hF : (fun w : WalkDriver => fun i : Finset.Iic (n + 1) => cylPath B x w i.1)
      = G ∘ (fun w : WalkDriver => ((fun i : Finset.Iic n => cylPath B x w i.1), w n)) := by
    funext w i
    by_cases h : i.1 ≤ n
    · simp only [Function.comp, G, IicProdIoc_def, dif_pos h]
    · obtain ⟨m, hm⟩ := i
      have hm' : m = n + 1 := by have := Finset.mem_Iic.mp hm; simp only at h; omega
      simp only [Function.comp, G, IicProdIoc_def, dif_neg (show ¬ m ≤ n by omega)]
      subst hm'
      rw [cylPath_succ]
      rfl
  have hcoord : walkDriverLaw.map (fun w : WalkDriver => w n) = stepLaw.prod stepLaw := by
    unfold walkDriverLaw
    exact Measure.infinitePi_map_eval (fun _ : ℕ => stepLaw.prod stepLaw) n
  have hsplit := (indepFun_iff_map_prod_eq_prod_map_map hpath.aemeasurable
    (measurable_pi_apply n).aemeasurable).mp (indepFun_cylPath_prefix_last B x n)
  rw [hF, ← Measure.map_map hG hpair, hsplit, hcoord,
    Kernel.partialTraj_succ_of_le (Nat.zero_le n), Kernel.map_apply]
  ext s hs
  rw [Measure.map_apply hG hs, Measure.map_apply measurable_IicProdIoc hs,
    Measure.prod_apply (hG hs)]
  have hc := Kernel.comp_apply' (Kernel.id ×ₖ ((cylITKernel B n).map
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Site B) n)))
    (Kernel.partialTraj (X := fun _ : ℕ => Site B) (cylITKernel B) 0 n) (fun _ => x)
    (measurable_IicProdIoc (X := fun _ : ℕ => Site B) (m := n) (n := n + 1) hs)
  rw [hc, ← ih]
  refine lintegral_congr fun y => ?_
  have hIs : MeasurableSet (IicProdIoc (X := fun _ : ℕ => Site B) n (n + 1) ⁻¹' s) :=
    measurable_IicProdIoc hs
  have hA : MeasurableSet (Prod.mk y ⁻¹' (IicProdIoc (X := fun _ : ℕ => Site B) n (n + 1) ⁻¹' s)) :=
    measurable_prodMk_left hIs
  rw [Kernel.prod_apply, Kernel.id_apply, Kernel.map_apply, Measure.dirac_prod,
    Measure.map_apply measurable_prodMk_left hIs,
    Measure.map_apply (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Site B) n).measurable hA]
  have hB : MeasurableSet (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Site B) n ⁻¹'
      (Prod.mk y ⁻¹' (IicProdIoc (X := fun _ : ℕ => Site B) n (n + 1) ⁻¹' s))) :=
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Site B) n).measurable hA
  have hK : cylITKernel B n y = (stepLaw.prod stepLaw).map
      (cylStep B (y ⟨n, Finset.mem_Iic.2 le_rfl⟩)) :=
    (cylStep_map_eq B _).symm
  rw [hK, Measure.map_apply (measurable_cylStep B _) hB]
  rfl
  all_goals first
    | exact measurable_IicProdIoc (X := fun _ : ℕ => Site B)
    | exact (MeasurableEquiv.piSingleton (X := fun _ : ℕ => Site B) n).measurable

/-- The finite-dimensional marginals of the driven path, on each initial segment `Π i : Iic n`,
are the partial trajectories of the canonical kernel family `cylITKernel B`. -/
theorem cylPath_fdd (B : Base) (n : ℕ) (x : Site B) :
    walkDriverLaw.map (fun w : WalkDriver => fun i : Finset.Iic n => cylPath B x w i.1)
      = (Kernel.partialTraj (X := fun _ : ℕ => Site B) (cylITKernel B) 0 n) (fun _ => x) := by
  induction n with
  | zero => exact cylPath_fdd_zero B x
  | succ n ih => exact cylPath_fdd_succ B n x ih

/-- The driven path from `x`, with the driver drawn from `walkDriverLaw`, has the law of the
canonical walk `walkPathLaw x`. -/
theorem drivenPath_law (B : Base) (x : Site B) :
    walkDriverLaw.map (fun w : WalkDriver => cylPath B x w) = walkPathLaw B x := by
  haveI : IsProbabilityMeasure stepLaw := ⟨by norm_num [stepLaw, Measure.restrict_apply_univ]⟩
  haveI : IsProbabilityMeasure walkDriverLaw := by unfold walkDriverLaw; infer_instance
  let η : Kernel (Finset.Iic 0 → Site B) (ℕ → Site B) := Kernel.ofFunOfCountable
    (fun y : Finset.Iic 0 → Site B =>
      walkDriverLaw.map (fun w : WalkDriver => cylPath B (y ⟨0, Finset.mem_Iic.2 le_rfl⟩) w))
  have hE := Kernel.eq_traj (X := fun _ : ℕ => Site B) (cylITKernel B) η (fun b => by
      ext y : 1
      have hy : y = fun _ : Finset.Iic 0 => y ⟨0, Finset.mem_Iic.2 le_rfl⟩ := by
        funext i
        have h0 : i.1 = 0 := Nat.le_zero.mp (Finset.mem_Iic.mp i.2)
        congr 1
        exact Subtype.ext h0
      have hpt : Kernel.partialTraj (X := fun _ : ℕ => Site B) (cylITKernel B) 0 b y
          = walkDriverLaw.map (fun w : WalkDriver => fun i : Finset.Iic b => cylPath B (y ⟨0, Finset.mem_Iic.2 le_rfl⟩) w i.1) := by
        rw [hy]
        exact (cylPath_fdd B b _).symm
      rw [Kernel.map_apply _ (Preorder.measurable_frestrictLe (X := fun _ : ℕ => Site B) b), hpt]
      show (walkDriverLaw.map (fun w : WalkDriver => cylPath B (y ⟨0, Finset.mem_Iic.2 le_rfl⟩) w)).map _ = _
      rw [Measure.map_map (Preorder.measurable_frestrictLe (X := fun _ : ℕ => Site B) b) (measurable_cylPath B _)]
      rfl
  )
  unfold walkPathLaw Kernel.trajMeasure
  rw [Measure.map_dirac, Measure.dirac_bind, ← hE]
  · rfl
  all_goals first
    | exact (MeasurableEquiv.piUnique _).symm.measurable
    | exact Kernel.measurable _

end IdlaCyl.Silvestri
