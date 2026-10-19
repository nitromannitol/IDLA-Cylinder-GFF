/-
First hitting of a horizontal layer by the cylinder walk: the harmonic profile
`H_ζ` and the uniformity of the first hit.

Paper: `paper/idla-cylinder-gff.tex`.

* `tex:595-610`  `unif-first-hit`: "`X̂_{τ_{m-1}}` is uniformly distributed on
  `V_N` regardless of the vertical history" — `unif_first_hit` below.
* `tex:1185-1187` the definition of `H_ζ`, with the convention
  `H_ζ(x,y) = 0` for `y > ζ₂` — `hitProb`.
* `tex:1189`  `H_ζ` is discrete harmonic on `R_{ζ₂-1}` — `hitProb_harmonic`.
* `tex:1200-1203` optional stopping for `H_ζ` — `hitProb_exit_mean`.
* `tex:1208`  `H_ζ² ≤ H_ζ` — `hitProb_sq_le`.
* `tex:1231`  `H_ζ(x,h) = 1(x = z)` — `hitProb_at_layer`.
* `tex:608`, `tex:1204`, `tex:1230`, `tex:1297` the layer form
  `∑_{x ∈ V_N} H_ζ(x,y) = 1` — `hitProb_layer_sum`.

## Errata honoured here

There is no optional-stopping hypothesis.  The paper's
"optional stopping at the walk's settlement" (`tex:1200`) is obtained here
*without* any optional-stopping citation: the truncated exit index `exitIdx`
satisfies a one-step recursion, so `hitProbE_exitIdx` is an induction on the
truncation level whose inductive step is exactly the harmonicity of `H_ζ`, and
the truncation is removed by dominated convergence.  Consequently
`hitProb_exit_mean` needs no optional-stopping binder; the a.s.-finiteness of
`exitTime'` that replaces it is *derived* from `hrec` (a walk that a.s. reaches
level `ζ₂` has a.s. already left `R_{ζ₂-1} ⊇ S`), so no new binder is
introduced either.  This is the minimal adjustment.

`IdlaCyl.Support.Stopping` is imported for optional stopping at an a.s.-finite time, but
`IdlaCyl.integral_stoppedValue_of_ae_finite` is not needed: the whole argument
stays in `ℝ≥0∞` — `hitProbE_exitIdx` is an identity of `lintegral`s, and only
the last line of `hitProb_exit_mean` converts to a Bochner integral — so the
`ℝ`-valued bounded martingale machinery never has to be set up on path space.

## The backbone

Everything rests on two facts about `walkPathLaw`, proved here from Mathlib's
Ionescu-Tulcea API:

* `walkPathLaw_pathCyl`: the finite-dimensional distributions of the walk are
  the obvious products of `cylKernel` entries (`tex:246-255`);
* `measure_ext_of_pathCyl`: a finite measure on path space is determined by
  those cylinder values.

From these follow the one-step Markov identity `walkPathLaw_map_pathShift` and
the equivariance `walkPathLaw_map_siteEquiv` under any bijection of sites
preserving `cylKernel`.  Equivariance is used twice: under a graph automorphism
of `V_N` (this is where vertex-transitivity, `tex:229`, enters, and it is what
makes the first hit uniform) and under the vertical reflection `y ↦ -y`, which
turns the *upward* recurrence supplied by `External.LazyRwRecurrent`
(`tex:600-604`) into downward recurrence.

## `ℕ∞` versus `WithTop ℕ`

`MeasureTheory.hittingAfter` lands in `WithTop ι`, while `hitLevel` and
`exitTime'` are declared with codomain `ℕ∞ = ENat`, which is a *def*, not an
abbreviation.  The two types are definitionally equal, so term-mode
application of Mathlib's hitting-time lemmas works, but `rw`/`simp`, which
match at `instances` transparency, do not: `rw [hitLevel]` produces a goal that
is not type-correct at that transparency.  Every characterisation of a hitting
time below is therefore proved by `Iff.mp`/`Iff.mpr` in term mode, never by
rewriting the definition.

## Junk values

`hitLevel` is `ℕ∞`-valued and `firstHitSite` is `stoppedValue`, whose value on
`{hitLevel = ⊤}` is the opaque `WithTop.untopA ⊤`.  Every statement that reads
`firstHitSite` is therefore guarded by `walkPathLaw_hitLevel_top_null`, which
says that event is null; `hitProb` itself is a `toReal` of a probability, so it
is genuinely in `[0,1]` rather than `0` by accident.  `hitProb_at_layer` and
`hitProb_layer_sum` would both be false on the junk branch, so they are the
places to look if the guard is ever weakened.
-/
import IdlaCyl.Support.CanonicalIdla
import IdlaCyl.Support.Exit
import IdlaCyl.Support.Stopping
import IdlaCyl.External.Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace IdlaCyl

/-! ### `ℕ∞` scaffolding -/

/-- An element of `ℕ∞` is determined by the naturals that bound it. -/
theorem enat_eq_of_le_iff {a b : ℕ∞} (h : ∀ n : ℕ, a ≤ (n : ℕ∞) ↔ b ≤ (n : ℕ∞)) : a = b := by
  refine le_antisymm ?_ ?_
  · cases b with
    | top => exact le_top
    | coe n => exact (h n).mpr le_rfl
  · cases a with
    | top => exact le_top
    | coe n => exact (h n).mp le_rfl

theorem untopA_natCast (n : ℕ) : (WithTop.untopA ((n : ℕ) : ℕ∞)) = n := rfl

/-- On the finite branch the opaque `WithTop.untopA` agrees with `ENat.toNat`.
This is the only bridge needed between `stoppedValue`'s junk-tolerant reader and
the `toNat` form in which truncation arguments are phrased. -/
theorem untopA_eq_toNat {t : ℕ∞} (h : t ≠ ⊤) : WithTop.untopA t = t.toNat := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, t = ((n : ℕ) : ℕ∞) := ⟨t.toNat, (ENat.coe_toNat h).symm⟩
  rw [ENat.toNat_coe]
  exact untopA_natCast n

/-- The `n = 0` case of `hittingAfter`, in the form used throughout: the hitting
time equals `n` exactly when the process is in the set at time `n` and never
before. -/
theorem hittingAfter_zero_eq_coe_iff {Ω β : Type*} {u : ℕ → Ω → β} {s : Set β} {ω : Ω} {n : ℕ} :
    MeasureTheory.hittingAfter u s 0 ω = ((n : ℕ) : ℕ∞) ↔ u n ω ∈ s ∧ ∀ j < n, u j ω ∉ s := by
  constructor
  · intro h
    refine ⟨?_, fun j hj => ?_⟩
    · have hne : MeasureTheory.hittingAfter u s 0 ω ≠ ⊤ := by
        rw [h]; exact ENat.coe_ne_top n
      have hmem := MeasureTheory.hittingAfter_mem_set_of_ne_top hne
      rwa [h, untopA_natCast] at hmem
    · refine MeasureTheory.notMem_of_lt_hittingAfter ?_ (Nat.zero_le j)
      rw [h]
      exact ENat.coe_lt_coe.mpr hj
  · rintro ⟨h1, h2⟩
    refine le_antisymm (MeasureTheory.hittingAfter_le_of_mem (Nat.zero_le n) h1) ?_
    by_contra hlt
    obtain ⟨j, hj, hjs⟩ := MeasureTheory.hittingAfter_lt_iff.mp (not_le.mp hlt)
    exact h2 j hj.2 hjs

/-! ### Cylinder events on path space -/

/-- The event that the trajectory follows the prefix `f` up to time `b`. -/
def pathCyl (B : Base) (b : ℕ) (f : ℕ → Site B) : Set (ℕ → Site B) :=
  {X : ℕ → Site B | ∀ i ≤ b, X i = f i}

/-- The product of the kernel entries along the prefix `f` of length `b`. -/
noncomputable def pathWeight (B : Base) (b : ℕ) (f : ℕ → Site B) : ℝ≥0∞ :=
  ∏ i ∈ Finset.range b, ENNReal.ofReal (cylKernel B (f i) (f (i + 1)))

theorem pathWeight_zero (B : Base) (f : ℕ → Site B) : pathWeight B 0 f = 1 := by
  simp [pathWeight]

theorem pathWeight_succ (B : Base) (b : ℕ) (f : ℕ → Site B) :
    pathWeight B (b + 1) f
      = pathWeight B b f * ENNReal.ofReal (cylKernel B (f b) (f (b + 1))) :=
  Finset.prod_range_succ _ b

theorem pathCyl_succ (B : Base) (b : ℕ) (f : ℕ → Site B) :
    pathCyl B (b + 1) f = pathCyl B b f ∩ {X : ℕ → Site B | X (b + 1) = f (b + 1)} := by
  ext X
  simp only [pathCyl, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · intro h
    exact ⟨fun i hi => h i (hi.trans (Nat.le_succ b)), h (b + 1) le_rfl⟩
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.eq_or_lt_of_le hi with h | h
    · rw [h]; exact h2
    · exact h1 i (Nat.lt_succ_iff.mp h)

theorem measurableSet_pathCyl (B : Base) (b : ℕ) (f : ℕ → Site B) :
    MeasurableSet (pathCyl B b f) := by
  have hs : pathCyl B b f
      = ⋂ i ∈ Set.Iic b, ((fun X : ℕ → Site B => X i) ⁻¹' {f i}) := by
    ext X
    simp only [pathCyl, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_Iic]
  rw [hs]
  exact MeasurableSet.biInter (Set.to_countable _) fun i _ =>
    (measurable_pi_apply i) (measurableSet_singleton (f i))

/-- The prefix of `f` seen inside `Π i : Finset.Iic b, Site B`. -/
def prefixSet (B : Base) (b : ℕ) (f : ℕ → Site B) : Set (Π _ : Finset.Iic b, Site B) :=
  {z | ∀ i : Finset.Iic b, z i = f (i : ℕ)}

theorem prefixSet_eq_singleton (B : Base) (b : ℕ) (f : ℕ → Site B) :
    prefixSet B b f = ({Preorder.frestrictLe b f} : Set (Π _ : Finset.Iic b, Site B)) := by
  ext z
  simp only [prefixSet, Set.mem_setOf_eq, Set.mem_singleton_iff, funext_iff,
    Preorder.frestrictLe_apply]

theorem measurableSet_prefixSet (B : Base) (b : ℕ) (f : ℕ → Site B) :
    MeasurableSet (prefixSet B b f) := by
  rw [prefixSet_eq_singleton]
  exact measurableSet_singleton _

theorem preimage_frestrictLe_prefixSet (B : Base) (b : ℕ) (f : ℕ → Site B) :
    (Preorder.frestrictLe b) ⁻¹' (prefixSet B b f) = pathCyl B b f := by
  ext X
  simp only [Set.mem_preimage, prefixSet, Set.mem_setOf_eq, pathCyl,
    Preorder.frestrictLe_apply]
  exact ⟨fun h i hi => h ⟨i, Finset.mem_Iic.mpr hi⟩,
         fun h i => h (i : ℕ) (Finset.mem_Iic.mp i.2)⟩

/-- A total path extending a prefix; used only to name cylinders. -/
def ofPrefix (B : Base) (n : ℕ) (z : Π _ : Finset.Iic n, Site B) : ℕ → Site B :=
  fun i => z ⟨min i n, Finset.mem_Iic.mpr (min_le_right i n)⟩

theorem ofPrefix_apply_coe (B : Base) (n : ℕ) (z : Π _ : Finset.Iic n, Site B)
    (i : Finset.Iic n) : ofPrefix B n z (i : ℕ) = z i := by
  show z ⟨min (i : ℕ) n, _⟩ = z i
  congr 1
  exact Subtype.ext (min_eq_left (Finset.mem_Iic.mp i.2))

/-! ### The one-step law as point masses -/

theorem cylMeasure_singleton (B : Base) (p q : Site B) :
    cylMeasure B p {q} = ENNReal.ofReal (cylKernel B p q) := by
  unfold cylMeasure
  rw [Measure.sum_apply _ (measurableSet_singleton q)]
  rw [tsum_eq_single q (fun r hr => by
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (measurableSet_singleton q),
      Set.indicator_of_notMem (by simpa using hr), mul_zero])]
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton q),
    Set.indicator_of_mem (Set.mem_singleton q)]
  simp

theorem lintegral_cylMeasure (B : Base) (p : Site B) (g : Site B → ℝ≥0∞) :
    ∫⁻ q, g q ∂(cylMeasure B p) = ∑' q : Site B, ENNReal.ofReal (cylKernel B p q) * g q := by
  unfold cylMeasure
  rw [lintegral_sum_measure]
  refine tsum_congr fun q => ?_
  rw [lintegral_smul_measure, lintegral_dirac' _ (measurable_of_countable g), smul_eq_mul]

/-! ### Finite-dimensional distributions of `walkPathLaw` -/

/-- The Ionescu-Tulcea start vector of a one-point past reads back the start
site.  `Finset.Iic 0` is a subsingleton, so this is `Equiv.apply_symm_apply`. -/
theorem piUnique_symm_apply (B : Base) (p : Site B) (i : Finset.Iic (0 : ℕ)) :
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => Site B)).symm p i = p := by
  have hd : i = default := Subsingleton.elim i default
  rw [hd]
  exact (MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => Site B)).apply_symm_apply p

/-- The time-`0` past of the walk is the Dirac mass at its start: this is
`Kernel.partialTraj_self` read through `walkPathLaw_eq_traj`. -/
theorem walkPathLaw_map_frestrictLe_zero (B : Base) (p : Site B) :
    (walkPathLaw B p).map (Preorder.frestrictLe 0)
      = Measure.dirac
          ((MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => Site B)).symm p) := by
  rw [walkPathLaw_eq_traj, Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_self,
    Kernel.id_apply]

theorem walkPathLaw_map_zero (B : Base) (p : Site B) :
    (walkPathLaw B p).map (fun X : ℕ → Site B => X 0) = Measure.dirac p := by
  have h0 : Measurable (fun z : Π _ : Finset.Iic (0 : ℕ), Site B =>
      z ⟨0, Finset.mem_Iic.mpr le_rfl⟩) := measurable_pi_apply _
  have hmap : ((walkPathLaw B p).map (Preorder.frestrictLe 0)).map
        (fun z : Π _ : Finset.Iic (0 : ℕ), Site B => z ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
      = (walkPathLaw B p).map (fun X : ℕ → Site B => X 0) :=
    Measure.map_map h0 (Preorder.measurable_frestrictLe 0)
  have hdir : (Measure.dirac
        ((MeasurableEquiv.piUnique (fun _ : Finset.Iic (0 : ℕ) => Site B)).symm p)).map
        (fun z : Π _ : Finset.Iic (0 : ℕ), Site B => z ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
      = Measure.dirac p :=
    (Measure.map_dirac' h0 _).trans
      (congrArg (fun q : Site B => Measure.dirac q)
        (piUnique_symm_apply B p ⟨0, Finset.mem_Iic.mpr le_rfl⟩))
  rw [← hmap, walkPathLaw_map_frestrictLe_zero, hdir]

theorem walkPathLaw_ae_zero (B : Base) (p : Site B) :
    walkPathLaw B p {X : ℕ → Site B | X 0 ≠ p} = 0 := by
  have hset : {X : ℕ → Site B | X 0 ≠ p} = (fun X : ℕ → Site B => X 0) ⁻¹' ({p}ᶜ) := rfl
  rw [hset, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton p).compl,
    walkPathLaw_map_zero, Measure.dirac_apply' _ (measurableSet_singleton p).compl,
    Set.indicator_of_notMem (by simp)]

theorem walkPathLaw_ae_start (B : Base) (p : Site B) :
    ∀ᵐ X ∂(walkPathLaw B p), X 0 = p := by
  rw [MeasureTheory.ae_iff]
  exact walkPathLaw_ae_zero B p

/-- Mathlib's one-step disintegration of `trajMeasure`, stated for `walkPathLaw`. -/
theorem walkPathLaw_compProd (B : Base) (p : Site B) (a : ℕ) :
    (walkPathLaw B p).map (Preorder.frestrictLe a) ⊗ₘ (cylITKernel B a)
      = (walkPathLaw B p).map (fun X : ℕ → Site B => (Preorder.frestrictLe a X, X (a + 1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

/-- **The finite-dimensional distributions of the cylinder walk** (`tex:246-255`). -/
theorem walkPathLaw_pathCyl (B : Base) (p : Site B) (b : ℕ) (f : ℕ → Site B) :
    walkPathLaw B p (pathCyl B b f)
      = (if f 0 = p then 1 else 0) * pathWeight B b f := by
  induction b with
  | zero =>
    have hset : pathCyl B 0 f = (fun X : ℕ → Site B => X 0) ⁻¹' {f 0} := by
      ext X
      simp only [pathCyl, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => h 0 le_rfl, fun h i hi => by rw [Nat.le_zero.mp hi]; exact h⟩
    rw [hset, ← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton (f 0)),
      walkPathLaw_map_zero, Measure.dirac_apply' _ (measurableSet_singleton (f 0))]
    by_cases h : f 0 = p
    · subst h
      rw [Set.indicator_of_mem (Set.mem_singleton _)]
      simp [pathWeight_zero]
    · rw [Set.indicator_of_notMem (by simpa [eq_comm] using h)]
      simp [h]
  | succ b ih =>
    haveI : IsProbabilityMeasure ((walkPathLaw B p).map (Preorder.frestrictLe b)) :=
      Measure.isProbabilityMeasure_map (Preorder.measurable_frestrictLe b).aemeasurable
    have hmeas : Measurable (fun X : ℕ → Site B => (Preorder.frestrictLe b X, X (b + 1))) :=
      (Preorder.measurable_frestrictLe b).prodMk (measurable_pi_apply (b + 1))
    have hpre : (fun X : ℕ → Site B => (Preorder.frestrictLe b X, X (b + 1))) ⁻¹'
        (prefixSet B b f ×ˢ ({f (b + 1)} : Set (Site B))) = pathCyl B (b + 1) f := by
      ext X
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, prefixSet,
        Set.mem_setOf_eq, pathCyl, Preorder.frestrictLe_apply]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        rcases Nat.eq_or_lt_of_le hi with h | h
        · rw [h]; exact h2
        · exact h1 ⟨i, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp h)⟩
      · intro h
        exact ⟨fun i => h (i : ℕ) ((Finset.mem_Iic.mp i.2).trans (Nat.le_succ b)),
               h (b + 1) le_rfl⟩
    have key : walkPathLaw B p (pathCyl B (b + 1) f)
        = ∫⁻ z in prefixSet B b f, (cylITKernel B b) z {f (b + 1)}
            ∂((walkPathLaw B p).map (Preorder.frestrictLe b)) := by
      rw [← Measure.compProd_apply_prod (measurableSet_prefixSet B b f)
          (measurableSet_singleton (f (b + 1))), walkPathLaw_compProd,
        Measure.map_apply hmeas
          ((measurableSet_prefixSet B b f).prod (measurableSet_singleton _)), hpre]
    have hν : ((walkPathLaw B p).map (Preorder.frestrictLe b))
          ({Preorder.frestrictLe b f} : Set (Π _ : Finset.Iic b, Site B))
        = walkPathLaw B p (pathCyl B b f) := by
      rw [← prefixSet_eq_singleton, Measure.map_apply (Preorder.measurable_frestrictLe b)
        (measurableSet_prefixSet B b f), preimage_frestrictLe_prefixSet]
    have hker : (cylITKernel B b) (Preorder.frestrictLe b f) {f (b + 1)}
        = ENNReal.ofReal (cylKernel B (f b) (f (b + 1))) :=
      cylMeasure_singleton B (f b) (f (b + 1))
    calc walkPathLaw B p (pathCyl B (b + 1) f)
        = ∫⁻ z in prefixSet B b f, (cylITKernel B b) z {f (b + 1)}
            ∂((walkPathLaw B p).map (Preorder.frestrictLe b)) := key
      _ = walkPathLaw B p (pathCyl B b f)
            * ENNReal.ofReal (cylKernel B (f b) (f (b + 1))) := by
          rw [prefixSet_eq_singleton, Measure.restrict_singleton, lintegral_smul_measure,
            lintegral_dirac' _ (Kernel.measurable_coe _ (measurableSet_singleton (f (b + 1)))),
            smul_eq_mul, hker, hν]
      _ = (if f 0 = p then 1 else 0) * pathWeight B (b + 1) f := by
          rw [ih, pathWeight_succ]; ring

/-- **A finite measure on path space is determined by its cylinder values.** -/
theorem measure_ext_of_pathCyl (B : Base) {μ ν : Measure (ℕ → Site B)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (b : ℕ) (f : ℕ → Site B), μ (pathCyl B b f) = ν (pathCyl B b f)) :
    μ = ν := by
  have hIic : ∀ n : ℕ, μ.map (Preorder.frestrictLe n) = ν.map (Preorder.frestrictLe n) := by
    intro n
    refine Measure.ext_of_singleton fun z => ?_
    have hz : prefixSet B n (ofPrefix B n z) = {z} := by
      ext w
      simp only [prefixSet, Set.mem_setOf_eq, Set.mem_singleton_iff, funext_iff,
        ofPrefix_apply_coe]
    rw [Measure.map_apply (Preorder.measurable_frestrictLe n) (measurableSet_singleton z),
      Measure.map_apply (Preorder.measurable_frestrictLe n) (measurableSet_singleton z),
      ← hz, preimage_frestrictLe_prefixSet, h]
  have hall : ∀ I : Finset ℕ, μ.map I.restrict = ν.map I.restrict := by
    intro I
    have hIn : I ⊆ Finset.Iic (I.sup id) := fun i hi =>
      Finset.mem_Iic.mpr (Finset.le_sup (f := id) hi)
    have hcomp : (I.restrict : (ℕ → Site B) → Π _ : I, Site B)
        = (Finset.restrict₂ hIn) ∘ (Preorder.frestrictLe (I.sup id)) := rfl
    rw [hcomp, ← Measure.map_map (Finset.measurable_restrict₂ hIn)
        (Preorder.measurable_frestrictLe _),
      ← Measure.map_map (Finset.measurable_restrict₂ hIn)
        (Preorder.measurable_frestrictLe _), hIic]
  refine MeasureTheory.ext_of_generate_finite (measurableCylinders (fun _ : ℕ => Site B))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders (fun s hs => ?_) ?_
  · obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hs
    rw [cylinder, ← Measure.map_apply (Finset.measurable_restrict I) hS,
      ← Measure.map_apply (Finset.measurable_restrict I) hS, hall]
  · have h0 := congrArg (fun m => m (Set.univ : Set (Π _ : (∅ : Finset ℕ), Site B))) (hall ∅)
    simpa [Measure.map_apply (Finset.measurable_restrict (∅ : Finset ℕ)) MeasurableSet.univ]
      using h0

/-! ### The shift, and the one-step Markov property -/

/-- The one-step shift of a trajectory. -/
def pathShift (B : Base) (X : ℕ → Site B) : ℕ → Site B := fun n => X (n + 1)

theorem measurable_pathShift (B : Base) : Measurable (pathShift B) :=
  measurable_pi_lambda _ fun n => measurable_pi_apply (n + 1)

/-- Prepending a site to a prefix. -/
def consPath (B : Base) (q : Site B) (f : ℕ → Site B) : ℕ → Site B
  | 0 => q
  | (i + 1) => f i

@[simp] theorem consPath_zero (B : Base) (q : Site B) (f : ℕ → Site B) :
    consPath B q f 0 = q := rfl

@[simp] theorem consPath_succ (B : Base) (q : Site B) (f : ℕ → Site B) (i : ℕ) :
    consPath B q f (i + 1) = f i := rfl

theorem isProbabilityMeasure_bind_walkPathLaw (B : Base) (p : Site B) :
    IsProbabilityMeasure ((cylMeasure B p).bind (walkPathLaw B)) := by
  haveI := cylMeasure_isProbability B p
  constructor
  rw [Measure.bind_apply MeasurableSet.univ (measurable_of_countable _).aemeasurable]
  simp

theorem bind_walkPathLaw_apply (B : Base) (p : Site B) {A : Set (ℕ → Site B)}
    (hA : MeasurableSet A) :
    ((cylMeasure B p).bind (walkPathLaw B)) A
      = ∑' q : Site B, ENNReal.ofReal (cylKernel B p q) * walkPathLaw B q A := by
  rw [Measure.bind_apply hA (measurable_of_countable _).aemeasurable, lintegral_cylMeasure]

/-- **The one-step Markov property of the cylinder walk.** -/
theorem walkPathLaw_map_pathShift (B : Base) (p : Site B) :
    (walkPathLaw B p).map (pathShift B) = (cylMeasure B p).bind (walkPathLaw B) := by
  haveI : IsProbabilityMeasure ((walkPathLaw B p).map (pathShift B)) :=
    Measure.isProbabilityMeasure_map (measurable_pathShift B).aemeasurable
  haveI := isProbabilityMeasure_bind_walkPathLaw B p
  refine measure_ext_of_pathCyl B (fun b f => ?_)
  have hpre : (pathShift B) ⁻¹' (pathCyl B b f)
      = ⋃ q : Site B, pathCyl B (b + 1) (consPath B q f) := by
    ext X
    simp only [Set.mem_preimage, pathCyl, Set.mem_setOf_eq, Set.mem_iUnion, pathShift]
    constructor
    · intro h
      refine ⟨X 0, fun i hi => ?_⟩
      cases i with
      | zero => rfl
      | succ j => exact h j (Nat.succ_le_succ_iff.mp hi)
    · rintro ⟨q, hq⟩ i hi
      exact hq (i + 1) (Nat.succ_le_succ hi)
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun q : Site B => pathCyl B (b + 1) (consPath B q f))) := by
    intro q q' hqq'
    refine Set.disjoint_left.mpr fun X hX hX' => hqq' ?_
    have h1 : X 0 = q := hX 0 (Nat.zero_le _)
    have h2 : X 0 = q' := hX' 0 (Nat.zero_le _)
    exact h1.symm.trans h2
  have hw : ∀ q : Site B, pathWeight B (b + 1) (consPath B q f)
      = pathWeight B b f * ENNReal.ofReal (cylKernel B q (f 0)) := by
    intro q
    unfold pathWeight
    rw [Finset.prod_range_succ']
    simp [consPath_zero, consPath_succ]
  rw [Measure.map_apply (measurable_pathShift B) (measurableSet_pathCyl B b f), hpre,
    measure_iUnion hdisj (fun q => measurableSet_pathCyl B (b + 1) (consPath B q f))]
  rw [bind_walkPathLaw_apply B p (measurableSet_pathCyl B b f)]
  simp only [walkPathLaw_pathCyl, consPath_zero, hw]
  rw [tsum_eq_single p (fun q hq => by rw [if_neg hq, zero_mul]),
    tsum_eq_single (f 0) (fun q hq => by rw [if_neg (Ne.symm hq), zero_mul, mul_zero])]
  rw [if_pos rfl, if_pos rfl]
  ring

/-! ### Equivariance -/

/-- A bijection of sites preserving `cylKernel` intertwines the walk laws. -/
theorem walkPathLaw_map_siteEquiv (B : Base) (e : Site B ≃ Site B)
    (he : ∀ u v : Site B, cylKernel B (e u) (e v) = cylKernel B u v) (p : Site B) :
    (walkPathLaw B p).map (fun X : ℕ → Site B => fun n => e (X n))
      = walkPathLaw B (e p) := by
  have hmeas : Measurable (fun (X : ℕ → Site B) (n : ℕ) => e (X n)) :=
    measurable_pi_lambda _ fun n => (measurable_of_countable e).comp (measurable_pi_apply n)
  haveI : IsProbabilityMeasure
      ((walkPathLaw B p).map (fun X : ℕ → Site B => fun n => e (X n))) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine measure_ext_of_pathCyl B (fun b f => ?_)
  have hpre : (fun (X : ℕ → Site B) (n : ℕ) => e (X n)) ⁻¹' (pathCyl B b f)
      = pathCyl B b (fun i => e.symm (f i)) := by
    ext X
    simp only [Set.mem_preimage, pathCyl, Set.mem_setOf_eq]
    refine forall_congr' fun i => forall_congr' fun _ => ?_
    constructor
    · intro h; rw [← h, Equiv.symm_apply_apply]
    · intro h; rw [h, Equiv.apply_symm_apply]
  rw [Measure.map_apply hmeas (measurableSet_pathCyl B b f), hpre,
    walkPathLaw_pathCyl, walkPathLaw_pathCyl]
  congr 1
  · by_cases h : f 0 = e p
    · rw [if_pos h, if_pos (show e.symm (f 0) = p by rw [h, Equiv.symm_apply_apply])]
    · rw [if_neg h]
      refine if_neg ?_
      intro hc
      exact h (by rw [← hc, Equiv.apply_symm_apply])
  · simp only [pathWeight]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← he (e.symm (f i)) (e.symm (f (i + 1))), Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]

/-- Reflection of the cylinder in the layer `y = 0` (`tex:246-255` is symmetric
in the vertical coordinate). -/
def verNeg (B : Base) : Site B ≃ Site B where
  toFun q := (q.1, -q.2)
  invFun q := (q.1, -q.2)
  left_inv q := by simp
  right_inv q := by simp

@[simp] theorem verNeg_apply (B : Base) (q : Site B) : verNeg B q = (q.1, -q.2) := rfl

@[simp] theorem verNeg_verNeg (B : Base) (q : Site B) : verNeg B (verNeg B q) = q := by
  simp

theorem cylKernel_verNeg (B : Base) (u v : Site B) :
    cylKernel B (verNeg B u) (verNeg B v) = cylKernel B u v := by
  have h2 : ((-u.2 : ℤ) - (-v.2)).natAbs = (u.2 - v.2).natAbs := by
    have hx : ((-u.2 : ℤ) - (-v.2)) = -(u.2 - v.2) := by ring
    rw [hx, Int.natAbs_neg]
  unfold cylKernel
  simp only [verNeg_apply, neg_inj, h2]

/-- A graph automorphism of the base, acting on the cylinder. -/
def horIso (B : Base) (σ : B.graph ≃g B.graph) : Site B ≃ Site B where
  toFun q := (σ q.1, q.2)
  invFun q := (σ.symm q.1, q.2)
  left_inv q := Prod.ext_iff.mpr ⟨σ.symm_apply_apply q.1, rfl⟩
  right_inv q := Prod.ext_iff.mpr ⟨σ.apply_symm_apply q.1, rfl⟩

@[simp] theorem horIso_apply (B : Base) (σ : B.graph ≃g B.graph) (q : Site B) :
    horIso B σ q = (σ q.1, q.2) := rfl

theorem P_horIso (B : Base) (σ : B.graph ≃g B.graph) (x x' : B.V) :
    B.P (σ x) (σ x') = B.P x x' := by
  have hadj : B.graph.Adj (σ x) (σ x') ↔ B.graph.Adj x x' := σ.map_rel_iff
  have heq : (σ x = σ x') ↔ (x = x') := by
    constructor
    · intro h
      have hh := congrArg (fun y => σ.symm y) h
      simpa using hh
    · intro h; rw [h]
  unfold Base.P
  by_cases h : B.graph.Adj x x'
  · rw [if_pos (hadj.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (hadj.mp hc)), if_neg h]
    by_cases h2 : x = x'
    · rw [if_pos (heq.mpr h2), if_pos h2]
    · rw [if_neg (fun hc => h2 (heq.mp hc)), if_neg h2]

theorem cylKernel_horIso (B : Base) (σ : B.graph ≃g B.graph) (u v : Site B) :
    cylKernel B (horIso B σ u) (horIso B σ v) = cylKernel B u v := by
  have heq : ((σ u.1) = (σ v.1)) ↔ (u.1 = v.1) := by
    constructor
    · intro h
      have hh := congrArg (fun y => σ.symm y) h
      simpa using hh
    · intro h; rw [h]
  unfold cylKernel
  simp only [horIso_apply, heq, P_horIso]

/-! ### The walk moves by at most one level per step -/

theorem ver_step_le_of_cylKernel_ne_zero (B : Base) (u v : Site B)
    (h : cylKernel B u v ≠ 0) : (v.2 - u.2).natAbs ≤ 1 := by
  unfold cylKernel at h
  split_ifs at h with h1 h2
  · have := h1.2
    omega
  · omega
  · exact absurd rfl h

theorem measurableSet_step_zero (B : Base) (n : ℕ) :
    MeasurableSet {X : ℕ → Site B | cylKernel B (X n) (X (n + 1)) = 0} := by
  have hs : {X : ℕ → Site B | cylKernel B (X n) (X (n + 1)) = 0}
      = (fun X : ℕ → Site B => (X n, X (n + 1))) ⁻¹'
        {uv : Site B × Site B | cylKernel B uv.1 uv.2 = 0} := rfl
  rw [hs]
  exact ((measurable_pi_apply n).prodMk (measurable_pi_apply (n + 1)))
    ((Set.to_countable _).measurableSet)

theorem walkPathLaw_step_null (B : Base) (n : ℕ) (p : Site B) :
    walkPathLaw B p {X : ℕ → Site B | cylKernel B (X n) (X (n + 1)) = 0} = 0 := by
  induction n generalizing p with
  | zero =>
    have hmeasD : MeasurableSet {Y : ℕ → Site B | cylKernel B p (Y 0) = 0} := by
      have hset : {Y : ℕ → Site B | cylKernel B p (Y 0) = 0}
          = (fun Y : ℕ → Site B => Y 0) ⁻¹' {q : Site B | cylKernel B p q = 0} := rfl
      rw [hset]
      exact (measurable_pi_apply 0) ((Set.to_countable _).measurableSet)
    have hsub : {X : ℕ → Site B | cylKernel B (X 0) (X 1) = 0}
        ⊆ {X : ℕ → Site B | X 0 ≠ p} ∪
          (pathShift B) ⁻¹' {Y : ℕ → Site B | cylKernel B p (Y 0) = 0} := by
      intro X hX
      by_cases h0 : X 0 = p
      · refine Or.inr ?_
        show cylKernel B p ((pathShift B X) 0) = 0
        rw [← h0]
        exact hX
      · exact Or.inl h0
    refine measure_mono_null hsub (measure_union_null (walkPathLaw_ae_zero B p) ?_)
    rw [← Measure.map_apply (measurable_pathShift B) hmeasD, walkPathLaw_map_pathShift,
      bind_walkPathLaw_apply B p hmeasD]
    refine ENNReal.tsum_eq_zero.mpr fun q => ?_
    by_cases hq : cylKernel B p q = 0
    · rw [hq, ENNReal.ofReal_zero, zero_mul]
    · have hz : walkPathLaw B q {Y : ℕ → Site B | cylKernel B p (Y 0) = 0} = 0 := by
        refine measure_mono_null (fun Y hY => ?_) (walkPathLaw_ae_zero B q)
        have hY' : cylKernel B p (Y 0) = 0 := hY
        intro hc
        rw [hc] at hY'
        exact hq hY'
      rw [hz, mul_zero]
  | succ n ih =>
    have hset : {X : ℕ → Site B | cylKernel B (X (n + 1)) (X (n + 1 + 1)) = 0}
        = (pathShift B) ⁻¹' {X : ℕ → Site B | cylKernel B (X n) (X (n + 1)) = 0} := rfl
    rw [hset, ← Measure.map_apply (measurable_pathShift B) (measurableSet_step_zero B n),
      walkPathLaw_map_pathShift, bind_walkPathLaw_apply B p (measurableSet_step_zero B n)]
    simp only [ih, mul_zero, tsum_zero]

theorem walkPathLaw_ae_steps (B : Base) (p : Site B) :
    ∀ᵐ X ∂(walkPathLaw B p), ∀ n : ℕ, ((X (n + 1)).2 - (X n).2).natAbs ≤ 1 := by
  rw [MeasureTheory.ae_all_iff]
  intro n
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (fun X hX => ?_) (walkPathLaw_step_null B n p)
  by_contra hc
  exact hX (ver_step_le_of_cylKernel_ne_zero B (X n) (X (n + 1)) hc)

/-- Discrete intermediate value theorem for a `±1`-bounded integer sequence. -/
theorem exists_ver_eq (k : ℤ) (Y : ℕ → ℤ)
    (hstep : ∀ n : ℕ, (Y (n + 1) - Y n).natAbs ≤ 1)
    (h0 : Y 0 ≤ k) (hex : ∃ n, k ≤ Y n) : ∃ m, Y m = k := by
  classical
  refine ⟨Nat.find hex, ?_⟩
  have hn : k ≤ Y (Nat.find hex) := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h]; rw [h] at hn; omega
  · obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hmin : ¬ (k ≤ Y m) := Nat.find_min hex (by omega)
    have hs := hstep m
    rw [hm] at hn ⊢
    omega

/-! ### The hitting time of a layer -/

/-- The first time the walk is at vertical level `k` (`tex:596`). -/
noncomputable def hitLevel (B : Base) (k : ℤ) : (ℕ → Site B) → ℕ∞ :=
  MeasureTheory.hittingAfter (fun (n : ℕ) (X : ℕ → Site B) => (X n).2) {k} 0

/-- The site at which the walk first meets level `k` (`tex:597`). -/
noncomputable def firstHitSite (B : Base) (k : ℤ) : (ℕ → Site B) → Site B :=
  MeasureTheory.stoppedValue (fun (n : ℕ) (X : ℕ → Site B) => X n) (hitLevel B k)

theorem hitLevel_le_iff (B : Base) (k : ℤ) (X : ℕ → Site B) (n : ℕ) :
    hitLevel B k X ≤ ((n : ℕ) : ℕ∞) ↔ ∃ j ≤ n, (X j).2 = k := by
  constructor
  · intro h
    obtain ⟨j, hj, hjk⟩ := MeasureTheory.hittingAfter_le_iff.mp h
    exact ⟨j, hj.2, hjk⟩
  · rintro ⟨j, hj, hjk⟩
    exact MeasureTheory.hittingAfter_le_iff.mpr ⟨j, ⟨Nat.zero_le j, hj⟩, hjk⟩

theorem hitLevel_eq_coe_iff (B : Base) (k : ℤ) (X : ℕ → Site B) (n : ℕ) :
    hitLevel B k X = ((n : ℕ) : ℕ∞) ↔ (X n).2 = k ∧ ∀ j < n, (X j).2 ≠ k :=
  hittingAfter_zero_eq_coe_iff

theorem hitLevel_eq_top_iff (B : Base) (k : ℤ) (X : ℕ → Site B) :
    hitLevel B k X = ⊤ ↔ ∀ n, (X n).2 ≠ k := by
  constructor
  · intro h n
    exact MeasureTheory.hittingAfter_eq_top_iff.mp h n (Nat.zero_le n)
  · intro h
    exact MeasureTheory.hittingAfter_eq_top_iff.mpr (fun n _ => h n)

theorem firstHitSite_eq_of_hitLevel_eq (B : Base) (k : ℤ) (X : ℕ → Site B) (n : ℕ)
    (h : hitLevel B k X = ((n : ℕ) : ℕ∞)) : firstHitSite B k X = X n := by
  show X (WithTop.untopA (hitLevel B k X)) = X n
  rw [h, untopA_natCast]

theorem firstHitSite_ver (B : Base) (k : ℤ) (X : ℕ → Site B) (h : hitLevel B k X ≠ ⊤) :
    (firstHitSite B k X).2 = k := by
  have hm := MeasureTheory.hittingAfter_mem_set_of_ne_top
    (u := fun (n : ℕ) (Y : ℕ → Site B) => (Y n).2) (s := ({k} : Set ℤ)) (n := 0) (ω := X) h
  show (X (WithTop.untopA (hitLevel B k X))).2 = k
  exact hm

theorem hitLevel_congr (B : Base) (k : ℤ) {X Y : ℕ → Site B} (h : ∀ n, (X n).2 = (Y n).2) :
    hitLevel B k X = hitLevel B k Y := by
  refine enat_eq_of_le_iff fun n => ?_
  rw [hitLevel_le_iff, hitLevel_le_iff]
  exact exists_congr fun j => and_congr_right fun _ => by rw [h j]

/-- `firstHitSite` commutes with any site map that fixes the vertical coordinate. -/
theorem firstHitSite_map (B : Base) (k : ℤ) (e : Site B → Site B)
    (he : ∀ q, (e q).2 = q.2) (X : ℕ → Site B) :
    firstHitSite B k (fun n => e (X n)) = e (firstHitSite B k X) := by
  have h : hitLevel B k (fun n => e (X n)) = hitLevel B k X :=
    hitLevel_congr B k (fun n => he (X n))
  show (fun n => e (X n)) (WithTop.untopA (hitLevel B k (fun n => e (X n))))
      = e (X (WithTop.untopA (hitLevel B k X)))
  rw [h]

/-- If the walk misses level `k` before time `n+1`, the first hit is unchanged by
one shift. -/
theorem firstHitSite_shift (B : Base) (k : ℤ) (X : ℕ → Site B)
    (h0 : (X 0).2 ≠ k) (hfin : hitLevel B k X ≠ ⊤) :
    firstHitSite B k X = firstHitSite B k (pathShift B X) := by
  have hcoe : hitLevel B k X = (((hitLevel B k X).toNat : ℕ) : ℕ∞) :=
    (ENat.coe_toNat hfin).symm
  set n := (hitLevel B k X).toNat with hn
  have hspec := (hitLevel_eq_coe_iff B k X n).mp hcoe
  have hn0 : n ≠ 0 := by
    intro h
    rw [h] at hspec
    exact h0 hspec.1
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hshift : hitLevel B k (pathShift B X) = ((m : ℕ) : ℕ∞) := by
    rw [hitLevel_eq_coe_iff]
    refine ⟨?_, ?_⟩
    · show (X (m + 1)).2 = k
      rw [← hm]; exact hspec.1
    · intro j hj
      show (X (j + 1)).2 ≠ k
      exact hspec.2 (j + 1) (by omega)
  rw [firstHitSite_eq_of_hitLevel_eq B k X n hcoe,
    firstHitSite_eq_of_hitLevel_eq B k (pathShift B X) m hshift]
  show X n = X (m + 1)
  rw [hm]

/-! ### Measurability -/

theorem measurableSet_hitLevel_eq (B : Base) (k : ℤ) (t : ℕ∞) :
    MeasurableSet {X : ℕ → Site B | hitLevel B k X = t} := by
  cases t with
  | top =>
    have hset : {X : ℕ → Site B | hitLevel B k X = ⊤}
        = ⋂ n : ℕ, ((fun X : ℕ → Site B => (X n).2) ⁻¹' ({k}ᶜ)) := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff, hitLevel_eq_top_iff]
    rw [hset]
    exact MeasurableSet.iInter fun n =>
      ((measurable_pi_apply n).snd) (measurableSet_singleton k).compl
  | coe n =>
    have hset : {X : ℕ → Site B | hitLevel B k X = ((n : ℕ) : ℕ∞)}
        = ((fun X : ℕ → Site B => (X n).2) ⁻¹' {k})
          ∩ ⋂ j ∈ Set.Iio n, ((fun X : ℕ → Site B => (X j).2) ⁻¹' ({k}ᶜ)) := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
        Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_Iio, hitLevel_eq_coe_iff]
    rw [hset]
    exact (((measurable_pi_apply n).snd) (measurableSet_singleton k)).inter
      (MeasurableSet.biInter (Set.to_countable _) fun j _ =>
        ((measurable_pi_apply j).snd) (measurableSet_singleton k).compl)

theorem measurable_firstHitSite (B : Base) (k : ℤ) : Measurable (firstHitSite B k) := by
  refine measurable_to_countable' fun q => ?_
  have hset : firstHitSite B k ⁻¹' {q}
      = ⋃ t : ℕ∞, ({X : ℕ → Site B | hitLevel B k X = t}
          ∩ (fun X : ℕ → Site B => X (WithTop.untopA t)) ⁻¹' {q}) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    constructor
    · intro hX; exact ⟨hitLevel B k X, rfl, hX⟩
    · rintro ⟨t, ht, hq⟩
      show X (WithTop.untopA (hitLevel B k X)) = q
      rw [ht]; exact hq
  rw [hset]
  exact MeasurableSet.iUnion fun t =>
    (measurableSet_hitLevel_eq B k t).inter
      ((measurable_pi_apply (WithTop.untopA t)) (measurableSet_singleton q))

/-! ### Almost sure finiteness of the hitting time -/

theorem ae_exists_ver_eq (hrec : External.LazyRwRecurrent) (B : Base) (p : Site B) (k : ℤ) :
    ∀ᵐ X ∂(walkPathLaw B p), ∃ n, (X n).2 = k := by
  have hup : ∀ (q : Site B) (m : ℤ), q.2 ≤ m →
      ∀ᵐ X ∂(walkPathLaw B q), ∃ n, (X n).2 = m := by
    intro q m hqm
    filter_upwards [hrec B q m, walkPathLaw_ae_start B q, walkPathLaw_ae_steps B q]
      with X h1 h2 h3
    refine exists_ver_eq m (fun n => (X n).2) h3 ?_ h1
    rw [h2]; exact hqm
  rcases le_or_gt p.2 k with h | h
  · exact hup p k h
  · have hmap : (walkPathLaw B (verNeg B p)).map
        (fun X : ℕ → Site B => fun n => verNeg B (X n)) = walkPathLaw B p := by
      rw [walkPathLaw_map_siteEquiv B (verNeg B) (cylKernel_verNeg B) (verNeg B p),
        verNeg_verNeg]
    have hE : Measurable (fun (X : ℕ → Site B) (n : ℕ) => verNeg B (X n)) :=
      measurable_pi_lambda _ fun n =>
        (measurable_of_countable (verNeg B)).comp (measurable_pi_apply n)
    have hmeasSet : MeasurableSet {Y : ℕ → Site B | ∃ n, (Y n).2 = k} := by
      have hs : {Y : ℕ → Site B | ∃ n, (Y n).2 = k}
          = ⋃ n : ℕ, ((fun Y : ℕ → Site B => (Y n).2) ⁻¹' {k}) := by
        ext Y
        simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff]
      rw [hs]
      exact MeasurableSet.iUnion fun n =>
        ((measurable_pi_apply n).snd) (measurableSet_singleton k)
    have hstart : (verNeg B p).2 ≤ -k := by
      show -p.2 ≤ -k
      omega
    have hbase := hup (verNeg B p) (-k) hstart
    have hpush : ∀ᵐ Y ∂((walkPathLaw B (verNeg B p)).map
        (fun X : ℕ → Site B => fun n => verNeg B (X n))), ∃ n, (Y n).2 = k := by
      refine (MeasureTheory.ae_map_iff hE.aemeasurable hmeasSet).mpr ?_
      filter_upwards [hbase] with X hX
      obtain ⟨n, hn⟩ := hX
      refine ⟨n, ?_⟩
      show -(X n).2 = k
      omega
    rwa [hmap] at hpush

theorem walkPathLaw_hitLevel_top_null (hrec : External.LazyRwRecurrent) (B : Base)
    (p : Site B) (k : ℤ) :
    walkPathLaw B p {X : ℕ → Site B | hitLevel B k X = ⊤} = 0 := by
  have hex := ae_exists_ver_eq hrec B p k
  rw [MeasureTheory.ae_iff] at hex
  refine measure_mono_null (fun X hX => ?_) hex
  rw [Set.mem_setOf_eq, hitLevel_eq_top_iff] at hX
  rintro ⟨n, hn⟩
  exact hX n hn

theorem ae_hitLevel_ne_top (hrec : External.LazyRwRecurrent) (B : Base)
    (p : Site B) (k : ℤ) :
    ∀ᵐ X ∂(walkPathLaw B p), hitLevel B k X ≠ ⊤ := by
  have h := walkPathLaw_hitLevel_top_null hrec B p k
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (fun X hX => ?_) h
  simpa using not_not.mp hX

/-! ### `H_ζ` -/

/-- `H_ζ` before taking `toReal`: the probability that the walk from `p` first
meets the layer of `ζ` at `ζ` (`tex:1185-1187`). -/
noncomputable def hitProbE (B : Base) (ζ : Site B) (p : Site B) : ℝ≥0∞ :=
  (walkPathLaw B p) {X | firstHitSite B ζ.2 X = ζ}

/-- The same quantity written as the measure of a preimage; needed to line
`hitProbE` up with `map_firstHitSite_singleton`. -/
theorem hitProbE_eq_preimage (B : Base) (ζ p : Site B) :
    hitProbE B ζ p = walkPathLaw B p (firstHitSite B ζ.2 ⁻¹' {ζ}) := rfl

theorem measurableSet_firstHit (B : Base) (ζ : Site B) :
    MeasurableSet {X : ℕ → Site B | firstHitSite B ζ.2 X = ζ} :=
  (measurable_firstHitSite B ζ.2) (measurableSet_singleton ζ)

theorem hitProbE_le_one (B : Base) (ζ p : Site B) : hitProbE B ζ p ≤ 1 :=
  prob_le_one

theorem hitProbE_ne_top (B : Base) (ζ p : Site B) : hitProbE B ζ p ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (hitProbE_le_one B ζ p)

/-- `H_ζ(x,y)`: the probability that the cylinder walk from `(x,y)` reaches the
layer `V_N × {ζ.2}` for the first time at `ζ`, with the paper's convention
`H_ζ(x,y) = 0` for `y > ζ.2` (`tex:1185-1187`). -/
noncomputable def hitProb (B : Base) (ζ : Site B) (p : Site B) : ℝ :=
  if ζ.2 < p.2 then 0
  else ((walkPathLaw B p) {X | firstHitSite B ζ.2 X = ζ}).toReal

theorem hitProb_eq_toReal (B : Base) (ζ p : Site B) (h : ¬ ζ.2 < p.2) :
    hitProb B ζ p = (hitProbE B ζ p).toReal := if_neg h

theorem hitProb_nonneg (B : Base) (ζ p : Site B) : 0 ≤ hitProb B ζ p := by
  unfold hitProb
  split_ifs
  · exact le_rfl
  · exact ENNReal.toReal_nonneg

theorem hitProb_le_one (B : Base) (ζ p : Site B) : hitProb B ζ p ≤ 1 := by
  unfold hitProb
  split_ifs
  · norm_num
  · have h := ENNReal.toReal_mono ENNReal.one_ne_top (hitProbE_le_one B ζ p)
    rwa [ENNReal.toReal_one] at h

/-- `H_ζ² ≤ H_ζ` (`tex:1208`). -/
theorem hitProb_sq_le (B : Base) (ζ p : Site B) : hitProb B ζ p ^ 2 ≤ hitProb B ζ p := by
  have h0 := hitProb_nonneg B ζ p
  have h1 := hitProb_le_one B ζ p
  have h := mul_le_of_le_one_left h0 h1
  calc hitProb B ζ p ^ 2 = hitProb B ζ p * hitProb B ζ p := by ring
    _ ≤ hitProb B ζ p := h

theorem hitProb_above (B : Base) (ζ p : Site B) (h : ζ.2 < p.2) : hitProb B ζ p = 0 :=
  if_pos h

/-- `H_ζ(x,h) = 1(x = z)` on the stopping layer (`tex:1231`). -/
theorem hitProb_at_layer (B : Base) (ζ : Site B) (x : B.V) :
    hitProb B ζ (x, ζ.2) = if x = ζ.1 then 1 else 0 := by
  have hfh : ∀ X : ℕ → Site B, X 0 = ((x, ζ.2) : Site B) →
      firstHitSite B ζ.2 X = ((x, ζ.2) : Site B) := by
    intro X hX
    have h0 : hitLevel B ζ.2 X = (((0 : ℕ) : ℕ) : ℕ∞) := by
      rw [hitLevel_eq_coe_iff]
      exact ⟨by rw [hX], fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    rw [firstHitSite_eq_of_hitLevel_eq B ζ.2 X 0 h0, hX]
  rw [hitProb_eq_toReal B ζ _ (by simp)]
  by_cases hx : x = ζ.1
  · have hzeta : ((x, ζ.2) : Site B) = ζ := by
      rw [hx]
    have hone : hitProbE B ζ ((x, ζ.2) : Site B) = 1 := by
      have hc : walkPathLaw B ((x, ζ.2) : Site B)
          ({X : ℕ → Site B | firstHitSite B ζ.2 X = ζ}ᶜ) = 0 := by
        refine measure_mono_null (fun X hX => ?_) (walkPathLaw_ae_zero B ((x, ζ.2) : Site B))
        intro h0
        exact hX (by simpa [Set.mem_setOf_eq] using (hfh X h0).trans hzeta)
      have hadd := measure_add_measure_compl
        (μ := walkPathLaw B ((x, ζ.2) : Site B)) (measurableSet_firstHit B ζ)
      rw [hc, add_zero, measure_univ] at hadd
      exact hadd
    rw [hone, if_pos hx]
    simp
  · have hzero : hitProbE B ζ ((x, ζ.2) : Site B) = 0 := by
      refine measure_mono_null (fun X hX => ?_) (walkPathLaw_ae_zero B ((x, ζ.2) : Site B))
      intro h0
      apply hx
      have hv := hfh X h0
      rw [Set.mem_setOf_eq] at hX
      rw [hv] at hX
      exact congrArg Prod.fst hX
    rw [hzero, if_neg hx]
    simp

/-! ### Harmonicity -/

/-- `H_ζ` is harmonic off the layer of `ζ`, in `ℝ≥0∞` form (`tex:1189`). -/
theorem hitProbE_harmonic (B : Base) (ζ : Site B) (p : Site B) (hp : p.2 ≠ ζ.2)
    (hrec : External.LazyRwRecurrent) :
    ∑' q : Site B, ENNReal.ofReal (cylKernel B p q) * hitProbE B ζ q = hitProbE B ζ p := by
  have hA := measurableSet_firstHit B ζ
  have hshift : walkPathLaw B p {X : ℕ → Site B | firstHitSite B ζ.2 X = ζ}
      = walkPathLaw B p ((pathShift B) ⁻¹' {X : ℕ → Site B | firstHitSite B ζ.2 X = ζ}) := by
    refine measure_congr ?_
    filter_upwards [walkPathLaw_ae_start B p, ae_hitLevel_ne_top hrec B p ζ.2] with X h0 hfin
    have hEq := firstHitSite_shift B ζ.2 X (by rw [h0]; exact hp) hfin
    show (firstHitSite B ζ.2 X = ζ) = (firstHitSite B ζ.2 (pathShift B X) = ζ)
    rw [hEq]
  have hrhs : hitProbE B ζ p
      = ∑' q : Site B, ENNReal.ofReal (cylKernel B p q) * hitProbE B ζ q := by
    show walkPathLaw B p {X : ℕ → Site B | firstHitSite B ζ.2 X = ζ} = _
    rw [hshift, ← Measure.map_apply (measurable_pathShift B) hA, walkPathLaw_map_pathShift,
      bind_walkPathLaw_apply B p hA]
    rfl
  exact hrhs.symm

/-- `H_ζ` is discrete harmonic on `R_{ζ.2 - 1}` (`tex:1189`). -/
theorem hitProb_harmonic (B : Base) (ζ : Site B) (p : Site B) (hp : p.2 < ζ.2)
    (hrec : External.LazyRwRecurrent) :
    (1/4) * hitProb B ζ (p.1, p.2 + 1) + (1/4) * hitProb B ζ (p.1, p.2 - 1)
      + (1/2) * ∑ x' : B.V, B.P p.1 x' * hitProb B ζ (x', p.2) = hitProb B ζ p := by
  classical
  set F : Finset (Site B) := Finset.univ ×ˢ ({p.2 - 1, p.2, p.2 + 1} : Finset ℤ) with hF
  have hzero : ∀ q ∉ F, ENNReal.ofReal (cylKernel B p q) * hitProbE B ζ q = 0 := by
    intro q hq
    simp only [hF, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, not_or] at hq
    obtain ⟨hq1, hq2, hq3⟩ := hq
    have hk0 : cylKernel B p q = 0 := by
      unfold cylKernel
      split_ifs with h1 h2
      · exfalso
        have := h1.2
        omega
      · exact absurd h2.symm hq2
      · rfl
    rw [hk0, ENNReal.ofReal_zero, zero_mul]
  have hfin : ∑ q ∈ F, ENNReal.ofReal (cylKernel B p q) * hitProbE B ζ q = hitProbE B ζ p := by
    have hharm := hitProbE_harmonic B ζ p (by omega) hrec
    rwa [tsum_eq_sum hzero] at hharm
  -- pass to real numbers
  have hlev : ∀ q ∈ F, ¬ ζ.2 < q.2 := by
    intro q hq
    simp only [hF, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at hq
    rcases hq with h | h | h <;> omega
  have hreal : ∑ q ∈ F, cylKernel B p q * hitProb B ζ q = hitProb B ζ p := by
    have h1 := congrArg ENNReal.toReal hfin
    rw [ENNReal.toReal_sum (fun q _ => by
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hitProbE_ne_top B ζ q))] at h1
    rw [hitProb_eq_toReal B ζ p (by omega)]
    rw [← h1]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (cylKernel_nonneg p q),
      hitProb_eq_toReal B ζ q (hlev q hq)]
  rw [← hreal, hF, Finset.sum_product]
  have hT : ∀ x : B.V, ∑ y ∈ ({p.2 - 1, p.2, p.2 + 1} : Finset ℤ),
      cylKernel B p (x, y) * hitProb B ζ (x, y)
      = cylKernel B p (x, p.2 - 1) * hitProb B ζ (x, p.2 - 1)
        + (1/2 : ℝ) * B.P p.1 x * hitProb B ζ (x, p.2)
        + cylKernel B p (x, p.2 + 1) * hitProb B ζ (x, p.2 + 1) := by
    intro x
    have h1 : p.2 - 1 ∉ ({p.2, p.2 + 1} : Finset ℤ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    have h2 : p.2 ∉ ({p.2 + 1} : Finset ℤ) := by
      simp only [Finset.mem_singleton]; omega
    have hmid : cylKernel B p (x, p.2) = (1/2 : ℝ) * B.P p.1 x := by
      unfold cylKernel; simp
    rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton, hmid]
    ring
  have hbot : ∀ x : B.V, cylKernel B p (x, p.2 - 1) = if p.1 = x then (1/4 : ℝ) else 0 := by
    intro x
    unfold cylKernel
    have hne : p.2 ≠ p.2 - 1 := by omega
    simp [hne]
  have htop : ∀ x : B.V, cylKernel B p (x, p.2 + 1) = if p.1 = x then (1/4 : ℝ) else 0 := by
    intro x
    unfold cylKernel
    have hne : p.2 ≠ p.2 + 1 := by omega
    simp [hne]
  have hsel : ∀ (g : B.V → ℝ), ∑ x : B.V, (if p.1 = x then (1/4 : ℝ) else 0) * g x
      = (1/4 : ℝ) * g p.1 := by
    intro g
    have hrw : ∀ x : B.V, (if p.1 = x then (1/4 : ℝ) else 0) * g x
        = if p.1 = x then (1/4 : ℝ) * g x else 0 := by
      intro x; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun x _ => hrw x),
      Finset.sum_ite_eq Finset.univ p.1 (fun x => (1/4 : ℝ) * g x), if_pos (Finset.mem_univ _)]
  have hmid2 : ∑ x : B.V, (1/2 : ℝ) * B.P p.1 x * hitProb B ζ (x, p.2)
      = (1/2 : ℝ) * ∑ x : B.V, B.P p.1 x * hitProb B ζ (x, p.2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  simp_rw [hT, hbot, htop]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsel, hsel, hmid2]
  ring

/-! ### Uniformity of the first hit -/

theorem layerLawAt_singleton (B : Base) (k : ℤ) (q : Site B) :
    layerLawAt B k {q} = if q.2 = k then ((B.card : ℝ≥0∞))⁻¹ else 0 := by
  classical
  have hdir : ∀ x : B.V, (Measure.dirac ((x, k) : Site B)) {q}
      = if ((x, k) : Site B) = q then 1 else 0 := by
    intro x
    rw [Measure.dirac_apply' _ (measurableSet_singleton q), Set.indicator_apply]
    simp [Set.mem_singleton_iff]
  unfold layerLawAt
  rw [Measure.sum_apply _ (measurableSet_singleton q)]
  simp only [Measure.smul_apply, smul_eq_mul, hdir]
  by_cases hq : q.2 = k
  · rw [tsum_eq_single q.1 (fun x hx => by
      rw [if_neg (fun hc => hx (congrArg Prod.fst hc)), mul_zero])]
    rw [if_pos (by rw [← hq]), mul_one, if_pos hq]
  · rw [if_neg hq]
    refine ENNReal.tsum_eq_zero.mpr fun x => ?_
    rw [if_neg (fun hc => hq (by rw [← hc])), mul_zero]

theorem map_firstHitSite_singleton (B : Base) (j k : ℤ) (q : Site B) :
    ((walkLawUniformAt B j).map (firstHitSite B k)) {q}
      = ∑' x : B.V, ((B.card : ℝ≥0∞))⁻¹
          * walkPathLaw B (x, j) (firstHitSite B k ⁻¹' {q}) := by
  rw [Measure.map_apply (measurable_firstHitSite B k) (measurableSet_singleton q),
    walkLawUniformAt_eq_bind,
    Measure.bind_apply ((measurable_firstHitSite B k) (measurableSet_singleton q))
      (measurable_of_countable _).aemeasurable]
  unfold layerLawAt
  rw [lintegral_sum_measure]
  refine tsum_congr fun x => ?_
  rw [lintegral_smul_measure, lintegral_dirac' _ (measurable_of_countable _), smul_eq_mul]

/-- **`unif-first-hit`** (`tex:595-610`): "`X̂_{τ_{m-1}}` is uniformly distributed
on `V_N` regardless of the vertical history".  `P_N` preserves the uniform
measure and `X̂_0` is uniform, so the first hit of any level is uniform on that
level's layer. -/
theorem unif_first_hit (B : Base) (j k : ℤ) (hrec : External.LazyRwRecurrent) :
    (walkLawUniformAt B j).map (firstHitSite B k) = layerLawAt B k := by
  classical
  haveI : IsProbabilityMeasure ((walkLawUniformAt B j).map (firstHitSite B k)) :=
    Measure.isProbabilityMeasure_map (measurable_firstHitSite B k).aemeasurable
  -- singletons off the layer are null
  have hoff : ∀ (r : Site B) (q : Site B), q.2 ≠ k →
      walkPathLaw B r (firstHitSite B k ⁻¹' {q}) = 0 := by
    intro r q hq
    refine measure_mono_null (fun X hX => ?_) (walkPathLaw_hitLevel_top_null hrec B r k)
    by_contra hne
    have hv := firstHitSite_ver B k X (by simpa using hne)
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hX
    rw [hX] at hv
    exact hq hv
  have hzero : ∀ q : Site B, q.2 ≠ k →
      ((walkLawUniformAt B j).map (firstHitSite B k)) {q} = 0 := by
    intro q hq
    rw [map_firstHitSite_singleton]
    exact ENNReal.tsum_eq_zero.mpr fun x => by rw [hoff _ q hq, mul_zero]
  -- equivariance under graph automorphisms
  have hW : ∀ (σ : B.graph ≃g B.graph) (r q : Site B),
      walkPathLaw B (horIso B σ r) (firstHitSite B k ⁻¹' {horIso B σ q})
        = walkPathLaw B r (firstHitSite B k ⁻¹' {q}) := by
    intro σ r q
    have hE : Measurable (fun (X : ℕ → Site B) (n : ℕ) => horIso B σ (X n)) :=
      measurable_pi_lambda _ fun n =>
        (measurable_of_countable (horIso B σ)).comp (measurable_pi_apply n)
    have hpre : (fun (X : ℕ → Site B) (n : ℕ) => horIso B σ (X n)) ⁻¹'
        (firstHitSite B k ⁻¹' {horIso B σ q}) = firstHitSite B k ⁻¹' {q} := by
      ext X
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      rw [firstHitSite_map B k (horIso B σ) (fun w => rfl) X]
      exact (horIso B σ).injective.eq_iff
    rw [← walkPathLaw_map_siteEquiv B (horIso B σ) (cylKernel_horIso B σ) r,
      Measure.map_apply hE ((measurable_firstHitSite B k) (measurableSet_singleton _)), hpre]
  have hconst : ∀ x x' : B.V,
      ((walkLawUniformAt B j).map (firstHitSite B k)) {((x, k) : Site B)}
        = ((walkLawUniformAt B j).map (firstHitSite B k)) {((x', k) : Site B)} := by
    intro x x'
    obtain ⟨σ, hσ⟩ := B.vertexTransitive x x'
    have hq : ((x', k) : Site B) = horIso B σ ((x, k) : Site B) := by
      simp only [horIso_apply, hσ]
    rw [map_firstHitSite_singleton, map_firstHitSite_singleton, tsum_fintype, tsum_fintype, hq]
    refine Fintype.sum_equiv σ.toEquiv _ _ fun y => ?_
    show ((B.card : ℝ≥0∞))⁻¹ * walkPathLaw B ((y, j) : Site B)
          (firstHitSite B k ⁻¹' {((x, k) : Site B)})
        = ((B.card : ℝ≥0∞))⁻¹ * walkPathLaw B (horIso B σ ((y, j) : Site B))
          (firstHitSite B k ⁻¹' {horIso B σ ((x, k) : Site B)})
    rw [hW σ ((y, j) : Site B) ((x, k) : Site B)]
  -- normalisation
  obtain ⟨x₀⟩ : Nonempty B.V := inferInstance
  have hNpos : (0 : ℕ) < B.card := lt_of_lt_of_le (by norm_num) B.nontrivial
  have hne : ((B.card : ℝ≥0∞)) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
  have htop : ((B.card : ℝ≥0∞)) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsum : ∑' q : Site B, ((walkLawUniformAt B j).map (firstHitSite B k)) {q} = 1 := by
    rw [← measure_iUnion (fun a b hab => Set.disjoint_singleton.mpr hab)
      (fun q => measurableSet_singleton q), Set.iUnion_of_singleton, measure_univ]
  have hsum2 : ∑' q : Site B, ((walkLawUniformAt B j).map (firstHitSite B k)) {q}
      = (B.card : ℝ≥0∞) * ((walkLawUniformAt B j).map (firstHitSite B k)) {((x₀, k) : Site B)} := by
    rw [ENNReal.tsum_prod']
    have hinner : ∀ x : B.V,
        ∑' y : ℤ, ((walkLawUniformAt B j).map (firstHitSite B k)) {((x, y) : Site B)}
          = ((walkLawUniformAt B j).map (firstHitSite B k)) {((x₀, k) : Site B)} := by
      intro x
      rw [tsum_eq_single k (fun y hy => hzero ((x, y) : Site B) hy)]
      exact hconst x x₀
    rw [tsum_congr hinner, tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rfl
  have hc : ((walkLawUniformAt B j).map (firstHitSite B k)) {((x₀, k) : Site B)}
      = ((B.card : ℝ≥0∞))⁻¹ := by
    have h1 : (B.card : ℝ≥0∞)
        * ((walkLawUniformAt B j).map (firstHitSite B k)) {((x₀, k) : Site B)} = 1 := by
      rw [← hsum2, hsum]
    have h2 := congrArg (fun t => ((B.card : ℝ≥0∞))⁻¹ * t) h1
    simpa [← mul_assoc, ENNReal.inv_mul_cancel hne htop] using h2
  refine Measure.ext_of_singleton fun q => ?_
  rw [layerLawAt_singleton]
  by_cases hq : q.2 = k
  · have hqe : q = ((q.1, k) : Site B) := by rw [← hq]
    rw [if_pos hq, hqe, hconst q.1 x₀, hc]
  · rw [if_neg hq, hzero q hq]

/-- The layer form actually consumed, three times over (`tex:608`, `tex:1204`,
`tex:1230`, `tex:1297`): `∑_{x ∈ V_N} H_ζ(x,y) = 1` for every `y ≤ ζ.2`. -/
theorem hitProb_layer_sum (B : Base) (ζ : Site B) (y : ℤ) (hy : y ≤ ζ.2)
    (hrec : External.LazyRwRecurrent) : ∑ x : B.V, hitProb B ζ (x, y) = 1 := by
  have hNpos : (0 : ℕ) < B.card := lt_of_lt_of_le (by norm_num) B.nontrivial
  have hne : ((B.card : ℝ≥0∞)) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
  have htop : ((B.card : ℝ≥0∞)) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hU := unif_first_hit B y ζ.2 hrec
  have hlay : layerLawAt B ζ.2 {ζ} = ((B.card : ℝ≥0∞))⁻¹ := by
    rw [layerLawAt_singleton]
    exact if_pos rfl
  have h1 : ∑' x : B.V, ((B.card : ℝ≥0∞))⁻¹ * hitProbE B ζ ((x, y) : Site B)
      = ((B.card : ℝ≥0∞))⁻¹ := by
    have hms := map_firstHitSite_singleton B y ζ.2 ζ
    rw [hU, hlay] at hms
    simp only [hitProbE_eq_preimage]
    exact hms.symm
  rw [ENNReal.tsum_mul_left] at h1
  have h2 : ∑' x : B.V, hitProbE B ζ ((x, y) : Site B) = 1 := by
    have hmul : (B.card : ℝ≥0∞) * ((B.card : ℝ≥0∞))⁻¹ = 1 :=
      ENNReal.mul_inv_cancel hne htop
    have h3 : (B.card : ℝ≥0∞) * (((B.card : ℝ≥0∞))⁻¹
        * ∑' x : B.V, hitProbE B ζ ((x, y) : Site B))
        = (B.card : ℝ≥0∞) * ((B.card : ℝ≥0∞))⁻¹ := by rw [h1]
    rw [← mul_assoc, hmul, one_mul] at h3
    exact h3
  rw [tsum_fintype] at h2
  have h4 : ∀ x : B.V, hitProbE B ζ ((x, y) : Site B) ≠ ⊤ := fun x => hitProbE_ne_top B ζ _
  calc ∑ x : B.V, hitProb B ζ (x, y)
      = ∑ x : B.V, (hitProbE B ζ ((x, y) : Site B)).toReal := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact hitProb_eq_toReal B ζ _ (by simpa using not_lt.mpr hy)
    _ = (∑ x : B.V, hitProbE B ζ ((x, y) : Site B)).toReal :=
        (ENNReal.toReal_sum (fun x _ => h4 x)).symm
    _ = 1 := by rw [h2]; simp

/-! ### Optional stopping for `H_ζ` -/

theorem exitTime'_le_iff (B : Base) (S : Set (Site B)) (X : ℕ → Site B) (n : ℕ) :
    exitTime' B S X ≤ ((n : ℕ) : ℕ∞) ↔ ∃ j ≤ n, X j ∉ S := by
  constructor
  · intro h
    obtain ⟨j, hj, hjS⟩ := MeasureTheory.hittingAfter_le_iff.mp h
    exact ⟨j, hj.2, hjS⟩
  · rintro ⟨j, hj, hjS⟩
    exact MeasureTheory.hittingAfter_le_iff.mpr ⟨j, ⟨Nat.zero_le j, hj⟩, hjS⟩

theorem exitTime'_eq_coe_iff (B : Base) (S : Set (Site B)) (X : ℕ → Site B) (n : ℕ) :
    exitTime' B S X = ((n : ℕ) : ℕ∞) ↔ X n ∉ S ∧ ∀ j < n, X j ∈ S := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := hittingAfter_zero_eq_coe_iff.mp h
    refine ⟨h1, fun j hj => ?_⟩
    by_contra hc
    exact (h2 j hj) hc
  · rintro ⟨h1, h2⟩
    exact hittingAfter_zero_eq_coe_iff.mpr ⟨h1, fun j hj hc => hc (h2 j hj)⟩

/-- On the finite branch the exit site is the walk at the exit index. -/
theorem exitSite'_eq_apply_toNat (B : Base) (S : Set (Site B)) {X : ℕ → Site B}
    (h : exitTime' B S X ≠ ⊤) : exitSite' B S X = X ((exitTime' B S X).toNat) :=
  congrArg X (untopA_eq_toNat h)

open scoped Classical in
/-- The exit index, truncated after `m` steps.  The one-step recursion is the
whole point: it turns the paper's optional stopping (`tex:1200`) into an
induction on `m`. -/
noncomputable def exitIdx (B : Base) (S : Set (Site B)) : ℕ → (ℕ → Site B) → ℕ
  | 0, _ => 0
  | (m + 1), X => if X 0 ∈ S then exitIdx B S m (pathShift B X) + 1 else 0

@[simp] theorem exitIdx_zero (B : Base) (S : Set (Site B)) (X : ℕ → Site B) :
    exitIdx B S 0 X = 0 := rfl

open scoped Classical in
theorem exitIdx_succ (B : Base) (S : Set (Site B)) (m : ℕ) (X : ℕ → Site B) :
    exitIdx B S (m + 1) X = if X 0 ∈ S then exitIdx B S m (pathShift B X) + 1 else 0 := rfl

theorem measurable_exitIdx (B : Base) (S : Set (Site B)) (m : ℕ) :
    Measurable (exitIdx B S m) := by
  classical
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    have hS : MeasurableSet {X : ℕ → Site B | X 0 ∈ S} :=
      (measurable_pi_apply 0) ((Set.to_countable S).measurableSet)
    have hsucc : Measurable (fun n : ℕ => n + 1) := measurable_of_countable _
    have h1 : Measurable (fun X : ℕ → Site B => exitIdx B S m (pathShift B X) + 1) :=
      hsucc.comp (ih.comp (measurable_pathShift B))
    have hfun : exitIdx B S (m + 1)
        = fun X : ℕ → Site B => if X 0 ∈ S then exitIdx B S m (pathShift B X) + 1 else 0 :=
      funext (fun X => exitIdx_succ B S m X)
    rw [hfun]
    exact Measurable.ite hS h1 measurable_const

theorem measurable_exitIdxSite (B : Base) (S : Set (Site B)) (m : ℕ) :
    Measurable (fun X : ℕ → Site B => X (exitIdx B S m X)) := by
  refine measurable_to_countable' fun q => ?_
  have hset : (fun X : ℕ → Site B => X (exitIdx B S m X)) ⁻¹' {q}
      = ⋃ n : ℕ, ((exitIdx B S m) ⁻¹' {n} ∩ (fun X : ℕ → Site B => X n) ⁻¹' {q}) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h; exact ⟨exitIdx B S m X, rfl, h⟩
    · rintro ⟨n, hn, hq⟩; rw [hn]; exact hq
  rw [hset]
  exact MeasurableSet.iUnion fun n =>
    ((measurable_exitIdx B S m) (measurableSet_singleton n)).inter
      ((measurable_pi_apply n) (measurableSet_singleton q))

theorem exitIdx_spec (B : Base) (S : Set (Site B)) :
    ∀ (m : ℕ) (X : ℕ → Site B), (∃ j ≤ m, X j ∉ S) →
      exitTime' B S X = ((exitIdx B S m X : ℕ) : ℕ∞) := by
  intro m
  induction m with
  | zero =>
    intro X hX
    obtain ⟨j, hj, hjS⟩ := hX
    have hj0 : j = 0 := Nat.le_zero.mp hj
    subst hj0
    rw [exitIdx_zero, exitTime'_eq_coe_iff]
    exact ⟨hjS, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | succ m ih =>
    intro X hX
    by_cases h0 : X 0 ∈ S
    · have hshift : ∃ j ≤ m, (pathShift B X) j ∉ S := by
        obtain ⟨j, hj, hjS⟩ := hX
        cases j with
        | zero => exact absurd h0 hjS
        | succ i => exact ⟨i, Nat.succ_le_succ_iff.mp hj, hjS⟩
      have hi := ih (pathShift B X) hshift
      rw [exitIdx_succ, if_pos h0]
      rw [exitTime'_eq_coe_iff] at hi ⊢
      refine ⟨hi.1, ?_⟩
      intro j hj
      cases j with
      | zero => exact h0
      | succ i => exact hi.2 i (Nat.succ_lt_succ_iff.mp hj)
    · rw [exitIdx_succ, if_neg h0, exitTime'_eq_coe_iff]
      exact ⟨h0, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

/-- The truncated optional-stopping identity: an induction on the truncation
level whose inductive step is exactly harmonicity of `H_ζ` (`tex:1200-1203`). -/
theorem hitProbE_exitIdx (B : Base) (ζ : Site B) (S : Set (Site B))
    (hSlev : ∀ q ∈ S, q.2 ≤ ζ.2 - 1) (hrec : External.LazyRwRecurrent) :
    ∀ (m : ℕ) (q : Site B),
      ∫⁻ X, hitProbE B ζ (X (exitIdx B S m X)) ∂(walkPathLaw B q) = hitProbE B ζ q := by
  intro m
  induction m with
  | zero =>
    intro q
    have hcongr : ∀ᵐ X ∂(walkPathLaw B q),
        hitProbE B ζ (X (exitIdx B S 0 X)) = hitProbE B ζ q := by
      filter_upwards [walkPathLaw_ae_start B q] with X hX
      rw [exitIdx_zero, hX]
    rw [lintegral_congr_ae hcongr, lintegral_const, measure_univ, mul_one]
  | succ m ih =>
    intro q
    by_cases hq : q ∈ S
    · have hqlev : q.2 ≠ ζ.2 := by
        have := hSlev q hq
        omega
      have hcongr : ∀ᵐ X ∂(walkPathLaw B q),
          hitProbE B ζ (X (exitIdx B S (m + 1) X))
            = hitProbE B ζ ((pathShift B X) (exitIdx B S m (pathShift B X))) := by
        filter_upwards [walkPathLaw_ae_start B q] with X hX
        rw [exitIdx_succ, if_pos (by rw [hX]; exact hq)]
        rfl
      have hGmeas : Measurable
          (fun Y : ℕ → Site B => hitProbE B ζ (Y (exitIdx B S m Y))) :=
        (measurable_of_countable (hitProbE B ζ)).comp (measurable_exitIdxSite B S m)
      rw [lintegral_congr_ae hcongr]
      rw [← lintegral_map hGmeas (measurable_pathShift B), walkPathLaw_map_pathShift,
        Measure.lintegral_bind (measurable_of_countable _).aemeasurable hGmeas.aemeasurable]
      simp only [ih]
      rw [lintegral_cylMeasure]
      exact hitProbE_harmonic B ζ q hqlev hrec
    · have hcongr : ∀ᵐ X ∂(walkPathLaw B q),
          hitProbE B ζ (X (exitIdx B S (m + 1) X)) = hitProbE B ζ q := by
        filter_upwards [walkPathLaw_ae_start B q] with X hX
        rw [exitIdx_succ, if_neg (by rw [hX]; exact hq), hX]
      rw [lintegral_congr_ae hcongr, lintegral_const, measure_univ, mul_one]

/-- Bounded optional stopping for `H_ζ` (`tex:1200-1203`).  `S ⊆ R_{ζ.2-1}` is
where harmonicity holds, and the exit is a.s. finite because `S` has bounded
height.

There is no optional-stopping binder; the a.s.-finiteness of the exit is derived
from `hrec`. -/
theorem hitProb_exit_mean (B : Base) (ζ : Site B) (S : Set (Site B))
    (hS : S ⊆ R B ((ζ.2 : ℝ) - 1)) (p : Site B) (hp : p ∈ S)
    (hrec : External.LazyRwRecurrent) :
    ∫ X, hitProb B ζ (exitSite' B S X) ∂(walkPathLaw B p) = hitProb B ζ p := by
  -- levels inside `S`
  have hSlev : ∀ q ∈ S, q.2 ≤ ζ.2 - 1 := by
    intro q hq
    have hr := hS hq
    rw [mem_R] at hr
    have h2 : ((q.2 : ℝ)) ≤ (((ζ.2 - 1 : ℤ)) : ℝ) := by push_cast; linarith only [hr]
    exact_mod_cast h2
  -- the exit time is a.s. finite
  have hτfin : ∀ q : Site B, ∀ᵐ X ∂(walkPathLaw B q), exitTime' B S X ≠ ⊤ := by
    intro q
    filter_upwards [hrec B q ζ.2] with X hX
    obtain ⟨n, hn⟩ := hX
    have hnotS : X n ∉ S := by
      intro hc
      have := hSlev _ hc
      omega
    have hle : exitTime' B S X ≤ ((n : ℕ) : ℕ∞) :=
      (exitTime'_le_iff B S X n).mpr ⟨n, le_rfl, hnotS⟩
    intro htop
    rw [htop] at hle
    exact absurd hle (by simp)
  -- the exit site never lies above the layer of `ζ`
  have hexitle : ∀ᵐ X ∂(walkPathLaw B p), ¬ (ζ.2 < (exitSite' B S X).2) := by
    filter_upwards [hτfin p, walkPathLaw_ae_start B p, walkPathLaw_ae_steps B p]
      with X hfin hstart hsteps
    have hcoe : exitTime' B S X = (((exitTime' B S X).toNat : ℕ) : ℕ∞) :=
      (ENat.coe_toNat hfin).symm
    set n := (exitTime' B S X).toNat with hn
    have hspec := (exitTime'_eq_coe_iff B S X n).mp hcoe
    have hsite : exitSite' B S X = X n := by
      show X (WithTop.untopA (exitTime' B S X)) = X n
      rw [hcoe, untopA_natCast]
    have hn0 : n ≠ 0 := by
      intro h
      apply hspec.1
      rw [h, hstart]
      exact hp
    obtain ⟨i, hi⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
    have hiS : X i ∈ S := hspec.2 i (by omega)
    have hilev : (X i).2 ≤ ζ.2 - 1 := hSlev _ hiS
    have hstep := hsteps i
    rw [hsite, hi]
    omega
  -- the truncated index eventually agrees with the exit index
  have hlim : ∀ᵐ X ∂(walkPathLaw B p), Filter.Tendsto
      (fun m : ℕ => hitProbE B ζ (X (exitIdx B S m X))) Filter.atTop
      (nhds (hitProbE B ζ (exitSite' B S X))) := by
    filter_upwards [hτfin p] with X hfin
    refine tendsto_atTop_of_eventually_const
      (i₀ := (exitTime' B S X).toNat) (fun m hm => ?_)
    have hcoe : exitTime' B S X = (((exitTime' B S X).toNat : ℕ) : ℕ∞) :=
      (ENat.coe_toNat hfin).symm
    have hout : X ((exitTime' B S X).toNat) ∉ S :=
      ((exitTime'_eq_coe_iff B S X ((exitTime' B S X).toNat)).mp hcoe).1
    have hex : ∃ j ≤ m, X j ∉ S := ⟨(exitTime' B S X).toNat, hm, hout⟩
    have hidx := exitIdx_spec B S m X hex
    have heq : exitIdx B S m X = (exitTime' B S X).toNat := by
      have hcc : (((exitIdx B S m X : ℕ)) : ℕ∞) = (((exitTime' B S X).toNat : ℕ) : ℕ∞) := by
        rw [← hidx, ← hcoe]
      exact_mod_cast hcc
    rw [heq, exitSite'_eq_apply_toNat B S hfin]
  -- dominated convergence
  have hdct := tendsto_lintegral_of_dominated_convergence
    (μ := walkPathLaw B p)
    (F := fun (m : ℕ) (X : ℕ → Site B) => hitProbE B ζ (X (exitIdx B S m X)))
    (f := fun X : ℕ → Site B => hitProbE B ζ (exitSite' B S X))
    (bound := fun _ => 1)
    (fun m => (measurable_of_countable (hitProbE B ζ)).comp (measurable_exitIdxSite B S m))
    (fun m => Filter.Eventually.of_forall fun X => hitProbE_le_one B ζ _)
    (by simp) hlim
  have hlintegral : ∫⁻ X, hitProbE B ζ (exitSite' B S X) ∂(walkPathLaw B p)
      = hitProbE B ζ p := by
    have hconst : (fun m : ℕ => ∫⁻ X, hitProbE B ζ (X (exitIdx B S m X)) ∂(walkPathLaw B p))
        = fun _ : ℕ => hitProbE B ζ p :=
      funext fun m => hitProbE_exitIdx B ζ S hSlev hrec m p
    rw [hconst] at hdct
    exact (tendsto_nhds_unique tendsto_const_nhds hdct).symm
  -- back to the Bochner integral
  have hnn : 0 ≤ᵐ[walkPathLaw B p] fun X => hitProb B ζ (exitSite' B S X) :=
    Filter.Eventually.of_forall fun X => hitProb_nonneg B ζ _
  have hmeasf : AEStronglyMeasurable
      (fun X : ℕ → Site B => hitProb B ζ (exitSite' B S X)) (walkPathLaw B p) :=
    ((measurable_of_countable (hitProb B ζ)).comp
      (measurable_exitSite' B S)).aestronglyMeasurable
  have hofReal : ∀ᵐ X ∂(walkPathLaw B p),
      ENNReal.ofReal (hitProb B ζ (exitSite' B S X)) = hitProbE B ζ (exitSite' B S X) := by
    filter_upwards [hexitle] with X hX
    rw [hitProb_eq_toReal B ζ _ hX, ENNReal.ofReal_toReal (hitProbE_ne_top B ζ _)]
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeasf, lintegral_congr_ae hofReal, hlintegral,
    hitProb_eq_toReal B ζ p (by have := hSlev p hp; omega)]

end IdlaCyl
