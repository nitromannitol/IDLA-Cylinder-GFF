module

public import IdlaCyl.Support.FirstHit
public import IdlaCyl.Support.Spectral
public import IdlaCyl.Support.Harmonic
public import IdlaCyl.Support.WalkMartingale
public import IdlaCyl.Support.Stopping

@[expose] public section


/-!
The spectral law of the first hit of a layer for the cylinder walk.

For a layer `h` and a start `p` at or below it, the first hitting site of layer `h`
has law `H_{(z,h)}(p)`, and the spectral modes `f_k(x) e^{q_k (y - h)}` are discrete
harmonic and bounded below `h`.  Optional stopping at the almost surely finite hitting
time gives, for each `1 ≤ k ≤ N`,

  `∑_z H_{(z,h)}(p) f_k(z) = f_k(p) e^{-q_k (h - p.2)}`.

Inverting this with the completeness relation `∑_k f_k(z) f_k(w) = N [z = w]` gives the
spectral formula for `H_{(z,h)}(p)`, and Cauchy–Schwarz with the orthogonality of the
modes gives the total variation bound
`(1/2) ∑_z |H_{(z,h)}(p) - 1/N| ≤ (1/2) √(N - 1) e^{-q_2 (h - p.2)}`.

The recurrence hypothesis `External.LazyRwRecurrent` makes the hitting time almost
surely finite; it is a cited input and is carried as an explicit binder.  The
optional-stopping lemma is `integral_stoppedValue_of_ae_finite` of `Support/Stopping.lean`
with its uniform bound weakened to the times before the stopping time, because a
harmonic mode is unbounded above the target layer after the hit.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace IdlaCyl.Reduction

variable (B : Base)

/-- The hitting time of a layer is a stopping time for the walk filtration. -/
theorem measurableSet_hitLevel_le_walk (h : ℤ) (n : ℕ) :
    MeasurableSet[walkFiltration B n] {X : ℕ → Site B | hitLevel B h X ≤ (n : ℕ∞)} := by
  have hc : ∀ j, j ≤ n → Measurable[walkFiltration B n] (fun X : ℕ → Site B => X j) := by
    intro j hj
    rw [measurable_iff_comap_le]
    exact le_iSup₂ (f := fun k (_ : k ≤ n) =>
      MeasurableSpace.comap (fun X : ℕ → Site B => X k) inferInstance) j hj
  have hset : {X : ℕ → Site B | hitLevel B h X ≤ (n : ℕ∞)}
      = ⋃ j ∈ Finset.range (n + 1), {X : ℕ → Site B | (X j).2 = h} := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range, exists_prop]
    rw [hitLevel_le_iff]
    constructor
    · rintro ⟨j, hj, hjh⟩
      exact ⟨j, by omega, hjh⟩
    · rintro ⟨j, hj, hjh⟩
      exact ⟨j, by omega, hjh⟩
  rw [hset]
  refine MeasurableSet.biUnion (Finset.range (n + 1)).countable_toSet fun j hj => ?_
  have hj' : j ≤ n := by
    simp only [Finset.coe_range, Set.mem_Iio] at hj
    omega
  exact (measurable_snd.comp (hc j hj')) (measurableSet_singleton h)

/-- A minimum with a natural number has the untopped value at most the original value. -/
theorem untopA_min_le_walk (a : ℕ∞) (n : ℕ) :
    ((min a (n : ℕ∞)).untopA : ℕ∞) ≤ a := by
  induction a using ENat.recTopCoe with
  | top =>
    have h1 : min (⊤ : ℕ∞) (n : ℕ∞) = (n : ℕ∞) := min_eq_right le_top
    rw [h1, untopA_natCast]
    exact le_top
  | coe m =>
    have h1 : min (m : ℕ∞) (n : ℕ∞) = ((min m n : ℕ) : ℕ∞) := by norm_cast
    rw [h1, untopA_natCast]
    exact_mod_cast min_le_left m n

/-- Bounded optional stopping at an a.s. finite `ℕ∞`-valued stopping time for a
martingale which is bounded only at the times up to the stopping time.  This is
`integral_stoppedValue_of_ae_finite` with the bound weakened to the stopped range. -/
theorem integral_stoppedValue_of_ae_finite_of_bdd_before
    {Ω : Type*} [MeasurableSpace Ω] {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (M : ℕ → Ω → ℝ) (τ : Ω → ℕ∞) (C : ℝ)
    (hM : Martingale M ℱ P) (hbdd : ∀ᵐ ω ∂P, ∀ t : ℕ, (t : ℕ∞) ≤ τ ω → |M t ω| ≤ C)
    (hτ : ∀ n : ℕ, MeasurableSet[ℱ n] {ω | τ ω ≤ (n : ℕ∞)})
    (hfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    ∫ ω, M ((τ ω).toNat) ω ∂P = ∫ ω, M 0 ω ∂P := by
  have hτ' : IsStoppingTime ℱ τ := hτ
  have hM' : Submartingale M ℱ P := hM.submartingale
  have hMneg' : Submartingale (-M) ℱ P := hM.neg.submartingale
  have hprog : IsStronglyProgressive ℱ M := hM.stronglyAdapted.isStronglyProgressive_of_discrete
  have hstep : ∀ n : ℕ,
      ∫ ω, stoppedValue M (fun ω => min (τ ω) (n : ℕ∞)) ω ∂P = ∫ ω, M 0 ω ∂P := by
    intro n
    have hπ : IsStoppingTime ℱ (fun ω => min (τ ω) (n : ℕ∞)) := hτ'.min_const n
    have hbddπ : ∀ ω, min (τ ω) (n : ℕ∞) ≤ (n : ℕ∞) := fun ω => min_le_right _ _
    have h1 := hM'.expected_stoppedValue_mono (isStoppingTime_const ℱ 0) hπ (fun _ => zero_le)
      hbddπ
    have h2 := hMneg'.expected_stoppedValue_mono (isStoppingTime_const ℱ 0) hπ (fun _ => zero_le)
      hbddπ
    simp only [stoppedValue_const] at h1 h2
    have hnegπ : ∀ ω, stoppedValue (-M) (fun ω' => min (τ ω') (n : ℕ∞)) ω
        = -(stoppedValue M (fun ω' => min (τ ω') (n : ℕ∞)) ω) := fun ω => rfl
    have hneg0 : ∀ ω, (-M) 0 ω = -(M 0 ω) := fun ω => rfl
    simp only [hneg0, hnegπ, integral_neg] at h2
    linarith
  have hmeasπ : ∀ n : ℕ,
      AEStronglyMeasurable (stoppedValue M (fun ω => min (τ ω) (n : ℕ∞))) P := fun n =>
    ((stronglyMeasurable_stoppedValue_of_le hprog (hτ'.min_const n)
      (fun ω => min_le_right (τ ω) (n : ℕ∞))).mono (ℱ.le n)).aestronglyMeasurable
  have hbound : ∀ n : ℕ,
      ∀ᵐ ω ∂P, ‖stoppedValue M (fun ω => min (τ ω) (n : ℕ∞)) ω‖ ≤ C := fun n => by
    filter_upwards [hbdd] with ω hω
    rw [Real.norm_eq_abs]
    exact hω _ (untopA_min_le_walk (τ ω) n)
  have key : ∀ ω, τ ω ≠ ⊤ → ∀ n : ℕ, (τ ω).toNat ≤ n →
      stoppedValue M (fun ω' => min (τ ω') (n : ℕ∞)) ω = M (τ ω).toNat ω := by
    intro ω hω n hn
    have hcoe : ((τ ω).toNat : ℕ∞) = τ ω := ENat.coe_toNat hω
    have hle : τ ω ≤ (n : ℕ∞) := by rw [← hcoe]; exact_mod_cast hn
    have hmin : min (τ ω) (n : ℕ∞) = ((τ ω).toNat : ℕ∞) := by
      rw [hcoe]; exact min_eq_left hle
    calc stoppedValue M (fun ω' => min (τ ω') (n : ℕ∞)) ω
        = M (min (τ ω) (n : ℕ∞)).untopA ω := rfl
      _ = M (((τ ω).toNat : ℕ∞)).untopA ω := by rw [hmin]
      _ = M (τ ω).toNat ω := congrFun (stoppedValue_const M (τ ω).toNat) ω
  have hlim : ∀ᵐ ω ∂P, Filter.Tendsto
      (fun n : ℕ => stoppedValue M (fun ω' => min (τ ω') (n : ℕ∞)) ω) Filter.atTop
      (nhds (M (τ ω).toNat ω)) := by
    filter_upwards [hfin] with ω hω
    exact tendsto_atTop_of_eventually_const (key ω hω)
  have hdct := tendsto_integral_of_dominated_convergence (fun _ : Ω => C) hmeasπ
    (integrable_const C) hbound hlim
  have hconst : Filter.Tendsto (fun n : ℕ =>
      ∫ ω, stoppedValue M (fun ω => min (τ ω) (n : ℕ∞)) ω ∂P) Filter.atTop
      (nhds (∫ ω, M 0 ω ∂P)) := by
    have heq : (fun n : ℕ => ∫ ω, stoppedValue M (fun ω => min (τ ω) (n : ℕ∞)) ω ∂P)
        = fun _ => ∫ ω, M 0 ω ∂P := funext hstep
    rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hdct hconst

/-- Before the hit of layer `h`, a walk that starts at or below `h` stays at or below `h`. -/
theorem height_le_of_le_hitLevel (h : ℤ) (X : ℕ → Site B) (hstart : (X 0).2 ≤ h)
    (hsteps : ∀ n : ℕ, ((X (n + 1)).2 - (X n).2).natAbs ≤ 1) :
    ∀ t : ℕ, (t : ℕ∞) ≤ hitLevel B h X → (X t).2 ≤ h := by
  intro t
  induction t with
  | zero => intro _; simpa using hstart
  | succ t ih =>
    intro ht
    have hlt : ((t : ℕ) : ℕ∞) < hitLevel B h X :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self t) ht
    have hth := ih hlt.le
    have hne : (X t).2 ≠ h := by
      intro heq
      exact not_le.mpr hlt ((hitLevel_le_iff B h X t).mpr ⟨t, le_rfl, heq⟩)
    have hstep := hsteps t
    omega

/-- Optional stopping at the first hit of layer `h`: a discrete harmonic `ψ` bounded
by `C` on the layers at or below `h` satisfies `E_p[ψ(firstHitSite)] = ψ p` for
`p` at or below `h`. -/
theorem integral_psi_firstHit (h : ℤ) (ψ : Site B → ℝ) (hharm : DiscreteHarmonic B ψ)
    (p : Site B) (hp : p.2 ≤ h) (C : ℝ) (hC : ∀ q : Site B, q.2 ≤ h → |ψ q| ≤ C)
    (hrec : External.LazyRwRecurrent) :
    ∫ X, ψ (firstHitSite B h X) ∂(walkPathLaw B p) = ψ p := by
  have hM := walkMartingale_of_discreteHarmonic B p ψ hharm
  have hbdd : ∀ᵐ X ∂(walkPathLaw B p), ∀ t : ℕ,
      (t : ℕ∞) ≤ hitLevel B h X → |ψ (X t)| ≤ C := by
    filter_upwards [walkPathLaw_ae_start B p, walkPathLaw_ae_steps B p] with X h0 hs t ht
    apply hC
    refine height_le_of_le_hitLevel B h X ?_ ?_ t ht
    · rw [h0]; exact hp
    · intro n
      have := hs n
      omega
  have hopt := integral_stoppedValue_of_ae_finite_of_bdd_before (walkPathLaw B p)
    (walkFiltration B) (fun s (X : ℕ → Site B) => ψ (X s)) (hitLevel B h) C hM hbdd
    (fun n => measurableSet_hitLevel_le_walk B h n) (ae_hitLevel_ne_top hrec B p h)
  have hae : ∀ᵐ X ∂(walkPathLaw B p), ψ (firstHitSite B h X)
      = ψ (X (hitLevel B h X).toNat) := by
    filter_upwards [ae_hitLevel_ne_top hrec B p h] with X hX
    congr 1
    show X (WithTop.untopA (hitLevel B h X)) = X (hitLevel B h X).toNat
    rw [untopA_eq_toNat hX]
  have hae0 : ∀ᵐ X ∂(walkPathLaw B p), ψ (X 0) = ψ p := by
    filter_upwards [walkPathLaw_ae_start B p] with X h0
    rw [h0]
  rw [integral_congr_ae hae, hopt, integral_congr_ae hae0]
  simp

/-- The mode `f(x) e^{q (y - h)}` for an eigenpair of `P_N` with `cosh q = 2 - λ`
is discrete harmonic, and it is bounded below `h` by the `ℓ¹` norm of `f`. -/
theorem mode_harmonic_bdd (S : SpectralData B) (h : ℤ) (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ B.card) :
    DiscreteHarmonic B (exponentialMode B (S.f k) (S.qk k) (h : ℝ)) ∧
      0 ≤ S.qk k := by
  refine ⟨exponentialMode_harmonic B (S.f k) (S.lam k) (S.qk k) (h : ℝ)
    (fun x => S.eigen k hk hkN x) (S.cosh_qk hk hkN), ?_⟩
  have hle : S.lam k ≤ 1 := by
    calc S.lam k ≤ S.lam 1 := S.antitone 1 k le_rfl hk hkN
      _ = 1 := S.lam_one
  exact Real.arcosh_nonneg (by linarith)

/-- The first-hit mode identity: for `1 ≤ k ≤ N` and `p` at or below `h`,
`E_p[f_k((firstHitSite)_1)] = f_k(p) e^{-q_k (h - p.2)}`. -/
theorem integral_firstHit_mode (S : SpectralData B) (h : ℤ) (p : Site B) (hp : p.2 ≤ h)
    (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ B.card) (hrec : External.LazyRwRecurrent) :
    ∫ X, S.f k (firstHitSite B h X).1 ∂(walkPathLaw B p)
      = S.f k p.1 * Real.exp (-(S.qk k) * ((h : ℝ) - p.2)) := by
  obtain ⟨hharm, hq0⟩ := mode_harmonic_bdd B S h k hk hkN
  have hp' : (p.2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hp
  have hopt := integral_psi_firstHit B h _ hharm p hp (∑ x : B.V, |S.f k x|)
    (fun q hq => exponentialMode_bounded_below B (S.f k) (S.qk k) (h : ℝ) hq0 q
      (by exact_mod_cast hq)) hrec
  have hae : ∀ᵐ X ∂(walkPathLaw B p), S.f k (firstHitSite B h X).1
      = exponentialMode B (S.f k) (S.qk k) (h : ℝ) (firstHitSite B h X) := by
    filter_upwards [ae_hitLevel_ne_top hrec B p h] with X hX
    have hv := firstHitSite_ver B h X hX
    unfold exponentialMode
    rw [hv]
    simp
  rw [integral_congr_ae hae, hopt]
  unfold exponentialMode
  rw [show S.qk k * ((p.2 : ℝ) - (h : ℝ)) = -(S.qk k) * ((h : ℝ) - p.2) by ring]

/-- **The first-hit spectral identity, in mode form.**  For a
layer `h`, a start `p` at or below it, and a mode `1 ≤ k ≤ N`,
`∑_z H_{(z,h)}(p) f_k(z) = f_k(p) e^{-q_k (h - p.2)}`. -/
theorem sum_hitProb_mul_f (S : SpectralData B) (h : ℤ) (p : Site B) (hp : p.2 ≤ h)
    (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ B.card) (hrec : External.LazyRwRecurrent) :
    ∑ z : B.V, hitProb B (z, h) p * S.f k z
      = S.f k p.1 * Real.exp (-(S.qk k) * ((h : ℝ) - p.2)) := by
  classical
  -- the integrand as a finite sum of indicators of the hitting events
  have hpt : ∀ᵐ X ∂(walkPathLaw B p), S.f k (firstHitSite B h X).1
      = ∑ z : B.V, S.f k z *
          (({X : ℕ → Site B | firstHitSite B h X = (z, h)}).indicator (fun _ => (1 : ℝ)) X) := by
    filter_upwards [ae_hitLevel_ne_top hrec B p h] with X hX
    have hv := firstHitSite_ver B h X hX
    have hG : firstHitSite B h X = ((firstHitSite B h X).1, h) := Prod.ext rfl hv
    rw [Finset.sum_eq_single (firstHitSite B h X).1
      (fun z _ hz => by
        simp only [Set.indicator_apply, Set.mem_setOf_eq]
        rw [if_neg (fun heq => hz (congrArg Prod.fst heq).symm), mul_zero])
      (fun hn => absurd (Finset.mem_univ _) hn)]
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    rw [if_pos hG, mul_one]
  have hmeas : ∀ z : B.V, MeasurableSet {X : ℕ → Site B | firstHitSite B h X = (z, h)} :=
    fun z => measurableSet_firstHit B (z, h)
  have hint : ∫ X, S.f k (firstHitSite B h X).1 ∂(walkPathLaw B p)
      = ∑ z : B.V, S.f k z * (walkPathLaw B p {X : ℕ → Site B | firstHitSite B h X = (z, h)}).toReal := by
    rw [integral_congr_ae hpt, integral_finsetSum]
    · refine Finset.sum_congr rfl fun z _ => ?_
      rw [integral_const_mul, integral_indicator_const _ (hmeas z)]
      simp [measureReal_def]
    · intro z _
      exact (((integrable_const (1 : ℝ)).indicator (hmeas z)).const_mul (S.f k z))
  have hconv : ∀ z : B.V, hitProb B (z, h) p
      = (walkPathLaw B p {X : ℕ → Site B | firstHitSite B h X = (z, h)}).toReal :=
    fun z => hitProb_eq_toReal B (z, h) p (not_lt.mpr hp)
  rw [← integral_firstHit_mode B S h p hp k hk hkN hrec, hint]
  exact Finset.sum_congr rfl fun z _ => by rw [hconv z, mul_comm]

/-- A sum over the modes `1 ≤ k ≤ N` is a sum over `Fin N` shifted by one. -/
theorem sum_Icc_one_eq_fin (g : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, g k = ∑ i : Fin N, g (1 + (i : ℕ)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, add_comm 1 n]

/-- The completeness relation for the eigenvectors of `P_N`:
`∑_{k=1}^N f_k(z) f_k(w) = N [z = w]`.  The `N × N` matrix `(f_{i+1}(e⁻¹ j)/√N)` is
orthogonal, so its transpose-product is the identity too. -/
theorem spectral_complete (S : SpectralData B) (z w : B.V) :
    ∑ k ∈ Finset.Icc 1 B.card, S.f k z * S.f k w
      = (B.card : ℝ) * (if z = w then 1 else 0) := by
  classical
  have hNpos : (0 : ℕ) < B.card := lt_of_lt_of_le (by norm_num) B.nontrivial
  have hN0 : (B.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
  have hsq : Real.sqrt (B.card : ℝ) * Real.sqrt (B.card : ℝ) = (B.card : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  let e : B.V ≃ Fin B.card := Fintype.equivFinOfCardEq rfl
  let M : Matrix (Fin B.card) (Fin B.card) ℝ :=
    fun i j => S.f (1 + (i : ℕ)) (e.symm j) / Real.sqrt (B.card : ℝ)
  -- `M` is orthogonal: its rows are orthonormal for the counting measure
  have hMM : M * Matrix.transpose M = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hi := i.isLt
    have hj := j.isLt
    have hx := S.orthonormal (1 + (i : ℕ)) (1 + (j : ℕ)) (by omega) (by omega)
      (by omega) (by omega)
    have hxi : (1 + (i : ℕ)) = (1 + (j : ℕ)) ↔ i = j := by
      constructor
      · intro h
        exact Fin.ext (by omega)
      · intro h
        rw [h]
    let F : B.V → ℝ := fun x => S.f (1 + (i : ℕ)) x / Real.sqrt (B.card : ℝ)
      * (S.f (1 + (j : ℕ)) x / Real.sqrt (B.card : ℝ))
    have hsum : ∑ k : Fin B.card, F (e.symm k) = ∑ x : B.V, F x := Equiv.sum_comp e.symm F
    have hF : ∑ x : B.V, F x = (1 / (B.card : ℝ)) * ∑ x : B.V, S.f (1 + (i : ℕ)) x * S.f (1 + (j : ℕ)) x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [F]
      rw [div_mul_div_comm, hsq, one_div, ← div_eq_inv_mul, div_eq_mul_inv]
    calc ∑ k : Fin B.card, M i k * Matrix.transpose M k j = ∑ k : Fin B.card, F (e.symm k) := rfl
      _ = ∑ x : B.V, F x := hsum
      _ = (1 / (B.card : ℝ)) * ∑ x : B.V, S.f (1 + (i : ℕ)) x * S.f (1 + (j : ℕ)) x := hF
      _ = if 1 + (i : ℕ) = 1 + (j : ℕ) then 1 else 0 := hx
      _ = if i = j then 1 else 0 := by
        by_cases hij : i = j
        · rw [if_pos hij, if_pos (hxi.mpr hij)]
        · rw [if_neg hij, if_neg (fun h => hij (hxi.mp h))]
  -- hence the transpose-product is the identity as well, which is the completeness relation
  have hMM' : Matrix.transpose M * M = 1 := mul_eq_one_comm.mp hMM
  have hT := congrFun (congrFun hMM' (e z)) (e w)
  have hterm : ∀ k : Fin B.card, Matrix.transpose M (e z) k * M k (e w)
      = S.f (1 + (k : ℕ)) z * S.f (1 + (k : ℕ)) w / (B.card : ℝ) := by
    intro k
    show S.f (1 + (k : ℕ)) (e.symm (e z)) / Real.sqrt (B.card : ℝ)
      * (S.f (1 + (k : ℕ)) (e.symm (e w)) / Real.sqrt (B.card : ℝ)) = _
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, div_mul_div_comm, hsq]
  have hez : e z = e w ↔ z = w := e.injective.eq_iff
  rw [Matrix.mul_apply, Matrix.one_apply] at hT
  simp only [hterm, hez, ← Finset.sum_div] at hT
  rw [sum_Icc_one_eq_fin (fun k => S.f k z * S.f k w) B.card]
  calc ∑ i : Fin B.card, (fun k => S.f k z * S.f k w) (1 + (i : ℕ))
      = (∑ k : Fin B.card, S.f (1 + (k : ℕ)) z * S.f (1 + (k : ℕ)) w) / (B.card : ℝ) * B.card :=
        (div_mul_cancel₀ _ hN0).symm
    _ = (if z = w then 1 else 0) * B.card := by rw [hT]
    _ = (B.card : ℝ) * (if z = w then 1 else 0) := mul_comm _ _

/-- **The first-hit spectral formula.**  For a layer `h`, a start
`p` at or below it, and `z` in the base, the first-hit probability of `(z, h)` from `p`
is `(1/N) ∑_{k=1}^N e^{-q_k (h - p.2)} f_k(p) f_k(z)`. -/
theorem hitProb_spectral (S : SpectralData B) (h : ℤ) (p : Site B) (hp : p.2 ≤ h)
    (hrec : External.LazyRwRecurrent) (z : B.V) :
    hitProb B (z, h) p = (1 / (B.card : ℝ)) * ∑ k ∈ Finset.Icc 1 B.card,
      Real.exp (-(S.qk k) * ((h : ℝ) - p.2)) * S.f k p.1 * S.f k z := by
  classical
  have hNpos : (0 : ℕ) < B.card := lt_of_lt_of_le (by norm_num) B.nontrivial
  have hN0 : (B.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
  -- the coefficients of `H_{(·,h)}(p)` in the modes are the first-hit mode identity
  have hc : ∀ k ∈ Finset.Icc 1 B.card, ∑ w : B.V, hitProb B (w, h) p * S.f k w
      = S.f k p.1 * Real.exp (-(S.qk k) * ((h : ℝ) - p.2)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact sum_hitProb_mul_f B S h p hp k hk.1 hk.2 hrec
  -- expanding `H_{(z,h)}(p)` through the completeness relation
  have hexp : ∑ k ∈ Finset.Icc 1 B.card, S.f k z * ∑ w : B.V, hitProb B (w, h) p * S.f k w
      = hitProb B (z, h) p * B.card := by
    calc ∑ k ∈ Finset.Icc 1 B.card, S.f k z * ∑ w : B.V, hitProb B (w, h) p * S.f k w
        = ∑ k ∈ Finset.Icc 1 B.card, ∑ w : B.V, hitProb B (w, h) p * (S.f k w * S.f k z) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          ring
      _ = ∑ w : B.V, hitProb B (w, h) p * ∑ k ∈ Finset.Icc 1 B.card, S.f k w * S.f k z := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ w : B.V, hitProb B (w, h) p * ((B.card : ℝ) * (if w = z then 1 else 0)) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [spectral_complete B S w z]
      _ = hitProb B (z, h) p * B.card := by
          simp [mul_ite, Finset.sum_ite_eq']
  have hfin : hitProb B (z, h) p = (1 / (B.card : ℝ)) * ∑ k ∈ Finset.Icc 1 B.card,
      S.f k z * ∑ w : B.V, hitProb B (w, h) p * S.f k w := by
    rw [hexp]
    field_simp
  rw [hfin]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [hc k hk]
  ring

/-- The modes are orthogonal in the unnormalised sum over the base. -/
theorem sum_mode_mul (B : Base) (S : SpectralData B) (j k : ℕ) (hj : 1 ≤ j) (hjN : j ≤ B.card)
    (hk : 1 ≤ k) (hkN : k ≤ B.card) :
    ∑ x : B.V, S.f j x * S.f k x = (B.card : ℝ) * (if j = k then 1 else 0) := by
  have hNpos : (0 : ℕ) < B.card := lt_of_lt_of_le (by norm_num) B.nontrivial
  have hN0 : (B.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
  rw [← S.orthonormal j k hj hjN hk hkN, ← mul_assoc, mul_one_div_cancel hN0, one_mul]

/-- The sum over the base of the square of a combination of modes. -/
theorem sum_sq_modes (B : Base) (S : SpectralData B) (c : ℕ → ℝ) (T : Finset ℕ)
    (hT : ∀ k ∈ T, 1 ≤ k ∧ k ≤ B.card) :
    ∑ z : B.V, (∑ k ∈ T, c k * S.f k z) ^ 2 = (B.card : ℝ) * ∑ k ∈ T, (c k) ^ 2 := by
  calc ∑ z : B.V, (∑ k ∈ T, c k * S.f k z) ^ 2
      = ∑ z : B.V, ∑ k ∈ T, ∑ l ∈ T, c k * S.f k z * (c l * S.f l z) := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ k ∈ T, ∑ l ∈ T, c k * c l * ∑ z : B.V, S.f k z * S.f l z := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        ring
    _ = ∑ k ∈ T, ∑ l ∈ T, c k * c l * ((B.card : ℝ) * (if k = l then 1 else 0)) := by
        refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun l hl => ?_
        rw [sum_mode_mul B S k l (hT k hk).1 (hT k hk).2 (hT l hl).1 (hT l hl).2]
    _ = (B.card : ℝ) * ∑ k ∈ T, (c k) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.sum_eq_single k]
        · rw [if_pos rfl]
          ring
        · intro l _ hl
          rw [if_neg (fun h => hl h.symm), mul_zero, mul_zero]
        · intro hk'
          exact absurd hk hk'

/-- Elementary step of the total variation bound: `(W/N)² ≤ S` from `W² ≤ N² S`. -/
theorem tv_sq_aux (N W S2 : ℝ) (hN : 0 < N) (hW : W ^ 2 ≤ N * (N * S2)) :
    ((1 / N) * W) ^ 2 ≤ S2 := by
  rw [mul_pow]
  have h1 : (1 / N) ^ 2 * W ^ 2 ≤ (1 / N) ^ 2 * (N * (N * S2)) :=
    mul_le_mul_of_nonneg_left hW (sq_nonneg _)
  have h2 : (1 / N) ^ 2 * (N * (N * S2)) = S2 := by
    field_simp
  linarith

/-- **The first-hit total variation bound.**  For a layer `h` and a
start `p` at or below it, `(1/2) ∑_z |H_{(z,h)}(p) - 1/N| ≤ (1/2) √(N - 1) e^{-q_2 (h - p.2)}`. -/
theorem hitProb_tv (B : Base) (S : SpectralData B) (h : ℤ) (p : Site B) (hp : p.2 ≤ h)
    (hrec : External.LazyRwRecurrent) :
    (1 / 2 : ℝ) * ∑ z : B.V, |hitProb B (z, h) p - 1 / (B.card : ℝ)|
      ≤ (1 / 2 : ℝ) * Real.sqrt ((B.card : ℝ) - 1)
          * Real.exp (-(S.qk 2) * ((h : ℝ) - p.2)) := by
  have hNpos : (0 : ℕ) < B.card := lt_of_lt_of_le (by norm_num) B.nontrivial
  have hN0 : (B.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNpos.ne'
  have hNpos' : (0 : ℝ) < (B.card : ℝ) := Nat.cast_pos.mpr hNpos
  have hN2 : 2 ≤ B.card := B.nontrivial
  have hd : (0 : ℝ) ≤ (h : ℝ) - p.2 := by
    have : (p.2 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hp
    linarith
  have hT : ∀ k ∈ Finset.Icc 2 B.card, 1 ≤ k ∧ k ≤ B.card := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact ⟨by omega, hk.2⟩
  have hI : Finset.Icc 1 B.card = insert 1 (Finset.Icc 2 B.card) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : (1 : ℕ) ∉ Finset.Icc 2 B.card := by simp
  have hq1 : S.qk 1 = 0 := by
    unfold SpectralData.qk
    rw [S.lam_one]
    norm_num
  -- the deviation from uniform is the sum over the modes `k ≥ 2`
  have hy : ∀ z : B.V, hitProb B (z, h) p - 1 / (B.card : ℝ)
      = (1 / (B.card : ℝ)) * ∑ k ∈ Finset.Icc 2 B.card,
          Real.exp (-(S.qk k) * ((h : ℝ) - p.2)) * S.f k p.1 * S.f k z := by
    intro z
    have h1 : Real.exp (-(S.qk 1) * ((h : ℝ) - p.2)) * S.f 1 p.1 * S.f 1 z = 1 := by
      rw [hq1, S.f_one p.1, S.f_one z]
      simp
    rw [hitProb_spectral B S h p hp hrec z, hI, Finset.sum_insert hnot, h1]
    ring
  -- Cauchy–Schwarz and orthogonality bound the `ℓ¹` deviation by the `ℓ²` norm of the coefficients
  have hsq := sum_sq_modes B S (fun k => Real.exp (-(S.qk k) * ((h : ℝ) - p.2)) * S.f k p.1)
    (Finset.Icc 2 B.card) hT
  beta_reduce at hsq
  have hCS := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset B.V))
    (f := fun z : B.V => |∑ k ∈ Finset.Icc 2 B.card,
      Real.exp (-(S.qk k) * ((h : ℝ) - p.2)) * S.f k p.1 * S.f k z|)
  simp only [Finset.card_univ, sq_abs] at hCS
  have hA : ∑ z : B.V, |hitProb B (z, h) p - 1 / (B.card : ℝ)|
      = (1 / (B.card : ℝ)) * ∑ z : B.V, |∑ k ∈ Finset.Icc 2 B.card,
          Real.exp (-(S.qk k) * ((h : ℝ) - p.2)) * S.f k p.1 * S.f k z| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hy z, abs_mul, abs_of_pos (one_div_pos.mpr hNpos')]
  have hCS' : (∑ z : B.V, |∑ k ∈ Finset.Icc 2 B.card,
          Real.exp (-(S.qk k) * ((h : ℝ) - p.2)) * S.f k p.1 * S.f k z|) ^ 2
      ≤ (B.card : ℝ) * ((B.card : ℝ) * ∑ k ∈ Finset.Icc 2 B.card,
          (Real.exp (-(S.qk k) * ((h : ℝ) - p.2)) * S.f k p.1) ^ 2) := by
    calc _ ≤ (B.card : ℝ) * ∑ z : B.V, (∑ k ∈ Finset.Icc 2 B.card,
            Real.exp (-(S.qk k) * ((h : ℝ) - p.2)) * S.f k p.1 * S.f k z) ^ 2 := hCS
      _ = _ := by rw [hsq]
  -- the coefficients are dominated by their `k = 2` value, and `∑_{k ≥ 2} f_k(p)² = N - 1`
  have hS2 : ∑ k ∈ Finset.Icc 2 B.card, (Real.exp (-(S.qk k) * ((h : ℝ) - p.2)) * S.f k p.1) ^ 2
      ≤ (Real.exp (-(S.qk 2) * ((h : ℝ) - p.2))) ^ 2 * ((B.card : ℝ) - 1) := by
    have hF : ∑ k ∈ Finset.Icc 2 B.card, S.f k p.1 ^ 2 = (B.card : ℝ) - 1 := by
      have hc := spectral_complete B S p.1 p.1
      rw [if_pos rfl, mul_one, hI, Finset.sum_insert hnot, S.f_one p.1] at hc
      simp only [sq]
      linarith
    rw [← hF, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hkN : k ≤ B.card := (Finset.mem_Icc.mp hk).2
    have hlam : S.lam k ≤ S.lam 2 := S.antitone 2 k (by norm_num) hk2 hkN
    have hlam2 : S.lam 2 < 1 := S.lam_two_lt hN2
    have hqk : S.qk 2 ≤ S.qk k := by
      unfold SpectralData.qk
      exact (Real.arcosh_le_arcosh (by linarith) (by linarith)).mpr (by linarith)
    have hle : Real.exp (-(S.qk k) * ((h : ℝ) - p.2))
        ≤ Real.exp (-(S.qk 2) * ((h : ℝ) - p.2)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hqk hd])
    calc (Real.exp (-(S.qk k) * ((h : ℝ) - p.2)) * S.f k p.1) ^ 2
        = Real.exp (-(S.qk k) * ((h : ℝ) - p.2)) ^ 2 * S.f k p.1 ^ 2 := by ring
      _ ≤ Real.exp (-(S.qk 2) * ((h : ℝ) - p.2)) ^ 2 * S.f k p.1 ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le hle 2) (sq_nonneg _)
  -- assemble: `A² ≤ ∑ c²`, then take square roots
  have hAsq : (∑ z : B.V, |hitProb B (z, h) p - 1 / (B.card : ℝ)|) ^ 2
      ≤ ∑ k ∈ Finset.Icc 2 B.card, (Real.exp (-(S.qk k) * ((h : ℝ) - p.2)) * S.f k p.1) ^ 2 := by
    rw [hA]
    exact tv_sq_aux (B.card : ℝ) _ _ hNpos' hCS'
  have hA' := le_trans (le_abs_self _) (Real.abs_le_sqrt hAsq)
  have hsqrt := Real.sqrt_le_sqrt hS2
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_pos _).le] at hsqrt
  calc (1 / 2 : ℝ) * ∑ z : B.V, |hitProb B (z, h) p - 1 / (B.card : ℝ)|
      ≤ (1 / 2 : ℝ) * (Real.exp (-(S.qk 2) * ((h : ℝ) - p.2)) * Real.sqrt ((B.card : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left (le_trans hA' hsqrt) (by norm_num)
    _ = (1 / 2 : ℝ) * Real.sqrt ((B.card : ℝ) - 1)
          * Real.exp (-(S.qk 2) * ((h : ℝ) - p.2)) := by ring

end IdlaCyl.Reduction
