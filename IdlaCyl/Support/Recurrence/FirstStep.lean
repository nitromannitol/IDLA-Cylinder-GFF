import IdlaCyl.Support.FirstHit

/-!
# First-step analysis for the never-reach event

Let `f(p)` be the probability that the cylinder walk from `p` never reaches
height `k` (`tex:600-604`), i.e. stays strictly below `k` forever.  This file
proves the two elementary facts that feed the recurrence argument there:

* `neverReach_of_le`: `f = 0` at heights `≥ k`;
* `neverReach_harmonic`: `f` is harmonic at every `p` of height `< k`, for the
  kernel `cylKernel`.

The proof of the second is the first-step (one-step Markov) identity of
`IdlaCyl.hitProbE_harmonic`, with the event `{X | ∀ n, (X n).2 < k}` in place of
the first-hit event; no recurrence hypothesis is needed.
-/

namespace IdlaCyl.Recurrence

open MeasureTheory

/-- The never-reach event is measurable. -/
theorem neverReach_measurableSet (B : Base) (k : ℤ) :
    MeasurableSet {X : ℕ → Site B | ∀ n, (X n).2 < k} := by
  have hset : {X : ℕ → Site B | ∀ n, (X n).2 < k}
      = ⋂ n : ℕ, (fun X : ℕ → Site B => (X n).2) ⁻¹' {y : ℤ | y < k} := by
    ext X
    simp
  rw [hset]
  exact MeasurableSet.iInter fun n =>
    ((measurable_pi_apply n).snd) (MeasurableSet.of_discrete)

theorem neverReach_of_le (B : Base) (k : ℤ) (p : Site B) (hp : k ≤ p.2) :
    walkPathLaw B p {X : ℕ → Site B | ∀ n, (X n).2 < k} = 0 := by
  refine measure_mono_null ?_ (walkPathLaw_ae_zero B p)
  intro X hX h0
  have h := hX 0
  rw [h0] at h
  omega

/-- The first-step identity for the never-reach event, in `ℝ≥0∞` form. -/
theorem neverReach_firstStep (B : Base) (k : ℤ) (p : Site B) (hp : p.2 < k) :
    ∑' q : Site B, ENNReal.ofReal (cylKernel B p q) *
        walkPathLaw B q {X : ℕ → Site B | ∀ n, (X n).2 < k}
      = walkPathLaw B p {X : ℕ → Site B | ∀ n, (X n).2 < k} := by
  have hE := neverReach_measurableSet B k
  have hshift : walkPathLaw B p {X : ℕ → Site B | ∀ n, (X n).2 < k}
      = walkPathLaw B p ((pathShift B) ⁻¹' {X : ℕ → Site B | ∀ n, (X n).2 < k}) := by
    refine measure_congr ?_
    filter_upwards [walkPathLaw_ae_start B p] with X h0
    show (∀ n, (X n).2 < k) = (∀ n, (pathShift B X n).2 < k)
    refine propext ⟨fun h n => h (n + 1), fun h n => ?_⟩
    cases n with
    | zero => rw [h0]; exact hp
    | succ n => exact h n
  have hrhs : walkPathLaw B p {X : ℕ → Site B | ∀ n, (X n).2 < k}
      = ∑' q : Site B, ENNReal.ofReal (cylKernel B p q) *
          walkPathLaw B q {X : ℕ → Site B | ∀ n, (X n).2 < k} := by
    rw [hshift, ← Measure.map_apply (measurable_pathShift B) hE, walkPathLaw_map_pathShift,
      bind_walkPathLaw_apply B p hE]
  exact hrhs.symm

theorem neverReach_harmonic (B : Base) (k : ℤ) (p : Site B) (hp : p.2 < k) :
    (1/4 : ℝ) * (walkPathLaw B (p.1, p.2 + 1) {X : ℕ → Site B | ∀ n, (X n).2 < k}).toReal
      + (1/4 : ℝ) * (walkPathLaw B (p.1, p.2 - 1) {X : ℕ → Site B | ∀ n, (X n).2 < k}).toReal
      + (1/2 : ℝ) * ∑ x' : B.V, B.P p.1 x' *
          (walkPathLaw B (x', p.2) {X : ℕ → Site B | ∀ n, (X n).2 < k}).toReal
      = (walkPathLaw B p {X : ℕ → Site B | ∀ n, (X n).2 < k}).toReal := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : Site B → ℝ, ∀ q : Site B,
      g q = (walkPathLaw B q {X : ℕ → Site B | ∀ n, (X n).2 < k}).toReal :=
    ⟨fun q => (walkPathLaw B q {X : ℕ → Site B | ∀ n, (X n).2 < k}).toReal, fun _ => rfl⟩
  simp only [← hg]
  set F : Finset (Site B) := Finset.univ ×ˢ ({p.2 - 1, p.2, p.2 + 1} : Finset ℤ) with hF
  have hzero : ∀ q ∉ F, ENNReal.ofReal (cylKernel B p q) *
      walkPathLaw B q {X : ℕ → Site B | ∀ n, (X n).2 < k} = 0 := by
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
  have hfin : ∑ q ∈ F, ENNReal.ofReal (cylKernel B p q) *
      walkPathLaw B q {X : ℕ → Site B | ∀ n, (X n).2 < k}
        = walkPathLaw B p {X : ℕ → Site B | ∀ n, (X n).2 < k} := by
    have hharm := neverReach_firstStep B k p hp
    rwa [tsum_eq_sum hzero] at hharm
  have hreal : ∑ q ∈ F, cylKernel B p q * g q = g p := by
    have h1 := congrArg ENNReal.toReal hfin
    rw [ENNReal.toReal_sum (fun q _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top _ _))] at h1
    rw [hg p, ← h1]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (cylKernel_nonneg p q), hg q]
  rw [← hreal, hF, Finset.sum_product]
  have hT : ∀ x : B.V, ∑ y ∈ ({p.2 - 1, p.2, p.2 + 1} : Finset ℤ),
      cylKernel B p (x, y) * g (x, y)
      = cylKernel B p (x, p.2 - 1) * g (x, p.2 - 1)
        + (1/2 : ℝ) * B.P p.1 x * g (x, p.2)
        + cylKernel B p (x, p.2 + 1) * g (x, p.2 + 1) := by
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
  have hsel : ∀ (h : B.V → ℝ), ∑ x : B.V, (if p.1 = x then (1/4 : ℝ) else 0) * h x
      = (1/4 : ℝ) * h p.1 := by
    intro h
    have hrw : ∀ x : B.V, (if p.1 = x then (1/4 : ℝ) else 0) * h x
        = if p.1 = x then (1/4 : ℝ) * h x else 0 := by
      intro x; split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun x _ => hrw x),
      Finset.sum_ite_eq Finset.univ p.1 (fun x => (1/4 : ℝ) * h x), if_pos (Finset.mem_univ _)]
  have hmid2 : ∑ x : B.V, (1/2 : ℝ) * B.P p.1 x * g (x, p.2)
      = (1/2 : ℝ) * ∑ x : B.V, B.P p.1 x * g (x, p.2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  simp_rw [hT, hbot, htop]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsel, hsel, hmid2]
  ring

end IdlaCyl.Recurrence
