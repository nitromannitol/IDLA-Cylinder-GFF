/-
`CylAdmissible`: the support of the cylinder-walk law, and the discrete
intermediate-value theorem it powers (`tex:576`, `tex:598`).

A trajectory is admissible when every step has positive `cylKernel` weight.
This is the hypothesis that the pathwise lemmas need (e.g. `Ā_h(t) ⊆ R_h`);
it is *discharged a.s.* for `walkPathLaw`/`idlaMeasure`, never assumed silently.
-/
import IdlaCyl.Support.FirstHit

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IdlaCyl

/-- A trajectory is a legal cylinder-walk path: every step has positive kernel
weight (`def:SRW`, `tex:246-255`).  This is the *support* of the walk law. -/
def CylAdmissible (B : Base) (X : ℕ → Site B) : Prop := ∀ n, 0 < cylKernel B (X n) (X (n+1))

theorem CylAdmissible.ver_step_aux (B : Base) (p q : Site B)
    (h : 0 < cylKernel B p q) :
    q.2 = p.2 ∨ q.2 = p.2 + 1 ∨ q.2 = p.2 - 1 := by
  by_cases h1 : p.1 = q.1 ∧ (p.2 - q.2).natAbs = 1
  · obtain ⟨-, hstep⟩ := h1
    rcases Int.natAbs_eq (p.2 - q.2) with hd | hd
    · right; right; rw [hstep] at hd; omega
    · right; left; rw [hstep] at hd; omega
  · by_cases h2 : p.2 = q.2
    · exact Or.inl h2.symm
    · exfalso
      have hz : cylKernel B p q = 0 := by
        simp only [cylKernel, if_neg h1, if_neg h2]
      rw [hz] at h
      exact absurd h (lt_irrefl (0 : ℝ))

theorem CylAdmissible.ver_step (B : Base) {X : ℕ → Site B} (h : CylAdmissible B X) (n : ℕ) :
    (X (n+1)).2 = (X n).2 ∨ (X (n+1)).2 = (X n).2 + 1 ∨ (X (n+1)).2 = (X n).2 - 1 := by
  exact CylAdmissible.ver_step_aux B (X n) (X (n+1)) (h n)

/-- The per-step admissibility statement underlying `walkPathLaw_ae_admissible`,
parametrised over the starting site so it is also reusable for
`walkLawUniformAt_ae_admissible`.  This is `walkPathLaw_step_null`
(`IdlaCyl/Support/FirstHit.lean`), the statement that the walk law charges no
mass to a step of zero kernel weight.  The sets agree because `cylKernel` is
nonnegative (`cylKernel_nonneg`), so `¬ 0 < c ↔ c = 0`. -/
theorem walkPathLaw_ae_pos_step (B : Base) (x : Site B) (n : ℕ) :
    ∀ᵐ X ∂ walkPathLaw B x, 0 < cylKernel B (X n) (X (n + 1)) := by
  rw [MeasureTheory.ae_iff]
  have hset : {X : ℕ → Site B | ¬ 0 < cylKernel B (X n) (X (n + 1))}
      = {X : ℕ → Site B | cylKernel B (X n) (X (n + 1)) = 0} := by
    ext X
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h => le_antisymm (not_lt.mp h) (cylKernel_nonneg (X n) (X (n + 1))),
           fun h => by rw [h]; exact lt_irrefl 0⟩
  rw [hset]
  exact walkPathLaw_step_null B n x

theorem walkPathLaw_ae_admissible (B : Base) (p : Site B) :
    ∀ᵐ X ∂walkPathLaw B p, CylAdmissible B X :=
  MeasureTheory.ae_all_iff.mpr (walkPathLaw_ae_pos_step B p)

/-- The per-step admissibility statement underlying `walkLawUniformAt_ae_admissible`:
`walkLawUniformAt B k` is the bind of `layerLawAt B k` against `walkPathLaw B`
(`walkLawUniformAt_eq_bind`), and the integrand vanishes on the bad event for
every starting site by `walkPathLaw_ae_pos_step`. -/
theorem walkLawUniformAt_ae_pos_step (B : Base) (k : ℤ) (n : ℕ) :
    ∀ᵐ X ∂ walkLawUniformAt B k, 0 < cylKernel B (X n) (X (n + 1)) := by
  rw [walkLawUniformAt_eq_bind, MeasureTheory.ae_iff]
  have hSmeas : MeasurableSet {pq : Site B × Site B | ¬ 0 < cylKernel B pq.1 pq.2} :=
    (Set.to_countable _).measurableSet
  have hcoordmeas : Measurable (fun X : ℕ → Site B => (X n, X (n + 1))) := by fun_prop
  have hSmeas' : MeasurableSet {X : ℕ → Site B | ¬ 0 < cylKernel B (X n) (X (n + 1))} :=
    hcoordmeas hSmeas
  rw [Measure.bind_apply hSmeas' (measurable_of_countable (walkPathLaw B)).aemeasurable]
  have hzero : ∀ y : Site B,
      (walkPathLaw B y) {X : ℕ → Site B | ¬ 0 < cylKernel B (X n) (X (n + 1))} = 0 :=
    fun y => MeasureTheory.ae_iff.mp (walkPathLaw_ae_pos_step B y n)
  simp only [hzero, lintegral_zero]

theorem walkLawUniformAt_ae_admissible (B : Base) (k : ℤ) :
    ∀ᵐ X ∂walkLawUniformAt B k, CylAdmissible B X :=
  MeasureTheory.ae_all_iff.mpr (walkLawUniformAt_ae_pos_step B k)

theorem idlaMeasure_ae_admissible (B : Base) :
    ∀ᵐ ω ∂idlaMeasure B, ∀ j, CylAdmissible B (ω j) := by
  have hstep : ∀ j : ℕ, ∀ᵐ ω ∂ idlaMeasure B, CylAdmissible B (ω j) := by
    intro j
    have hmarg : ∀ᵐ X ∂ walkLawUniform B, CylAdmissible B X :=
      walkLawUniformAt_ae_admissible B 0
    have heval : (idlaMeasure B).map (fun ω : TrajSeq B => ω j) = walkLawUniform B :=
      Measure.infinitePi_map_eval (fun _ : ℕ => walkLawUniform B) j
    rw [← heval] at hmarg
    exact MeasureTheory.ae_of_ae_map (measurable_pi_apply j).aemeasurable hmarg
  exact MeasureTheory.ae_all_iff.mpr hstep

/-- Discrete intermediate value theorem: an admissible path from level `≤ k` to
level `≥ k` visits level `k` (`tex:576`, `tex:598`). -/
theorem CylAdmissible.exists_eq_level (B : Base) {X : ℕ → Site B} (h : CylAdmissible B X) {k : ℤ}
    (h0 : (X 0).2 ≤ k) {n : ℕ} (hn : k ≤ (X n).2) : ∃ m ≤ n, (X m).2 = k := by
  exact (Nat.rec (motive := fun n => k ≤ (X n).2 → ∃ m ≤ n, (X m).2 = k)
          (fun hn0 => ⟨0, le_refl 0, le_antisymm h0 hn0⟩)
          (fun n ih hn' =>
            if hk : k ≤ (X n).2 then
              let ⟨m, hm, hmk⟩ := ih hk; ⟨m, Nat.le_trans hm (Nat.le_succ n), hmk⟩
            else
              have hlt : (X n).2 < k := not_le.mp hk
              Or.elim (CylAdmissible.ver_step B h n)
                (fun h1 => False.elim (by rw [h1] at hn'; omega))
                (fun hbc => Or.elim hbc
                  (fun h2 => ⟨n + 1, le_refl (n + 1), by rw [h2] at hn' ⊢; omega⟩)
                  (fun h3 => False.elim (by rw [h3] at hn'; omega))))
          n) hn

end IdlaCyl
