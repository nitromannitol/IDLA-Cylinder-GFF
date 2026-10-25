module

/-
The event-inclusion consumers of `pr:inner` at `tex:1164` and `tex:1183`, on the canonical driver
`idlaMeasure` (`tex:1155-1158`).

Each printed inequality compares the probabilities of two events of one driving law.  It follows
from an almost-sure set inclusion between the stopped clusters and the IDLA cluster, proved in
`StoppedAe.lean`; `measure_mono_ae` turns that inclusion into the inequality, with no measurability
hypothesis.  The frozen statement `IdlaCyl.Frozen.pr_inner` is stated for the legacy `driverLaw` and
`cluster` of `Idla.lean`, with `barA` as a free parameter, so these consumers do not close it.
-/
public import IdlaCyl.Support.StoppedAe

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace IdlaCyl

/-- The first inequality of `pr:inner` (`tex:1164`): the IDLA cluster misses `R_h` no more often
than the stopped cluster `Ā_h(T)` does, for every height `h ≥ 1` and every time `T`. -/
theorem pr_inner_ineq_first (B : Base) {h : ℤ} (hh : 1 ≤ h) (T : ℕ) :
    idlaMeasure B {ω | ¬ R B (h : ℝ) ⊆ clusterTraj B ω T}
      ≤ idlaMeasure B {ω | ¬ R B (h : ℝ) ⊆ stoppedCluster B h ω T} := by
  refine measure_mono_ae ?_
  filter_upwards [stoppedCluster_ae_subset_clusterTraj B] with ω hω
  intro hA hR
  exact hA (hR.trans (hω T h hh))

/-- The reduction step of `pr:inner` (`tex:1183`): for `1 ≤ ζ₂ ≤ h` with `ζ = (ζ₁, ζ₂)`, the
stopped cluster `Ā_h(T)` misses `ζ` no more often than `Ā_{ζ₂}(T)` does. -/
theorem pr_inner_ineq_reduction (B : Base) {h : ℤ}
    (ζ : Site B) (hζ : 1 ≤ ζ.2) (hζh : ζ.2 ≤ h) (T : ℕ) :
    idlaMeasure B {ω | ζ ∉ stoppedCluster B h ω T}
      ≤ idlaMeasure B {ω | ζ ∉ stoppedCluster B ζ.2 ω T} := by
  refine measure_mono_ae ?_
  filter_upwards [stoppedCluster_ae_mono B] with ω hω
  intro hnot hmem
  exact hnot (hω T ζ.2 h hζ hζh hmem)

/-- Non-vacuity: under the probability measure `idlaMeasure B`, some driving sequence meets every
pathwise hypothesis used above, because those hypotheses hold on an event of full measure. -/
theorem exists_traj_stopped_hyp (B : Base) :
    ∃ ω : TrajSeq B, (∀ j, CylAdmissible B (ω j)) ∧ (∀ j : ℕ, ω j 0 ∈ R B 0) ∧
      (∀ t : ℕ, ∀ h : ℤ, 1 ≤ h →
        exitTime' B (stoppedCluster B h ω t ∩ R B ((h : ℝ) - 1)) (ω t) ≠ ⊤) ∧
      (∀ t : ℕ, exitTime' B (clusterTraj B ω t) (ω t) ≠ ⊤) :=
  (idlaMeasure_ae_stopped_hyp B).exists

/-- The registered recurrence input `LazyRwRecurrent` (`tex:600-604`) holds for the cylinder walk:
the repository proves it (`External.lazyRwRecurrent_holds`), and `StoppedAe.lean` applies that
proof, so no result carries it as a hypothesis. -/
theorem lazyRwRecurrent_nonvacuous : External.LazyRwRecurrent :=
  External.lazyRwRecurrent_holds

/-- Non-vacuity of the reduction hypotheses: for every `h ≥ 1` some site `ζ` satisfies
`1 ≤ ζ₂ ≤ h` (`tex:1183`), namely the site `(B.pt, 1)`. -/
theorem exists_site_for_reduction (B : Base) {h : ℤ} (hh : 1 ≤ h) :
    ∃ ζ : Site B, 1 ≤ ζ.2 ∧ ζ.2 ≤ h :=
  ⟨(B.pt, 1), le_rfl, hh⟩

/-- The monotonicity lemma `stoppedCluster_mono_height` applied at a driving sequence that meets
its hypothesis: `Ā_{h₁}(t) ⊆ Ā_{h₂}(t)` for every `t` at that sequence (`tex:1156`). -/
theorem stoppedCluster_mono_at_witness (B : Base) {h₁ h₂ : ℤ}
    (hh₁ : 1 ≤ h₁) (hh₁₂ : h₁ ≤ h₂) :
    ∃ ω : TrajSeq B, (∀ j, CylAdmissible B (ω j)) ∧
      ∀ t : ℕ, stoppedCluster B h₁ ω t ⊆ stoppedCluster B h₂ ω t := by
  obtain ⟨ω, hadm, -, hfin, -⟩ := exists_traj_stopped_hyp B
  exact ⟨ω, hadm, fun t => stoppedCluster_mono_height B hh₁₂ ω
    (fun s => hfin s h₂ (le_trans hh₁ hh₁₂)) t⟩

end IdlaCyl
