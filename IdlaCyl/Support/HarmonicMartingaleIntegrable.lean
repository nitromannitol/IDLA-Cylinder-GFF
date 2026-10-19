/-
Integrability of the harmonic statistic without any hypothesis on the test function.

`tex:687-700` (Lemma `le:martingale`): the cluster starts from `R_0`, and a
nearest-neighbour walk exits a cluster in `R_h` at height at most `h + 1`.
Induction gives the deterministic almost-sure cap `A(t) ⊆ R_t`. The `k`-th
settling site therefore lies in the finite strip `V_N × [1, k+1]`. Every
real-valued test function is bounded on this strip, and is measurable because
the cylinder is countable. Thus every summand, and hence `M(t)`, is integrable.

The martingale conclusion uses the existing optional-stopping theorem with
exactly the paper's harmonicity, zero-average and exponential-decay hypotheses.
-/
import IdlaCyl.Support.CondExpZeroHonest

namespace IdlaCyl

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private theorem exitSite_ver_le_succ (B : Base) (S : Set (Site B)) (h : ℤ)
    (hS : S ⊆ R B (h : ℝ)) (X : ℕ → Site B)
    (hadm : CylAdmissible B X) (hstart : (X 0).2 ≤ h + 1)
    (hfin : exitTime' B S X ≠ ⊤) : (exitSite' B S X).2 ≤ h + 1 := by
  have hout : X (exitTime' B S X).toNat ∉ S :=
    ((exitTime'_eq_coe_iff B S X _).mp (ENat.coe_toNat hfin).symm).1
  have hidx := exitIdx_spec B S (exitTime' B S X).toNat X
    ⟨(exitTime' B S X).toNat, le_rfl, hout⟩
  have hbound := ver_exitIdx_le B S h hS (exitTime' B S X).toNat X hadm hstart
  rw [exitSite'_eq_apply_toNat B S hfin, hidx, ENat.toNat_coe]
  exact hbound

private theorem idlaMeasure_ae_start_ver_zero (B : Base) :
    ∀ᵐ ω ∂idlaMeasure B, ∀ j, ((ω j) 0).2 = 0 := by
  apply ae_all_iff.mpr
  intro j
  have hmarg := walkLawUniform_ae_ver_zero B
  have heval : (idlaMeasure B).map (fun ω : TrajSeq B => ω j) = walkLawUniform B :=
    Measure.infinitePi_map_eval (fun _ : ℕ => walkLawUniform B) j
  rw [← heval] at hmarg
  exact ae_of_ae_map (measurable_pi_apply j).aemeasurable hmarg

private theorem clusterTraj_subset_R_time_of (B : Base) (ω : TrajSeq B)
    (hadm : ∀ j, CylAdmissible B (ω j)) (hstart : ∀ j, ((ω j) 0).2 = 0)
    (hfin : ∀ j, exitTime' B (clusterTraj B ω j) (ω j) ≠ ⊤) (t : ℕ) :
    clusterTraj B ω t ⊆ R B (t : ℝ) := by
  induction t with
  | zero =>
    simpa only [clusterTraj, clusterFrom_zero, Nat.cast_zero] using
      (Set.Subset.rfl : R B 0 ⊆ R B 0)
  | succ k ih =>
    have hsettle : (settleSite B ω k).2 ≤ (k : ℤ) + 1 :=
      exitSite_ver_le_succ B (clusterTraj B ω k) (k : ℤ)
        (by simpa only [Int.cast_natCast] using ih) (ω k) (hadm k)
        (by rw [hstart k]; omega) (hfin k)
    rw [clusterTraj_plus_ncard_of_succ]
    intro p hp
    rcases hp with hp | hp
    · exact R_mono (by exact_mod_cast Nat.le_succ k) (ih hp)
    · have hp' : p = settleSite B ω k := hp
      rw [hp', mem_R]
      exact_mod_cast hsettle

/-- The canonical cluster after `t` particles lies below height `t` almost
surely (`tex:695-700`), with a cap independent of the sample trajectory. -/
theorem clusterTraj_ae_subset_R_time (B : Base) (t : ℕ) :
    ∀ᵐ ω ∂idlaMeasure B, clusterTraj B ω t ⊆ R B (t : ℝ) := by
  have hfin : ∀ᵐ ω ∂idlaMeasure B,
      ∀ j, exitTime' B (clusterTraj B ω j) (ω j) ≠ ⊤ :=
    ae_all_iff.mpr (exitTraj_ae_finite B)
  filter_upwards [idlaMeasure_ae_admissible B, idlaMeasure_ae_start_ver_zero B, hfin]
    with ω hadm hstart hfin
  exact clusterTraj_subset_R_time_of B ω hadm hstart hfin t

/-- Particle `k` (indexed from zero) settles at a height in `[1, k+1]`
almost surely (`tex:695-700`). -/
theorem settleSite_ae_height_bounds (B : Base) (k : ℕ) :
    ∀ᵐ ω ∂idlaMeasure B,
      1 ≤ (settleSite B ω k).2 ∧ (settleSite B ω k).2 ≤ (k : ℤ) + 1 := by
  filter_upwards [clusterTraj_ae_subset_R_time B k, idlaMeasure_ae_admissible B,
    idlaMeasure_ae_start_ver_zero B, exitTraj_ae_finite B k]
    with ω hcap hadm hstart hfin
  refine ⟨(clusterTraj_plus_ncard_of_settle B ω k hfin).2, ?_⟩
  exact exitSite_ver_le_succ B (clusterTraj B ω k) (k : ℤ)
    (by simpa only [Int.cast_natCast] using hcap) (ω k) (hadm k)
    (by rw [hstart k]; omega) hfin

/-- Every real-valued test function at a fixed settling site is integrable:
its almost-sure range is a finite strip, regardless of its growth elsewhere. -/
theorem integrable_psi_settleSite (B : Base) (ψ : Site B → ℝ) (k : ℕ) :
    Integrable (fun ω : TrajSeq B => ψ (settleSite B ω k)) (idlaMeasure B) := by
  classical
  let F : Finset (Site B) := Finset.univ ×ˢ Finset.Icc 1 ((k : ℤ) + 1)
  refine Integrable.of_bound
    (((measurable_of_countable ψ).comp (measurable_settleSite B k)).aestronglyMeasurable)
    (∑ p ∈ F, ‖ψ p‖) ?_
  filter_upwards [settleSite_ae_height_bounds B k] with ω hω
  have hmem : settleSite B ω k ∈ F :=
    Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_Icc.mpr hω⟩
  exact Finset.single_le_sum (fun p _ => norm_nonneg (ψ p)) hmem

/-- The statistic `M(t)` is integrable for every `ψ`, without harmonicity or
decay assumptions (`tex:687-700`). -/
theorem harmonicMartingale_integrable (B : Base) (ψ : Site B → ℝ) (t : ℕ) :
    Integrable (harmonicMartingale B ψ t) (idlaMeasure B) := by
  unfold harmonicMartingale
  exact (integrable_finsetSum (Finset.range t)
    (fun k _ => integrable_psi_settleSite B ψ k)).const_mul _

/-- Lemma `le:martingale` with precisely its printed hypotheses
(`tex:687-700`), and no integrability premise. -/
theorem harmonicMartingale_isMartingale' (B : Base) (ψ : Site B → ℝ)
    (hharm : DiscreteHarmonic B ψ) (hzero : ZeroHorizontalAverage B ψ)
    (hd : ExpDecayBelow B ψ) :
    Martingale (harmonicMartingale B ψ) (idlaFiltration B) (idlaMeasure B) :=
  harmonicMartingale_isMartingale_of_expDecayBelow B ψ hharm hzero hd
    (harmonicMartingale_integrable B ψ)

namespace HarmonicMartingaleIntegrableExamples

/-- A concrete admissible base: the complete graph on two vertices. -/
def twoVertexBase : Base where
  V := Fin 2
  graph := ⊤
  connected := SimpleGraph.connected_top
  vertexTransitive x y :=
    ⟨SimpleGraph.Iso.completeGraph (Equiv.swap x y), Equiv.swap_apply_left x y⟩
  nontrivial := by decide

/-- The height test function is nonzero and has no imposed decay hypothesis. -/
example : (fun p : Site twoVertexBase => (p.2 : ℝ)) ≠ 0 := by
  intro h
  have hp := congrFun h ((0 : Fin 2), (1 : ℤ))
  norm_num at hp

example (t : ℕ) :
    Integrable (harmonicMartingale twoVertexBase (fun p => (p.2 : ℝ)) t)
      (idlaMeasure twoVertexBase) :=
  harmonicMartingale_integrable twoVertexBase (fun p => (p.2 : ℝ)) t

/-- At time one the cluster has height at most one. -/
example (B : Base) : ∀ᵐ ω ∂idlaMeasure B, clusterTraj B ω 1 ⊆ R B 1 := by
  simpa only [Nat.cast_one] using clusterTraj_ae_subset_R_time B 1

/-- The first particle settles exactly on level one. -/
example (B : Base) : ∀ᵐ ω ∂idlaMeasure B, (settleSite B ω 0).2 = 1 := by
  filter_upwards [settleSite_ae_height_bounds B 0] with ω hω
  omega

example (B : Base) : ∀ᵐ ω ∂idlaMeasure B,
    1 ≤ (settleSite B ω 1).2 ∧ (settleSite B ω 1).2 ≤ 2 := by
  simpa only [Nat.cast_one, one_add_one_eq_two] using settleSite_ae_height_bounds B 1

end HarmonicMartingaleIntegrableExamples

end IdlaCyl
