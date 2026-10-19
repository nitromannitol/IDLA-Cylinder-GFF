/-
Independent trajectory growth and its finite-state release kernels.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396.
-/
import IdlaCyl.Support.Outer.ResumeKernels
import Mathlib.Data.List.OfFn

attribute [local instance] Classical.propDecidable

namespace IdlaCyl
open MeasureTheory ProbabilityTheory
noncomputable section

/-- Ordinary growth represented as a canonical finite extension. -/
def resumeGrow (B : Base) (F : ResumeFinite B) (ω : TrajSeq B) : ℕ → ResumeFinite B
  | 0 => F
  | n + 1 => resumeInsert B (resumeGrow B F ω n)
      (exitSite' B (resumeSeed B (resumeGrow B F ω n)) (ω n))

theorem resumeSeed_grow (B : Base) (F : ResumeFinite B) (ω : TrajSeq B) (n : ℕ) :
    resumeSeed B (resumeGrow B F ω n) = clusterFrom B (resumeSeed B F) ω n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change resumeSeed B (resumeInsert B _ _) = _
      rw [resumeSeed_insert, ih, clusterFrom_succ]

theorem measurable_resumeGrow (B : Base) (F : ResumeFinite B) (n : ℕ) :
    Measurable (fun ω : TrajSeq B => resumeGrow B F ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      change Measurable (fun ω : TrajSeq B => resumeInsert B (resumeGrow B F ω n)
        (exitSite' B (resumeSeed B (resumeGrow B F ω n)) (ω n)))
      have hstep : Measurable (fun GX : ResumeFinite B × (ℕ → Site B) =>
          resumeInsert B GX.1 (exitSite' B (resumeSeed B GX.1) GX.2)) := by
        apply measurable_from_prod_countable_right
        intro G
        exact measurable_resumeStep_output B G
      have hin : Measurable (fun ω : TrajSeq B => (resumeGrow B F ω n, ω n)) :=
        ih.prodMk (measurable_pi_apply n)
      change Measurable ((fun GX : ResumeFinite B × (ℕ → Site B) =>
        resumeInsert B GX.1 (exitSite' B (resumeSeed B GX.1) GX.2)) ∘
          (fun ω : TrajSeq B => (resumeGrow B F ω n, ω n)))
      exact hstep.comp hin

theorem resumeGrow_congr (B : Base) (F : ResumeFinite B) (ω η : TrajSeq B)
    (n : ℕ) (hω : ∀ j < n, ω j = η j) : resumeGrow B F ω n = resumeGrow B F η n := by
  apply resumeSeed_injective B
  rw [resumeSeed_grow, resumeSeed_grow]
  exact clusterFrom_congr B _ ω η hω

/-- Any measurable function of earlier particles is independent of the next whole path. -/
theorem resume_indep_past (B : Base) {α : Type*} [MeasurableSpace α]
    (P : ℕ → Measure (ℕ → Site B)) [∀ j, IsProbabilityMeasure (P j)]
    (n : ℕ) (f : TrajSeq B → α) (hf : Measurable f)
    (hdep : ∀ ω η, (∀ j < n, ω j = η j) → f ω = f η) :
    IndepFun f (fun ω : TrajSeq B => ω n) (Measure.infinitePi P) := by
  have hi : iIndepFun (fun j (ω : TrajSeq B) => ω j) (Measure.infinitePi P) :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hraw := hi.indepFun_finset (Finset.range n) {n} (by simp)
    (fun j => measurable_pi_apply j)
  let φ : ({i : ℕ // i ∈ Finset.range n} → (ℕ → Site B)) → α :=
    fun s => f (extendTuple B n (fun i => s ⟨i.1, Finset.mem_range.mpr i.2⟩))
  have hφ : Measurable φ := hf.comp ((measurable_extendTuple B n).comp
    (measurable_pi_iff.mpr (fun i =>
      measurable_pi_apply (⟨i.1, Finset.mem_range.mpr i.2⟩ : ↥(Finset.range n)))))
  let ψ : ({i : ℕ // i ∈ ({n} : Finset ℕ)} → (ℕ → Site B)) → (ℕ → Site B) :=
    fun s => s ⟨n, by simp⟩
  have hψ : Measurable ψ := measurable_pi_apply (⟨n, by simp⟩ : ↥({n} : Finset ℕ))
  apply IndepFun.congr (hraw.comp hφ hψ)
  · apply Filter.Eventually.of_forall
    intro ω
    apply hdep
    intro j hj
    exact extendTuple_apply_of_lt B _ hj
  · exact Filter.Eventually.of_forall (fun _ => rfl)

/-- The law recursion for independent whole trajectories; no Markov law is assumed. -/
theorem resumeGrow_law_step (B : Base) (F : ResumeFinite B)
    (P : ℕ → Measure (ℕ → Site B)) [∀ j, IsProbabilityMeasure (P j)] (n : ℕ) :
    (Measure.infinitePi P).map (fun ω => resumeGrow B F ω (n + 1)) =
      ((Measure.infinitePi P).map (fun ω => resumeGrow B F ω n)).bind
        (fun G => (P n).map
          (fun X => resumeInsert B G (exitSite' B (resumeSeed B G) X))) := by
  let step := fun GX : ResumeFinite B × (ℕ → Site B) =>
    resumeInsert B GX.1 (exitSite' B (resumeSeed B GX.1) GX.2)
  have hs : Measurable step := by
    apply measurable_from_prod_countable_right
    intro G
    exact measurable_resumeStep_output B G
  have hj := IndepFun.map_prod_eq_prod_map_map
    (measurable_resumeGrow B F n).aemeasurable (measurable_pi_apply n).aemeasurable
    (resume_indep_past B P n _ (measurable_resumeGrow B F n)
      (fun ω η h => resumeGrow_congr B F ω η n h))
  rw [Measure.infinitePi_map_eval] at hj
  calc
    _ = ((Measure.infinitePi P).map
        (fun ω => (resumeGrow B F ω n, ω n))).map step :=
      (Measure.map_map hs ((measurable_resumeGrow B F n).prodMk
        (measurable_pi_apply n))).symm
    _ = (((Measure.infinitePi P).map (fun ω => resumeGrow B F ω n)).prod (P n)).map step := by
      rw [hj]
    _ = _ := resume_prod_map _ _ step hs

/-- The independent prescribed driver realizes the finite release queue. -/
theorem prescribedMeasure_map_resumeGrow (B : Base) (F : ResumeFinite B)
    (start : ℕ → Site B) (n : ℕ) :
    (prescribedMeasure B start).map (fun ω => resumeGrow B F ω n) =
      resumeRun B F (List.ofFn (fun i : Fin n => start i)) := by
  induction n with
  | zero => simp only [resumeGrow, Measure.map_const, measure_univ, one_smul,
      List.ofFn_zero, resumeRun]
  | succ n ih =>
      change (Measure.infinitePi (fun j => walkPathLaw B (start j))).map _ = _
      rw [resumeGrow_law_step]
      change ((prescribedMeasure B start).map (fun ω => resumeGrow B F ω n)).bind
        (resumeStep B (start n)) = _
      rw [ih, List.ofFn_succ', List.concat_eq_append, resumeRun_append]
      congr 1
      funext G
      change resumeStep B (start n) G = (resumeStep B (start n) G).bind Measure.dirac
      exact Measure.bind_dirac.symm

/-- Fresh prescribed growth agrees with the literal `clusterFrom` output law. -/
theorem resumeRun_clusterFrom_law (B : Base) (F : ResumeFinite B)
    (start : ℕ → Site B) (n : ℕ) :
    (resumeRun B F (List.ofFn (fun i : Fin n => start i))).map
        (fun G => clusterCode B (resumeSeed B G)) =
      (prescribedMeasure B start).map (fun ω => clusterCode B
        (clusterFrom B (resumeSeed B F) ω n)) := by
  rw [← prescribedMeasure_map_resumeGrow, Measure.map_map
    (resumeCode_measurableEmbedding B).measurable (measurable_resumeGrow B F n)]
  congr 1
  funext ω
  exact congrArg (clusterCode B) (resumeSeed_grow B F ω n)

/-- One uniform-start release on finite cluster states. -/
def resumeUniformStep (B : Base) (F : ResumeFinite B) : Measure (ResumeFinite B) :=
  (walkLawUniform B).map (fun X => resumeInsert B F (exitSite' B (resumeSeed B F) X))

instance resumeUniformStep_isProbability (B : Base) (F : ResumeFinite B) :
    IsProbabilityMeasure (resumeUniformStep B F) :=
  Measure.isProbabilityMeasure_map (measurable_resumeStep_output B F).aemeasurable

/-- The ordinary law recursion on the same finite state space. -/
theorem idlaMeasure_map_resumeGrow_succ (B : Base) (F : ResumeFinite B) (n : ℕ) :
    (idlaMeasure B).map (fun ω => resumeGrow B F ω (n + 1)) =
      ((idlaMeasure B).map (fun ω => resumeGrow B F ω n)).bind (resumeUniformStep B) :=
  resumeGrow_law_step B F (fun _ => walkLawUniform B) n

example : IsProbabilityMeasure (resumeUniformStep PrInnerTail.K2
    (resumeEmpty PrInnerTail.K2)) := inferInstance

example (start : ℕ → Site PrInnerTail.K2) :
    (prescribedMeasure PrInnerTail.K2 start).map
      (fun ω => resumeGrow PrInnerTail.K2 (resumeEmpty PrInnerTail.K2) ω 0) =
        Measure.dirac (resumeEmpty PrInnerTail.K2) := by
  simp only [resumeGrow, Measure.map_const, measure_univ, one_smul]

end
end IdlaCyl
