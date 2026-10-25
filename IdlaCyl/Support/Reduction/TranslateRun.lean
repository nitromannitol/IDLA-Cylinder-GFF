module

/-
Translation of prescribed releases by a vertical shift, read on Boolean occupation codes.
Source: paper/idla-cylinder-gff.tex, tex:1427-1431.
A run from a translated seed with translated starts has the translated occupation law.
The shift acts on the Boolean code only through the set identity `clusterCode (σ '' A) = clusterCode A ∘ σ⁻¹`.
-/
public import IdlaCyl.Support.Outer.ResumeGrowth
public import IdlaCyl.Support.Outer.Translation

@[expose] public section

attribute [local instance] Classical.propDecidable

namespace IdlaCyl.Reduction

open MeasureTheory ProbabilityTheory

/-- The occupation code of a translated set is the code of the set, read at the preimage. -/
theorem clusterCode_image_outerShift (B : Base) (L : ℤ) (A : Set (Site B)) :
    clusterCode B (outerShift B L '' A) = clusterCode B A ∘ (outerShift B L).symm := by
  funext x
  have h : x ∈ outerShift B L '' A ↔ (outerShift B L).symm x ∈ A := by
    constructor
    · rintro ⟨p, hp, rfl⟩
      simpa using hp
    · intro hx
      exact ⟨(outerShift B L).symm x, hx, by simp⟩
  show decide (x ∈ outerShift B L '' A) = decide ((outerShift B L).symm x ∈ A)
  exact decide_eq_decide.mpr h

/-- The occupation code after fresh growth is measurable in the release trajectory. -/
theorem measurable_clusterCode_clusterFrom (B : Base) (F : ResumeFinite B) (n : ℕ) :
    Measurable (fun ω : TrajSeq B => clusterCode B (clusterFrom B (resumeSeed B F) ω n)) := by
  have hfun : (fun ω : TrajSeq B => clusterCode B (clusterFrom B (resumeSeed B F) ω n)) =
      (fun C : ResumeFinite B => clusterCode B (resumeSeed B C)) ∘
        (fun ω : TrajSeq B => resumeGrow B F ω n) := by
    funext ω
    rw [Function.comp_apply, resumeSeed_grow]
  rw [hfun]
  exact (resumeCode_measurableEmbedding B).measurable.comp (measurable_resumeGrow B F n)

/-- The shifted run on an indexed family of starts, before the list is recovered. -/
theorem shifted_prescribed_growth_ofFn (B : Base) (F G : ResumeFinite B) (L : ℤ)
    (hFG : resumeSeed B G = outerShift B L '' resumeSeed B F) (start : ℕ → Site B) (n : ℕ) :
    (resumeRun B G (List.ofFn (fun i : Fin n => outerShift B L (start i)))).map
        (fun C => clusterCode B (resumeSeed B C)) =
      (resumeRun B F (List.ofFn (fun i : Fin n => start i))).map
        (fun C => clusterCode B (outerShift B L '' resumeSeed B C)) := by
  have hcode : Measurable (fun C : ResumeFinite B => clusterCode B (resumeSeed B C)) :=
    (resumeCode_measurableEmbedding B).measurable
  have hfun : (fun C : ResumeFinite B => clusterCode B (outerShift B L '' resumeSeed B C)) =
      (fun c : Site B → Bool => c ∘ (outerShift B L).symm) ∘
        (fun C : ResumeFinite B => clusterCode B (resumeSeed B C)) := by
    funext C
    exact clusterCode_image_outerShift B L _
  have hshift : Measurable (fun c : Site B → Bool => c ∘ (outerShift B L).symm) :=
    measurable_pi_iff.mpr (fun a => measurable_pi_apply ((outerShift B L).symm a))
  have hωF := measurable_clusterCode_clusterFrom B F n
  have hωG := measurable_clusterCode_clusterFrom B G n
  have hL : (resumeRun B G (List.ofFn (fun i : Fin n => outerShift B L (start i)))).map
        (fun C => clusterCode B (resumeSeed B C)) =
      (prescribedMeasure B (fun j => outerShift B L (start j))).map
        (fun ω => clusterCode B (clusterFrom B (resumeSeed B G) ω n)) :=
    resumeRun_clusterFrom_law B G (fun j => outerShift B L (start j)) n
  have hR : (resumeRun B F (List.ofFn (fun i : Fin n => start i))).map
        (fun C => clusterCode B (resumeSeed B C)) =
      (prescribedMeasure B start).map
        (fun ω => clusterCode B (clusterFrom B (resumeSeed B F) ω n)) :=
    resumeRun_clusterFrom_law B F start n
  rw [hfun, ← Measure.map_map hshift hcode, hR, Measure.map_map hshift hωF, hL,
    ← prescribedMeasure_map_outerShift B L start,
    Measure.map_map hωG (measurable_outerShiftTraj B L)]
  congr 1
  funext ω
  simp only [Function.comp_apply]
  rw [hFG, clusterFrom_outerShift]
  exact clusterCode_image_outerShift B L _

/-- A run from a translated seed with translated starts is the translated occupation run. -/
theorem shifted_prescribed_growth (B : Base) (F G : ResumeFinite B) (L : ℤ)
    (hFG : resumeSeed B G = outerShift B L '' resumeSeed B F)
    (s : List (Site B)) :
    (resumeRun B G (s.map (outerShift B L))).map
        (fun C => clusterCode B (resumeSeed B C)) =
      (resumeRun B F s).map
        (fun C => clusterCode B (outerShift B L '' resumeSeed B C)) := by
  obtain ⟨x₀⟩ : Nonempty (Site B) := inferInstance
  have hsOf : List.ofFn (fun i : Fin s.length => s.getD i x₀) = s := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp
  obtain ⟨n, start, rfl⟩ : ∃ (n : ℕ) (start : ℕ → Site B),
      s = List.ofFn (fun i : Fin n => start i) :=
    ⟨s.length, fun j => s.getD j x₀, hsOf.symm⟩
  rw [List.map_ofFn]
  exact shifted_prescribed_growth_ofFn B F G L hFG start n

end IdlaCyl.Reduction
