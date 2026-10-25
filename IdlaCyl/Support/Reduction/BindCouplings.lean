module

/-
Integrating sequential coupling kernels preserves both exact marginals.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.
The history and intermediate cluster spaces are countable. The initial
measure's total mass is retained explicitly, rather than silently set to one.
-/
public import IdlaCyl.Support.Reduction.Laws

@[expose] public section

namespace IdlaCyl.Reduction

open MeasureTheory

/-- The two-stage kernel calculation used for deep and remaining-particle comparisons. -/
theorem bind_coupling_marginals {H C D Z W : Type*}
    [Countable H] [Countable C] [Countable D]
    [MeasurableSpace H] [MeasurableSpace C] [MeasurableSpace D]
    [MeasurableSpace Z] [MeasurableSpace W]
    [MeasurableSingletonClass H] [MeasurableSingletonClass C]
    [MeasurableSingletonClass D]
    (π : Measure H) (U : H → Measure C) (F : Measure D)
    (J : H → Measure (C × D))
    (V : H → C → Measure Z) (G : D → Measure W)
    (K : H → C → D → Measure (Z × W))
    (hV : ∀ h, Measurable (V h)) (hG : Measurable G)
    (hJ : ∀ h, (J h).map Prod.fst = U h ∧ (J h).map Prod.snd = F)
    (hK : ∀ h c d, (K h c d).map Prod.fst = V h c ∧
      (K h c d).map Prod.snd = G d) :
    (π.bind (fun h => (J h).bind (fun cd => K h cd.1 cd.2))).map Prod.fst =
        π.bind (fun h => (U h).bind (V h)) ∧
    (π.bind (fun h => (J h).bind (fun cd => K h cd.1 cd.2))).map Prod.snd =
        (π Set.univ) • (F.bind G) := by
  have hfirst (h : H) :
      ((J h).bind (fun cd => K h cd.1 cd.2)).map Prod.fst = (U h).bind (V h) := by
    rw [resume_map_bind _ _ _ (measurable_of_countable _) measurable_fst]
    have heq : (fun cd : C × D => (K h cd.1 cd.2).map Prod.fst) =
        (fun cd => V h cd.1) := funext (fun cd => (hK h cd.1 cd.2).1)
    rw [heq, ← resume_bind_map _ _ _ measurable_fst (hV h), (hJ h).1]
  have hsecond (h : H) :
      ((J h).bind (fun cd => K h cd.1 cd.2)).map Prod.snd = F.bind G := by
    rw [resume_map_bind _ _ _ (measurable_of_countable _) measurable_snd]
    have heq : (fun cd : C × D => (K h cd.1 cd.2).map Prod.snd) =
        (fun cd => G cd.2) := funext (fun cd => (hK h cd.1 cd.2).2)
    rw [heq, ← resume_bind_map _ _ _ measurable_snd hG, (hJ h).2]
  constructor
  · rw [resume_map_bind _ _ _ (measurable_of_countable _) measurable_fst]
    simp_rw [hfirst]
  · rw [resume_map_bind _ _ _ (measurable_of_countable _) measurable_snd]
    simp_rw [hsecond]
    exact Measure.bind_const

end IdlaCyl.Reduction
