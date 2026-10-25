module

public import IdlaCyl.Support.PrInnerTail.SlabUnion
public import IdlaCyl.Support.PrInnerTail.Threshold

@[expose] public section

/-!
# Nonvacuity of the slab union bound

The complete graph on `N ≥ 2` vertices is a legitimate paper base (`tex:229`): it is finite,
connected, vertex-transitive, and has `N ≥ 2`. This module checks the slab union bound and its
reduction at the complete graph on two vertices `K2`. The canonical driver `idlaMeasure K2` is a
probability measure (`idlaMeasure_isProbability`), and the bound applies to it with no extra
argument. The slab of height `2` has `N · 2 = 4` sites.
-/

namespace IdlaCyl.PrInnerTail

open MeasureTheory

/-- The complete graph on `N ≥ 2` vertices, a legitimate paper base (`tex:229`). -/
def completeBase (N : ℕ) (hN : 2 ≤ N) : Base where
  V := Fin N
  graph := SimpleGraph.completeGraph (Fin N)
  connected := by
    haveI : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
    exact SimpleGraph.connected_top
  vertexTransitive := fun x y => ⟨
    { toEquiv := Equiv.swap x y
      map_rel_iff' := by
        intro a b
        simp [SimpleGraph.completeGraph] }, Equiv.swap_apply_left x y⟩
  nontrivial := by simpa using hN

/-- The complete graph on two vertices, a legitimate base with `N = 2`. -/
def K2 : Base := completeBase 2 le_rfl

/-- The canonical driver of the base `K2` is a probability measure, so the union bound below
compares probabilities under a probability measure. -/
theorem K2_idlaMeasure_isProbability : IsProbabilityMeasure (idlaMeasure K2) :=
  inferInstance

/-- The slab of height `2` over `K2` has `N · 2 = 4` sites. -/
theorem K2_slab_card : (slab K2 2).card = 4 := by
  rw [card_slab]
  rfl

/-- The slab union bound and its reduction (`pr_inner_slab_reduced_le`) apply at `K2` with no
extra argument, at height `2` and every time `T`. -/
theorem K2_slab_reduced_le (T : ℕ) :
    idlaMeasure K2 {ω | ¬ R K2 ((2 : ℤ) : ℝ) ⊆ stoppedCluster K2 2 ω T}
      ≤ ∑ ζ ∈ slab K2 2, idlaMeasure K2 {ω | ζ ∉ stoppedCluster K2 ζ.2 ω T} :=
  pr_inner_slab_reduced_le K2 2 T

end IdlaCyl.PrInnerTail
