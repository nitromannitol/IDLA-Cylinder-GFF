/-
The first comparison for the actual deep queue of a successful paused history.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396,1440-1453;
The canonical marginal is independent of the history.
-/
import IdlaCyl.Support.Reduction.DeepCoupling
import IdlaCyl.Support.Reduction.PausedCompletion
import IdlaCyl.Support.Reduction.DeepReserve
import IdlaCyl.Support.Reduction.LayerRelease

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Deep resumptions couple to canonical growth from the exact raw rectangle. -/
theorem silvestri_deep_comparison (hsil : External.silvestri_prop2)
    (r : ℕ) (p : ℝ) (hp : 0 < p) :
    ∃ b : ℝ, 1 ≤ b ∧ ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card →
      ∀ M β ℓ ρ : ℕ, 2 * B.card ≤ M → 0 < β → 3 * β ≤ ℓ →
      b * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ) ≤ (β : ℝ) →
      (M - B.card) * (ℓ - β) ≤ B.card ^ r →
      ∀ s : ResumeState B × ℕ, s ∈ goodPaused B M ℓ ρ →
        ClusterCoupling B (resumeRun B s.1.1 (deepQueue B β ℓ s))
          (layerGrowthLaw B (shiftFinite B ℓ (resumeEmpty B)) (ℓ : ℤ)
            ((M - B.card) * (ℓ - β))) 0 ((B.card : ℝ) ^ (-p)) := by
  obtain ⟨b, hb, N₀, hc⟩ := silvestri_uniform_comparison hsil r p hp
  refine ⟨b, hb, N₀, ?_⟩
  intro B hN M β ℓ ρ hM hβ hℓ hbuf hD s hs
  have hβℓ : β ≤ ℓ := by omega
  have hNpos : 0 < B.card := lt_of_lt_of_le (by decide : 0 < 2) B.nontrivial
  have hpos := (comparison_counts B.card M β ℓ ρ hNpos hM hβ hℓ).2.1
  have hlen : (deepQueue B β ℓ s).length = (M - B.card) * (ℓ - β) :=
    (goodPaused_split_counts B M β ℓ ρ hβℓ s hs).1
  have hstarts (i : Fin (deepQueue B β ℓ s).length) :
      ((deepQueue B β ℓ s).get i).2 ≤ ((ℓ - β : ℕ) : ℤ) := by
    have hm := List.get_mem (deepQueue B β ℓ s) i
    simp only [deepQueue, List.mem_filter, decide_eq_true_eq] at hm
    exact hm.2
  have hbuffer : R B (((ℓ - β : ℕ) : ℝ) +
      b * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ)) ⊆ resumeSeed B s.1.1 := by
    rw [hs.1]
    intro z hz
    apply mem_R.mpr
    have hh := mem_R.mp hz
    have hcast : ((ℓ - β : ℕ) : ℝ) + (β : ℝ) = (ℓ : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel hβℓ
    linarith
  have hm := hc B hN (deepQueue B β ℓ s).length
    (by rw [hlen]; exact hpos) (by rw [hlen]; exact hD)
    s.1.1 (ℓ - β) (deepQueue B β ℓ s).get
    (by rw [hs.1]; exact seedConnected_R B (ℓ : ℝ)) hstarts hbuffer
  rw [List.ofFn_get] at hm
  have hrelease := below_layer_release_growth B s.1.1 ((ℓ - β : ℕ) : ℤ) (ℓ : ℤ)
    (by exact_mod_cast Nat.sub_le ℓ β) (by simpa only [hs.1, Int.cast_natCast] using
      (Set.Subset.rfl : R B (ℓ : ℝ) ⊆ R B (ℓ : ℝ))) (deepQueue B β ℓ s).length
  rw [hrelease, hlen, goodPaused_seed_eq B M ℓ ρ s hs] at hm
  simpa only [goodPaused_seed_eq B M ℓ ρ s hs] using hm

end IdlaCyl.Reduction
