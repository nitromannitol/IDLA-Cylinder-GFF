module

/-
The second comparison includes every shallow copy and every unreleased start.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396,1440-1453;
The current occupied seed may be irregular above its buffer.
-/
public import IdlaCyl.Support.Reduction.DeepCoupling
public import IdlaCyl.Support.Reduction.PausedCompletion

@[expose] public section

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Mixing the hidden zero-layer starts preserves the original full completion marginal. -/
theorem silvestri_shallow_comparison (hsil : External.silvestri_prop2)
    (r : ℕ) (p : ℝ) (hp : 0 < p) :
    ∃ b : ℝ, 1 ≤ b ∧ ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card →
      ∀ M β ℓ ρ : ℕ, β ≤ ℓ → 0 < (M - B.card) * β + ρ →
      (M - B.card) * β + ρ ≤ B.card ^ r →
      b * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ) ≤ (β : ℝ) →
      ∀ s : ResumeState B × ℕ, s ∈ goodPaused B M ℓ ρ →
      ∀ F : ResumeFinite B, F ∈ filled B ((ℓ : ℤ) + (β : ℤ)) →
        SeedConnected B (resumeSeed B F) →
        ClusterCoupling B
          ((resumeRun B F (shallowQueue B β ℓ s)).bind
            (fun C => layerGrowthLaw B C 0 ρ))
          (layerGrowthLaw B F (ℓ : ℤ) ((M - B.card) * β + ρ))
          0 ((B.card : ℝ) ^ (-p)) := by
  obtain ⟨b, hb, N₀, hc⟩ := silvestri_uniform_comparison hsil r p hp
  refine ⟨b, hb, N₀, ?_⟩
  intro B hN M β ℓ ρ hβℓ hQ hQr hbuf s hs F hF hconn
  let σ := Measure.pi (fun _ : Fin ρ => layerLawAt B 0)
  have hlen : (shallowQueue B β ℓ s).length = (M - B.card) * β :=
    (goodPaused_split_counts B M β ℓ ρ hβℓ s hs).2.1
  have hbuffer : R B ((ℓ : ℝ) +
      b * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ)) ⊆ resumeSeed B F := by
    intro z hz
    apply hF
    apply mem_R.mpr
    have hh := mem_R.mp hz
    push_cast
    linarith
  have hm := mix_cluster_couplings_ae B σ
    (fun u => resumeRun B F (shallowQueue B β ℓ s ++ List.ofFn u))
    (fun _ => layerGrowthLaw B F (ℓ : ℤ) ((M - B.card) * β + ρ))
    0 ((B.card : ℝ) ^ (-p)) (by
      filter_upwards [layer_vector_ae_height B 0 ρ] with u hu
      have hlength : (shallowQueue B β ℓ s ++ List.ofFn u).length =
          (M - B.card) * β + ρ := by rw [List.length_append, List.length_ofFn, hlen]
      have hstarts (i : Fin (shallowQueue B β ℓ s ++ List.ofFn u).length) :
          ((shallowQueue B β ℓ s ++ List.ofFn u).get i).2 ≤ (ℓ : ℤ) := by
        have hz := List.get_mem (shallowQueue B β ℓ s ++ List.ofFn u) i
        rcases List.mem_append.mp hz with hz | hz
        · have hz' := (List.mem_filter.mp hz).1
          exact (goodPaused_queue_heights B M ℓ ρ s hs _ hz').2
        · obtain ⟨j, hj⟩ := List.mem_ofFn.mp hz
          rw [← hj, hu j]
          exact Nat.cast_nonneg ℓ
      have hc' := hc B hN (shallowQueue B β ℓ s ++ List.ofFn u).length
        (by rw [hlength]; exact hQ) (by rw [hlength]; exact hQr)
        F ℓ (shallowQueue B β ℓ s ++ List.ofFn u).get hconn hstarts hbuffer
      rw [List.ofFn_get] at hc'
      rw [hlength] at hc'
      exact hc')
  have hleft : σ.bind (fun u => resumeRun B F (shallowQueue B β ℓ s ++ List.ofFn u)) =
      (resumeRun B F (shallowQueue B β ℓ s)).bind (fun C => layerGrowthLaw B C 0 ρ) := by
    simp_rw [resumeRun_append]
    rw [resume_bind_swap]
    congr 1
    funext C
    exact uniform_start_mixture B C 0 ρ
  rw [hleft, Measure.bind_const, measure_univ, one_smul] at hm
  exact hm

end IdlaCyl.Reduction
