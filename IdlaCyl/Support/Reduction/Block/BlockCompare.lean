module

/-
The deep and shallow comparisons for one block round, with explicit seed hypotheses.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396,1440-1453.
-/
public import IdlaCyl.Support.Reduction.DeepCoupling
public import IdlaCyl.Support.Reduction.LayerRelease
public import IdlaCyl.Support.Reduction.ShiftFinite
public import IdlaCyl.Support.Reduction.MixCouplingsAe
public import IdlaCyl.Support.Reduction.UniformStartMixture
public import IdlaCyl.Support.Outer.ResumeFinish

@[expose] public section

/-!
# Deep and shallow comparisons for a block round

Two finite-cluster couplings used by one block reduction step, with `N = B.card`.

* `block_deep_comparison`: resumptions of `d ≤ T` deep particles, released from layer `(ℓ-1)H`
  and started at heights at most `(ℓ-1)H`, couple with canonical growth from layer `ℓH` on the
  seed `R_{ℓH}`, with failure probability at most `N^{-p}`.
* `block_shallow_comparison`: resumptions of a list of starts at heights at most `ℓH`, followed
  by `ρ` fresh releases from layer zero, couple with canonical growth from layer `ℓH` on any
  connected seed containing the rectangle of height `(ℓ+1)H`, with failure probability at most
  `N^{-p}`.

Both comparisons assume Silvestri's Proposition 2, `External.silvestri_prop2`, and the buffer
condition `b √τ log N ≤ H`, with `b` and the base-size cutoff chosen before every base.
-/

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Deep resumptions of a block seed `R_{ℓH}` couple with canonical growth from layer `ℓH`.
The starts lie at heights at most `(ℓ-1)H`, and the release layer is moved up to `ℓH`. -/
theorem block_deep_comparison (hsil : External.silvestri_prop2)
    (r : ℕ) (p : ℝ) (hp : 0 < p) :
    ∃ b : ℝ, 1 ≤ b ∧ ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card →
      ∀ (H ℓ : ℕ) (F : ResumeFinite B) (L : List (Site B)), 1 ≤ ℓ →
      b * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ) ≤ (H : ℝ) →
      resumeSeed B F = R B ((ℓ * H : ℕ) : ℝ) →
      (∀ z ∈ L, z.2 ≤ (((ℓ - 1) * H : ℕ) : ℤ)) → 0 < L.length → L.length ≤ B.card ^ r →
      ClusterCoupling B (resumeRun B F L)
        (layerGrowthLaw B (shiftFinite B (ℓ * H) (resumeEmpty B)) ((ℓ * H : ℕ) : ℤ) L.length)
        0 ((B.card : ℝ) ^ (-p)) := by
  obtain ⟨b, hb, N₀, hc⟩ := silvestri_uniform_comparison hsil r p hp
  refine ⟨b, hb, N₀, ?_⟩
  intro B hN H ℓ F L hℓ hbH hseed hstarts hpos hr
  have hsub : (ℓ - 1) * H + H = ℓ * H := by
    obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
    simp [Nat.add_mul]
  have hle : (ℓ - 1) * H ≤ ℓ * H := by
    rw [← hsub]
    exact Nat.le_add_right _ _
  have hF : R B ((((ℓ - 1) * H : ℕ) : ℝ) + b * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ))
      ⊆ resumeSeed B F := by
    rw [hseed]
    intro z hz
    apply mem_R.mpr
    have hh := mem_R.mp hz
    have hcast : ((ℓ * H : ℕ) : ℝ) = (((ℓ - 1) * H : ℕ) : ℝ) + (H : ℝ) := by
      exact_mod_cast hsub.symm
    linarith
  have hconn : SeedConnected B (resumeSeed B F) := by
    rw [hseed]
    exact seedConnected_R B _
  have hm := hc B hN L.length hpos hr F ((ℓ - 1) * H) L.get hconn
    (fun i => hstarts _ (List.get_mem L i)) hF
  rw [List.ofFn_get] at hm
  have hFeq : F = shiftFinite B (ℓ * H) (resumeEmpty B) := by
    apply resumeSeed_injective B
    rw [hseed, resumeSeed_shiftFinite_empty]
  subst hFeq
  have hrel := below_layer_release_growth B (shiftFinite B (ℓ * H) (resumeEmpty B))
    (((ℓ - 1) * H : ℕ) : ℤ) ((ℓ * H : ℕ) : ℤ) (by exact_mod_cast hle)
    (by rw [resumeSeed_shiftFinite_empty, Int.cast_natCast]) L.length
  rw [hrel] at hm
  exact hm

/-- Shallow resumptions on a connected seed containing the rectangle of height `(ℓ+1)H`,
followed by `ρ` fresh releases from layer zero, couple with canonical growth from layer `ℓH`.
The fresh releases are mixed over their uniform starts. -/
theorem block_shallow_comparison (hsil : External.silvestri_prop2)
    (r : ℕ) (p : ℝ) (hp : 0 < p) :
    ∃ b : ℝ, 1 ≤ b ∧ ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card →
      ∀ (H ℓ ρ : ℕ) (c : ResumeFinite B) (L : List (Site B)),
      b * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ) ≤ (H : ℝ) →
      c ∈ filled B (((ℓ + 1) * H : ℕ) : ℤ) → SeedConnected B (resumeSeed B c) →
      (∀ z ∈ L, z.2 ≤ ((ℓ * H : ℕ) : ℤ)) → 0 < L.length + ρ → L.length + ρ ≤ B.card ^ r →
      ClusterCoupling B ((resumeRun B c L).bind (fun C => layerGrowthLaw B C 0 ρ))
        (layerGrowthLaw B c ((ℓ * H : ℕ) : ℤ) (L.length + ρ)) 0 ((B.card : ℝ) ^ (-p)) := by
  obtain ⟨b, hb, N₀, hc⟩ := silvestri_uniform_comparison hsil r p hp
  refine ⟨b, hb, N₀, ?_⟩
  intro B hN H ℓ ρ c L hbH hF hconn hstarts hpos hr
  have hF' : R B ((((ℓ + 1) * H : ℕ) : ℤ) : ℝ) ⊆ resumeSeed B c := hF
  have hbuffer : R B (((ℓ * H : ℕ) : ℝ) + b * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ))
      ⊆ resumeSeed B c := by
    intro z hz
    apply hF'
    apply mem_R.mpr
    have hh := mem_R.mp hz
    have hcast : ((((ℓ + 1) * H : ℕ) : ℤ) : ℝ) = ((ℓ * H : ℕ) : ℝ) + (H : ℝ) := by
      push_cast
      ring
    linarith
  let σ := Measure.pi (fun _ : Fin ρ => layerLawAt B 0)
  have hm := mix_cluster_couplings_ae B σ
    (fun u => resumeRun B c (L ++ List.ofFn u))
    (fun _ => layerGrowthLaw B c ((ℓ * H : ℕ) : ℤ) (L.length + ρ))
    0 ((B.card : ℝ) ^ (-p)) (by
      filter_upwards [layer_vector_ae_height B 0 ρ] with u hu
      have hlength : (L ++ List.ofFn u).length = L.length + ρ := by
        rw [List.length_append, List.length_ofFn]
      have hstarts' (i : Fin (L ++ List.ofFn u).length) :
          ((L ++ List.ofFn u).get i).2 ≤ ((ℓ * H : ℕ) : ℤ) := by
        have hz := List.get_mem (L ++ List.ofFn u) i
        rcases List.mem_append.mp hz with hz | hz
        · exact hstarts _ hz
        · obtain ⟨j, hj⟩ := List.mem_ofFn.mp hz
          rw [← hj, hu j]
          exact Nat.cast_nonneg _
      have hc' := hc B hN (L ++ List.ofFn u).length
        (by rw [hlength]; exact hpos) (by rw [hlength]; exact hr)
        c (ℓ * H) (L ++ List.ofFn u).get hconn hstarts' hbuffer
      rw [List.ofFn_get] at hc'
      rw [hlength] at hc'
      exact hc')
  have hleft : σ.bind (fun u => resumeRun B c (L ++ List.ofFn u)) =
      (resumeRun B c L).bind (fun C => layerGrowthLaw B C 0 ρ) := by
    simp_rw [resumeRun_append]
    rw [resume_bind_swap]
    congr 1
    funext C
    exact uniform_start_mixture B C 0 ρ
  rw [hleft, Measure.bind_const, measure_univ, one_smul] at hm
  exact hm

end IdlaCyl.Reduction
