import IdlaCyl.Support.Reduction.Block.ExplicitComparison
import IdlaCyl.Support.Reduction.DeepCoupling
import IdlaCyl.Support.Reduction.LayerRelease
import IdlaCyl.Support.Reduction.MixCouplingsAe
import IdlaCyl.Support.Reduction.ShiftFinite
import IdlaCyl.Support.Reduction.ShiftLaws
import IdlaCyl.Support.Reduction.TranslateSeed
import IdlaCyl.Support.Reduction.UniformStartMixture
import IdlaCyl.Support.Outer.ResumeFinish

/-!
# Explicit round inputs for the block reduction

The explicit endpoint `explicit_endpoint` couples two deterministic release lists of length `T`,
started at heights at most `0`, with failure allowance `T η_H`, where
`η_H = √N e^{-H/√τ_rel}` is `explicitEta`. This file turns that coupling into the four round
inputs of the block reduction, following the Silvestri round inputs line by line. None of the
statements assumes connectedness of the seed or a size cutoff on `N`.

* `explicit_uniform_zero`: `T` releases from uniform starts on layer `0` couple with canonical
  growth from layer `0`, with allowance `T η_H`.
* `explicit_uniform_comparison`: the same from any layer `L`, on a seed containing `R_{L+H}`.
* `block_deep_explicit`: the deep resumptions of a block seed `R_{ℓH}`, started at heights at
  most `(ℓ-1)H`, couple with canonical growth from layer `ℓH`.
* `block_shallow_explicit`: shallow resumptions on a seed containing `R_{(ℓ+1)H}`, followed by
  `ρ` fresh uniform releases, couple with canonical growth from layer `ℓH`.

In each case the allowance is the number of releases times `η_H`.
-/

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Finite mixing of the explicit endpoint over independent uniform starts on layer `0` gives
the canonical uniform law, with allowance `T η_H`. -/
theorem explicit_uniform_zero (B : Base) (S : SpectralData B) (H : ℕ) (hH : 1 ≤ H) (T : ℕ)
    (F : ResumeFinite B) (s : Fin T → Site B) (hs : ∀ i, (s i).2 ≤ 0)
    (hF : R B (H : ℝ) ⊆ resumeSeed B F) :
    ClusterCoupling B (resumeRun B F (List.ofFn s)) (layerGrowthLaw B F 0 T) 0
      ((T : ℝ) * explicitEta B S H) := by
  have hm := mix_cluster_couplings_ae B (Measure.pi (fun _ : Fin T => layerLawAt B 0))
    (fun _ => resumeRun B F (List.ofFn s)) (fun u => resumeRun B F (List.ofFn u))
    0 ((T : ℝ) * explicitEta B S H) (by
      filter_upwards [layer_vector_ae_height B 0 T] with u hu
      exact explicit_endpoint B S B.nontrivial H hH T F hF s u hs (fun i => (hu i).le))
  rw [Measure.bind_const, measure_univ, one_smul, uniform_start_mixture] at hm
  exact hm

/-- The explicit endpoint from layer `L`: `T` releases started at heights at most `L`, on a seed
containing `R_{L+H}`, couple with canonical growth from layer `L`, with allowance `T η_H`. -/
theorem explicit_uniform_comparison (B : Base) (S : SpectralData B) (H : ℕ) (hH : 1 ≤ H)
    (T : ℕ) (F : ResumeFinite B) (L : ℕ) (s : Fin T → Site B) (hs : ∀ i, (s i).2 ≤ (L : ℤ))
    (hF : R B ((L : ℝ) + H) ⊆ resumeSeed B F) :
    ClusterCoupling B (resumeRun B F (List.ofFn s)) (layerGrowthLaw B F L T) 0
      ((T : ℝ) * explicitEta B S H) := by
  have hL : R B (L : ℝ) ⊆ resumeSeed B F := by
    intro z hz
    apply hF
    apply mem_R.mpr
    exact (mem_R.mp hz).trans (le_add_of_nonneg_right (by positivity))
  obtain ⟨G, hFG⟩ := translated_seed_exists B F L hL
  let sd : Fin T → Site B := fun i => (outerShift B (L : ℤ)).symm (s i)
  have hsd (i : Fin T) : (sd i).2 ≤ 0 := by
    change (s i).2 - (L : ℤ) ≤ 0
    exact sub_nonpos.mpr (hs i)
  have hG : R B (H : ℝ) ⊆ resumeSeed B G := by
    intro z hz
    have hzF : outerShift B (L : ℤ) z ∈ resumeSeed B F := by
      apply hF
      apply mem_R.mpr
      change ((z.2 + (L : ℤ) : ℤ) : ℝ) ≤ _
      push_cast
      have hh := mem_R.mp hz
      linarith
    rw [hFG] at hzF
    obtain ⟨w, hw, heq⟩ := hzF
    exact (outerShift B (L : ℤ)).injective heq ▸ hw
  have hcode : F = shiftFinite B L G := by
    apply resumeSeed_injective B
    rw [resumeSeed_shiftFinite]
    exact hFG
  have hqueue : (List.ofFn sd).map (outerShift B (L : ℤ)) = List.ofFn s := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact (outerShift B (L : ℤ)).apply_symm_apply (s i)
  have hm := clusterCoupling_shiftFinite B L _ _ _
    (explicit_uniform_zero B S H hH T G sd hsd hG)
  rw [resumeRun_map_shiftFinite, hqueue, layerGrowthLaw_map_shiftFinite, zero_add,
    ← hcode] at hm
  exact hm

/-- Deep resumptions of a block seed `R_{ℓH}`, started at heights at most `(ℓ-1)H`, couple with
canonical growth from layer `ℓH`, with allowance `(number of releases) η_H`. The release layer is
moved up from `(ℓ-1)H` to `ℓH`. -/
theorem block_deep_explicit (B : Base) (S : SpectralData B) (H : ℕ) (hH : 1 ≤ H) (ℓ : ℕ)
    (F : ResumeFinite B) (L : List (Site B)) (hℓ : 1 ≤ ℓ)
    (hseed : resumeSeed B F = R B ((ℓ * H : ℕ) : ℝ))
    (hstarts : ∀ z ∈ L, z.2 ≤ (((ℓ - 1) * H : ℕ) : ℤ)) :
    ClusterCoupling B (resumeRun B F L)
      (layerGrowthLaw B (shiftFinite B (ℓ * H) (resumeEmpty B)) ((ℓ * H : ℕ) : ℤ) L.length) 0
      ((L.length : ℝ) * explicitEta B S H) := by
  have hsub : (ℓ - 1) * H + H = ℓ * H := by
    obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
    simp [Nat.add_mul]
  have hle : (ℓ - 1) * H ≤ ℓ * H := by
    rw [← hsub]
    exact Nat.le_add_right _ _
  have hF : R B ((((ℓ - 1) * H : ℕ) : ℝ) + (H : ℝ)) ⊆ resumeSeed B F := by
    rw [hseed]
    intro z hz
    apply mem_R.mpr
    have hh := mem_R.mp hz
    have hcast : ((ℓ * H : ℕ) : ℝ) = (((ℓ - 1) * H : ℕ) : ℝ) + (H : ℝ) := by
      exact_mod_cast hsub.symm
    linarith
  have hm := explicit_uniform_comparison B S H hH L.length F ((ℓ - 1) * H) L.get
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

/-- Shallow resumptions of starts at heights at most `ℓH`, on a seed containing the rectangle of
height `(ℓ+1)H`, followed by `ρ` fresh uniform releases from layer `0`, couple with canonical
growth from layer `ℓH`, with allowance `(number of releases) η_H`. The fresh releases are mixed
over their uniform starts. -/
theorem block_shallow_explicit (B : Base) (S : SpectralData B) (H : ℕ) (hH : 1 ≤ H) (ℓ ρ : ℕ)
    (c : ResumeFinite B) (L : List (Site B))
    (hF : c ∈ filled B (((ℓ + 1) * H : ℕ) : ℤ))
    (hstarts : ∀ z ∈ L, z.2 ≤ ((ℓ * H : ℕ) : ℤ)) :
    ClusterCoupling B ((resumeRun B c L).bind (fun C => layerGrowthLaw B C 0 ρ))
      (layerGrowthLaw B c ((ℓ * H : ℕ) : ℤ) (L.length + ρ)) 0
      (((L.length + ρ : ℕ) : ℝ) * explicitEta B S H) := by
  have hF' : R B ((((ℓ + 1) * H : ℕ) : ℤ) : ℝ) ⊆ resumeSeed B c := hF
  have hbuffer : R B (((ℓ * H : ℕ) : ℝ) + (H : ℝ)) ⊆ resumeSeed B c := by
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
    0 (((L.length + ρ : ℕ) : ℝ) * explicitEta B S H) (by
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
      have hc' := explicit_uniform_comparison B S H hH (L ++ List.ofFn u).length c (ℓ * H)
        (L ++ List.ofFn u).get hstarts' hbuffer
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
