/-
Translated uniform-start specialization of Silvestri's Proposition 2.
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.
The base-size cutoff follows the constant and precedes every base and time.
Arbitrary excess occupied sites above the filled rectangle are retained.
-/
import IdlaCyl.Support.Reduction.TranslateSeed
import IdlaCyl.Support.Reduction.TranslateRun
import IdlaCyl.Support.Reduction.UniformStartMixture
import IdlaCyl.Support.Reduction.CitationEndpoint
import IdlaCyl.Support.Reduction.MixCouplingsAe
import IdlaCyl.Support.Reduction.ShiftLaws
import IdlaCyl.Support.Reduction.SeedGrowth

namespace IdlaCyl.Reduction

open MeasureTheory

/-- Translation of prescribed growth in the injective canonical finite code. -/
theorem resumeRun_map_shiftFinite (B : Base) (F : ResumeFinite B) (L : ℕ)
    (s : List (Site B)) :
    (resumeRun B F s).map (shiftFinite B L) =
      resumeRun B (shiftFinite B L F) (s.map (outerShift B (L : ℤ))) := by
  apply (resumeCode_measurableEmbedding B).map_injective
  rw [Measure.map_map (resumeCode_measurableEmbedding B).measurable
    (measurable_of_countable _)]
  change (resumeRun B F s).map
    (fun C => clusterCode B (resumeSeed B (shiftFinite B L C))) = _
  simp_rw [resumeSeed_shiftFinite]
  exact (shifted_prescribed_growth B F (shiftFinite B L F) (L : ℤ)
    (resumeSeed_shiftFinite B L F) s).symm

/-- Finite mixing of the zero-baseline endpoint citation gives the canonical uniform law. -/
theorem silvestri_uniform_zero (hsil : External.silvestri_prop2)
    (m : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    ∃ b : ℝ, 0 < b ∧ ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card →
      ∀ T : ℕ, 0 < T → T ≤ B.card ^ m →
      ∀ (F : ResumeFinite B) (s : Fin T → Site B),
        SeedConnected B (resumeSeed B F) →
        (∀ i, (s i).2 ≤ 0) →
        R B (b * Real.sqrt (External.silvestriMixingTime B) *
          Real.log (B.card : ℝ)) ⊆ resumeSeed B F →
        ClusterCoupling B (resumeRun B F (List.ofFn s)) (layerGrowthLaw B F 0 T)
          0 ((B.card : ℝ) ^ (-γ)) := by
  obtain ⟨b, hb, N₀, hc⟩ := silvestri_endpoint hsil m γ hγ
  refine ⟨b, hb, N₀, fun B hN T hT hTm F s hconn hs hF => ?_⟩
  have hm := mix_cluster_couplings_ae B (Measure.pi (fun _ : Fin T => layerLawAt B 0))
    (fun _ => resumeRun B F (List.ofFn s)) (fun u => resumeRun B F (List.ofFn u))
    0 ((B.card : ℝ) ^ (-γ)) (by
      filter_upwards [layer_vector_ae_height B 0 T] with u hu
      exact hc B hN T hT hTm F s u hconn hs (fun i => (hu i).le) hF)
  rw [Measure.bind_const, measure_univ, one_smul, uniform_start_mixture] at hm
  exact hm

/-- The same comparison holds above any baseline and for any actual buffered seed. -/
theorem silvestri_uniform_comparison (hsil : External.silvestri_prop2)
    (m : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    ∃ b : ℝ, 1 ≤ b ∧ ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card →
      ∀ T : ℕ, 0 < T → T ≤ B.card ^ m →
      ∀ (F : ResumeFinite B) (L : ℕ) (s : Fin T → Site B),
        SeedConnected B (resumeSeed B F) →
        (∀ i, (s i).2 ≤ (L : ℤ)) →
        R B ((L : ℝ) + b * Real.sqrt (mixingTime B) *
          Real.log (B.card : ℝ)) ⊆ resumeSeed B F →
        ClusterCoupling B (resumeRun B F (List.ofFn s))
          (layerGrowthLaw B F L T) 0 ((B.card : ℝ) ^ (-γ)) := by
  obtain ⟨b₀, hb₀, N₀, hc⟩ := silvestri_uniform_zero hsil m γ hγ
  refine ⟨max b₀ 1, le_max_right _ _, N₀, ?_⟩
  intro B hN T hT hTm F L s hconn hs hF
  have hlog : 0 ≤ Real.log (B.card : ℝ) :=
    Real.log_nonneg (by exact_mod_cast ((by decide : 1 ≤ 2).trans B.nontrivial))
  have hb : 0 ≤ max b₀ 1 := le_trans (by norm_num) (le_max_right _ _)
  have hscale : b₀ * Real.sqrt (External.silvestriMixingTime B) *
        Real.log (B.card : ℝ) ≤
      max b₀ 1 * Real.sqrt (mixingTime B) * Real.log (B.card : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ hlog
    exact mul_le_mul (le_max_left _ _)
      (Real.sqrt_le_sqrt (by exact_mod_cast External.silvestriMixingTime_le B))
      (Real.sqrt_nonneg _) hb
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
  have hG : R B (b₀ * Real.sqrt (External.silvestriMixingTime B) *
      Real.log (B.card : ℝ)) ⊆ resumeSeed B G := by
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
  have hconnG : SeedConnected B (resumeSeed B G) :=
    seedConnected_of_image_outerShift B (L : ℤ) (hFG ▸ hconn)
  have hm := clusterCoupling_shiftFinite B L _ _ _ (hc B hN T hT hTm G sd hconnG hsd hG)
  rw [resumeRun_map_shiftFinite, hqueue, layerGrowthLaw_map_shiftFinite, zero_add,
    ← hcode] at hm
  exact hm

end IdlaCyl.Reduction
