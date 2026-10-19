/-
Successful layered exploration has the exact raw rectangle and M-N mobile copies per layer.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396,1440-1453.
Layer counts quantify ALL integer heights, including negative
ones, so they also exclude mobile particles hidden below the recorded layers.
-/
import IdlaCyl.Support.Reduction.LayerCounts
import IdlaCyl.Support.Reduction.LayeredSupport

namespace IdlaCyl.Reduction

open MeasureTheory

/-- The finite code for an exact raw rectangle contains precisely its positive integer layers. -/
theorem finite_rectangle_mem (B : Base) (F : ResumeFinite B) (ℓ : ℕ)
    (hF : resumeSeed B F = R B (ℓ : ℝ)) (z : Site B) :
    z ∈ F.val ↔ 1 ≤ z.2 ∧ z.2 ≤ (ℓ : ℤ) := by
  constructor
  · intro hz
    have hpos : (0 : ℝ) < (z.2 : ℝ) := lt_of_not_ge (F.property z hz)
    have hposZ : (0 : ℤ) < z.2 := by exact_mod_cast hpos
    have hm : z ∈ R B (ℓ : ℝ) := hF ▸ (show z ∈ resumeSeed B F from Or.inr hz)
    have hupper : z.2 ≤ (ℓ : ℤ) := by exact_mod_cast (mem_R.mp hm)
    exact ⟨by omega, hupper⟩
  · rintro ⟨hlo, hup⟩
    have hm : z ∈ resumeSeed B F := by
      rw [hF]
      exact mem_R.mpr (by exact_mod_cast hup)
    rcases hm with hzero | hz
    · have hz0 : z.2 ≤ 0 := by exact_mod_cast (mem_R.mp hzero)
      omega
    · exact hz

/-- Each actual positive layer of a raw rectangle has exactly N occupied sites. -/
theorem occupiedOnLayer_rectangle (B : Base) (F : ResumeFinite B) (ℓ : ℕ)
    (hF : resumeSeed B F = R B (ℓ : ℝ)) (k : ℤ) :
    occupiedOnLayer B F k = if 1 ≤ k ∧ k ≤ (ℓ : ℤ) then B.card else 0 := by
  by_cases hk : 1 ≤ k ∧ k ≤ (ℓ : ℤ)
  · have heq : F.val.filter (fun z => z.2 = k) = Finset.univ ×ˢ ({k} : Finset ℤ) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
        Finset.mem_singleton, true_and]
      constructor
      · exact fun h => h.2
      · intro hz
        refine ⟨(finite_rectangle_mem B F ℓ hF z).mpr ?_, hz⟩
        rwa [hz]
    rw [occupiedOnLayer, heq, Finset.card_product, Finset.card_univ,
      Finset.card_singleton, Nat.mul_one, if_pos hk]
    rfl
  · have heq : F.val.filter (fun z => z.2 = k) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨hzF, hzk⟩ := Finset.mem_filter.mp hz
      have h := (finite_rectangle_mem B F ℓ hF z).mp hzF
      exact hk (by rwa [hzk] at h)
    rw [occupiedOnLayer, heq, Finset.card_empty, if_neg hk]

/-- Exact successful paused-state ledger, including the entire integer height axis. -/
def goodPaused (B : Base) (M ℓ ρ : ℕ) : Set (ResumeState B × ℕ) :=
  {s | resumeSeed B s.1.1 = R B (ℓ : ℝ) ∧ s.2 = ρ ∧
    ∀ k : ℤ, mobileOnLayer B s.1.2 k =
      if 1 ≤ k ∧ k ≤ (ℓ : ℤ) then M - B.card else 0}

/-- Successful filling and exact hidden-start count force every per-layer mobile count. -/
theorem layeredPause_good_ae (B : Base) (M ℓ ρ : ℕ) :
    ∀ᵐ s ∂layeredPause B M ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ),
      (resumeSeed B s.1.1 = R B (ℓ : ℝ) ∧ s.2 = ρ) → s ∈ goodPaused B M ℓ ρ := by
  filter_upwards [ae_all_iff.mpr (fun k => layeredPause_flat_layer_mass B M ℓ ρ k)] with s hs
  rintro ⟨hrect, hρ⟩
  refine ⟨hrect, hρ, fun k => ?_⟩
  have hm := hs k hρ
  rw [occupiedOnLayer_rectangle B s.1.1 ℓ hrect k] at hm
  by_cases hk : 1 ≤ k ∧ k ≤ (ℓ : ℤ)
  · simp only [if_pos hk] at hm ⊢
    omega
  · simp only [if_neg hk] at hm ⊢
    omega

/-- The full successful paused-state ledger has the same unconditional coupon failure bound. -/
theorem layeredPause_good (B : Base) (M ℓ ρ : ℕ) (q : ℝ)
    (hM : (q + 1) * (B.card : ℝ) * Real.log (B.card : ℝ) ≤ (M : ℝ)) :
    layeredPause B M ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ)
        (goodPaused B M ℓ ρ)ᶜ ≤
      ENNReal.ofReal ((ℓ : ℝ) * (B.card : ℝ) ^ (-q)) := by
  apply (measure_mono_ae (show (goodPaused B M ℓ ρ)ᶜ ≤ᵐ[
        layeredPause B M ℓ 0 (resumeEmpty B, []) (M * ℓ + ρ)]
      {s | resumeSeed B s.1.1 = R B (ℓ : ℝ) ∧ s.2 = ρ}ᶜ from ?_)).trans
  · exact layeredPause_flat_rectangle B M ℓ ρ q hM
  · filter_upwards [layeredPause_good_ae B M ℓ ρ] with s hs
    intro hbad hgood
    exact hbad (hs hgood)

/-- The all-integer layer ledger excludes every mobile particle outside layers 1,...,ℓ. -/
theorem goodPaused_queue_heights (B : Base) (M ℓ ρ : ℕ) (s : ResumeState B × ℕ)
    (hs : s ∈ goodPaused B M ℓ ρ) (z : Site B) (hz : z ∈ s.1.2) :
    1 ≤ z.2 ∧ z.2 ≤ (ℓ : ℤ) := by
  by_contra hbad
  have hc := hs.2.2 z.2
  rw [if_neg hbad] at hc
  have hm : z ∈ s.1.2.filter (fun w => w.2 = z.2) := by
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨hz, True.intro⟩
  have hnil : s.1.2.filter (fun w => w.2 = z.2) = [] := List.length_eq_zero_iff.mp hc
  rw [hnil] at hm
  exact List.not_mem_nil hm

end IdlaCyl.Reduction
