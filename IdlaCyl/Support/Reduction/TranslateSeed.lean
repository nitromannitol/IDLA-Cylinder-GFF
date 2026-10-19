/-
Translating a finite seed down by `L` keeps every site of it above the filled `R_L`.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396,1427-1431.
The comparison seed is translated down by `L`; the filled `R_L`
premise supplies the `R_0` part after translation.
-/
import IdlaCyl.Support.Outer.ResumeKernels
import IdlaCyl.Support.Outer.Translation

namespace IdlaCyl.Reduction

open MeasureTheory ProbabilityTheory

/-- Membership in the flat half-cylinder `R_0` is a bound on the vertical coordinate. -/
theorem translateSeed_mem_R_zero (B : Base) (p : Site B) :
    p ∈ R B 0 ↔ p.2 ≤ 0 := by
  rw [mem_R]
  norm_cast

/-- A vertical translation adds its shift to the height of a site. -/
theorem translateSeed_snd (B : Base) (h : ℤ) (p : Site B) :
    (outerShift B h p).2 = p.2 + h := rfl

/-- Translating down by `L` and then back up by `L` is the identity on sites. -/
theorem translateSeed_shift_cancel (B : Base) (L : ℤ) (p : Site B) :
    outerShift B L (outerShift B (-L) p) = p := by
  apply Prod.ext
  · rfl
  · change p.2 + -L + L = p.2
    omega

/-- The seed of a finite extension is the flat cylinder together with its finite part. -/
theorem translateSeed_mem_seed (B : Base) (F : ResumeFinite B) (p : Site B) :
    p ∈ resumeSeed B F ↔ p ∈ R B 0 ∨ p ∈ F.val := by
  unfold resumeSeed
  rw [Set.mem_union, Finset.mem_coe]

/-- Keep the sites of `F` strictly above height `L` and move them down by `L`. -/
def translateDown (B : Base) (F : ResumeFinite B) (L : ℕ) : ResumeFinite B :=
  ⟨(F.val.filter (fun z => (L : ℤ) < z.2)).map (outerShift B (-(L : ℤ))).toEmbedding, by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hz
    obtain ⟨_, hL⟩ := Finset.mem_filter.mp ha
    intro hmem
    have h0 := (translateSeed_mem_R_zero B _).mp hmem
    change a.2 + -(L : ℤ) ≤ 0 at h0
    omega⟩

/-- A site lies in the translated finite part exactly when it is a shifted site of `F`
above height `L`. -/
theorem mem_translateDown (B : Base) (F : ResumeFinite B) (L : ℕ) (z : Site B) :
    z ∈ (translateDown B F L).val ↔
      ∃ a, a ∈ F.val ∧ (L : ℤ) < a.2 ∧ outerShift B (-(L : ℤ)) a = z := by
  show z ∈ (F.val.filter (fun z => (L : ℤ) < z.2)).map (outerShift B (-(L : ℤ))).toEmbedding ↔ _
  rw [Finset.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨ha', hL⟩ := Finset.mem_filter.mp ha
    exact ⟨a, ha', hL, rfl⟩
  · rintro ⟨a, ha, hL, rfl⟩
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, hL⟩, rfl⟩

/-- Translating a finite seed down by `L` gives a finite seed whose translate up by `L`
recovers the original seed, provided the translated flat cylinder `R_L` is already filled. -/
theorem translated_seed_exists (B : Base) (F : ResumeFinite B) (L : ℕ)
    (hF : R B (L : ℝ) ⊆ resumeSeed B F) :
    ∃ G : ResumeFinite B,
      resumeSeed B F = outerShift B (L : ℤ) '' resumeSeed B G := by
  refine ⟨translateDown B F L, ?_⟩
  ext p
  constructor
  · intro hp
    refine ⟨outerShift B (-(L : ℤ)) p, ?_, translateSeed_shift_cancel B (L : ℤ) p⟩
    rw [translateSeed_mem_seed]
    by_cases hpL : p.2 ≤ (L : ℤ)
    · left
      rw [translateSeed_mem_R_zero]
      change p.2 + -(L : ℤ) ≤ 0
      omega
    · right
      rw [mem_translateDown]
      rcases (translateSeed_mem_seed B F p).mp hp with h0 | hpF
      · exact absurd ((translateSeed_mem_R_zero B p).mp h0) (by omega)
      · exact ⟨p, hpF, by omega, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    rw [translateSeed_mem_seed] at hq
    rcases hq with h0 | hqG
    · apply hF
      rw [mem_R]
      have h0' : (q.2 : ℝ) ≤ 0 := by exact_mod_cast (translateSeed_mem_R_zero B q).mp h0
      change (((q.2 + (L : ℤ)) : ℤ) : ℝ) ≤ (L : ℝ)
      push_cast
      linarith
    · obtain ⟨a, ha, _, rfl⟩ := (mem_translateDown B F L q).mp hqG
      rw [translateSeed_shift_cancel, translateSeed_mem_seed]
      exact Or.inr ha

end IdlaCyl.Reduction
