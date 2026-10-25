module

/-
The cycle theorem as the cofinal specialisation of the GFF theorem. Source:
tex:474-498, `paper/idla-cylinder-gff.tex`: the cycle family `V_N = Z_N` with
`a_N = N` and `γ_k = √2 π ⌊k/2⌋`. The conclusion of `th:GFF` enters as the
premise `hgff`, quantified over every `Setup`.
-/
public import IdlaCyl.Support.Cycle.Setup
public import IdlaCyl.Definitions.RectangularMass
public import IdlaCyl.Definitions.TestFunction
public import IdlaCyl.Support.CanonicalIdla

@[expose] public section

namespace IdlaCyl
open IdlaCyl.Defs Filter MeasureTheory ProbabilityTheory
open scoped Topology

/-- The cycle setup with a given lawful eigenbasis on each base and `a_N = max N 1`. -/
noncomputable def cycleSetupOf (S : (N : ℕ) → SpectralData (CycleSpectrum.indexedBase N)) : Setup :=
  { cycleSetup with S := S }

namespace CycleSpectrum

lemma indexedBase_eq_cycleBase (N : ℕ) (hN : 3 ≤ N) :
    indexedBase N = cycleBase N hN :=
  dif_pos hN

lemma cycleSetupOf_lam (S : (N : ℕ) → SpectralData (indexedBase N)) (N : ℕ) (hN : 3 ≤ N)
    (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    ((cycleSetupOf S).S N).lam k = value N (k / 2) := by
  have hb := indexedBase_eq_cycleBase N hN
  have h := cycle_lam_eq N hN (hb ▸ S N) k hk hkN
  rw [lam_transport] at h
  exact h

end CycleSpectrum

theorem cycleSetupOf_scale_bridge (S : (N : ℕ) → SpectralData (CycleSpectrum.indexedBase N))
    (n : ℕ) : (cycleSetupOf S).a (n + 3) = ((n + 3 : ℕ) : ℝ) :=
  cycleSetup_scale_bridge n

theorem cycleSetupOf_spectralAssumption (S : (N : ℕ) → SpectralData (CycleSpectrum.indexedBase N))
    (K : ℕ) :
    (cycleSetupOf S).SpectralAssumption (fun k => Real.sqrt 2 * Real.pi * ((k / 2 : ℕ) : ℝ)) K := by
  intro k hk _
  constructor
  · change Tendsto _ atTop _
    apply (tendsto_add_atTop_iff_nat 3).mp
    apply (CycleSpectrum.value_limit (k / 2)).congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    rw [cycleSetupOf_scale_bridge, CycleSpectrum.cycleSetupOf_lam S (n + 3) (by omega) k
      (by omega) (by omega)]
  · have hj : (0 : ℝ) < ((k / 2 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
    exact mul_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) Real.pi_pos) hj

theorem cycleSetupOf_growthCondition (S : (N : ℕ) → SpectralData (CycleSpectrum.indexedBase N)) :
    (cycleSetupOf S).GrowthCondition :=
  cycleSetup_growthCondition

/-- The cycle theorem, obtained from the GFF theorem applied to the cycle setup with
`a_N = N`, `V_N = Z_N` and `γ_k = √2 π ⌊k/2⌋` (`tex:474-498`). -/
theorem thm_cycle_of_gff
    (hgff : ∀ (U : Setup) (y₀ : ℝ), 0 < y₀ → ∀ (K : ℕ), 2 ≤ K → ∀ (α : ℕ → ℝ → ℝ), regular α K y₀ →
      ∀ (γ : ℕ → ℝ), U.SpectralAssumption γ K → U.GrowthCondition →
      ∀ g : BoundedContinuousFunction ℝ ℝ,
        Tendsto (fun N : ℕ => ∫ ω : TrajSeq (U.B N),
          g ((Real.sqrt ((N : ℝ) * U.a N))⁻¹ *
            pairingTraj (U.B N) ω (N * Nat.floor (y₀ * U.a N))
              (testAt (U.B N) (U.S N) (U.a N) K α)) ∂idlaMeasure (U.B N))
          atTop (𝓝 (∫ z : ℝ, g z ∂gaussianReal 0 (Real.toNNReal (variance K α γ y₀)))))
    (S : (N : ℕ) → SpectralData (CycleSpectrum.indexedBase N))
    (K : ℕ) (hK : 2 ≤ K) (α : ℕ → ℝ → ℝ)
    (hd : ∀ k ∈ Finset.Icc 2 K, Differentiable ℝ (α k))
    (hb : ∀ k ∈ Finset.Icc 2 K, ∃ M : ℝ, ∀ y, |deriv (α k) y| ≤ M)
    (y₀ : ℝ) (hy₀ : 0 < y₀) :
    ∀ g : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun N : ℕ => ∫ ω : TrajSeq (CycleSpectrum.indexedBase N),
        g ((1 / (N : ℝ)) *
          pairingTraj (CycleSpectrum.indexedBase N) ω (N * Nat.floor (y₀ * (N : ℝ)))
            (testAt (CycleSpectrum.indexedBase N) (S N) (N : ℝ) K α))
          ∂idlaMeasure (CycleSpectrum.indexedBase N))
        atTop (𝓝 (∫ z : ℝ, g z ∂gaussianReal 0
          (Real.toNNReal (variance K α (fun k => Real.sqrt 2 * Real.pi * ((k / 2 : ℕ) : ℝ)) y₀))))
    := by
  intro g
  have hreg : regular α K y₀ := by
    intro k hk2 hkK
    have hk : k ∈ Finset.Icc 2 K := Finset.mem_Icc.mpr ⟨hk2, hkK⟩
    obtain ⟨M, hM⟩ := hb k hk
    exact ⟨Set.univ, Filter.univ_mem, fun y _ => hd k hk y, M, fun y _ => hM y⟩
  have key := hgff (cycleSetupOf S) y₀ hy₀ K hK α hreg
    (fun k => Real.sqrt 2 * Real.pi * ((k / 2 : ℕ) : ℝ))
    (cycleSetupOf_spectralAssumption S K) (cycleSetupOf_growthCondition S) g
  refine Tendsto.congr' ?_ key
  filter_upwards [eventually_ge_atTop 1] with N hN
  have ha : (cycleSetupOf S).a N = (N : ℝ) := by
    change max (N : ℝ) 1 = N
    exact max_eq_left (by exact_mod_cast hN)
  have hc : (Real.sqrt ((N : ℝ) * (cycleSetupOf S).a N))⁻¹ = 1 / (N : ℝ) := by
    rw [ha, Real.sqrt_mul_self (Nat.cast_nonneg N), one_div]
  rw [hc, ha]
  rfl

end IdlaCyl
