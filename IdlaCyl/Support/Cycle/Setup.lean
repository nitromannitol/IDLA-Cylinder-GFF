module

/-
The cofinal indexing bridge from cycles on `n+3` vertices to `Setup`, whose
cardinality index is `N`. Source: tex:474-484 and tex:486-500,
`paper/idla-cylinder-gff.tex`. The two-vertex base only fills the finite prefix.
-/
public import IdlaCyl.Support.Cycle.Limit
public import IdlaCyl.Support.Obligations

@[expose] public section

namespace IdlaCyl
open Filter
open scoped Topology

namespace CycleSpectrum

/-- The connected two-vertex base used at the finite prefix of `Setup`. -/
def pairBase : Base where
  V := Fin 2
  graph := ⊤
  connected := SimpleGraph.connected_top
  vertexTransitive := by
    intro x y
    refine ⟨{ toEquiv := Equiv.swap x y, map_rel_iff' := ?_ }, ?_⟩
    · intro u v
      simp only [SimpleGraph.top_adj, (Equiv.swap x y).injective.ne_iff]
    · exact Equiv.swap_apply_left x y
  nontrivial := by norm_num

/-- A base with exactly `N` vertices for every `N ≥ 2`, eventually the cycle. -/
def indexedBase (N : ℕ) : Base :=
  if hN : 3 ≤ N then cycleBase N hN else pairBase

lemma indexedBase_card (N : ℕ) (hN : 2 ≤ N) : (indexedBase N).card = N := by
  by_cases h3 : 3 ≤ N
  · simp only [indexedBase, dif_pos h3, cycleBase_card]
  · have h2 : N = 2 := by omega
    subst N
    rfl

end CycleSpectrum

/-- The cardinality-indexed setup whose cofinal tail is `cycleSeq`. -/
noncomputable def cycleSetup : Setup where
  B := CycleSpectrum.indexedBase
  card_eq := CycleSpectrum.indexedBase_card
  S N := Classical.choice (spectralData_exists (CycleSpectrum.indexedBase N))
  a N := max (N : ℝ) 1
  a_pos N := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  a_tendsto := tendsto_atTop_mono (fun N => le_max_left (N : ℝ) 1)
    tendsto_natCast_atTop_atTop

/-- Reindexing the setup by `n+3` gives exactly the cycle family. -/
theorem cycleSetup_base_bridge (n : ℕ) : cycleSetup.B (n + 3) = cycleSeq n := by
  simp only [cycleSetup, CycleSpectrum.indexedBase, dif_pos (by omega : 3 ≤ n + 3), cycleSeq]

/-- The normalizing sequence on the cofinal cycle tail is `n+3`. -/
theorem cycleSetup_scale_bridge (n : ℕ) : cycleSetup.a (n + 3) = ((n + 3 : ℕ) : ℝ) := by
  change max (((n + 3 : ℕ) : ℝ)) 1 = _
  exact max_eq_left (by exact_mod_cast (show 1 ≤ n + 3 by omega))

namespace CycleSpectrum

lemma lam_transport {B C : Base} (h : B = C) (S : SpectralData B) (k : ℕ) :
    (h ▸ S).lam k = S.lam k := by
  subst C
  rfl

lemma setup_lam (N : ℕ) (hN : 3 ≤ N) (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) :
    (cycleSetup.S N).lam k = value N (k / 2) := by
  have hb : cycleSetup.B N = cycleBase N hN := by
    change indexedBase N = _
    exact dif_pos hN
  have h := cycle_lam_eq N hN (hb ▸ cycleSetup.S N) k hk hkN
  rw [lam_transport] at h
  exact h

end CycleSpectrum

/-- The cycle setup satisfies every finite-mode spectral assumption. -/
theorem cycleSetup_spectralAssumption (K : ℕ) :
    cycleSetup.SpectralAssumption (fun k => Real.sqrt 2 * Real.pi * (k / 2 : ℕ)) K := by
  intro k hk _
  constructor
  · change Tendsto _ atTop _
    apply (tendsto_add_atTop_iff_nat 3).mp
    apply (CycleSpectrum.value_limit (k / 2)).congr'
    filter_upwards [eventually_ge_atTop k] with n hn
    rw [cycleSetup_scale_bridge, CycleSpectrum.setup_lam (n + 3) (by omega) k (by omega) (by omega)]
  · have hj : (0 : ℝ) < (k / 2 : ℕ) := Nat.cast_pos.mpr (by omega)
    exact mul_pos (mul_pos (Real.sqrt_pos.mpr (by norm_num)) Real.pi_pos) hj

/-- The normalization `a_N = N` on the tail satisfies the paper's growth condition. -/
theorem cycleSetup_growthCondition : cycleSetup.GrowthCondition := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, pow_one, one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsum := hlog.add hlog
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  change Real.log (N : ℝ) / (N : ℝ) + Real.log (N : ℝ) / (N : ℝ) =
    (Real.log (N : ℝ) + logPlus (max (N : ℝ) 1)) / max (N : ℝ) 1
  rw [max_eq_left hNr, logPlus, max_eq_left (Real.log_nonneg hNr), add_div]

end IdlaCyl
