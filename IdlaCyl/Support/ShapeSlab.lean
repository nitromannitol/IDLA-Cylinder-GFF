module

/-
The good-event geometry behind `clm:Q-W` (`tex:1016-1030`).

On the shape event `R_{⌊T/N−Δ⌋} ⊆ A(T) ⊆ R_{T/N+Δ}`, the symmetric difference
`A(T) △ R_{T/N}` is contained in the slab `R_{T/N+Δ} \ R_{⌊T/N−Δ⌋}`.  Combined
with `quadratic_mass_difference_le_slab` this gives the paper's
`|Q_N − W_N| ≤ (1/(N a_N)) ∑_{A(T) △ R_{T/N}} |ψ|²`.
-/
public import IdlaCyl.Support.CanonicalIdla
public import IdlaCyl.Support.Discrepancy

@[expose] public section

namespace IdlaCyl

variable (B : Base)

/-- If `A(T)` lies between the half-cylinders `R_lo` and `R_hi`, then
`A(T) △ R_mid ⊆ R_hi \ R_lo` for any `lo ≤ mid ≤ hi`. -/
theorem clusterTraj_symmDiff_subset_slab (ω : TrajSeq B) (T : ℕ) {lo mid hi : ℝ}
    (hlm : lo ≤ mid) (hmh : mid ≤ hi)
    (hsub : R B lo ⊆ clusterTraj B ω T) (hsup : clusterTraj B ω T ⊆ R B hi) :
    (clusterTraj B ω T \ R B mid) ∪ (R B mid \ clusterTraj B ω T) ⊆ R B hi \ R B lo := by
  intro p hp
  rcases hp with ⟨hpA, hpR⟩ | ⟨hpR, hpA⟩
  · refine ⟨hsup hpA, ?_⟩
    intro hpLo
    exact hpR (R_mono hlm hpLo)
  · refine ⟨R_mono hmh hpR, ?_⟩
    intro hpLo
    exact hpA (hsub hpLo)

/-- The same containment with the paper's two half-cylinder heights. -/
theorem clusterTraj_symmDiff_subset_slab' (ω : TrajSeq B) (T : ℕ) (d : ℝ) (hd : 0 ≤ d)
    (hsub : R B ((T : ℝ) / B.card - d) ⊆ clusterTraj B ω T)
    (hsup : clusterTraj B ω T ⊆ R B ((T : ℝ) / B.card + d)) :
    (clusterTraj B ω T \ R B ((T : ℝ) / B.card)) ∪
        (R B ((T : ℝ) / B.card) \ clusterTraj B ω T)
      ⊆ R B ((T : ℝ) / B.card + d) \ R B ((T : ℝ) / B.card - d) :=
  clusterTraj_symmDiff_subset_slab B ω T (by linarith) (by linarith) hsub hsup

end IdlaCyl
