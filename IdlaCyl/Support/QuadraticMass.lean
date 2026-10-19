/-
The deterministic slab estimate behind `clm:Q-W` (`tex:1003-1038`).

For non-negative `ψ²` and finite sets `L ⊆ A, B ⊆ U`, two quadratic masses
differ only on the slab `U \ L`:

  `|∑_A ψ² − ∑_B ψ²| ≤ ∑_{U \ L} ψ²`.

This is the deterministic core of the paper's bound
`|Q_N − W_N| ≤ (1/(N a_N)) ∑_{A(T) △ R_{T/N}} |ψ|²`; only the geometry of the
good event `E` (which puts `A(T)` and `R_{T/N}` between `R_{⌊T/N−Δ⌋}` and
`R_{T/N+Δ}`) is handled where the bound is used.  Finite sums only; no `finsum`/`tsum`.
-/
import IdlaCyl.Support.WeightedStability

namespace IdlaCyl

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- Two finite sets trapped between `L` and `U` can differ only in `U \ L`. -/
theorem differenceSupport_subset_slab (A B L U : Finset α)
    (hLA : L ⊆ A) (hAU : A ⊆ U) (hLB : L ⊆ B) (hBU : B ⊆ U) :
    differenceSupport A B ⊆ U \ L := by
  intro x hx
  rcases mem_differenceSupport.mp hx with ⟨hA, hnB⟩ | ⟨hB, hnA⟩
  · exact Finset.mem_sdiff.mpr ⟨hAU hA, fun hL => hnB (hLB hL)⟩
  · exact Finset.mem_sdiff.mpr ⟨hBU hB, fun hL => hnA (hLA hL)⟩

/-- The deterministic support estimate underlying the `clm:Q-W` bound. -/
theorem quadratic_mass_difference_le_slab (A B L U : Finset α)
    (hLA : L ⊆ A) (hAU : A ⊆ U) (hLB : L ⊆ B) (hBU : B ⊆ U)
    (ψ : α → ℝ) :
    |(∑ x ∈ A, ψ x ^ 2) - ∑ x ∈ B, ψ x ^ 2| ≤ ∑ x ∈ U \ L, ψ x ^ 2 := by
  exact abs_pairing_le_slab_sum A B (U \ L) (fun x => ψ x ^ 2)
    (fun x => sq_nonneg (ψ x))
    (differenceSupport_subset_slab A B L U hLA hAU hLB hBU)

end IdlaCyl
