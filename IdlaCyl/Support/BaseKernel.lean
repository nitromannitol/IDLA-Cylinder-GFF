/-
The bridge from the canonical base kernel `Base.P` to the
`SymmetricKernel` library of `Support/FiniteKernel.lean`.

`Base.P` already carries everything `SymmetricKernel` asks for:
nonnegativity (`P_nonneg`), stochasticity (`P_row_sum`) and symmetry
(`P_symm`).  Bundling it lets every `SymmetricKernel` lemma
(`col_sum`, `sum_applyFn`, `eigenfunction_sum_zero`, `row_bessel`, the
`CountingOrthonormal` layer, …) apply to `Base.P` without re-derivation.
-/
import IdlaCyl.Support.Base
import IdlaCyl.Support.FiniteKernel

namespace IdlaCyl

open scoped BigOperators

/-- The lazy base kernel `P_N` (`tex:230-236`) as a `SymmetricKernel`. -/
noncomputable def kernelOfBase (B : Base) : SymmetricKernel B.V where
  weight x x' := B.P x x'
  nonneg := B.P_nonneg
  row_sum := B.P_row_sum
  symmetric := B.P_symm

@[simp]
theorem kernelOfBase_weight (B : Base) (x x' : B.V) :
    (kernelOfBase B).weight x x' = B.P x x' := rfl

/-- The kernel's `applyFn` is the horizontal part of the canonical
`cylinderOp` (`tex:681-684`, `eq:PN`). -/
theorem kernelOfBase_applyFn (B : Base) (f : B.V → ℝ) (x : B.V) :
    (kernelOfBase B).applyFn f x = ∑ x' : B.V, B.P x x' * f x' := rfl

end IdlaCyl
