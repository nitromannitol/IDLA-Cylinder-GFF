/-
Discharge of `External.Freedman` from `LatticeProb.freedman`
(`~/lean/Lattice-Probability/LatticeProb/Prob/Freedman.lean`).

`LatticeProb.freedman` concludes with `(P {…}).toReal ≤ Real.exp …`; our
`External.Freedman` concludes with `P {…} ≤ ENNReal.ofReal (Real.exp …)`.  The
adapter is `ENNReal.ofReal_toReal` (a probability measure is finite) plus
monotonicity of `ENNReal.ofReal`.  The extra `Integrable` binder in
`External.Freedman` is unused by the underlying theorem and is simply ignored.
-/
import IdlaCyl.External.Basic
import LatticeProb.Prob.Freedman

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace IdlaCyl.External

-- FROZEN-STATEMENT-BEGIN
theorem freedman_of_latticeProb : Freedman := by
  intro Ω _ P _ ℱ M n b v r hMart hM0 _hint hb hv hr hbnd hvar
  have h := LatticeProb.freedman (P := P) (ℱ := ℱ) (M := M) (n := n)
    hMart hM0 hb hv hbnd hvar r hr
  calc P {ω | M n ω ≤ -r}
      = ENNReal.ofReal ((P {ω | M n ω ≤ -r}).toReal) :=
        (ENNReal.ofReal_toReal (measure_ne_top P _)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-(r ^ 2 / (2 * (v + b * r / 3))))) :=
        ENNReal.ofReal_le_ofReal h
-- FROZEN-STATEMENT-END

end IdlaCyl.External
