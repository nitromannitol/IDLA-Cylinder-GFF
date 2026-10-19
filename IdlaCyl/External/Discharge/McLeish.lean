/-
Discharge of `External.martingale_clt_v2` from
`LatticeProb.McLeish.tendstoInDistribution_martingale_clt`
(`~/lean/Lattice-Probability/LatticeProb/Prob/McLeish/MartingaleCLT.lean`).

The Lattice-Probability theorem has exactly the hypotheses of `martingale_clt_v2` except
`0 < σsq`, which its proof does not use (it also covers `σsq = 0`); that binder is ignored.
-/
import IdlaCyl.External.MartingaleCltV2
import LatticeProb.Prob.McLeish.MartingaleCLT

namespace IdlaCyl.External

-- FROZEN-STATEMENT-BEGIN
theorem martingale_clt_v2_of_latticeProb : martingale_clt_v2 := by
  intro Ω _ P _ ℱ 𝒳 t ht σsq _hσ hmart hint hbdd hmax hsq
  exact LatticeProb.McLeish.tendstoInDistribution_martingale_clt P ℱ 𝒳 t ht σsq hmart hint
    hbdd hmax hsq
-- FROZEN-STATEMENT-END

end IdlaCyl.External
