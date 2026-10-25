module

/-
Discharge of `External.silvestri_prop2`, Silvestri's Proposition 2 (ECP 25 (2020) paper 61,
Proposition 2), by the proof in `IdlaCyl/Support/Silvestri/`.

The coupling family pairs the walkers one by one. For each pair of starts it runs a ladder of
first-passage blocks to the levels `h, 2h, …` with `h = ⌈13 √τ log N⌉`: the vertical parts of the
two blocks are independent, their horizontal windows are maximally coupled given the numbers of
horizontal steps, and once the two block ends agree the walkers share one continuation
(`Silvestri.pairLaw`). Each attempt fails with probability at most `N^{-3}`, through the holding
count of a block and the dyadic decay of the pairwise mixing distance, and a union bound over the
walkers gives the proposition. The proof does not use the connectedness of the initial cluster,
which the proposition assumes.
-/
public import IdlaCyl.Support.Silvestri.PairLaw
public import IdlaCyl.Support.Silvestri.BlockPairEnd

@[expose] public section

namespace IdlaCyl.External

-- FROZEN-STATEMENT-BEGIN
theorem silvestri_prop2_proved : silvestri_prop2
-- FROZEN-STATEMENT-END
    :=
  Silvestri.silvestri_prop2_of_end_bound fun B hN ℓ p p' hp hp' =>
    Silvestri.blockPair_fail_le B hN ℓ p p' hp hp'

end IdlaCyl.External
