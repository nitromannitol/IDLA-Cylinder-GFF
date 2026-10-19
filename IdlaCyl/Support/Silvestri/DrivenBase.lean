import IdlaCyl.Support.Idla
import LatticeProb.Prob.InfinitePiSplit

/-!
# The driven cylinder path

For a starting site `x` and a driver `w : ℕ → ℝ × ℝ`, the cylinder path
`cylPath B x w` is a measurable function of `w`. Splitting the driver at its
first entry restarts the path from the one-step position: the path driven by
`LatticeProb.consNat u w` from `x`, read one time step later, is the path driven
by `w` from `cylStep B x u`.

Main results:
* `IdlaCyl.Silvestri.measurable_cylPath`: for each starting site, the path is a
  measurable function of the driver.
* `IdlaCyl.Silvestri.cylPath_consNat`: the restart identity after one step.
-/

namespace IdlaCyl.Silvestri

open MeasureTheory

/-- One cylinder step is measurable jointly in the current site and the
uniform pair that drives it. -/
theorem measurable_cylStep_pair (B : Base) :
    Measurable (fun z : Site B × (ℝ × ℝ) => cylStep B z.1 z.2) := by
  let values : B.V × ℕ → B.V := fun z =>
    (B.graph.neighborFinset z.1).toList.getD z.2 z.1
  have hvalues : Measurable values := measurable_of_countable values
  have hx : Measurable (fun z : Site B × (ℝ × ℝ) => z.1.1) :=
    measurable_fst.comp measurable_fst
  have hs : Measurable (fun z : Site B × (ℝ × ℝ) => 2 * z.2.2 - 1) := by
    fun_prop
  have hbase : Measurable (fun z : Site B × (ℝ × ℝ) =>
      values (z.1.1, ⌊(B.deg : ℝ) * (2 * z.2.2 - 1)⌋₊)) :=
    hvalues.comp (hx.prodMk (by fun_prop))
  have hcond₁ : MeasurableSet {z : Site B × (ℝ × ℝ) | z.2.1 < 1 / 2} := by
    exact measurableSet_lt (by fun_prop) measurable_const
  have hcond₂ : MeasurableSet {z : Site B × (ℝ × ℝ) | z.2.2 < 1 / 2} := by
    exact measurableSet_lt (by fun_prop) measurable_const
  have hdown : Measurable (fun z : Site B × (ℝ × ℝ) => (z.1.1, z.1.2 - 1)) := by
    fun_prop
  have hup : Measurable (fun z : Site B × (ℝ × ℝ) => (z.1.1, z.1.2 + 1)) := by
    fun_prop
  have hhold : Measurable (fun z : Site B × (ℝ × ℝ) => z.1) := measurable_fst
  have hvertical : Measurable (fun z : Site B × (ℝ × ℝ) =>
      if z.2.2 < 1 / 2 then (z.1.1, z.1.2 - 1) else (z.1.1, z.1.2 + 1)) :=
    Measurable.ite hcond₂ hdown hup
  unfold cylStep baseNeighbor
  dsimp only [values] at hbase
  change Measurable (fun z : Site B × (ℝ × ℝ) =>
    if z.2.1 < 1 / 2 then
      if z.2.2 < 1 / 2 then (z.1.1, z.1.2 - 1) else (z.1.1, z.1.2 + 1)
    else if z.2.2 < 1 / 2 then z.1 else
      ((B.graph.neighborFinset z.1.1).toList.getD
        ⌊(B.deg : ℝ) * (2 * z.2.2 - 1)⌋₊ z.1.1, z.1.2))
  exact Measurable.ite hcond₁ hvertical
    (Measurable.ite hcond₂ hhold (hbase.prodMk (by fun_prop)))

/-- For each starting site `x`, the cylinder path `cylPath B x w` is a
measurable function of the driver `w`. -/
theorem measurable_cylPath (B : Base) (x : Site B) :
    Measurable (fun w : WalkDriver => cylPath B x w) := by
  refine measurable_pi_lambda _ fun k => ?_
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    change Measurable fun w : WalkDriver => cylStep B (cylPath B x w k) (w k)
    exact (measurable_cylStep_pair B).comp (ih.prodMk (measurable_pi_apply k))

/-- The restart identity: after the first driver entry `u` has been split off,
the path driven by `LatticeProb.consNat u w` from `p`, read at time `k + 1`,
equals the path driven by `w` from `cylStep B p u`, read at time `k`. -/
theorem cylPath_consNat (B : Base) (p : Site B) (u : ℝ × ℝ) (w : WalkDriver)
    (k : ℕ) :
    cylPath B p (LatticeProb.consNat u w) (k + 1) = cylPath B (cylStep B p u) w k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change cylStep B (cylPath B p (LatticeProb.consNat u w) (k + 1)) (w k)
      = cylStep B (cylPath B (cylStep B p u) w k) (w k)
    rw [ih]

end IdlaCyl.Silvestri
