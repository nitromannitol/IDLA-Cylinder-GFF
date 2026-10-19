import IdlaCylAudit.SolutionBasic
import IdlaCylAudit.Support.BridgeShape
import IdlaCyl.Frozen.MaxFluctV3

/-!
# The maximal fluctuation bound, Theorem 1.1

The maximal fluctuation bound of the paper, stated in the vocabulary of the comparator challenge.
The library theorem `IdlaCyl.Frozen.max_fluct_v3` is applied to the library base sequence
`Bridge.baseSeq V`, and the bridge equalities identify its statement with the vocabulary's.
-/

namespace IdlaCylAudit

open IdlaCylAudit.Defs MeasureTheory

/-- For every `ν > 0` and `m ≥ 1` there is `C > 0` such that, for every sequence of bases and all
large `N`, every time `1 ≤ T ≤ N^m` satisfies the shape event of width `Δ_N` except with
probability at most `N^{-ν}`. -/
theorem max_fluct (ν : ℝ) (hν : 0 < ν) (m : ℝ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : BaseSeq, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ T : ℕ,
      1 ≤ T → (T : ℝ) ≤ (N : ℝ) ^ m →
      idlaMeasure (V.B N) ((eventAt (V.B N) T (delta (V.B N) C T))ᶜ) ≤
        ENNReal.ofReal ((N : ℝ) ^ (-ν)) := by
  obtain ⟨C, hC, h⟩ := IdlaCyl.Frozen.max_fluct_v3 ν hν m hm
  refine ⟨C, hC, fun V => ?_⟩
  obtain ⟨N₀, hN₀⟩ := h (Bridge.baseSeq V)
  refine ⟨N₀, fun N hN T hT hTm => ?_⟩
  have key := hN₀ N hN T hT hTm
  rw [Bridge.idlaMeasure_eq, Bridge.eventAt_eq, Bridge.delta_eq]
  exact key

end IdlaCylAudit
