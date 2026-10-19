import IdlaCylAudit.Support.BridgeBase
import IdlaCyl.Support.Cycle.Setup
import IdlaCyl.Support.Torus.Setup
import IdlaCyl.Support.Torus.Shells

/-!
# Bridges for the cycle and torus examples

The cycle bases, the indexed cycle base, the torus base, the torus sequence and the torus shells
of the vocabulary are the library's objects under `Bridge.base`. The cycle and torus bases are
built from the same fields in both namespaces, so their equalities hold by `rfl`. The indexed
cycle base is a case split on `3 ≤ N`, and each case is then definitional.
-/

namespace IdlaCylAudit.Bridge

/-- The vocabulary's cycle base `ℤ_N` for `N ≥ 3`, read as a library base, is the library's. -/
theorem cycleBase_eq (N : ℕ) (hN : 3 ≤ N) :
    base (IdlaCylAudit.cycleBase N hN) = IdlaCyl.cycleBase N hN :=
  rfl

/-- The vocabulary's two-vertex base, read as a library base, is the library's. -/
theorem pairBase_eq :
    base IdlaCylAudit.CycleSpectrum.pairBase = IdlaCyl.CycleSpectrum.pairBase :=
  rfl

/-- The vocabulary's indexed cycle base, read as a library base, is the library's indexed cycle
base. The equality is proved by cases on `3 ≤ N`. -/
theorem indexedBase_eq (N : ℕ) :
    base (IdlaCylAudit.CycleSpectrum.indexedBase N) = IdlaCyl.CycleSpectrum.indexedBase N := by
  by_cases hN : 3 ≤ N
  · simp only [IdlaCylAudit.CycleSpectrum.indexedBase, IdlaCyl.CycleSpectrum.indexedBase,
      dif_pos hN]
    exact cycleBase_eq N hN
  · simp only [IdlaCylAudit.CycleSpectrum.indexedBase, IdlaCyl.CycleSpectrum.indexedBase,
      dif_neg hN]
    exact pairBase_eq

/-- The vocabulary's torus base on `(ℤ/N)^d`, read as a library base, is the library's. -/
theorem torusBase_eq (d N : ℕ) (hd : 1 ≤ d) (hN : 3 ≤ N) :
    base (IdlaCylAudit.torusBase d N hd hN) = IdlaCyl.torusBase d N hd hN :=
  rfl

/-- The vocabulary's torus sequence, read as a library base, is the library's torus sequence. -/
theorem torusSeq_eq (d : ℕ) (hd : 1 ≤ d) (n : ℕ) :
    base (IdlaCylAudit.torusSeq d hd n) = IdlaCyl.torusSeq d hd n :=
  rfl

/-- The torus shells of the vocabulary are the library's torus shells. -/
theorem shell_eq (d : ℕ) (hd : 1 ≤ d) (k : ℕ) :
    IdlaCylAudit.TorusSpectrum.shell d hd k = IdlaCyl.TorusSpectrum.shell d hd k :=
  rfl

end IdlaCylAudit.Bridge
