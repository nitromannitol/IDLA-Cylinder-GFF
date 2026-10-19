import IdlaCylAudit.Support.BridgeBase
import IdlaCyl.Support.Spectral
import IdlaCyl.Support.Discrepancy
import IdlaCyl.Definitions.TestFunction
import IdlaCyl.Definitions.RectangularMass

/-!
# The bridge for the spectral vocabulary

The diagonalisation of the base kernel, the normalised sequence of bases with its setup, the
discrepancy and the pairing of a trajectory, the test function, the limiting variance, the
coefficient regularity, and the assumptions on the setup are transported from the vocabulary to
the library.  The non-recursive definitions agree with their library counterparts by `rfl`.  The
discrepancy and the pairing depend on the cluster of a trajectory, which is transported by
`clusterTraj_eq` from `IdlaCylAudit.Support.BridgeBase`.
-/

namespace IdlaCylAudit.Bridge

/-- The library's diagonalisation on `base B`, with the fields of a vocabulary diagonalisation. -/
def spectralData {B : IdlaCylAudit.Base} (S : IdlaCylAudit.SpectralData B) :
    IdlaCyl.SpectralData (base B) where
  lam := S.lam
  f := S.f
  eigen := S.eigen
  orthonormal := S.orthonormal
  lam_one := S.lam_one
  f_one := S.f_one
  antitone := S.antitone
  lam_two_lt := S.lam_two_lt
  lam_nonneg := S.lam_nonneg

/-- The library setup with the bases, the diagonalisations, and the normalising sequence of a
vocabulary setup. -/
def setup (U : IdlaCylAudit.Setup) : IdlaCyl.Setup where
  toBaseSeq := baseSeq U.toBaseSeq
  S N := spectralData (U.S N)
  a := U.a
  a_pos := U.a_pos
  a_tendsto := U.a_tendsto

/-- The base of the library setup at `N` is the library base of the vocabulary base at `N`. -/
theorem setup_B (U : IdlaCylAudit.Setup) (N : ℕ) :
    (setup U).B N = base (U.B N) :=
  rfl

/-- The normalising sequence of the library setup is the vocabulary's. -/
theorem setup_a (U : IdlaCylAudit.Setup) :
    (setup U).a = U.a :=
  rfl

/-- The discrepancy function of the vocabulary is the library's. -/
theorem discrepancyTraj_eq (B : IdlaCylAudit.Base) (ω : IdlaCylAudit.TrajSeq B) (t : ℕ)
    (p : IdlaCylAudit.Site B) :
    IdlaCylAudit.discrepancyTraj B ω t p = IdlaCyl.discrepancyTraj (base B) ω t p := by
  unfold IdlaCylAudit.discrepancyTraj IdlaCyl.discrepancyTraj
  rw [clusterTraj_eq]
  rfl

/-- The pairing of a trajectory with a test function is the library's. -/
theorem pairingTraj_eq (B : IdlaCylAudit.Base) (ω : IdlaCylAudit.TrajSeq B) (t : ℕ)
    (f : IdlaCylAudit.Site B → ℝ) :
    IdlaCylAudit.pairingTraj B ω t f = IdlaCyl.pairingTraj (base B) ω t f := by
  unfold IdlaCylAudit.pairingTraj IdlaCyl.pairingTraj
  exact finsum_congr fun p => by rw [discrepancyTraj_eq]

/-- The test function of the vocabulary is the library's, on the transported diagonalisation. -/
theorem testAt_eq (B : IdlaCylAudit.Base) (S : IdlaCylAudit.SpectralData B) (a : ℝ) (K : ℕ)
    (α : ℕ → ℝ → ℝ) (p : IdlaCylAudit.Site B) :
    IdlaCylAudit.Defs.testAt B S a K α p =
      IdlaCyl.Defs.testAt (base B) (spectralData S) a K α p :=
  rfl

/-- The limiting variance of the vocabulary is the library's; it involves no base. -/
theorem variance_eq (K : ℕ) (α : ℕ → ℝ → ℝ) (γ : ℕ → ℝ) (y₀ : ℝ) :
    IdlaCylAudit.Defs.variance K α γ y₀ = IdlaCyl.Defs.variance K α γ y₀ :=
  rfl

/-- The coefficient regularity of the vocabulary is the library's; it involves no base. -/
theorem regular_iff (α : ℕ → ℝ → ℝ) (K : ℕ) (y₀ : ℝ) :
    IdlaCylAudit.Defs.regular α K y₀ ↔ IdlaCyl.Defs.regular α K y₀ :=
  Iff.rfl

/-- The limit of `a_N √(2(1 - λ_k(N)))` is the same for a vocabulary setup and its library
setup. -/
theorem gammaLimit_iff (U : IdlaCylAudit.Setup) (γ : ℕ → ℝ) (k : ℕ) :
    U.GammaLimit γ k ↔ (setup U).GammaLimit γ k :=
  Iff.rfl

/-- The standing spectral assumption is the same for a vocabulary setup and its library setup. -/
theorem spectralAssumption_iff (U : IdlaCylAudit.Setup) (γ : ℕ → ℝ) (K : ℕ) :
    U.SpectralAssumption γ K ↔ (setup U).SpectralAssumption γ K :=
  Iff.rfl

/-- The growth condition `(log N + log₊ a_N) / a_N → 0` is the same for a vocabulary setup and
its library setup. -/
theorem growthCondition_iff (U : IdlaCylAudit.Setup) :
    U.GrowthCondition ↔ (setup U).GrowthCondition :=
  Iff.rfl

end IdlaCylAudit.Bridge
