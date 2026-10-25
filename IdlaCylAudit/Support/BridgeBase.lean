module

public import IdlaCylAudit.SolutionBasic
public import IdlaCyl.Definitions.ShapeEvent

@[expose] public section

/-!
# The bridge for the base graph and the canonical IDLA law

`base B` is the library's base with the same fields as the vocabulary's base `B`; the sites,
the driving sequences and every law of the vocabulary are then definitionally the library's.
-/

namespace IdlaCylAudit.Bridge

/-- The library base with the fields of a vocabulary base. -/
def base (B : IdlaCylAudit.Base) : IdlaCyl.Base where
  V := B.V
  fintypeV := B.fintypeV
  decEqV := B.decEqV
  graph := B.graph
  decRel := B.decRel
  connected := B.connected
  vertexTransitive := B.vertexTransitive
  nontrivial := B.nontrivial

/-- The canonical IDLA driving law of the vocabulary is the library's. -/
theorem idlaMeasure_eq (B : IdlaCylAudit.Base) :
    IdlaCylAudit.idlaMeasure B = IdlaCyl.idlaMeasure (base B) := rfl

/-- The library base sequence with the bases of a vocabulary base sequence. -/
def baseSeq (V : IdlaCylAudit.BaseSeq) : IdlaCyl.BaseSeq where
  B N := base (V.B N)
  card_eq N hN := V.card_eq N hN

/-- The clusters grown from a seed are the library's. -/
theorem clusterFrom_eq (B : IdlaCylAudit.Base) (A0 : Set (IdlaCylAudit.Site B))
    (ω : IdlaCylAudit.TrajSeq B) (t : ℕ) :
    IdlaCylAudit.clusterFrom B A0 ω t = IdlaCyl.clusterFrom (base B) A0 ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [IdlaCylAudit.clusterFrom, IdlaCyl.clusterFrom, ih]
      rfl

/-- The clusters of the vocabulary are the library's. -/
theorem clusterTraj_eq (B : IdlaCylAudit.Base) (ω : IdlaCylAudit.TrajSeq B) (t : ℕ) :
    IdlaCylAudit.clusterTraj B ω t = IdlaCyl.clusterTraj (base B) ω t :=
  clusterFrom_eq B _ ω t

end IdlaCylAudit.Bridge
