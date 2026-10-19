import IdlaCyl.Support.Outer.GhostMarkov
import Mathlib

/-!
# Blocks: the walk up to its first arrival at a level

A block is the list of sites that a cylinder walk visits after its start, up to and including
its first arrival at height `ℓ` from below. The file defines blocks, the block of a path and
the block law of a walk, and proves that the walk from `p` is the mixture over blocks of the
walk restarted at the block end.

The results proved here are the following. The first block is measurable, and its law is a
probability measure. The walk law factorises through the first block: it is the mixture over
blocks of the walk restarted at the block end, spliced after the block (the strong Markov
property at the first exit from `below B ℓ`, from `GhostMarkov`). Almost every block of a walk
started below the level is valid, and the block law of a valid block is the path weight of its
path.
-/

namespace IdlaCyl.Silvestri

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

variable (B : Base)

/-- The sites strictly below height `ℓ`. -/
def below (ℓ : ℤ) : Set (Site B) := {q | q.2 < ℓ}

/-- A block: a finite list of sites, used as a type synonym so that it carries the discrete
σ-algebra `⊤` rather than the one of `List`. -/
def Block : Type := List (Site B)

/-- Blocks carry the discrete σ-algebra. -/
instance instMeasurableSpaceBlock : MeasurableSpace (Block B) := ⊤

/-- Every singleton of a block is measurable. -/
instance instMeasurableSingletonBlock : MeasurableSingletonClass (Block B) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- Blocks are countable, since sites are. -/
instance instCountableBlock : Countable (Block B) :=
  inferInstanceAs (Countable (List (Site B)))

/-- The empty block is a default block. -/
instance instInhabitedBlock : Inhabited (Block B) := ⟨([] : List (Site B))⟩

/-- The end of the block `c` started at `p`: the last entry of `p :: c`. -/
def blockEnd (p : Site B) (c : Block B) : Site B :=
  (p :: (c : List (Site B))).getLastD p

/-- The path of a block: the entries of `p :: c`, held at `blockEnd p c` after its length. -/
def blockPath (p : Site B) (c : Block B) : ℕ → Site B :=
  fun n => (p :: (c : List (Site B))).getD n (blockEnd B p c)

/-- Splice the block `c` started at `p` in front of the continuation `Y`. -/
def prepend (p : Site B) (c : Block B) (Y : ℕ → Site B) : ℕ → Site B :=
  ghostSplicePath B (blockPath B p c) Y (c : List (Site B)).length

/-- The block of a path `X`: the sites `X 1, …, X τ` where `τ` is the first exit time from
`below B ℓ`. The junk value `τ = ⊤` gives the empty block. -/
def firstBlock (ℓ : ℤ) (X : ℕ → Site B) : Block B :=
  (List.ofFn fun i : Fin (WithTop.untopA (exitTime' B (below B ℓ) X)) => X ((i : ℕ) + 1) :
    List (Site B))

/-- A valid block from `p` to level `ℓ`: nonempty, below `ℓ` before its end, ending at
height `ℓ`, and with every step of positive cylinder probability. -/
def ValidBlock (ℓ : ℤ) (p : Site B) (c : Block B) : Prop :=
  (c : List (Site B)) ≠ [] ∧ (∀ n < (c : List (Site B)).length, (blockPath B p c n).2 < ℓ) ∧
    (blockEnd B p c).2 = ℓ ∧
    ∀ n < (c : List (Site B)).length, 0 < cylKernel B (blockPath B p c n) (blockPath B p c (n + 1))

/-- The law of the first block of the cylinder walk started at `p`. -/
def blockLaw (ℓ : ℤ) (p : Site B) : Measure (Block B) :=
  (walkPathLaw B p).map (firstBlock B ℓ)

/-- The first block is a measurable function of the path. -/
theorem measurable_firstBlock (ℓ : ℤ) : Measurable (firstBlock B ℓ) := by
  have hF : Measurable (fun q : (ℕ → Site B) × ℕ =>
      (show Block B from List.ofFn fun i : Fin q.2 => q.1 ((i : ℕ) + 1))) := by
    apply measurable_from_prod_countable_left
    intro n
    exact (measurable_of_countable (fun w : Fin n → Site B => (show Block B from List.ofFn w))).comp
      (measurable_pi_lambda _ fun i => by dsimp only; exact measurable_pi_apply _)
  have hτ : Measurable (fun X : ℕ → Site B => WithTop.untopA (exitTime' B (below B ℓ) X)) :=
    measurable_ghostExitIndex B (below B ℓ)
  exact hF.comp (measurable_id.prodMk hτ)

/-- The block law is a probability measure. -/
instance isProbabilityMeasure_blockLaw (ℓ : ℤ) (p : Site B) :
    IsProbabilityMeasure (blockLaw B ℓ p) :=
  Measure.isProbabilityMeasure_map (measurable_firstBlock B ℓ).aemeasurable

/-- The first block of a path that exits at time `n` has `n` entries. -/
theorem length_firstBlock (ℓ : ℤ) (X : ℕ → Site B) (n : ℕ)
    (hn : WithTop.untopA (exitTime' B (below B ℓ) X) = n) :
    (firstBlock B ℓ X : List (Site B)).length = n := by
  unfold firstBlock
  rw [hn]
  simp

/-- The block `p :: c` of a path started at `p` and exiting at time `n` is `X 0, …, X n`. -/
theorem cons_firstBlock_eq (ℓ : ℤ) (p : Site B) (X : ℕ → Site B) (n : ℕ)
    (hX0 : X 0 = p) (hn : WithTop.untopA (exitTime' B (below B ℓ) X) = n) :
    (p :: (firstBlock B ℓ X : List (Site B))) = List.ofFn (fun i : Fin (n + 1) => X i) := by
  unfold firstBlock
  rw [hn, List.ofFn_succ]
  simp [hX0]

/-- Along a block of exit time `n`, the block path agrees with the walk up to time `n`. -/
theorem blockPath_firstBlock (ℓ : ℤ) (p : Site B) (X : ℕ → Site B) (n : ℕ)
    (hX0 : X 0 = p) (hn : WithTop.untopA (exitTime' B (below B ℓ) X) = n) (k : ℕ) (hk : k ≤ n) :
    blockPath B p (firstBlock B ℓ X) k = X k := by
  unfold blockPath
  rw [cons_firstBlock_eq B ℓ p X n hX0 hn, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [Nat.lt_succ_of_le hk]

/-- The end of a block of exit time `n` is the walk at time `n`. -/
theorem blockEnd_firstBlock (ℓ : ℤ) (p : Site B) (X : ℕ → Site B) (n : ℕ)
    (hX0 : X 0 = p) (hn : WithTop.untopA (exitTime' B (below B ℓ) X) = n) :
    blockEnd B p (firstBlock B ℓ X) = X n := by
  unfold blockEnd
  rw [cons_firstBlock_eq B ℓ p X n hX0 hn, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?,
    List.length_ofFn, List.getElem?_ofFn]
  simp

/-- The continuation spliced after a block is the splice of the walk at its exit time. -/
theorem prepend_firstBlock (ℓ : ℤ) (p : Site B) (X : ℕ → Site B) (n : ℕ)
    (hX0 : X 0 = p) (hn : WithTop.untopA (exitTime' B (below B ℓ) X) = n) :
    prepend B p (firstBlock B ℓ X) = fun Y => ghostSplicePath B X Y n := by
  have hlen := length_firstBlock B ℓ X n hn
  funext Y m
  unfold prepend ghostSplicePath
  rw [hlen]
  by_cases hm : m ≤ n
  · simp [hm, blockPath_firstBlock B ℓ p X n hX0 hn m hm]
  · simp [hm]

/-- Below the level `ℓ`, the set `below B ℓ` lies in the half-cylinder of height `ℓ - 1`. -/
theorem below_subset_R (ℓ : ℤ) : below B ℓ ⊆ R B ((ℓ : ℝ) - 1) := by
  intro q hq
  have h1 : q.2 + 1 ≤ ℓ := by
    have := hq
    simp only [below, Set.mem_setOf_eq] at this
    omega
  have h2 : ((q.2 + 1 : ℤ) : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h1
  rw [mem_R]
  push_cast at h2
  linarith

/-- The walk started at `p` exits `below B ℓ` in finite time, almost surely. -/
theorem exitTime_ae_ne_top (ℓ : ℤ) (p : Site B) :
    ∀ᵐ X ∂(walkPathLaw B p), exitTime' B (below B ℓ) X ≠ ⊤ := by
  filter_upwards [ae_exists_ver_eq External.lazyRwRecurrent_holds B p ℓ] with X hX
  obtain ⟨n, hn⟩ := hX
  exact exitTime'_ne_top_of_height B (below_subset_R B ℓ) hn.ge

/-- The block decomposition of the walk law: the walk from `p` is the mixture over its first
block of the walk from the block end, spliced after the block (the strong Markov property at
the first exit from `below B ℓ`). -/
theorem walkPathLaw_eq_bind_blockLaw (ℓ : ℤ) (p : Site B) :
    walkPathLaw B p = (blockLaw B ℓ p).bind
      (fun c => (walkPathLaw B (blockEnd B p c)).map (prepend B p c)) := by
  have hG : Measurable (fun c : Block B => (walkPathLaw B (blockEnd B p c)).map (prepend B p c)) :=
    measurable_from_top
  have hS := below_subset_R B ℓ
  have hkey : (walkPathLaw B p).bind (ghostExitRefreshKernel B (below B ℓ)) = walkPathLaw B p :=
    walkPathLaw_bind_ghostExitRefresh_of_subset B p (below B ℓ) ℓ hS
  have hfin := exitTime_ae_ne_top B ℓ p
  have hae : ∀ᵐ X ∂(walkPathLaw B p), ghostExitRefreshKernel B (below B ℓ) X =
      (walkPathLaw B (blockEnd B p (firstBlock B ℓ X))).map (prepend B p (firstBlock B ℓ X)) := by
    filter_upwards [walkPathLaw_ae_start B p, hfin] with X hX0 hfX
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfX
    have hτ : WithTop.untopA (exitTime' B (below B ℓ) X) = n := by
      rw [← hn]
      exact untopA_natCast n
    have hsite : exitSite' B (below B ℓ) X = X n := by
      show X (WithTop.untopA (exitTime' B (below B ℓ) X)) = X n
      rw [hτ]
    rw [ghostExitRefreshKernel_apply, hsite, hτ,
      blockEnd_firstBlock B ℓ p X n hX0 hτ, prepend_firstBlock B ℓ p X n hX0 hτ]
  calc walkPathLaw B p
      = (walkPathLaw B p).bind (ghostExitRefreshKernel B (below B ℓ)) := hkey.symm
    _ = (walkPathLaw B p).bind (fun X =>
          (walkPathLaw B (blockEnd B p (firstBlock B ℓ X))).map (prepend B p (firstBlock B ℓ X))) :=
        Measure.bind_congr_right hae
    _ = (blockLaw B ℓ p).bind
          (fun c => (walkPathLaw B (blockEnd B p c)).map (prepend B p c)) := by
        unfold blockLaw Measure.bind
        rw [Measure.map_map hG (measurable_firstBlock B ℓ)]
        rfl

/-- The block path at the length of the block is the block end. -/
theorem blockPath_length (p : Site B) (c : Block B) :
    blockPath B p c (c : List (Site B)).length = blockEnd B p c := by
  unfold blockPath blockEnd
  simp [List.getD_eq_getElem?_getD, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]

/-- The block path at the initial position is the start. -/
theorem blockPath_zero (p : Site B) (c : Block B) : blockPath B p c 0 = p := by
  unfold blockPath
  simp

/-- The block path steps along the entries of the block. -/
theorem blockPath_succ (p : Site B) (c : Block B) (i : ℕ) (hi : i < (c : List (Site B)).length) :
    blockPath B p c (i + 1) = (show List (Site B) from c)[i]'hi := by
  unfold blockPath
  simp [List.getD_eq_getElem?_getD, hi]

/-- Almost every first block of a walk started below the level is valid. -/
theorem blockLaw_ae_valid (ℓ : ℤ) (p : Site B) (hp : p.2 < ℓ) :
    ∀ᵐ c ∂(blockLaw B ℓ p), ValidBlock B ℓ p c := by
  unfold blockLaw
  rw [ae_map_iff (measurable_firstBlock B ℓ).aemeasurable
    (Set.to_countable {c : Block B | ValidBlock B ℓ p c}).measurableSet]
  filter_upwards [walkPathLaw_ae_start B p, exitTime_ae_ne_top B ℓ p, walkPathLaw_ae_steps B p,
    walkPathLaw_ae_admissible B p] with X hX0 hfin hsteps hadm
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  have hτ : WithTop.untopA (exitTime' B (below B ℓ) X) = n := by
    rw [← hn]
    exact untopA_natCast n
  obtain ⟨hXn, hbel⟩ := (exitTime'_eq_coe_iff B (below B ℓ) X n).mp hn.symm
  have hn1 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exact (hXn (by rw [hX0]; exact hp)).elim
    · exact h
  have hlen := length_firstBlock B ℓ X n hτ
  unfold ValidBlock
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    rw [h] at hlen
    simp at hlen
    omega
  · intro m hm
    rw [hlen] at hm
    rw [blockPath_firstBlock B ℓ p X n hX0 hτ m hm.le]
    exact hbel m hm
  · rw [blockEnd_firstBlock B ℓ p X n hX0 hτ]
    have h5 : ¬ (X n).2 < ℓ := hXn
    have h1 := hsteps (n - 1)
    rw [show n - 1 + 1 = n by omega] at h1
    have h4 : (X (n - 1)).2 < ℓ := hbel (n - 1) (by omega)
    omega
  · intro m hm
    rw [hlen] at hm
    rw [blockPath_firstBlock B ℓ p X n hX0 hτ m hm.le,
      blockPath_firstBlock B ℓ p X n hX0 hτ (m + 1) hm]
    exact hadm m

/-- The block law of a valid block is the path weight of its path. -/
theorem blockLaw_singleton (ℓ : ℤ) (p : Site B) (c : Block B) (hc : ValidBlock B ℓ p c) :
    blockLaw B ℓ p {c} = IdlaCyl.pathWeight B (c : List (Site B)).length (blockPath B p c) := by
  unfold blockLaw
  rw [Measure.map_apply (measurable_firstBlock B ℓ) (measurableSet_singleton c)]
  have hae : firstBlock B ℓ ⁻¹' {c} =ᵐ[walkPathLaw B p]
      pathCyl B (c : List (Site B)).length (blockPath B p c) := by
    rw [Filter.eventuallyEq_set]
    filter_upwards [walkPathLaw_ae_start B p, exitTime_ae_ne_top B ℓ p] with X hX0 hfin
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
    have hτ : WithTop.untopA (exitTime' B (below B ℓ) X) = m := by
      rw [← hm]
      exact untopA_natCast m
    have hlen := length_firstBlock B ℓ X m hτ
    show firstBlock B ℓ X = c ↔ ∀ i ≤ (c : List (Site B)).length, X i = blockPath B p c i
    constructor
    · intro h i hi
      have hmi : i ≤ m := by
        have := hlen
        rw [h] at this
        omega
      rw [← h]
      exact (blockPath_firstBlock B ℓ p X m hX0 hτ i hmi).symm
    · intro h
      have hXc : ∀ i ≤ (c : List (Site B)).length, X i = blockPath B p c i := h
      have hexit : exitTime' B (below B ℓ) X = ((c : List (Site B)).length : ℕ∞) := by
        rw [exitTime'_eq_coe_iff]
        refine ⟨fun hmem => ?_, fun j hj => ?_⟩
        · have h1 : (X (c : List (Site B)).length).2 < ℓ := hmem
          rw [hXc _ le_rfl, blockPath_length, hc.2.2.1] at h1
          exact lt_irrefl ℓ h1
        · show (X j).2 < ℓ
          rw [hXc j hj.le]
          exact hc.2.1 j hj
      have hml : m = (c : List (Site B)).length := by
        have h2 := hm
        rw [hexit] at h2
        exact_mod_cast h2
      have hfb : firstBlock B ℓ X = c := by
        unfold firstBlock
        rw [hexit, untopA_natCast]
        apply List.ext_getElem
        · simp
        · intro i h1 h2
          simp only [List.getElem_ofFn]
          rw [hXc (i + 1) (by omega)]
          exact blockPath_succ B p c i h2
      exact hfb
  rw [measure_congr hae, walkPathLaw_pathCyl B p, if_pos (blockPath_zero B p c), one_mul]

end

end IdlaCyl.Silvestri
