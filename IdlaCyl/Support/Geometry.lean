import IdlaCyl.Support.FirstExit

set_option autoImplicit false

/-!
# Cylinder geometry and a deterministic height bound

The permanent seed is the full lower half-cylinder, not a finite truncation.
The integer-height rectangle stores its finite positive part only.
-/

namespace IdlaCyl

abbrev Cylinder (V : Type*) := V × ℤ

variable {V : Type*} [DecidableEq V]

def flatSeed (V : Type*) : Set (Cylinder V) := {z | z.2 ≤ 0}

def halfCylinder (h : ℤ) : Set (Cylinder V) := {z | z.2 ≤ h}

omit [DecidableEq V] in
@[simp] theorem mem_flatSeed (z : Cylinder V) :
    z ∈ flatSeed V ↔ z.2 ≤ 0 := Iff.rfl

omit [DecidableEq V] in
@[simp] theorem mem_halfCylinder (h : ℤ) (z : Cylinder V) :
    z ∈ halfCylinder h ↔ z.2 ≤ h := Iff.rfl

/-- Finite positive part of the integer rectangle. -/
noncomputable def rectangle [Fintype V] (h : ℕ) : Finset (Cylinder V) :=
  Finset.univ.product (Finset.Icc (1 : ℤ) (h : ℤ))

omit [DecidableEq V] in
@[simp] theorem mem_rectangle [Fintype V] (h : ℕ) (z : Cylinder V) :
    z ∈ rectangle (V := V) h ↔ 1 ≤ z.2 ∧ z.2 ≤ (h : ℤ) := by
  simp [rectangle]

omit [DecidableEq V] in
theorem rectangle_outside_seed [Fintype V] (h : ℕ) :
    ∀ z ∈ rectangle (V := V) h, z ∉ flatSeed V := by
  intro z hz
  have hz' := (mem_rectangle h z).mp hz
  simp only [mem_flatSeed]
  omega

omit [DecidableEq V] in
theorem rectangle_mono [Fintype V] {h k : ℕ} (hk : h ≤ k) :
    rectangle (V := V) h ⊆ rectangle k := by
  intro z hz
  obtain ⟨hz1, hz2⟩ := (mem_rectangle h z).mp hz
  apply (mem_rectangle k z).mpr
  constructor
  · exact hz1
  · have hh : (h : ℤ) ≤ k := by exact_mod_cast hk
    omega

/-- Membership in the represented infinite cluster. -/
def occupied (A : Finset (Cylinder V)) : Set (Cylinder V) :=
  flatSeed V ∪ (A : Set (Cylinder V))

omit [DecidableEq V] in
@[simp] theorem mem_occupied (A : Finset (Cylinder V)) (z : Cylinder V) :
    z ∈ occupied A ↔ z.2 ≤ 0 ∨ z ∈ A := Iff.rfl

/-- Every finite extension has a height upper bound. -/
theorem finite_height_bound (A : Finset (Cylinder V)) :
    ∃ h : ℤ, 0 ≤ h ∧ ∀ z ∈ A, z.2 ≤ h := by
  induction A using Finset.induction_on with
  | empty => exact ⟨0, le_refl 0, by simp⟩
  | @insert z A hz ih =>
      obtain ⟨h, hh, hA⟩ := ih
      refine ⟨max z.2 h, hh.trans (le_max_right _ _), ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with hx | hx
      · subst x
        exact le_max_left _ _
      · exact (hA x hx).trans (le_max_right _ _)

/-- A path with unbounded upward visits exits every finite extension of R₀. -/
def escapingOfCofinal (w : ℕ → Cylinder V)
    (hw : ∀ h : ℤ, ∃ n, h < (w n).2) : EscapingPath (flatSeed V) where
  position := w
  escapes := by
    intro A
    obtain ⟨h, hh, hA⟩ := finite_height_bound A
    obtain ⟨n, hn⟩ := hw h
    refine ⟨n, ?_, ?_⟩
    · change ¬ (w n).2 ≤ 0
      omega
    · intro hmem
      have hle := hA (w n) hmem
      omega

/-- Support of the paper's cylinder walk: vertical neighbors or a lazy horizontal step. -/
def CylinderStep (G : SimpleGraph V) (u v : Cylinder V) : Prop :=
  (u.1 = v.1 ∧ (v.2 = u.2 + 1 ∨ v.2 = u.2 - 1)) ∨
    (u.2 = v.2 ∧ (u.1 = v.1 ∨ G.Adj u.1 v.1))

def CylinderAdmissible (G : SimpleGraph V)
    (w : EscapingPath (flatSeed V)) : Prop :=
  (w.position 0).2 = 0 ∧ ∀ n, CylinderStep G (w.position n) (w.position (n + 1))

/-- The vertical conditions used for the deterministic height bound. -/
def VerticallyAdmissible (w : EscapingPath (flatSeed V)) : Prop :=
  (w.position 0).2 = 0 ∧ ∀ n : ℕ, (w.position (n + 1)).2 ≤ (w.position n).2 + 1

omit [DecidableEq V] in
theorem CylinderAdmissible.verticallyAdmissible (G : SimpleGraph V)
    (w : EscapingPath (flatSeed V)) (hw : CylinderAdmissible G w) :
    VerticallyAdmissible w := by
  refine ⟨hw.1, ?_⟩
  intro n
  rcases hw.2 n with ⟨_, h | h⟩ | ⟨h, _⟩ <;> omega

namespace EscapingPath

theorem exit_height_pos (w : EscapingPath (flatSeed V))
    (A : Finset (Cylinder V)) : 0 < (w.exitSite A).2 := by
  have h := w.exit_not_seed A
  change ¬ (w.exitSite A).2 ≤ 0 at h
  omega

/-- A new occupied site is at most one level above the previous upper bound. -/
theorem exit_height_le (w : EscapingPath (flatSeed V))
    (hw : VerticallyAdmissible w) (A : Finset (Cylinder V))
    (h : ℤ) (hh : 0 ≤ h) (hA : ∀ z ∈ A, z.2 ≤ h) :
    (w.exitSite A).2 ≤ h + 1 := by
  obtain ⟨hstart, hstep⟩ := hw
  cases ht : w.exitTime A with
  | zero =>
      have he : (w.exitSite A).2 = 0 := by
        simpa only [exitSite, ht] using hstart
      omega
  | succ n =>
      have hn : n < w.exitTime A := by omega
      have hp : (w.position n).2 ≤ h := by
        rcases w.occupied_before_exit A hn with hs | ha
        · change (w.position n).2 ≤ 0 at hs
          omega
        · exact hA _ ha
      have hnext := hstep n
      change (w.position (w.exitTime A)).2 ≤ h + 1
      rw [ht]
      omega

theorem settle_height_le (w : EscapingPath (flatSeed V))
    (hw : VerticallyAdmissible w) (A : Finset (Cylinder V))
    (h : ℤ) (hh : 0 ≤ h) (hA : ∀ z ∈ A, z.2 ≤ h) :
    ∀ z ∈ settle A w, z.2 ≤ h + 1 := by
  intro z hz
  rcases Finset.mem_insert.mp hz with hz | hz
  · subst z
    exact exit_height_le w hw A h hh hA
  · have hz' := hA z hz
    omega

/-- At most one new height level per particle, for any ordered admissible list. -/
theorem grow_height_le (A : Finset (Cylinder V))
    (ws : List (EscapingPath (flatSeed V)))
    (hw : ∀ w ∈ ws, VerticallyAdmissible w)
    (h : ℤ) (hh : 0 ≤ h) (hA : ∀ z ∈ A, z.2 ≤ h) :
    ∀ z ∈ grow A ws, z.2 ≤ h + (ws.length : ℤ) := by
  revert hA
  revert hh
  revert h
  revert hw
  revert A
  induction ws with
  | nil =>
      intro A hw h hh hA
      simpa using hA
  | cons w ws ih =>
      intro A hw h hh hA
      have hwa : VerticallyAdmissible w := hw w (by simp)
      have hws : ∀ v ∈ ws, VerticallyAdmissible v := by
        intro v hv
        exact hw v (by simp [hv])
      have hs := settle_height_le w hwa A h hh hA
      have hg := ih (settle A w) hws (h + 1) (by omega) hs
      intro z hz
      have hz' := hg z hz
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      omega

theorem empty_grow_height_le
    (ws : List (EscapingPath (flatSeed V)))
    (hw : ∀ w ∈ ws, VerticallyAdmissible w) :
    ∀ z ∈ grow ∅ ws, z.2 ≤ (ws.length : ℤ) := by
  simpa using grow_height_le ∅ ws hw 0 (le_refl 0) (by simp)

theorem empty_grow_positive
    (ws : List (EscapingPath (flatSeed V))) :
    ∀ z ∈ grow ∅ ws, 0 < z.2 := by
  intro z hz
  have h := grow_outside_seed ∅ ws (by simp) z hz
  change ¬ z.2 ≤ 0 at h
  omega

end EscapingPath
end IdlaCyl
