module

public import IdlaCyl.Support.FirstExit

@[expose] public section

set_option autoImplicit false

/-!
# Equivariance under relabelling of sites

The deterministic input to the vertex-transitivity argument: transport the
seed, initial cluster, and every trajectory by the same bijection. Particle
order is preserved throughout. No invariance of a probability law is asserted.
-/

namespace IdlaCyl

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] in
@[simp] theorem mem_equiv_image (e : α ≃ β) (A : Finset α) (x : α) :
    e x ∈ A.image e ↔ x ∈ A := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    have hyx : y = x := e.injective he
    simpa only [hyx] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

namespace EscapingPath

variable {seed : Set α} {seed' : Set β}

/-- Relabel a trajectory and its permanent seed. -/
def transport (e : α ≃ β) (hseed : ∀ x, x ∈ seed ↔ e x ∈ seed')
    (w : EscapingPath seed) : EscapingPath seed' where
  position := fun n => e (w.position n)
  escapes := by
    intro B
    obtain ⟨n, hnseed, hnA⟩ := w.escapes (B.image e.symm)
    refine ⟨n, ?_, ?_⟩
    · intro h
      exact hnseed ((hseed _).mpr h)
    · intro h
      apply hnA
      exact Finset.mem_image.mpr ⟨e (w.position n), h, e.symm_apply_apply _⟩

omit [DecidableEq β] in
@[simp] theorem transport_position (e : α ≃ β)
    (hseed : ∀ x, x ∈ seed ↔ e x ∈ seed') (w : EscapingPath seed) (n : ℕ) :
    (transport e hseed w).position n = e (w.position n) := rfl

theorem transport_exit_condition (e : α ≃ β)
    (hseed : ∀ x, x ∈ seed ↔ e x ∈ seed') (w : EscapingPath seed)
    (A : Finset α) (n : ℕ) :
    ((transport e hseed w).position n ∉ seed' ∧
      (transport e hseed w).position n ∉ A.image e) ↔
      (w.position n ∉ seed ∧ w.position n ∉ A) := by
  simp only [transport_position, mem_equiv_image, ← hseed]

theorem transport_exitTime (e : α ≃ β)
    (hseed : ∀ x, x ∈ seed ↔ e x ∈ seed') (w : EscapingPath seed)
    (A : Finset α) :
    (transport e hseed w).exitTime (A.image e) = w.exitTime A := by
  apply Nat.le_antisymm
  · apply (transport e hseed w).exitTime_le (A.image e)
    exact (transport_exit_condition e hseed w A _).mpr (w.exit_spec A)
  · apply w.exitTime_le A
    exact (transport_exit_condition e hseed w A _).mp
      ((transport e hseed w).exit_spec (A.image e))

theorem transport_exitSite (e : α ≃ β)
    (hseed : ∀ x, x ∈ seed ↔ e x ∈ seed') (w : EscapingPath seed)
    (A : Finset α) :
    (transport e hseed w).exitSite (A.image e) = e (w.exitSite A) := by
  simp only [exitSite, transport_exitTime, transport_position]

theorem transport_settle (e : α ≃ β)
    (hseed : ∀ x, x ∈ seed ↔ e x ∈ seed') (w : EscapingPath seed)
    (A : Finset α) :
    settle (A.image e) (transport e hseed w) = (settle A w).image e := by
  simp only [settle, transport_exitSite, Finset.image_insert]

/-- Relabelling commutes with ordered aggregation, unlike particle permutation. -/
theorem transport_grow (e : α ≃ β)
    (hseed : ∀ x, x ∈ seed ↔ e x ∈ seed')
    (ws : List (EscapingPath seed)) (A : Finset α) :
    grow (A.image e) (ws.map (transport e hseed)) = (grow A ws).image e := by
  induction ws generalizing A with
  | nil => rfl
  | cons w ws ih =>
      simp only [List.map_cons, grow_cons, transport_settle]
      exact ih (settle A w)

end EscapingPath
end IdlaCyl
