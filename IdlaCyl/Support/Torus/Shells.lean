/-
The continuum torus shells, with lattice multiplicity. Source: tex:502-507,
`paper/idla-cylinder-gff.tex`. Every count below is the card of an explicit
finite set; the minimum defining `shell` has a proved witness.
-/
import Mathlib

namespace IdlaCyl.TorusSpectrum
open scoped BigOperators

/-- Squared Euclidean norm on the integer frequency lattice. -/
def normSq (d : ℕ) (m : Fin d → ℤ) : ℕ := ∑ i, (m i).natAbs ^ 2

lemma coord_natAbs_le (d R : ℕ) (m : Fin d → ℤ) (hm : normSq d m ≤ R) (i : Fin d) :
    (m i).natAbs ≤ R := by
  have hi : (m i).natAbs ^ 2 ≤ normSq d m := by
    unfold normSq
    exact Finset.single_le_sum (fun j _ => Nat.zero_le ((m j).natAbs ^ 2)) (Finset.mem_univ i)
  have hsq : (m i).natAbs ≤ (m i).natAbs ^ 2 := Nat.le_self_pow (by omega) _
  exact hsq.trans (hi.trans hm)

/-- The complete finite sublevel set of the lattice norm; the box is only an implementation. -/
noncomputable def latticeBall (d R : ℕ) : Finset (Fin d → ℤ) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(R : ℤ)) R)).filter (fun m => normSq d m ≤ R)

lemma mem_latticeBall (d R : ℕ) (m : Fin d → ℤ) :
    m ∈ latticeBall d R ↔ normSq d m ≤ R := by
  rw [latticeBall, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hm
    refine ⟨Fintype.mem_piFinset.mpr (fun i => ?_), hm⟩
    apply Finset.mem_Icc.mpr
    apply abs_le.mp
    rw [← Int.natCast_natAbs]
    exact_mod_cast coord_natAbs_le d R m hm i

lemma latticeBall_mono (d : ℕ) : Monotone (latticeBall d) := by
  intro R S h m hm
  exact (mem_latticeBall d S m).mpr (((mem_latticeBall d R m).mp hm).trans h)

lemma normSq_single (d : ℕ) (i : Fin d) (a : ℤ) :
    normSq d (Pi.single i a) = a.natAbs ^ 2 := by
  simp only [normSq, Pi.single_apply, apply_ite (fun z : ℤ => z.natAbs ^ 2),
    Int.natAbs_zero, zero_pow (by omega : 2 ≠ 0), Finset.sum_ite_eq', Finset.mem_univ, ite_true]

lemma latticeBall_card_unbounded (d : ℕ) (hd : 1 ≤ d) (k : ℕ) :
    ∃ R, k ≤ (latticeBall d R).card := by
  let i : Fin d := ⟨0, hd⟩
  refine ⟨k ^ 2, ?_⟩
  have hinj : Function.Injective (fun j : ℕ => (Pi.single i (j : ℤ) : Fin d → ℤ)) := by
    intro a b h
    have h' := congrFun h i
    simpa only [Pi.single_eq_same, Int.natCast_inj] using h'
  have hs : (Finset.range k).image (fun j : ℕ => (Pi.single i (j : ℤ) : Fin d → ℤ)) ⊆
      latticeBall d (k ^ 2) := by
    intro m hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
    rw [mem_latticeBall, normSq_single, Int.natAbs_natCast]
    exact Nat.pow_le_pow_left (Finset.mem_range.mp hj).le 2
  have hc := Finset.card_le_card hs
  rwa [Finset.card_image_of_injective _ hinj, Finset.card_range] at hc

/-- The one-based ordered squared norms, with full lattice multiplicity.
The value at index zero is also defined by the same certified minimum. -/
noncomputable def shell (d : ℕ) (hd : 1 ≤ d) (k : ℕ) : ℕ :=
  Nat.find (latticeBall_card_unbounded d hd k)

lemma shell_spec (d : ℕ) (hd : 1 ≤ d) (k : ℕ) :
    k ≤ (latticeBall d (shell d hd k)).card := Nat.find_spec (latticeBall_card_unbounded d hd k)

lemma shell_min (d : ℕ) (hd : 1 ≤ d) (k R : ℕ) (hR : R < shell d hd k) :
    (latticeBall d R).card < k := by
  exact Nat.lt_of_not_ge (Nat.find_min (latticeBall_card_unbounded d hd k) hR)

lemma shell_le_iff (d : ℕ) (hd : 1 ≤ d) (k R : ℕ) :
    shell d hd k ≤ R ↔ k ≤ (latticeBall d R).card := by
  constructor
  · intro h
    exact (shell_spec d hd k).trans (Finset.card_le_card (latticeBall_mono d h))
  · exact Nat.find_min' (latticeBall_card_unbounded d hd k)

lemma shell_mono (d : ℕ) (hd : 1 ≤ d) : Monotone (shell d hd) := by
  intro j k hjk
  exact (shell_le_iff d hd j _).mpr (hjk.trans (shell_spec d hd k))

lemma normSq_eq_zero_iff (d : ℕ) (m : Fin d → ℤ) : normSq d m = 0 ↔ m = 0 := by
  simp only [normSq, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies,
    pow_eq_zero_iff (by omega : 2 ≠ 0), Int.natAbs_eq_zero, funext_iff, Pi.zero_apply]

lemma latticeBall_zero (d : ℕ) : latticeBall d 0 = {0} := by
  ext m
  simp only [mem_latticeBall, Nat.le_zero, normSq_eq_zero_iff, Finset.mem_singleton]

lemma shell_one (d : ℕ) (hd : 1 ≤ d) : shell d hd 1 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply (shell_le_iff d hd 1 0).mpr
  rw [latticeBall_zero, Finset.card_singleton]

lemma shell_pos (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : 2 ≤ k) :
    0 < shell d hd k := by
  have h := shell_spec d hd k
  by_contra hzero
  have hz : shell d hd k = 0 := by omega
  rw [hz, latticeBall_zero, Finset.card_singleton] at h
  omega

/-- Every selected radius is an actual squared lattice norm. -/
lemma shell_attained (d : ℕ) (hd : 1 ≤ d) (k : ℕ) :
    ∃ m : Fin d → ℤ, normSq d m = shell d hd k := by
  by_cases hr : shell d hd k = 0
  · refine ⟨0, ?_⟩
    rw [hr]
    exact (normSq_eq_zero_iff d 0).mpr rfl
  · by_contra h
    push Not at h
    have hs : latticeBall d (shell d hd k) ⊆ latticeBall d (shell d hd k - 1) := by
      intro m hm
      rw [mem_latticeBall] at hm ⊢
      have hne := h m
      omega
    have hc := Finset.card_le_card hs
    have hspec := shell_spec d hd k
    have hmin := shell_min d hd k (shell d hd k - 1) (by omega)
    omega

/-- The signed coordinate unit vectors in the integer lattice. -/
def unitFrequency (d : ℕ) (p : Fin d × Bool) : Fin d → ℤ :=
  Pi.single p.1 (cond p.2 1 (-1))

lemma unitFrequency_injective (d : ℕ) : Function.Injective (unitFrequency d) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have hi := congrFun h i
  dsimp only [unitFrequency] at hi
  by_cases hij : i = j
  · subst j
    rw [Pi.single_eq_same, Pi.single_eq_same] at hi
    cases b <;> cases c <;> simp_all
  · rw [Pi.single_eq_same, Pi.single_eq_of_ne hij] at hi
    cases b <;> norm_num at hi

lemma normSq_unitFrequency (d : ℕ) (p : Fin d × Bool) :
    normSq d (unitFrequency d p) = 1 := by
  rw [unitFrequency, normSq_single]
  cases p.2 <;> norm_num

lemma latticeBall_one_card_lower (d : ℕ) : 2 * d + 1 ≤ (latticeBall d 1).card := by
  classical
  let units := Finset.univ.image (unitFrequency d)
  have hz : (0 : Fin d → ℤ) ∉ units := by
    rintro h
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp h
    have hnorm := normSq_unitFrequency d p
    rw [hp] at hnorm
    simp [normSq] at hnorm
  have hs : insert 0 units ⊆ latticeBall d 1 := by
    intro m hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · rw [mem_latticeBall]
      simp [normSq]
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hm
      rw [mem_latticeBall, normSq_unitFrequency]
  have hc := Finset.card_le_card hs
  rw [Finset.card_insert_of_notMem hz, Finset.card_image_of_injective _ (unitFrequency_injective d),
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hc
  omega

/-- The first nonconstant shell has exactly the required initial slots. -/
lemma shell_eq_one (d : ℕ) (hd : 1 ≤ d) (k : ℕ) (hk : 2 ≤ k) (hkd : k ≤ 2 * d + 1) :
    shell d hd k = 1 := by
  have hlo := shell_pos d hd k hk
  have hhi := (shell_le_iff d hd k 1).mpr (hkd.trans (latticeBall_one_card_lower d))
  omega

end IdlaCyl.TorusSpectrum
