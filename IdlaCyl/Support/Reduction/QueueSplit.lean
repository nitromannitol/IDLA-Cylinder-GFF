module

/-
Deep/shallow partition of the actual mobile queue, with multiplicities.
Source: paper/idla-cylinder-gff.tex, tex:1385-1396,1440-1453.
-/
public import IdlaCyl.Support.Reduction.PausedLedger

@[expose] public section

attribute [local instance] Classical.propDecidable

namespace IdlaCyl.Reduction

open scoped BigOperators

/-- Counting a finite interval of layers counts every mobile copy once. -/
theorem queue_interval_count (B : Base) (L : List (Site B)) (a b : ℤ) :
    (L.filter (fun z => a ≤ z.2 ∧ z.2 ≤ b)).length =
      ∑ k ∈ Finset.Icc a b, mobileOnLayer B L k := by
  induction L with
  | nil => simp [mobileOnLayer]
  | cons z L ih =>
    have hstep (k : ℤ) : mobileOnLayer B (z :: L) k =
        (if z.2 = k then 1 else 0) + mobileOnLayer B L k := by
      by_cases h : z.2 = k
      · simp [mobileOnLayer, h, Nat.add_comm]
      · simp [mobileOnLayer, h]
    simp_rw [hstep]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_Icc]
    by_cases hz : a ≤ z.2 ∧ z.2 ≤ b
    · rw [List.filter_cons_of_pos (p := fun w : Site B => decide (a ≤ w.2 ∧ w.2 ≤ b)) (decide_eq_true hz), List.length_cons, ih, if_pos hz]
      omega
    · rw [List.filter_cons_of_neg (p := fun w : Site B => decide (a ≤ w.2 ∧ w.2 ≤ b))
          (by simpa only [decide_eq_true_eq] using hz),
        ih, if_neg hz, Nat.zero_add]

/-- The successful queue splits into exact deep and shallow counts. -/
theorem goodPaused_split_counts (B : Base) (M β ℓ ρ : ℕ) (hβ : β ≤ ℓ)
    (s : ResumeState B × ℕ) (hs : s ∈ goodPaused B M ℓ ρ) :
    (s.1.2.filter (fun z => z.2 ≤ ((ℓ - β : ℕ) : ℤ))).length =
        (M - B.card) * (ℓ - β) ∧
    (s.1.2.filter (fun z => ((ℓ - β : ℕ) : ℤ) < z.2)).length =
        (M - B.card) * β ∧
    s.1.2.Perm ((s.1.2.filter (fun z => z.2 ≤ ((ℓ - β : ℕ) : ℤ))) ++
      (s.1.2.filter (fun z => ((ℓ - β : ℕ) : ℤ) < z.2))) := by
  have hfilter (a b : ℤ) (h : ∀ z ∈ s.1.2,
      (a ≤ z.2 ∧ z.2 ≤ b) ↔ z.2 ≤ b) :
      s.1.2.filter (fun z => z.2 ≤ b) =
        s.1.2.filter (fun z => a ≤ z.2 ∧ z.2 ≤ b) := by
    apply List.filter_congr
    intro z hz
    simp only [decide_eq_decide]
    exact (h z hz).symm
  have hd := queue_interval_count B s.1.2 1 (ℓ - β : ℕ)
  have hall := queue_interval_count B s.1.2 1 ℓ
  have hcnt (K : ℕ) (hK : K ≤ ℓ) :
      ∑ k ∈ Finset.Icc (1 : ℤ) (K : ℤ), mobileOnLayer B s.1.2 k =
        (M - B.card) * K := by
    have hpoint (k : ℤ) (hk : k ∈ Finset.Icc (1 : ℤ) (K : ℤ)) :
        mobileOnLayer B s.1.2 k = M - B.card := by
      rw [hs.2.2, if_pos]
      have hh := Finset.mem_Icc.mp hk
      exact ⟨hh.1, hh.2.trans (by exact_mod_cast hK)⟩
    rw [Finset.sum_congr rfl hpoint, Finset.sum_const, nsmul_eq_mul]
    simp [Int.card_Icc, Nat.mul_comm]
  rw [hcnt (ℓ - β) (Nat.sub_le _ _)] at hd
  rw [hcnt ℓ le_rfl] at hall
  have hdeep := hfilter 1 (ℓ - β : ℕ) (fun z hz => by
    have hh := goodPaused_queue_heights B M ℓ ρ s hs z hz
    exact and_iff_right hh.1)
  have htotal : s.1.2.filter (fun z => (1 : ℤ) ≤ z.2 ∧ z.2 ≤ (ℓ : ℤ)) = s.1.2 := by
    apply List.filter_eq_self.mpr
    intro z hz
    exact decide_eq_true (goodPaused_queue_heights B M ℓ ρ s hs z hz)
  rw [← hdeep] at hd
  rw [htotal] at hall
  have hp := (List.filter_append_perm
    (fun z : Site B => decide (z.2 ≤ ((ℓ - β : ℕ) : ℤ))) s.1.2).symm
  have hcompl : (fun z : Site B => !decide (z.2 ≤ ((ℓ - β : ℕ) : ℤ))) =
      (fun z => decide (((ℓ - β : ℕ) : ℤ) < z.2)) := by
    funext z
    simp only [← decide_not, not_le]
  rw [hcompl] at hp
  refine ⟨hd, ?_, hp⟩
  have hlen := hp.length_eq
  rw [List.length_append, hd, hall] at hlen
  have hsum : (M - B.card) * (ℓ - β) + (M - B.card) * β = (M - B.card) * ℓ := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hβ]
  omega

end IdlaCyl.Reduction
