module

/-
Proposition `pr:exchange` (Stability under trajectory swap), frozen.
`paper/idla-cylinder-gff.tex:772-776`:

  "If `ω` and `ω̃` differ in exactly one coordinate, then
   `|A_+(T;ω) △ A_+(T;ω̃)| ≤ 2`."

The realization the paper has in mind is spelled out just above, at
`tex:765-770`: "Realize IDLA from independent infinite walk trajectories
`ω = (ω_1,…,ω_T)`, where `ω_j` starts from a point of `V_N × {0}` chosen
according to `π_N ⊗ δ_0` and follows the cylinder walk forever.  The `j`-th
particle settles at the first site of `ω_j` outside the current cluster."
That is exactly `cluster`, so `clusterPlus` is the paper's `A_+(T;ω)`.

## Junk values

The cardinality is `Set.encard`, valued in `ℕ∞`, not `Set.ncard`.  `ncard` of
an infinite set is `0`, so `ncard _ ≤ 2` would be satisfied by an infinite
symmetric difference and the statement would be vacuously true exactly in the
case it is meant to exclude.  `encard` of an infinite set is `⊤ > 2`.

## A note on the hypothesis

The paper's `ω` is the `T`-tuple actually consumed; the Lean hypothesis
`∃! t, ω t ≠ ω' t` says the two infinite drivers differ in exactly one
coordinate anywhere.  That is a slightly stronger hypothesis, hence a slightly
weaker theorem, and it is the reading of "differ in exactly one coordinate"
that does not require naming `T` twice.

## Status

Proved below, by counting the sites in which the two finite growth processes
differ (`pr_exchange_grow_one_change`).  The paper's proof (`tex:778-783`) runs
through the abelian property of Diaconis--Fulton.
-/
public import IdlaCyl.Support.Base
public import IdlaCyl.Support.Cylinder
public import IdlaCyl.Support.Idla

@[expose] public section

open IdlaCyl
open MeasureTheory
open scoped ENNReal

namespace IdlaCyl.Frozen

variable (B : Base)

noncomputable def pr_exchange_stepSite (P : Finset (Site B)) (d : StepDriver) : Site B :=
  exitSite B (R B 0 ∪ (P : Set (Site B))) d
noncomputable def pr_exchange_step (P : Finset (Site B)) (d : StepDriver) : Finset (Site B) :=
  if 1 ≤ (pr_exchange_stepSite B P d).2 then insert (pr_exchange_stepSite B P d) P else P
noncomputable def pr_exchange_grow (P : Finset (Site B)) : List StepDriver → Finset (Site B)
  | [] => P
  | d :: ds => pr_exchange_grow (pr_exchange_step B P d) ds

lemma pr_exchange_grow_nil (P : Finset (Site B)) : pr_exchange_grow B P [] = P := rfl
lemma pr_exchange_grow_cons (P : Finset (Site B)) (d : StepDriver) (ds : List StepDriver) :
    pr_exchange_grow B P (d :: ds) = pr_exchange_grow B (pr_exchange_step B P d) ds := rfl

lemma pr_exchange_stepSite_mem_R0 {P : Finset (Site B)} {d : StepDriver} :
    pr_exchange_stepSite B P d ∈ R B 0 ↔ ¬ 1 ≤ (pr_exchange_stepSite B P d).2 := by
  rw [mem_R]
  constructor
  · intro h h1
    have : (1 : ℝ) ≤ ((pr_exchange_stepSite B P d).2 : ℝ) := by exact_mod_cast h1
    linarith [h]
  · intro h
    have h2 : (pr_exchange_stepSite B P d).2 ≤ 0 := by omega
    exact_mod_cast h2

lemma pr_exchange_subset_step (P : Finset (Site B)) (d : StepDriver) :
    P ⊆ pr_exchange_step B P d := by
  rw [pr_exchange_step]
  by_cases h : 1 ≤ (pr_exchange_stepSite B P d).2
  · rw [if_pos h]; exact Finset.subset_insert _ _
  · rw [if_neg h]

lemma pr_exchange_exitTime_le_coe_of_not_mem {S : Set (Site B)} {X : ℕ → Site B} {j : ℕ}
    (hj : X j ∉ S) : exitTime B S X ≤ (j : ℕ∞) := by
  unfold exitTime; exact sInf_le ⟨j, rfl, hj⟩

lemma pr_exchange_sInf_image_coe {Bs : Set ℕ} (hne : Bs.Nonempty) :
    sInf ((↑) '' Bs : Set ℕ∞) = ((sInf Bs : ℕ) : ℕ∞) := by
  apply le_antisymm
  · exact sInf_le ⟨sInf Bs, csInf_mem hne, rfl⟩
  · apply le_sInf
    rintro k ⟨n, hn, rfl⟩
    exact_mod_cast csInf_le (OrderBot.bddBelow Bs) hn

lemma pr_exchange_exitTime_eq_coe_sInf {S : Set (Site B)} {X : ℕ → Site B}
    (hne : {n : ℕ | X n ∉ S}.Nonempty) :
    exitTime B S X = ((sInf {n : ℕ | X n ∉ S} : ℕ) : ℕ∞) := by
  have himg : {k : ℕ∞ | ∃ n : ℕ, (k : ℕ∞) = n ∧ X n ∉ S}
      = ((↑) '' {n : ℕ | X n ∉ S} : Set ℕ∞) := by
    ext k; constructor
    · rintro ⟨n, rfl, hn⟩; exact ⟨n, hn, rfl⟩
    · rintro ⟨n, hn, rfl⟩; exact ⟨n, rfl, hn⟩
  rw [exitTime, himg]; exact pr_exchange_sInf_image_coe hne

lemma pr_exchange_exitTime_ne_top_iff {S : Set (Site B)} {X : ℕ → Site B} :
    exitTime B S X ≠ ⊤ ↔ {n : ℕ | X n ∉ S}.Nonempty := by
  constructor
  · intro h; by_contra hne; apply h
    rw [exitTime, show {k : ℕ∞ | ∃ n : ℕ, (k : ℕ∞) = n ∧ X n ∉ S}
        = ((↑) '' {n : ℕ | X n ∉ S} : Set ℕ∞) from by
      ext k; constructor
      · rintro ⟨n, rfl, hn⟩; exact ⟨n, hn, rfl⟩
      · rintro ⟨n, hn, rfl⟩; exact ⟨n, rfl, hn⟩]
    rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.image_empty, sInf_empty]
  · rintro ⟨n, hn⟩ h
    have := pr_exchange_exitTime_eq_coe_sInf (B := B) (S := S) (X := X) ⟨n, hn⟩
    rw [this] at h; exact ENat.coe_ne_top _ h

lemma pr_exchange_exitSite_not_mem {S : Set (Site B)} (d : StepDriver)
    (h : exitTime B S (stepWalk B d) ≠ ⊤) : exitSite B S d ∉ S := by
  set X := stepWalk B d with hX
  have hne : {n : ℕ | X n ∉ S}.Nonempty :=
    (pr_exchange_exitTime_ne_top_iff (B := B) (S := S) (X := X)).mp h
  have hcoe : exitTime B S X = ((sInf {n : ℕ | X n ∉ S} : ℕ) : ℕ∞) :=
    pr_exchange_exitTime_eq_coe_sInf (B := B) hne
  have htoNat : (exitTime B S X).toNat = sInf {n : ℕ | X n ∉ S} := by rw [hcoe, ENat.toNat_coe]
  have hmem : sInf {n : ℕ | X n ∉ S} ∈ {n : ℕ | X n ∉ S} := csInf_mem hne
  show X (exitTime B S X).toNat ∉ S
  rw [htoNat]; exact hmem

lemma pr_exchange_exitSite_mem_of_lt {S S' : Set (Site B)} {X : ℕ → Site B}
    (h : exitTime B S X < exitTime B S' X) : X (exitTime B S X).toNat ∈ S' := by
  by_contra hmem
  have hle : exitTime B S' X ≤ ((exitTime B S X).toNat : ℕ∞) :=
    pr_exchange_exitTime_le_coe_of_not_mem (B := B) hmem
  have hcoe : ((exitTime B S X).toNat : ℕ∞) = exitTime B S X :=
    ENat.coe_toNat (lt_of_lt_of_le h le_top).ne
  rw [hcoe] at hle; exact not_lt.mpr hle h

lemma pr_exchange_step_sdiff_card_le (P Q : Finset (Site B)) (d : StepDriver) :
    (pr_exchange_step B P d \ pr_exchange_step B Q d).card ≤ (P \ Q).card := by
  set X := stepWalk B d with hX
  set τP := exitTime B (R B 0 ∪ (P : Set (Site B))) X with hτP
  set τQ := exitTime B (R B 0 ∪ (Q : Set (Site B))) X with hτQ
  have hsiteP : exitSite B (R B 0 ∪ (P : Set (Site B))) d = X τP.toNat := by
    rw [exitSite, ← hX, ← hτP]
  have hsiteQ : exitSite B (R B 0 ∪ (Q : Set (Site B))) d = X τQ.toNat := by
    rw [exitSite, ← hX, ← hτQ]
  have hstepP : pr_exchange_step B P d
      = if 1 ≤ (exitSite B (R B 0 ∪ (P : Set (Site B))) d).2
          then insert (exitSite B (R B 0 ∪ (P : Set (Site B))) d) P else P := by
    rw [pr_exchange_step, pr_exchange_stepSite]
  have hstepQ : pr_exchange_step B Q d
      = if 1 ≤ (exitSite B (R B 0 ∪ (Q : Set (Site B))) d).2
          then insert (exitSite B (R B 0 ∪ (Q : Set (Site B))) d) Q else Q := by
    rw [pr_exchange_step, pr_exchange_stepSite]
  rw [hstepP, hstepQ]
  rcases lt_trichotomy τP τQ with hlt | heq | hgt
  · have hτPne : exitTime B (R B 0 ∪ (P : Set (Site B))) (stepWalk B d) ≠ ⊤ := by
      rw [← hX, ← hτP]; exact (lt_of_lt_of_le hlt le_top).ne
    have hzP_notmem : exitSite B (R B 0 ∪ (P : Set (Site B))) d
        ∉ (R B 0 ∪ (P : Set (Site B))) :=
      pr_exchange_exitSite_not_mem (B := B) (S := R B 0 ∪ (P : Set (Site B))) d hτPne
    have hzP_mem : exitSite B (R B 0 ∪ (P : Set (Site B))) d
        ∈ (R B 0 ∪ (Q : Set (Site B))) := by
      have h := pr_exchange_exitSite_mem_of_lt (B := B)
        (S := R B 0 ∪ (P : Set (Site B))) (S' := R B 0 ∪ (Q : Set (Site B)))
        (X := stepWalk B d) ?_
      · exact h
      · rw [← hX, ← hτP, ← hτQ]; exact hlt
    have hzP_notR0 : exitSite B (R B 0 ∪ (P : Set (Site B))) d ∉ R B 0 :=
      fun h => hzP_notmem (Or.inl h)
    have hzP_memQ : exitSite B (R B 0 ∪ (P : Set (Site B))) d ∈ Q := by
      rcases hzP_mem with h | h
      · exact absurd h hzP_notR0
      · exact h
    have hzP1 : 1 ≤ (exitSite B (R B 0 ∪ (P : Set (Site B))) d).2 := by
      by_contra h
      exact hzP_notR0 ((pr_exchange_stepSite_mem_R0 (B := B) (P := P) (d := d)).mpr h)
    rw [if_pos hzP1]
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    obtain ⟨hxP, hxQ⟩ := hx
    have hxnQ : x ∉ Q := fun hq => hxQ (pr_exchange_subset_step B Q d hq)
    rcases Finset.mem_insert.mp hxP with hxz | hxP
    · exfalso
      exact hxQ (hxz ▸ pr_exchange_subset_step B Q d hzP_memQ)
    · exact ⟨hxP, hxnQ⟩
  · have hsite : exitSite B (R B 0 ∪ (P : Set (Site B))) d
        = exitSite B (R B 0 ∪ (Q : Set (Site B))) d := by
      rw [hsiteP, hsiteQ, heq]
    rw [hsite]
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_sdiff] at hx ⊢
    obtain ⟨hxP, hxQ⟩ := hx
    by_cases hc : 1 ≤ (exitSite B (R B 0 ∪ (Q : Set (Site B))) d).2
    · rw [if_pos hc] at hxP hxQ
      rcases Finset.mem_insert.mp hxP with hxz | hxP
      · exact absurd (hxz ▸ Finset.mem_insert_self _ _) hxQ
      · exact ⟨hxP, fun hq => hxQ (Finset.mem_insert_of_mem hq)⟩
    · rw [if_neg hc] at hxP hxQ
      exact ⟨hxP, hxQ⟩
  · have hτQne : exitTime B (R B 0 ∪ (Q : Set (Site B))) (stepWalk B d) ≠ ⊤ := by
      rw [← hX, ← hτQ]; exact (lt_of_lt_of_le hgt le_top).ne
    have hzQ_notmem : exitSite B (R B 0 ∪ (Q : Set (Site B))) d
        ∉ (R B 0 ∪ (Q : Set (Site B))) :=
      pr_exchange_exitSite_not_mem (B := B) (S := R B 0 ∪ (Q : Set (Site B))) d hτQne
    have hzQ_mem : exitSite B (R B 0 ∪ (Q : Set (Site B))) d
        ∈ (R B 0 ∪ (P : Set (Site B))) := by
      have h := pr_exchange_exitSite_mem_of_lt (B := B)
        (S := R B 0 ∪ (Q : Set (Site B))) (S' := R B 0 ∪ (P : Set (Site B)))
        (X := stepWalk B d) ?_
      · exact h
      · rw [← hX, ← hτQ, ← hτP]; exact hgt
    have hzQ_notR0 : exitSite B (R B 0 ∪ (Q : Set (Site B))) d ∉ R B 0 :=
      fun h => hzQ_notmem (Or.inl h)
    have hzQ_memP : exitSite B (R B 0 ∪ (Q : Set (Site B))) d ∈ P := by
      rcases hzQ_mem with h | h
      · exact absurd h hzQ_notR0
      · exact h
    have hzQ_notQ : exitSite B (R B 0 ∪ (Q : Set (Site B))) d ∉ Q :=
      fun h => hzQ_notmem (Or.inr h)
    have hzQ1 : 1 ≤ (exitSite B (R B 0 ∪ (Q : Set (Site B))) d).2 := by
      by_contra h
      exact hzQ_notR0 ((pr_exchange_stepSite_mem_R0 (B := B) (P := Q) (d := d)).mpr h)
    have hzQ_mem_diff : exitSite B (R B 0 ∪ (Q : Set (Site B))) d ∈ P \ Q :=
      Finset.mem_sdiff.mpr ⟨hzQ_memP, hzQ_notQ⟩
    rw [if_pos hzQ1]
    have hsub : (if 1 ≤ (exitSite B (R B 0 ∪ (P : Set (Site B))) d).2
          then insert (exitSite B (R B 0 ∪ (P : Set (Site B))) d) P else P)
        \ (insert (exitSite B (R B 0 ∪ (Q : Set (Site B))) d) Q) ⊆
        (P \ Q).erase (exitSite B (R B 0 ∪ (Q : Set (Site B))) d)
          ∪ {exitSite B (R B 0 ∪ (P : Set (Site B))) d} := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      obtain ⟨hxP, hxQ⟩ := hx
      have hxnQ : x ∉ Q := fun hq => hxQ (Finset.mem_insert_of_mem hq)
      have hxnezQ : x ≠ exitSite B (R B 0 ∪ (Q : Set (Site B))) d :=
        fun h => hxQ (h ▸ Finset.mem_insert_self _ _)
      by_cases hzP : 1 ≤ (exitSite B (R B 0 ∪ (P : Set (Site B))) d).2
      · rw [if_pos hzP, Finset.mem_insert] at hxP
        rcases hxP with hxz | hxP
        · rw [hxz]; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
        · exact Finset.mem_union_left _ (Finset.mem_erase.mpr
            ⟨hxnezQ, Finset.mem_sdiff.mpr ⟨hxP, hxnQ⟩⟩)
      · rw [if_neg hzP] at hxP
        exact Finset.mem_union_left _ (Finset.mem_erase.mpr
          ⟨hxnezQ, Finset.mem_sdiff.mpr ⟨hxP, hxnQ⟩⟩)
    calc
      ((if 1 ≤ (exitSite B (R B 0 ∪ (P : Set (Site B))) d).2
            then insert (exitSite B (R B 0 ∪ (P : Set (Site B))) d) P else P)
          \ (insert (exitSite B (R B 0 ∪ (Q : Set (Site B))) d) Q)).card
          ≤ ((P \ Q).erase (exitSite B (R B 0 ∪ (Q : Set (Site B))) d)
              ∪ {exitSite B (R B 0 ∪ (P : Set (Site B))) d}).card :=
            Finset.card_le_card hsub
      _ ≤ ((P \ Q).erase (exitSite B (R B 0 ∪ (Q : Set (Site B))) d)).card
            + ({exitSite B (R B 0 ∪ (P : Set (Site B))) d} : Finset (Site B)).card :=
            Finset.card_union_le _ _
      _ = (P \ Q).card := by
            rw [Finset.card_erase_of_mem hzQ_mem_diff, Finset.card_singleton]
            have : 0 < (P \ Q).card := Finset.card_pos.mpr ⟨_, hzQ_mem_diff⟩
            omega

lemma pr_exchange_step_sdiff_card_le_one (P : Finset (Site B)) (d d' : StepDriver) :
    (pr_exchange_step B P d \ pr_exchange_step B P d').card ≤ 1 := by
  have hsub : pr_exchange_step B P d \ pr_exchange_step B P d'
      ⊆ {pr_exchange_stepSite B P d} := by
    intro x hx
    rw [Finset.mem_sdiff] at hx
    obtain ⟨hxP, hxQ⟩ := hx
    rw [Finset.mem_singleton]
    by_contra hxz
    rw [pr_exchange_step] at hxP
    by_cases h : 1 ≤ (pr_exchange_stepSite B P d).2
    · rw [if_pos h] at hxP
      rcases Finset.mem_insert.mp hxP with h' | h'
      · exact hxz h'
      · exact hxQ (pr_exchange_subset_step B P d' h')
    · rw [if_neg h] at hxP
      exact hxQ (pr_exchange_subset_step B P d' hxP)
  calc (pr_exchange_step B P d \ pr_exchange_step B P d').card
      ≤ ({pr_exchange_stepSite B P d} : Finset (Site B)).card := Finset.card_le_card hsub
    _ = 1 := Finset.card_singleton _

lemma pr_exchange_grow_sdiff_card_le (P Q : Finset (Site B)) (ds : List StepDriver) :
    (pr_exchange_grow B P ds \ pr_exchange_grow B Q ds).card ≤ (P \ Q).card := by
  induction ds generalizing P Q with
  | nil => simp [pr_exchange_grow_nil]
  | cons d ds ih =>
      rw [pr_exchange_grow_cons, pr_exchange_grow_cons]
      exact (ih (pr_exchange_step B P d) (pr_exchange_step B Q d)).trans
        (pr_exchange_step_sdiff_card_le B P Q d)

lemma pr_exchange_grow_append (P : Finset (Site B)) (xs ys : List StepDriver) :
    pr_exchange_grow B P (xs ++ ys)
      = pr_exchange_grow B (pr_exchange_grow B P xs) ys := by
  induction xs generalizing P with
  | nil => rfl
  | cons d ds ih => rw [List.cons_append, pr_exchange_grow_cons, pr_exchange_grow_cons, ih]

lemma pr_exchange_coe_step (P : Finset (Site B)) (d : StepDriver) :
    (pr_exchange_step B P d : Set (Site B))
      = (P : Set (Site B)) ∪ ({pr_exchange_stepSite B P d} ∩ {p : Site B | 1 ≤ p.2}) := by
  rw [pr_exchange_step]
  by_cases h : 1 ≤ (pr_exchange_stepSite B P d).2
  · rw [if_pos h]
    ext p
    simp only [Finset.coe_insert, Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_coe]
    constructor
    · rintro (rfl | hp)
      · exact Or.inr ⟨rfl, h⟩
      · exact Or.inl hp
    · rintro (hp | ⟨rfl, -⟩)
      · exact Or.inr hp
      · exact Or.inl rfl
  · rw [if_neg h]
    ext p
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq,
      Finset.mem_coe]
    constructor
    · intro hp; exact Or.inl hp
    · rintro (hp | ⟨rfl, h1⟩)
      · exact hp
      · exact absurd h1 h

lemma pr_exchange_cluster_eq_union (ω : Driver) (t : ℕ) :
    cluster B ω t = R B 0 ∪ clusterPlus B ω t := by
  ext p
  constructor
  · intro hp
    by_cases h : 1 ≤ p.2
    · exact Or.inr ⟨hp, h⟩
    · exact Or.inl (by rw [mem_R]; exact_mod_cast (by omega : p.2 ≤ 0))
  · rintro (hp | ⟨hp, -⟩)
    · exact cluster_mono B ω (Nat.zero_le t) hp
    · exact hp

lemma pr_exchange_clusterPlus_succ (ω : Driver) (t : ℕ) :
    clusterPlus B ω (t + 1)
      = clusterPlus B ω t ∪ ({exitSite B (cluster B ω t) (ω t)} ∩ {p : Site B | 1 ≤ p.2}) := by
  unfold clusterPlus
  rw [cluster_succ]
  ext p
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
  tauto

lemma pr_exchange_grow_eq_clusterPlus (ω : Driver) (t : ℕ) :
    (pr_exchange_grow B ∅ ((List.range t).map ω) : Set (Site B)) = clusterPlus B ω t := by
  induction t with
  | zero =>
      rw [List.range_zero, List.map_nil, pr_exchange_grow_nil, clusterPlus, cluster_zero]
      ext p
      simp only [Finset.coe_empty, Set.mem_empty_iff_false, Set.mem_inter_iff, mem_R,
        Set.mem_setOf_eq]
      constructor
      · intro h; exact h.elim
      · rintro ⟨h0, h1⟩
        have : (1 : ℝ) ≤ (p.2 : ℝ) := by exact_mod_cast h1
        linarith
  | succ n ih =>
      have hlist : (List.range (n + 1)).map ω = ((List.range n).map ω) ++ [ω n] := by
        rw [List.range_succ, List.map_append]; rfl
      rw [hlist, pr_exchange_grow_append, pr_exchange_grow_cons, pr_exchange_grow_nil]
      have hz : pr_exchange_stepSite B (pr_exchange_grow B ∅ ((List.range n).map ω)) (ω n)
          = exitSite B (cluster B ω n) (ω n) := by
        rw [pr_exchange_stepSite, ih, pr_exchange_cluster_eq_union]
      rw [pr_exchange_coe_step, hz, pr_exchange_clusterPlus_succ, ← ih]

lemma pr_exchange_grow_one_change (ω ω' : Driver) (h : ∃! t : ℕ, ω t ≠ ω' t) (T : ℕ) :
    (pr_exchange_grow B ∅ ((List.range T).map ω)
        \ pr_exchange_grow B ∅ ((List.range T).map ω')).card ≤ 1 ∧
    (pr_exchange_grow B ∅ ((List.range T).map ω')
        \ pr_exchange_grow B ∅ ((List.range T).map ω)).card ≤ 1 := by
  induction T with
  | zero =>
      rw [List.range_zero, List.map_nil, List.map_nil]
      exact ⟨by simp, by simp⟩
  | succ n ih =>
      obtain ⟨j, hj, hju⟩ := h
      by_cases hne : ω n = ω' n
      · have hmaps : (List.range (n + 1)).map ω = ((List.range n).map ω) ++ [ω n] := by
          rw [List.range_succ, List.map_append]; rfl
        have hmaps' : (List.range (n + 1)).map ω' = ((List.range n).map ω') ++ [ω' n] := by
          rw [List.range_succ, List.map_append]; rfl
        rw [hmaps, hmaps', pr_exchange_grow_append, pr_exchange_grow_append,
          pr_exchange_grow_cons, pr_exchange_grow_cons, pr_exchange_grow_nil,
          pr_exchange_grow_nil, hne]
        exact ⟨(pr_exchange_grow_sdiff_card_le B _ _ [ω' n]).trans (by simpa using ih.1),
               (pr_exchange_grow_sdiff_card_le B _ _ [ω' n]).trans (by simpa using ih.2)⟩
      · have heq : (List.range n).map ω = (List.range n).map ω' := by
          apply List.map_congr_left
          intro i hi
          rw [List.mem_range] at hi
          by_contra hd
          have hin : i = n := by rw [hju i hd, ← hju n hne]
          omega
        have hmaps : (List.range (n + 1)).map ω = ((List.range n).map ω) ++ [ω n] := by
          rw [List.range_succ, List.map_append]; rfl
        have hmaps' : (List.range (n + 1)).map ω' = ((List.range n).map ω') ++ [ω' n] := by
          rw [List.range_succ, List.map_append]; rfl
        rw [hmaps, hmaps', pr_exchange_grow_append, pr_exchange_grow_append,
          pr_exchange_grow_cons, pr_exchange_grow_cons, pr_exchange_grow_nil,
          pr_exchange_grow_nil, heq]
        exact ⟨by simpa only [pr_exchange_grow_cons, pr_exchange_grow_nil] using
                 pr_exchange_step_sdiff_card_le_one B _ (ω n) (ω' n),
               by simpa only [pr_exchange_grow_cons, pr_exchange_grow_nil] using
                 pr_exchange_step_sdiff_card_le_one B _ (ω' n) (ω n)⟩

-- FROZEN-STATEMENT-BEGIN
/-- Proposition `pr:exchange`: changing one trajectory moves at most two sites
of the cluster. -/
theorem pr_exchange (B : Base) (T : ℕ) (ω ω' : Driver)
    (h : ∃! t : ℕ, ω t ≠ ω' t) :
    Set.encard (symmDiff (clusterPlus B ω T) (clusterPlus B ω' T)) ≤ 2
-- FROZEN-STATEMENT-END
:= by
  have hd := pr_exchange_grow_one_change B ω ω' h T
  have hcoeω := pr_exchange_grow_eq_clusterPlus B ω T
  have hcoeω' := pr_exchange_grow_eq_clusterPlus B ω' T
  rw [← hcoeω, ← hcoeω']
  rw [Set.symmDiff_def, ← Finset.coe_sdiff, ← Finset.coe_sdiff, ← Finset.coe_union]
  rw [Set.encard_coe_eq_coe_finsetCard]
  have hcard : (((pr_exchange_grow B ∅ ((List.range T).map ω)) \
        pr_exchange_grow B ∅ ((List.range T).map ω'))
      ∪ (pr_exchange_grow B ∅ ((List.range T).map ω') \
        pr_exchange_grow B ∅ ((List.range T).map ω))).card ≤ 2 := by
    have h := Finset.card_union_le
      (pr_exchange_grow B ∅ ((List.range T).map ω) \ pr_exchange_grow B ∅ ((List.range T).map ω'))
      (pr_exchange_grow B ∅ ((List.range T).map ω') \ pr_exchange_grow B ∅ ((List.range T).map ω))
    omega
  exact_mod_cast hcard

end IdlaCyl.Frozen
