/-
The spectral gap of the base kernel, lower-bounded through the second eigenfunction.

The lower bound `1/(2 N³) ≤ 1 - λ₂` on the spectral gap of the base kernel, as a
Poincaré inequality along paths applied to the second eigenfunction `f = f^N_2`.
The steps are: the split of the lazy kernel into adjacency and diagonal parts; the
pointwise Dirichlet identity `(1 - λ₂) f(x) = (1/(2d)) ∑_{x' ∼ x} (f(x) - f(x'))`;
the energy identity `(1 - λ₂) ∑ f² = D/(4d)`, where `D` sums `(f(x) - f(x'))²` over
ordered adjacent pairs; the normalisation `∑_{x,y} (f(y) - f(x))² = 2N²`; and the
bound `(f(y) - f(x))² ≤ N D` along a path of length at most `N`.

The statements use the paper's indexing of `SpectralData` (`tex:301-311`); no
statement in this file is a transcription of a numbered theorem of the paper.
-/
import IdlaCyl.Support.Spectral

namespace IdlaCyl

open scoped BigOperators

namespace Base

variable (B : Base)

/-- The lazy kernel as the sum of its adjacency part and its diagonal part. -/
theorem gap_P_split (x x' : B.V) :
    B.P x x' = 1 / (2 * (B.deg : ℝ)) * (if B.graph.Adj x x' then 1 else 0)
      + 1 / 2 * (if x = x' then 1 else 0) := by
  unfold P
  by_cases h : B.graph.Adj x x'
  · simp [h.ne]
  · by_cases hxx : x = x'
    · subst hxx
      simp
    · simp [h, hxx]

/-- Summing a constant over the neighbours of a vertex gives the degree times
that constant. -/
theorem gap_sum_adj (x : B.V) (c : ℝ) :
    ∑ x' : B.V, (if B.graph.Adj x x' then c else 0) = (B.deg : ℝ) * c := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
    ← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree,
    B.degree_eq]

end Base

namespace SpectralData

variable {B : Base} (S : SpectralData B)

/-- The pointwise Dirichlet identity for the second eigenfunction: at each vertex
`x`, `(1 - λ₂) f(x)` equals `(1/(2d))` times the sum of `f(x) - f(x')` over the
neighbours `x'` of `x`. -/
theorem gap_dirichlet_pt (hN : 2 ≤ B.card) (x : B.V) :
    (1 - S.lam 2) * S.f 2 x = 1 / (2 * (B.deg : ℝ)) *
      ∑ x' : B.V, (if B.graph.Adj x x' then S.f 2 x - S.f 2 x' else 0) := by
  have hd : (B.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr B.deg_pos.ne'
  have hk : 1 / (2 * (B.deg : ℝ)) * (B.deg : ℝ) = 1 / 2 := by
    rw [div_mul_eq_mul_div, one_mul, div_eq_iff (mul_ne_zero two_ne_zero hd)]
    ring
  have he := S.eigen 2 (by norm_num) hN x
  have hterm : ∀ x', B.P x x' * S.f 2 x' = 1 / (2 * (B.deg : ℝ)) *
      (if B.graph.Adj x x' then S.f 2 x' else 0) + 1 / 2 * (if x = x' then S.f 2 x' else 0) := by
    intro x'
    rw [Base.gap_P_split B x x']
    split_ifs <;> ring
  have hPf : ∑ x' : B.V, B.P x x' * S.f 2 x' = 1 / (2 * (B.deg : ℝ)) *
      ∑ x' : B.V, (if B.graph.Adj x x' then S.f 2 x' else 0) + 1 / 2 * S.f 2 x := by
    rw [Finset.sum_congr rfl (fun x' _ => hterm x'), Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hsplit : ∑ x' : B.V, (if B.graph.Adj x x' then S.f 2 x - S.f 2 x' else 0)
      = (B.deg : ℝ) * S.f 2 x - ∑ x' : B.V, (if B.graph.Adj x x' then S.f 2 x' else 0) := by
    rw [← Base.gap_sum_adj B x (S.f 2 x), ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x' _
    split_ifs <;> ring
  rw [hPf] at he
  rw [hsplit]
  linear_combination he - S.f 2 x * hk

end SpectralData

namespace Base

variable (B : Base)

/-- A scalar Cauchy–Schwarz step: `(a + b)² ≤ (L + 1)(S + b²)` whenever `a² ≤ L S`. -/
theorem gap_cs (a b L S : ℝ) (hL : 0 ≤ L) (hS : 0 ≤ S) (h : a ^ 2 ≤ L * S) :
    (a + b) ^ 2 ≤ (L + 1) * (S + b ^ 2) := by
  rcases hL.eq_or_lt with hL0 | hLpos
  · subst hL0
    have ha2 : a ^ 2 = 0 := le_antisymm (by simpa using h) (sq_nonneg a)
    have ha : a = 0 := (pow_eq_zero_iff two_ne_zero).mp ha2
    subst ha
    nlinarith [hS]
  · have h1 : 0 ≤ S + L * b ^ 2 - 2 * a * b := by
      nlinarith [sq_nonneg (L * b - a), hLpos, h]
    nlinarith [h1, h]

/-- Along a walk, the squared increment of `f` between its endpoints is at most the
length times the sum of the squared increments over its darts. -/
theorem gap_walk_bound (f : B.V → ℝ) {x y : B.V} (p : B.graph.Walk x y) :
    (f y - f x) ^ 2 ≤ (p.length : ℝ) * (p.darts.map (fun d => (f d.fst - f d.snd) ^ 2)).sum := by
  induction p with
  | nil => simp
  | @cons u v w h q ih =>
    have hS : 0 ≤ (q.darts.map (fun d => (f d.fst - f d.snd) ^ 2)).sum :=
      List.sum_nonneg fun r hr => by
        obtain ⟨d, _, rfl⟩ := List.mem_map.mp hr
        exact sq_nonneg _
    have key := gap_cs (f w - f v) (f v - f u) (q.length : ℝ) _ (Nat.cast_nonneg _) hS ih
    have e1 : f w - f v + (f v - f u) = f w - f u := by ring
    have e2 : (f v - f u) ^ 2 = (f u - f v) ^ 2 := by ring
    rw [e1, e2] at key
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.darts_cons, List.map_cons,
      List.sum_cons]
    push_cast
    linarith [key]

/-- For a path, the sum over its darts of a nonnegative function of the ordered
endpoints is at most the sum over all ordered adjacent pairs. -/
theorem gap_darts_le {u v : B.V} (p : B.graph.Walk u v) (hp : p.IsPath)
    (g : B.V → B.V → ℝ) (hg : ∀ x x', 0 ≤ g x x') :
    (p.darts.map (fun d => g d.fst d.snd)).sum
      ≤ ∑ x : B.V, ∑ x' : B.V, (if B.graph.Adj x x' then g x x' else 0) := by
  have hnd : (p.darts.map SimpleGraph.Dart.toProd).Nodup :=
    ((SimpleGraph.Walk.darts_nodup_of_support_nodup ((SimpleGraph.Walk.isPath_def p).mp hp))).map
      SimpleGraph.Dart.toProd_injective
  have hsub : (p.darts.map SimpleGraph.Dart.toProd).toFinset ⊆
      Finset.univ.filter (fun z : B.V × B.V => B.graph.Adj z.1 z.2) := by
    intro z hz
    rw [List.mem_toFinset, List.mem_map] at hz
    obtain ⟨d, _, rfl⟩ := hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact d.adj
  calc (p.darts.map (fun d => g d.fst d.snd)).sum
      = ∑ z ∈ (p.darts.map SimpleGraph.Dart.toProd).toFinset, g z.1 z.2 := by
        rw [List.sum_toFinset (fun z : B.V × B.V => g z.1 z.2) hnd, List.map_map]
        rfl
    _ ≤ ∑ z ∈ Finset.univ.filter (fun z : B.V × B.V => B.graph.Adj z.1 z.2), g z.1 z.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z _ _ => hg z.1 z.2)
    _ = ∑ x : B.V, ∑ x' : B.V, (if B.graph.Adj x x' then g x x' else 0) := by
        rw [Finset.sum_filter, Fintype.sum_prod_type]

end Base

namespace SpectralData

variable {B : Base} (S : SpectralData B)

/-- The Dirichlet energy identity for the second eigenfunction:
`(1 - λ₂) ∑ f² = (1/(4d)) D`, where `D` sums `(f x - f x')²` over ordered adjacent pairs. -/
theorem gap_energy (hN : 2 ≤ B.card) :
    (1 - S.lam 2) * ∑ x : B.V, S.f 2 x ^ 2 = 1 / (4 * (B.deg : ℝ)) *
      ∑ x : B.V, ∑ x' : B.V, (if B.graph.Adj x x' then (S.f 2 x - S.f 2 x') ^ 2 else 0) := by
  have hT : ∑ x : B.V, ∑ x' : B.V, (if B.graph.Adj x x' then (S.f 2 x - S.f 2 x') * S.f 2 x else 0)
      = 1 / 2 * ∑ x : B.V, ∑ x' : B.V,
          (if B.graph.Adj x x' then (S.f 2 x - S.f 2 x') ^ 2 else 0) := by
    have hFG : ∀ x x' : B.V, (if B.graph.Adj x x' then (S.f 2 x - S.f 2 x') * S.f 2 x' else 0)
        = -(if B.graph.Adj x' x then (S.f 2 x' - S.f 2 x) * S.f 2 x' else 0) := by
      intro x x'
      by_cases h : B.graph.Adj x x'
      · rw [if_pos h, if_pos h.symm]; ring
      · rw [if_neg h, if_neg (fun hc => h hc.symm)]; ring
    have hT2 : ∑ x : B.V, ∑ x' : B.V,
          (if B.graph.Adj x x' then (S.f 2 x - S.f 2 x') * S.f 2 x' else 0)
        = -∑ x : B.V, ∑ x' : B.V,
          (if B.graph.Adj x x' then (S.f 2 x - S.f 2 x') * S.f 2 x else 0) := by
      simp only [hFG, Finset.sum_neg_distrib]
      rw [Finset.sum_comm]
    have hD : ∑ x : B.V, ∑ x' : B.V, (if B.graph.Adj x x' then (S.f 2 x - S.f 2 x') ^ 2 else 0)
        = ∑ x : B.V, ∑ x' : B.V, (if B.graph.Adj x x' then (S.f 2 x - S.f 2 x') * S.f 2 x else 0)
          - ∑ x : B.V, ∑ x' : B.V,
            (if B.graph.Adj x x' then (S.f 2 x - S.f 2 x') * S.f 2 x' else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x' _
      split_ifs <;> ring
    rw [hD, hT2]
    ring
  have hsum : (1 - S.lam 2) * ∑ x : B.V, S.f 2 x ^ 2 = ∑ x : B.V, 1 / (2 * (B.deg : ℝ)) *
      ∑ x' : B.V, (if B.graph.Adj x x' then (S.f 2 x - S.f 2 x') * S.f 2 x else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    have hx := gap_dirichlet_pt S hN x
    have hmul : ∑ x' : B.V, (if B.graph.Adj x x' then (S.f 2 x - S.f 2 x') * S.f 2 x else 0)
        = (∑ x' : B.V, (if B.graph.Adj x x' then S.f 2 x - S.f 2 x' else 0)) * S.f 2 x := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x' _
      split_ifs <;> ring
    rw [hmul, ← mul_assoc, ← hx]
    ring
  rw [hsum, ← Finset.mul_sum, hT]
  ring

end SpectralData

namespace SpectralData

variable {B : Base} (S : SpectralData B)

/-- The mass of the second eigenfunction: `∑_x f₂(x)² = N` (`tex:305-308`). -/
theorem gap_mass_sq (hN : 2 ≤ B.card) : ∑ x : B.V, S.f 2 x ^ 2 = B.card := by
  have hcne : (B.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : B.card ≠ 0)
  have h := S.orthonormal 2 2 (by norm_num) hN (by norm_num) hN
  rw [if_pos rfl, one_div, inv_mul_eq_iff_eq_mul₀ hcne] at h
  simpa [sq] using h

/-- `f₂` is orthogonal to the constant eigenfunction: `∑_x f₂(x) = 0`. -/
theorem gap_mass_sum (hN : 2 ≤ B.card) : ∑ x : B.V, S.f 2 x = 0 := by
  have hcne : (B.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : B.card ≠ 0)
  have h := S.orthonormal 1 2 le_rfl (by omega) (by norm_num) hN
  rw [if_neg (show ¬ (1 : ℕ) = 2 by norm_num)] at h
  simp only [S.f_one, one_mul] at h
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd h0 (one_div_ne_zero hcne)
  · exact h0

/-- The pairwise energy `∑_{x,y} (f(y) - f(x))²` equals `2N ∑ f² - 2 (∑ f)²`. -/
theorem gap_normalise :
    ∑ x : B.V, ∑ y : B.V, (S.f 2 y - S.f 2 x) ^ 2
      = 2 * (Fintype.card B.V : ℝ) * ∑ x : B.V, S.f 2 x ^ 2 - 2 * (∑ x : B.V, S.f 2 x) ^ 2 := by
  have e : ∀ x : B.V, ∑ y : B.V, (S.f 2 y - S.f 2 x) ^ 2
      = (∑ y : B.V, S.f 2 y ^ 2) + (Fintype.card B.V : ℝ) * S.f 2 x ^ 2
        - 2 * S.f 2 x * ∑ y : B.V, S.f 2 y := by
    intro x
    have h2 : ∀ y : B.V, (S.f 2 y - S.f 2 x) ^ 2
        = S.f 2 y ^ 2 - 2 * S.f 2 x * S.f 2 y + S.f 2 x ^ 2 := fun y => by ring
    simp only [h2, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul]
  ring

/-- Each ordered pair is within `N` times the total Dirichlet sum `D`, by a path of
length at most `N`. -/
theorem gap_path_sq (x y : B.V) :
    (S.f 2 y - S.f 2 x) ^ 2 ≤ (Fintype.card B.V : ℝ) *
      ∑ a : B.V, ∑ b : B.V, (if B.graph.Adj a b then (S.f 2 a - S.f 2 b) ^ 2 else 0) := by
  obtain ⟨w⟩ := B.connected.preconnected x y
  have hp := w.bypass_isPath
  have hlen : (w.bypass.length : ℝ) ≤ (Fintype.card B.V : ℝ) := by
    have h : w.bypass.length < Fintype.card B.V := hp.length_lt
    exact_mod_cast h.le
  calc (S.f 2 y - S.f 2 x) ^ 2
      ≤ (w.bypass.length : ℝ) *
          (w.bypass.darts.map (fun d => (S.f 2 d.fst - S.f 2 d.snd) ^ 2)).sum :=
        Base.gap_walk_bound B (S.f 2) w.bypass
    _ ≤ (Fintype.card B.V : ℝ) * ∑ a : B.V, ∑ b : B.V,
          (if B.graph.Adj a b then (S.f 2 a - S.f 2 b) ^ 2 else 0) := by
        apply mul_le_mul hlen
        · exact Base.gap_darts_le B w.bypass hp (fun a b => (S.f 2 a - S.f 2 b) ^ 2)
            (fun _ _ => sq_nonneg _)
        · exact List.sum_nonneg fun r hr => by
            obtain ⟨d, _, rfl⟩ := List.mem_map.mp hr
            exact sq_nonneg _
        · exact Nat.cast_nonneg _

end SpectralData

end IdlaCyl

namespace IdlaCyl

/-- Auxiliary lower bound on the spectral gap of the base kernel: `1/(2N³) ≤ 1 - λ₂`,
by a Poincaré inequality along paths applied to the second eigenfunction. -/
theorem gap_ge_inv_two_card_cube (B : Base) (S : SpectralData B) :
    1 / (2 * (B.card : ℝ) ^ 3) ≤ S.gap := by
  have hN : 2 ≤ B.card := B.nontrivial
  have hN' : 2 ≤ Fintype.card B.V := B.nontrivial
  have hNpos : (0 : ℝ) < Fintype.card B.V := by exact_mod_cast (by omega : 0 < Fintype.card B.V)
  have hd0 : (0 : ℝ) < B.deg := by exact_mod_cast B.deg_pos
  have hdN : (B.deg : ℝ) ≤ (Fintype.card B.V : ℝ) := by
    have h := SimpleGraph.degree_lt_card_verts (G := B.graph) B.pt
    rw [B.degree_eq] at h
    exact_mod_cast h.le
  have hE := S.gap_energy hN
  have hM : ∑ x : B.V, S.f 2 x ^ 2 = (Fintype.card B.V : ℝ) := S.gap_mass_sq hN
  have hZ := S.gap_mass_sum hN
  have hNorm := S.gap_normalise
  have hg : 0 < 1 - S.lam 2 := by linarith [S.lam_two_lt hN]
  rw [hM] at hE hNorm
  rw [hZ] at hNorm
  set D := ∑ a : B.V, ∑ b : B.V, (if B.graph.Adj a b then (S.f 2 a - S.f 2 b) ^ 2 else 0)
    with hDdef
  have hpair : ∑ x : B.V, ∑ y : B.V, (S.f 2 y - S.f 2 x) ^ 2 ≤ ∑ x : B.V, ∑ y : B.V,
      ((Fintype.card B.V : ℝ) * D) :=
    Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => S.gap_path_sq x y
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hpair
  rw [hNorm] at hpair
  have hND : 2 ≤ (Fintype.card B.V : ℝ) * D := by
    have h2 : (Fintype.card B.V : ℝ) ^ 2 * 2
        ≤ (Fintype.card B.V : ℝ) ^ 2 * ((Fintype.card B.V : ℝ) * D) := by
      nlinarith [hpair]
    exact le_of_mul_le_mul_left h2 (by positivity)
  have hinv : 1 / (4 * (B.deg : ℝ)) * (4 * (B.deg : ℝ)) = 1 :=
    one_div_mul_cancel (mul_ne_zero (by norm_num) hd0.ne')
  have hE2 : (1 - S.lam 2) * (4 * (B.deg : ℝ) * (Fintype.card B.V : ℝ)) = D := by
    linear_combination (4 * (B.deg : ℝ)) * hE + D * hinv
  have hA : (1 - S.lam 2) * (4 * (B.deg : ℝ) * (Fintype.card B.V : ℝ) * (Fintype.card B.V : ℝ))
      = D * (Fintype.card B.V : ℝ) := by
    linear_combination (Fintype.card B.V : ℝ) * hE2
  have hfin : 1 ≤ (1 - S.lam 2) * (2 * (Fintype.card B.V : ℝ) ^ 3) := by
    nlinarith [mul_nonneg (mul_nonneg hg.le (sq_nonneg (Fintype.card B.V : ℝ)))
      (sub_nonneg.mpr hdN), hA, hND]
  show 1 / (2 * (Fintype.card B.V : ℝ) ^ 3) ≤ 1 - S.lam 2
  rw [div_le_iff₀ (mul_pos two_pos (pow_pos hNpos 3))]
  exact hfin

end IdlaCyl
