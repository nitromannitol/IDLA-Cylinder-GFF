/-
Every entry of some power of the lazy base kernel is positive.

`paper/idla-cylinder-gff.tex:229-237`: the base graph `V_N` is connected and
`P_N` is its lazy simple random walk, `P_N(x,x') = 1/(2d)` if `x ~ x'`,
`1/2` if `x = x'`, and `0` otherwise.

Connectedness gives a path of length `< N` between any two vertices, and
laziness lets the walk wait, so `P_N^m(x,y) ≥ (1/(2d))^m` for `m = N`.  This
is the positivity input to the obligation `IdlaCyl.mixingTime_spec`.
-/
import IdlaCyl.Support.Spectral

namespace IdlaCyl.Obligation

open IdlaCyl

/-- Every entry of `P_N^n` is nonnegative. -/
theorem basePow_nonneg (B : Base) (n : ℕ) (x y : B.V) : 0 ≤ basePow B n x y := by
  induction n generalizing y with
  | zero =>
      simp only [basePow]
      split_ifs <;> norm_num
  | succ n ih =>
      simp only [basePow]
      exact Finset.sum_nonneg fun z _ => mul_nonneg (ih z) (B.P_nonneg z y)

/-- One summand of the Chapman-Kolmogorov sum is a lower bound. -/
theorem basePow_pos_uniform_step (B : Base) (n : ℕ) (x z y : B.V) :
    basePow B n x z * B.P z y ≤ basePow B (n + 1) x y := by
  show _ ≤ ∑ w : B.V, basePow B n x w * B.P w y
  exact Finset.single_le_sum (f := fun w => basePow B n x w * B.P w y)
    (fun w _ => mul_nonneg (basePow_nonneg B n x w) (B.P_nonneg w y))
    (Finset.mem_univ z)

/-- The constants `c = 1/(2d)`: positive, at most `1/2`, and the values of `P`
on an edge and on the diagonal. -/
theorem basePow_pos_uniform_const (B : Base) :
    0 < 1 / (2 * (B.deg : ℝ)) ∧ 1 / (2 * (B.deg : ℝ)) ≤ 1 / 2 ∧
      (∀ z y : B.V, B.graph.Adj z y → B.P z y = 1 / (2 * (B.deg : ℝ))) ∧
      (∀ y : B.V, B.P y y = 1 / 2) := by
  have hd : (0 : ℝ) < B.deg := Nat.cast_pos.mpr B.deg_pos
  have hd1 : (1 : ℝ) ≤ B.deg := by exact_mod_cast B.deg_pos
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  · intro z y h
    simp [Base.P, h]
  · intro y
    simp [Base.P]

/-- A walk of length `≤ n` from `x` to `y` gives `c ^ n ≤ P_N^n(x,y)`. -/
theorem basePow_pos_uniform_walk (B : Base) (n : ℕ) :
    ∀ (x y : B.V) (w : B.graph.Walk x y), w.length ≤ n →
      (1 / (2 * (B.deg : ℝ))) ^ n ≤ basePow B n x y := by
  obtain ⟨hc0, hc2, hadj, hdiag⟩ := basePow_pos_uniform_const B
  induction n with
  | zero =>
      intro x y w hw
      have hxy : x = y := w.eq_of_length_eq_zero (Nat.le_zero.mp hw)
      subst hxy
      simp [basePow]
  | succ n ih =>
      intro x y w hw
      rcases Nat.lt_or_ge w.length (n + 1) with hlt | hge
      · have h1 := ih x y w (Nat.lt_succ_iff.mp hlt)
        have h2 := basePow_pos_uniform_step B n x y y
        rw [hdiag y] at h2
        calc (1 / (2 * (B.deg : ℝ))) ^ (n + 1)
            = (1 / (2 * (B.deg : ℝ))) ^ n * (1 / (2 * (B.deg : ℝ))) := pow_succ _ _
          _ ≤ basePow B n x y * (1 / 2) :=
              mul_le_mul h1 hc2 hc0.le (basePow_nonneg B n x y)
          _ ≤ basePow B (n + 1) x y := h2
      · have hlen : w.reverse.length = n + 1 := by
          rw [SimpleGraph.Walk.length_reverse]; omega
        cases hr : w.reverse with
        | nil => rw [hr] at hlen; simp at hlen
        | cons h p =>
            rename_i z
            rw [hr] at hlen
            have hp : p.length = n := by simpa using hlen
            have h1 := ih x z p.reverse (by rw [SimpleGraph.Walk.length_reverse]; omega)
            have h2 := basePow_pos_uniform_step B n x z y
            rw [hadj z y h.symm] at h2
            calc (1 / (2 * (B.deg : ℝ))) ^ (n + 1)
                = (1 / (2 * (B.deg : ℝ))) ^ n * (1 / (2 * (B.deg : ℝ))) := pow_succ _ _
              _ ≤ basePow B n x z * (1 / (2 * (B.deg : ℝ))) :=
                  mul_le_mul_of_nonneg_right h1 hc0.le
              _ ≤ basePow B (n + 1) x y := h2

/-- Some power of the lazy kernel has every entry bounded below by a positive
constant. -/
theorem basePow_pos_uniform (B : Base) :
    ∃ m : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ x y : B.V, δ ≤ basePow B m x y := by
  obtain ⟨hc0, -, -, -⟩ := basePow_pos_uniform_const B
  refine ⟨Fintype.card B.V, (1 / (2 * (B.deg : ℝ))) ^ Fintype.card B.V,
    pow_pos hc0 _, fun x y => ?_⟩
  obtain ⟨w⟩ := B.connected.preconnected x y
  exact basePow_pos_uniform_walk B _ x y w.bypass
    (w.bypass_isPath.length_lt.le)

end IdlaCyl.Obligation
