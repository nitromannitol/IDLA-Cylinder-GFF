import IdlaCyl.Support.FiniteKernel
import IdlaCyl.Support.FiniteLawOperations

set_option autoImplicit false

/-!
# A stochastic entrance kernel constructed without a hitting-law hypothesis

Start at the zero matrix and iterate
  A ↦ I/4 + P A/2 + A A/4.
All entries are nonnegative and increasing. Every row and column has the same
mass c_n, where c_0=0 and c_(n+1)=(1+c_n)^2/4. This mass converges to one.
Taking entrywise limits therefore constructs a doubly stochastic matrix.

Its interpretation as the first-upper-level hitting law is an additional
path-law identification, proved in the ordinary notes but not by this module.
Neither stochasticity nor convergence is an assumed field of an object.
-/
namespace IdlaCyl
open scoped BigOperators Topology
open Filter
noncomputable section
namespace Entrance
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Table := V → V → ℝ

def nn (A : Table (V := V)) : Prop := ∀ x y, 0 ≤ A x y

def mul (A B : Table (V := V)) (x y : V) : ℝ := ∑ z, A x z * B z y

omit [DecidableEq V] in
theorem mul_nonneg (A B : Table (V := V)) (hA : nn A) (hB : nn B) :
    nn (mul A B) := by
  intro x y
  exact Finset.sum_nonneg (fun z _ => _root_.mul_nonneg (hA x z) (hB z y))

omit [DecidableEq V] in
theorem mul_row (A B : Table (V := V)) (a b : ℝ)
    (hA : ∀ x, ∑ y, A x y = a) (hB : ∀ x, ∑ y, B x y = b) (x : V) :
    (∑ y, mul A B x y) = a*b := by
  unfold mul
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hB, ← Finset.sum_mul, hA]

omit [DecidableEq V] in
theorem mul_column (A B : Table (V := V)) (a b : ℝ)
    (hA : ∀ y, ∑ x, A x y = a) (hB : ∀ y, ∑ x, B x y = b) (y : V) :
    (∑ x, mul A B x y) = a*b := by
  unfold mul
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, hA, ← Finset.mul_sum, hB]

def mass : ℕ → ℝ
  | 0 => 0
  | n+1 => (1+mass n)^2/4

@[simp] theorem mass_zero : mass 0=0 := rfl
@[simp] theorem mass_succ (n : ℕ) : mass (n+1)=(1+mass n)^2/4 := rfl

theorem mass_bounds (n : ℕ) : 0 ≤ mass n ∧ mass n ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [mass_succ]
      constructor
      · positivity
      · nlinarith [ih.1, ih.2]

theorem mass_step_le (n : ℕ) : mass n ≤ mass (n+1) := by
  rw [mass_succ]
  nlinarith [sq_nonneg (1-mass n)]

theorem mass_monotone : Monotone mass := monotone_nat_of_le_succ mass_step_le

theorem mass_tendsto_one : Tendsto mass atTop (𝓝 (1:ℝ)) := by
  have hb : BddAbove (Set.range mass) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n,rfl⟩
    exact (mass_bounds n).2
  obtain ⟨l,hl⟩ : ∃ l : ℝ, Tendsto mass atTop (𝓝 l) :=
    ⟨_, tendsto_atTop_ciSup mass_monotone hb⟩
  have hn : Tendsto (fun n => mass (n+1)) atTop (𝓝 l) :=
    (tendsto_add_atTop_iff_nat 1).mpr hl
  have hr : Tendsto (fun n => (1+mass n)^2/4) atTop (𝓝 ((1+l)^2/4)) :=
    ((tendsto_const_nhds.add hl).pow 2).div_const 4
  have he : l=(1+l)^2/4 := tendsto_nhds_unique hn (by simpa only [mass_succ] using hr)
  have hs : (l-1)^2=0 := by nlinarith
  have hl1 : l=1 := by have := sq_eq_zero_iff.mp hs; linarith
  simpa only [hl1] using hl

/-- Explicit error bound for the scalar iteration, including its initial state. -/
theorem mass_error_rate (n : ℕ) : 1-mass n ≤ 4/((n:ℝ)+4) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have hn : (0:ℝ) ≤ (n:ℝ) := by positivity
      have hd : (0:ℝ) < (n:ℝ)+4 := by positivity
      let u : ℝ := 4/((n:ℝ)+4)
      change 1-mass n ≤ u at ih
      have hu1 : u ≤ 1 := by
        change 4/((n:ℝ)+4) ≤ 1
        apply (div_le_iff₀ hd).mpr
        linarith
      have hdu : ((n:ℝ)+4)*u=4 := by
        dsimp [u]
        field_simp [ne_of_gt hd]
      have hdu2 := congrArg (fun z : ℝ => z*u) hdu
      have hb := mass_bounds n
      have hmono : (1-mass n)-(1-mass n)^2/4 ≤ u-u^2/4 := by
        have hp := _root_.mul_nonneg (sub_nonneg.mpr ih)
          (show 0 ≤ 1-((1-mass n)+u)/4 by linarith)
        nlinarith
      have hnext : u-u^2/4 ≤ 4/((n:ℝ)+5) := by
        apply (le_div_iff₀ (show (0:ℝ) < (n:ℝ)+5 by positivity)).mpr
        nlinarith [sq_nonneg u]
      calc
        1-mass (n+1) = (1-mass n)-(1-mass n)^2/4 := by
          rw [mass_succ]
          ring
        _ ≤ u-u^2/4 := hmono
        _ ≤ 4/((n:ℝ)+5) := hnext
        _ = 4/(((n+1:ℕ):ℝ)+4) := by (congr 1; push_cast; ring)

def step (P : SymmetricKernel V) (A : Table (V := V)) (x y : V) : ℝ :=
  (if x=y then (1:ℝ)/4 else 0) + mul P.weight A x y/2 + mul A A x y/4

def approx (P : SymmetricKernel V) : ℕ → Table (V := V)
  | 0 => fun _ _ => 0
  | n+1 => step P (approx P n)

@[simp] theorem approx_zero (P : SymmetricKernel V) (x y : V) : approx P 0 x y=0 := rfl
@[simp] theorem approx_succ (P : SymmetricKernel V) (n : ℕ) :
    approx P (n+1)=step P (approx P n) := rfl

theorem step_nonneg (P : SymmetricKernel V) (A : Table (V := V)) (hA : nn A) :
    nn (step P A) := by
  intro x y
  have hp := mul_nonneg P.weight A P.nonneg hA x y
  have ha := mul_nonneg A A hA hA x y
  unfold step
  split_ifs <;> linarith

theorem approx_nonneg (P : SymmetricKernel V) (n : ℕ) : nn (approx P n) := by
  induction n with
  | zero => intro x y; exact le_rfl
  | succ n ih => exact step_nonneg P _ ih

theorem step_row (P : SymmetricKernel V) (A : Table (V := V)) (c : ℝ)
    (hA : ∀ x, ∑ y, A x y=c) (x : V) :
    (∑ y, step P A x y)=(1+c)^2/4 := by
  unfold step
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_div, ← Finset.sum_div]
  have hd : (∑ y, if x=y then (1:ℝ)/4 else 0)=(1:ℝ)/4 := by simp
  rw [hd, mul_row _ _ 1 c P.row_sum hA, mul_row _ _ c c hA hA]
  ring

theorem step_column (P : SymmetricKernel V) (A : Table (V := V)) (c : ℝ)
    (hA : ∀ y, ∑ x, A x y=c) (y : V) :
    (∑ x, step P A x y)=(1+c)^2/4 := by
  unfold step
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_div, ← Finset.sum_div]
  have hd : (∑ x, if x=y then (1:ℝ)/4 else 0)=(1:ℝ)/4 := by simp
  rw [hd, mul_column _ _ 1 c P.col_sum hA, mul_column _ _ c c hA hA]
  ring

theorem approx_row (P : SymmetricKernel V) (n : ℕ) (x : V) :
    (∑ y, approx P n x y)=mass n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      exact step_row P (approx P n) (mass n) ih x

theorem approx_column (P : SymmetricKernel V) (n : ℕ) (y : V) :
    (∑ x, approx P n x y)=mass n := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
      exact step_column P (approx P n) (mass n) ih y

theorem step_mono (P : SymmetricKernel V) (A B : Table (V := V))
    (hA : nn A) (hB : nn B) (hAB : ∀ x y, A x y ≤ B x y) :
    ∀ x y, step P A x y ≤ step P B x y := by
  intro x y
  have hp : mul P.weight A x y ≤ mul P.weight B x y := by
    apply Finset.sum_le_sum
    intro z _
    exact mul_le_mul_of_nonneg_left (hAB z y) (P.nonneg x z)
  have hq : mul A A x y ≤ mul B B x y := by
    apply Finset.sum_le_sum
    intro z _
    exact mul_le_mul (hAB x z) (hAB z y) (hA z y) (hB x z)
  unfold step
  linarith

theorem approx_step_le (P : SymmetricKernel V) (n : ℕ) :
    ∀ x y, approx P n x y ≤ approx P (n+1) x y := by
  induction n with
  | zero => exact approx_nonneg P 1
  | succ n ih =>
      exact step_mono P _ _ (approx_nonneg P n) (approx_nonneg P (n+1)) ih

theorem approx_monotone (P : SymmetricKernel V) (x y : V) :
    Monotone (fun n => approx P n x y) :=
  monotone_nat_of_le_succ (fun n => approx_step_le P n x y)

theorem approx_le_one (P : SymmetricKernel V) (n : ℕ) (x y : V) :
    approx P n x y ≤ 1 := by
  have hs : approx P n x y ≤ ∑ z, approx P n x z :=
    Finset.single_le_sum (fun z _ => approx_nonneg P n x z) (Finset.mem_univ y)
  rw [approx_row] at hs
  exact hs.trans (mass_bounds n).2

theorem entry_converges (P : SymmetricKernel V) (x y : V) :
    ∃ l : ℝ, Tendsto (fun n => approx P n x y) atTop (𝓝 l) := by
  have hb : BddAbove (Set.range fun n => approx P n x y) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n,rfl⟩
    exact approx_le_one P n x y
  exact ⟨_, tendsto_atTop_ciSup (approx_monotone P x y) hb⟩

def entrance (P : SymmetricKernel V) (x y : V) : ℝ :=
  Classical.choose (entry_converges P x y)

theorem entrance_tendsto (P : SymmetricKernel V) (x y : V) :
    Tendsto (fun n => approx P n x y) atTop (𝓝 (entrance P x y)) :=
  Classical.choose_spec (entry_converges P x y)

theorem entrance_nonneg (P : SymmetricKernel V) (x y : V) : 0 ≤ entrance P x y :=
  ge_of_tendsto (entrance_tendsto P x y)
    (Filter.Eventually.of_forall (fun n => approx_nonneg P n x y))

theorem entrance_row (P : SymmetricKernel V) (x : V) :
    (∑ y, entrance P x y)=1 := by
  have hs : Tendsto (fun n => ∑ y, approx P n x y) atTop
      (𝓝 (∑ y, entrance P x y)) :=
    tendsto_finsetSum _ (fun y _ => entrance_tendsto P x y)
  have hm : Tendsto (fun n => ∑ y, approx P n x y) atTop (𝓝 (1:ℝ)) := by
    simpa only [approx_row] using mass_tendsto_one
  exact tendsto_nhds_unique hs hm

theorem entrance_column (P : SymmetricKernel V) (y : V) :
    (∑ x, entrance P x y)=1 := by
  have hs : Tendsto (fun n => ∑ x, approx P n x y) atTop
      (𝓝 (∑ x, entrance P x y)) :=
    tendsto_finsetSum _ (fun x _ => entrance_tendsto P x y)
  have hm : Tendsto (fun n => ∑ x, approx P n x y) atTop (𝓝 (1:ℝ)) := by
    simpa only [approx_column] using mass_tendsto_one
  exact tendsto_nhds_unique hs hm

theorem step_tendsto (P : SymmetricKernel V) (x y : V) :
    Tendsto (fun n => step P (approx P n) x y) atTop
      (𝓝 (step P (entrance P) x y)) := by
  have hp : Tendsto (fun n => mul P.weight (approx P n) x y) atTop
      (𝓝 (mul P.weight (entrance P) x y)) := by
    apply tendsto_finsetSum
    intro z _
    exact tendsto_const_nhds.mul (entrance_tendsto P z y)
  have hq : Tendsto (fun n => mul (approx P n) (approx P n) x y) atTop
      (𝓝 (mul (entrance P) (entrance P) x y)) := by
    apply tendsto_finsetSum
    intro z _
    exact (entrance_tendsto P x z).mul (entrance_tendsto P z y)
  exact (tendsto_const_nhds.add (hp.div_const 2)).add (hq.div_const 4)

/-- The constructed stochastic matrix solves the first-step quadratic equation. -/
theorem entrance_fixedpoint (P : SymmetricKernel V) (x y : V) :
    entrance P x y = step P (entrance P) x y := by
  have hs : Tendsto (fun n => approx P (n+1) x y) atTop (𝓝 (entrance P x y)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (entrance_tendsto P x y)
  exact tendsto_nhds_unique hs (step_tendsto P x y)

theorem approx_le_supersolution (P : SymmetricKernel V) (A : Table (V := V))
    (hA : nn A) (hs : ∀ x y, step P A x y ≤ A x y) (n : ℕ) :
    ∀ x y, approx P n x y ≤ A x y := by
  induction n with
  | zero => exact hA
  | succ n ih =>
      intro x y
      exact (step_mono P _ _ (approx_nonneg P n) hA ih x y).trans (hs x y)

/-- Minimality follows from the iteration; it is not assumed for a chosen root. -/
theorem entrance_le_supersolution (P : SymmetricKernel V) (A : Table (V := V))
    (hA : nn A) (hs : ∀ x y, step P A x y ≤ A x y) (x y : V) :
    entrance P x y ≤ A x y :=
  le_of_tendsto (entrance_tendsto P x y)
    (Filter.Eventually.of_forall (fun n => approx_le_supersolution P A hA hs n x y))

theorem approx_le_entrance (P : SymmetricKernel V) (n : ℕ) (x y : V) :
    approx P n x y ≤ entrance P x y :=
  approx_le_supersolution P (entrance P) (entrance_nonneg P)
    (fun a b => (entrance_fixedpoint P a b).symm.le) n x y

/-- The entire row error equals the scalar missing mass. -/
theorem row_l1_error (P : SymmetricKernel V) (n : ℕ) (x : V) :
    (∑ y, |entrance P x y-approx P n x y|) = 1-mass n := by
  calc
    (∑ y, |entrance P x y-approx P n x y|) =
        ∑ y, (entrance P x y-approx P n x y) := by
      apply Finset.sum_congr rfl
      intro y _
      exact abs_of_nonneg (sub_nonneg.mpr (approx_le_entrance P n x y))
    _ = 1-mass n := by
      rw [Finset.sum_sub_distrib, entrance_row, approx_row]

theorem row_l1_error_rate (P : SymmetricKernel V) (n : ℕ) (x : V) :
    (∑ y, |entrance P x y-approx P n x y|) ≤ 4/((n:ℝ)+4) := by
  rw [row_l1_error]
  exact mass_error_rate n

/-- The horizontal entrance law is normalized by the proved recurrence limit. -/
def entranceLaw (P : SymmetricKernel V) (x : V) : FiniteLaw V where
  weight := entrance P x
  nonneg := entrance_nonneg P x
  total := entrance_row P x

end Entrance
end
end IdlaCyl
