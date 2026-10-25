module

public import Mathlib

@[expose] public section

set_option autoImplicit false

/-!
# Volume-preserving layered restart arithmetic

M walkers are assigned to each of ℓ layers. On filling those layers, exactly
Nℓ walkers have settled and exactly T-Nℓ remain. The lower ℓ-B layers contain
(M-N)(ℓ-B) frozen walkers. When ℓ≥3B and M≥2N, these suffice to build a B-layer
buffer using MB walkers. No stochastic coupling or shape estimate is assumed
or claimed in these arithmetic lemmas.
-/
namespace IdlaCyl
namespace Restart

def layers (M T : ℕ) : ℕ := T / M

def remaining (N M T : ℕ) : ℕ := T - N * layers M T

def deep (N M B ℓ : ℕ) : ℕ := (M-N)*(ℓ-B)

def shallow (N M B : ℕ) : ℕ := (M-N)*B

theorem batch_budget (M T : ℕ) : M * layers M T ≤ T := by
  simpa [layers, Nat.mul_comm] using Nat.div_mul_le_self T M

theorem settled_budget (N M T : ℕ) (hNM : N ≤ M) : N*layers M T ≤ T :=
  (Nat.mul_le_mul_right _ hNM).trans (batch_budget M T)

/-- Exact volume conservation; the shift is ℓ, not ℓ-B. -/
theorem volume_identity (N M T : ℕ) (hNM : N ≤ M) :
    N*layers M T + remaining N M T = T := by
  exact Nat.add_sub_of_le (settled_budget N M T hNM)

/-- No top-layer settled particles are counted twice. -/
theorem remaining_decomposition (N M B T : ℕ) (hNM : N ≤ M)
    (hB : B ≤ layers M T) :
    remaining N M T = deep N M B (layers M T) + shallow N M B +
      (T-M*layers M T) := by
  have hs : deep N M B (layers M T) + shallow N M B = (M-N)*layers M T := by
    unfold deep shallow
    rw [← Nat.mul_add, Nat.sub_add_cancel hB]
  rw [hs]
  have hMN : N*layers M T + (M-N)*layers M T = M*layers M T := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hNM]
  have hb := batch_budget M T
  have hv := volume_identity N M T hNM
  omega

/-- The deep reserve alone can fill the mixing buffer. -/
theorem deep_reserve (N M B ℓ : ℕ) (hM : 2*N ≤ M) (hℓ : 3*B ≤ ℓ) :
    M*B ≤ deep N M B ℓ := by
  have hNM : N ≤ M := by omega
  have hdiff : M ≤ 2*(M-N) := by omega
  have hℓB : 2*B ≤ ℓ-B := by omega
  calc
    M*B ≤ (2*(M-N))*B := Nat.mul_le_mul_right B hdiff
    _ = (M-N)*(2*B) := by ring
    _ ≤ (M-N)*(ℓ-B) := Nat.mul_le_mul_left (M-N) hℓB
    _ = deep N M B ℓ := rfl

theorem remaining_le (N M T : ℕ) : remaining N M T ≤ T := Nat.sub_le _ _

theorem remaining_lt (N M B T : ℕ) (hN : 0 < N) (hB : 0 < B)
    (hNM : N ≤ M) (hgo : 3*B ≤ layers M T) : remaining N M T < T := by
  have hℓ : 0 < layers M T := by omega
  have hpos : 0 < N*layers M T := Nat.mul_pos hN hℓ
  have hb := settled_budget N M T hNM
  unfold remaining
  omega

/-- A total reduction algorithm; fuel is separate from the stochastic process. -/
def reduce (N M B : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, T => (T,0)
  | fuel+1, T =>
      if 3*B ≤ layers M T then
        let z := reduce N M B fuel (remaining N M T)
        (z.1, layers M T + z.2)
      else (T,0)

/-- First component is remaining time; second component is the integer vertical shift. -/
theorem reduce_volume (N M B fuel T : ℕ) (hNM : N ≤ M) :
    T = N*(reduce N M B fuel T).2 + (reduce N M B fuel T).1 := by
  induction fuel generalizing T with
  | zero => simp [reduce]
  | succ fuel ih =>
      by_cases hgo : 3*B ≤ layers M T
      · simp only [reduce, if_pos hgo]
        have hi := ih (remaining N M T)
        have hv := volume_identity N M T hNM
        rw [Nat.mul_add]
        omega
      · simp [reduce, hgo]

theorem reduce_time_le (N M B fuel T : ℕ) : (reduce N M B fuel T).1 ≤ T := by
  induction fuel generalizing T with
  | zero => simp [reduce]
  | succ fuel ih =>
      by_cases hgo : 3*B ≤ layers M T
      · simp only [reduce, if_pos hgo]
        exact (ih _).trans (remaining_le _ _ _)
      · simp [reduce, hgo]

/-- T units of fuel suffice: every nonterminal step removes at least one particle. -/
theorem reduce_terminates (N M B fuel T : ℕ) (hN : 0 < N) (hB : 0 < B)
    (hNM : N ≤ M) (hfuel : T ≤ fuel) :
    layers M (reduce N M B fuel T).1 < 3*B := by
  induction fuel generalizing T with
  | zero =>
      have ht : T=0 := by omega
      subst T
      simp only [reduce, layers, Nat.zero_div]
      omega
  | succ fuel ih =>
      by_cases hgo : 3*B ≤ layers M T
      · simp only [reduce, if_pos hgo]
        apply ih (remaining N M T)
        have ht := remaining_lt N M B T hN hB hNM hgo
        omega
      · simp only [reduce, if_neg hgo]
        omega

/-- The terminal comparison time is below 3BM, with all integer remainders retained. -/
theorem reduce_terminal_bound (N M B T : ℕ) (hN : 0 < N) (hB : 0 < B)
    (hNM : N ≤ M) : (reduce N M B T T).1 < 3*B*M := by
  have hM : 0 < M := lt_of_lt_of_le hN hNM
  let t := (reduce N M B T T).1
  have hq : t/M < 3*B := reduce_terminates N M B T T hN hB hNM le_rfl
  have hqm : M*(t/M+1) ≤ M*(3*B) := Nat.mul_le_mul_left M (by omega)
  have hm : t % M < M := Nat.mod_lt _ hM
  have he := Nat.mod_add_div t M
  change t < 3*B*M
  nlinarith

end Restart
end IdlaCyl
