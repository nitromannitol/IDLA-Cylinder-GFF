module

/-
Ordered torus spectral limits with shell multiplicity. Source: tex:502-520,
`paper/idla-cylinder-gff.tex`. Counting inequalities allow all reorderings
within a continuum norm shell.
-/
public import IdlaCyl.Support.Torus.Counting
public import IdlaCyl.Support.Torus.Energy

@[expose] public section

namespace IdlaCyl.TorusSpectrum
open Filter
open scoped BigOperators Topology

/-- The squared rescaled gap, as a scalar function of an eigenvalue. -/
def squaredGap (n : ℕ) (z : ℝ) : ℝ := (n : ℝ) ^ 2 * (2 * (1 - z))

lemma spectral_energy_count (d n : ℕ) [NeZero n] (hd : 1 ≤ d) (hn : 3 ≤ n)
    (S : SpectralData (torusBase d n hd hn)) (p : ℝ → Prop) [DecidablePred p] :
    (Finset.univ.filter (fun j : Fin (n ^ d) => p (squaredGap n (S.lam (j.val + 1))))).card =
      (Finset.univ.filter (fun m : Fin d → ZMod n => p (energy d n (centered d n m)))).card := by
  have h := spectral_count d n hd hn S (fun z => p (squaredGap n z))
  have heq (m : Fin d → ZMod n) : squaredGap n (value d n m) = energy d n (centered d n m) := by
    rw [energy_value d n hd, frequency_centered]
    rfl
  simpa only [heq] using h

lemma squaredGap_monotone (d n : ℕ) [NeZero n] (hd : 1 ≤ d) (hn : 3 ≤ n)
    (S : SpectralData (torusBase d n hd hn)) :
    Monotone (fun j : Fin (n ^ d) => squaredGap n (S.lam (j.val + 1))) := by
  intro i j hij
  have hs := S.antitone (i.val + 1) (j.val + 1) (by omega) (by exact Nat.add_le_add_right hij 1)
    (by rw [torusBase_card]; exact j.isLt)
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sub_le_sub_left hs 1) (by norm_num))
    (sq_nonneg (n : ℝ))

lemma eventually_energy_upper (d : ℕ) (R : ℕ) (u : ℝ)
    (hu : (2 * Real.pi ^ 2 / d) * R < u) :
    ∀ᶠ n : ℕ in atTop, ∀ m ∈ latticeBall d R, energy d (n + 3) m < u := by
  apply (latticeBall d R).eventually_all.mpr
  intro m hm
  have hnorm : (normSq d m : ℝ) ≤ R := by exact_mod_cast (mem_latticeBall d R m).mp hm
  have hc : 0 ≤ 2 * Real.pi ^ 2 / (d : ℝ) := by positivity
  exact (energy_limit d m).eventually_lt_const
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hnorm hc) hu)

lemma eventually_energy_lower (d : ℕ) (R r : ℕ) (l : ℝ)
    (hl : l < (2 * Real.pi ^ 2 / d) * r) :
    ∀ᶠ n : ℕ in atTop, ∀ m ∈ latticeBall d R,
      r ≤ normSq d m → l < energy d (n + 3) m := by
  apply (latticeBall d R).eventually_all.mpr
  intro m _
  by_cases hm : r ≤ normSq d m
  · have hnorm : (r : ℝ) ≤ normSq d m := by exact_mod_cast hm
    have hc : 0 ≤ 2 * Real.pi ^ 2 / (d : ℝ) := by positivity
    exact ((energy_limit d m).eventually_const_lt
      (lt_of_lt_of_le hl (mul_le_mul_of_nonneg_left hnorm hc))).mono (fun _ hn _ => hn)
  · exact Eventually.of_forall (fun _ h => (hm h).elim)

lemma eventually_eigen_upper (d : ℕ) (hd : 1 ≤ d)
    (S : (n : ℕ) → SpectralData (torusBase d (n + 3) hd (by omega)))
    (k : ℕ) (hk : 1 ≤ k) (u : ℝ)
    (hu : (2 * Real.pi ^ 2 / d) * shell d hd k < u) :
    ∀ᶠ n : ℕ in atTop, squaredGap (n + 3) ((S n).lam k) ≤ u := by
  classical
  let r := shell d hd k
  filter_upwards [eventually_energy_upper d r u hu, eventually_gt_atTop (2 * r),
    eventually_ge_atTop k] with n henergy hn hnk
  haveI : NeZero (n + 3) := ⟨by omega⟩
  have hkn : k ≤ (n + 3) ^ d :=
    (show k ≤ n + 3 by omega).trans (Nat.le_self_pow (by omega : d ≠ 0) (n + 3))
  let j : Fin ((n + 3) ^ d) := ⟨k - 1, by omega⟩
  have hs : (latticeBall d r).image (frequency d (n + 3)) ⊆
      Finset.univ.filter (fun m => energy d (n + 3) (centered d (n + 3) m) ≤ u) := by
    intro m hm
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hm
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [centered_frequency d (n + 3) r (by omega) v hv]
    exact (henergy v hv).le
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injOn (frequency_injOn_ball d (n + 3) r (by omega))] at hc
  have hcount := (shell_spec d hd k).trans hc
  rw [← spectral_energy_count d (n + 3) hd (by omega) (S n) (fun x => x ≤ u)] at hcount
  have h := le_of_count_le _ (squaredGap_monotone d (n + 3) hd (by omega) (S n)) j u
    (by simpa only [j, Nat.sub_add_cancel hk] using hcount)
  simpa only [j, Nat.sub_add_cancel hk] using h

lemma eventually_eigen_lower (d : ℕ) (hd : 1 ≤ d)
    (S : (n : ℕ) → SpectralData (torusBase d (n + 3) hd (by omega)))
    (k : ℕ) (hk : 2 ≤ k) (l : ℝ)
    (hl : l < (2 * Real.pi ^ 2 / d) * shell d hd k) :
    ∀ᶠ n : ℕ in atTop, l ≤ squaredGap (n + 3) ((S n).lam k) := by
  classical
  let r := shell d hd k
  have hr : 0 < r := shell_pos d hd k hk
  have hcpos : (0 : ℝ) < 8 / (d : ℝ) := by positivity
  obtain ⟨R, hR⟩ := exists_nat_gt (l / (8 / (d : ℝ)))
  have hRl : l < (8 / (d : ℝ)) * R := by
    exact (div_lt_iff₀ hcpos).mp hR |>.trans_eq (mul_comm _ _)
  filter_upwards [eventually_energy_lower d R r l hl, eventually_ge_atTop k] with n henergy hnk
  haveI : NeZero (n + 3) := ⟨by omega⟩
  have hkn : k ≤ (n + 3) ^ d :=
    (show k ≤ n + 3 by omega).trans (Nat.le_self_pow (by omega : d ≠ 0) (n + 3))
  let j : Fin ((n + 3) ^ d) := ⟨k - 1, by omega⟩
  let low : Finset (Fin d → ZMod (n + 3)) :=
    Finset.univ.filter (fun m => energy d (n + 3) (centered d (n + 3) m) < l)
  have hmap : ∀ m ∈ low, centered d (n + 3) m ∈ latticeBall d (r - 1) := by
    intro m hm
    have hmE := (Finset.mem_filter.mp hm).2
    have hcoerce := energy_lower d (n + 3) hd (centered d (n + 3) m) (centered_bound d (n + 3) m)
    have hball : centered d (n + 3) m ∈ latticeBall d R := by
      rw [mem_latticeBall]
      by_contra hnR
      have hNR : (R : ℝ) ≤ normSq d (centered d (n + 3) m) := by exact_mod_cast (le_of_lt (lt_of_not_ge hnR))
      have hlow := mul_le_mul_of_nonneg_left hNR hcpos.le
      linarith
    have hnorm : normSq d (centered d (n + 3) m) < r := by
      by_contra hnr
      have he := henergy _ hball (le_of_not_gt hnr)
      linarith
    rw [mem_latticeBall]
    omega
  have hc : low.card ≤ (latticeBall d (r - 1)).card :=
    Finset.card_le_card_of_injOn (centered d (n + 3)) hmap
      (fun a _ b _ h => centered_injective d (n + 3) h)
  have hcount := hc.trans_lt (shell_min d hd k (r - 1) (by omega))
  change (Finset.univ.filter (fun m => energy d (n + 3) (centered d (n + 3) m) < l)).card < k at hcount
  rw [← spectral_energy_count d (n + 3) hd (by omega) (S n) (fun x => x < l)] at hcount
  have h := le_of_count_lt _ (squaredGap_monotone d (n + 3) hd (by omega) (S n)) j l
    (by simpa only [j, Nat.sub_add_cancel (by omega : 1 ≤ k)] using hcount)
  simpa only [j, Nat.sub_add_cancel (by omega : 1 ≤ k)] using h

/-- The ordered squared torus spectrum converges to the continuum shells. -/
theorem squaredGap_limit (d : ℕ) (hd : 1 ≤ d)
    (S : (n : ℕ) → SpectralData (torusBase d (n + 3) hd (by omega)))
    (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n => squaredGap (n + 3) ((S n).lam k)) atTop
      (𝓝 ((2 * Real.pi ^ 2 / d) * shell d hd k)) := by
  apply tendsto_order.mpr
  constructor
  · intro l hl
    have hm := eventually_eigen_lower d hd S k hk
      ((l + (2 * Real.pi ^ 2 / d) * shell d hd k) / 2) (by linarith)
    exact hm.mono (fun n hn => by linarith)
  · intro u hu
    have hm := eventually_eigen_upper d hd S k (by omega)
      ((u + (2 * Real.pi ^ 2 / d) * shell d hd k) / 2) (by linarith)
    exact hm.mono (fun n hn => by linarith)

/-- The spectral assumption along tori of side `n+3`, for every lawful choice
of eigenbasis and with the positive continuum value. -/
theorem gamma_limit (d : ℕ) (hd : 1 ≤ d)
    (S : (n : ℕ) → SpectralData (torusBase d (n + 3) hd (by omega)))
    (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun n : ℕ => ((n + 3 : ℕ) : ℝ) * Real.sqrt (2 * (1 - (S n).lam k))) atTop
      (𝓝 (Real.pi * Real.sqrt (2 / (d : ℝ)) * Real.sqrt (shell d hd k))) ∧
      0 < Real.pi * Real.sqrt (2 / (d : ℝ)) * Real.sqrt (shell d hd k) := by
  refine ⟨?_, gamma_pos d hd k hk⟩
  have h := (squaredGap_limit d hd S k hk).sqrt
  have heq : Real.sqrt ((2 * Real.pi ^ 2 / d) * shell d hd k) =
      Real.pi * Real.sqrt (2 / (d : ℝ)) * Real.sqrt (shell d hd k) := by
    rw [show (2 * Real.pi ^ 2 / (d : ℝ)) * shell d hd k =
      Real.pi ^ 2 * ((2 / (d : ℝ)) * shell d hd k) by ring,
      Real.sqrt_mul (sq_nonneg Real.pi), Real.sqrt_sq Real.pi_pos.le,
      Real.sqrt_mul (by positivity : 0 ≤ 2 / (d : ℝ)), mul_assoc]
  rw [heq] at h
  apply h.congr'
  filter_upwards with n
  rw [squaredGap, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

end IdlaCyl.TorusSpectrum
