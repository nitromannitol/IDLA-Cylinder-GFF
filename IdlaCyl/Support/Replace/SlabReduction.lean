import IdlaCyl.Support.Replace.SlabMean
import IdlaCyl.Definitions.ShapeEvent

/-!
Reduction of the discrepancy pairing to the finite slab on the shape event
(`tex:791-803`). Lower full layers cancel by zero horizontal average.
-/

namespace IdlaCyl.Replace

open Defs
open scoped BigOperators

variable (B : Base)

/-- Integer heights in the shape slab `R_{h+d} \ R_{⌊h-d⌋}`. -/
noncomputable def slabHeights (T : ℕ) (d : ℝ) : Finset ℤ :=
  Finset.Ioc ⌊(T : ℝ) / (B.card : ℝ) - d⌋ ⌊(T : ℝ) / (B.card : ℝ) + d⌋

/-- For a cluster bounded above by an integer layer, its positive part can be
summed over a fixed rectangle using its occupation indicator. -/
theorem sum_clusterPlus_eq_slabSum_Icc (ω : TrajSeq B) (T : ℕ) (H : ℤ)
    (hupper : clusterTraj B ω T ⊆ R B (H : ℝ)) (f : Site B → ℝ) :
    (∑ p ∈ clusterPlusFinset B ω T, f p) = slabSum B T (Finset.Icc 1 H) f ω := by
  classical
  let Q : Finset (Site B) := Finset.univ.product (Finset.Icc 1 H)
  have hsub : clusterPlusFinset B ω T ⊆ Q := by
    intro p hp
    have hp1 := (mem_clusterPlusFinset_iff B ω T p).mp hp |>.2
    have hpH := hupper (mem_clusterPlusFinset_cluster B ω T hp)
    have hpH' : p.2 ≤ H := by rw [mem_R] at hpH; exact_mod_cast hpH
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_Icc.mpr ⟨hp1, hpH'⟩⟩
  have hsum : (∑ p ∈ clusterPlusFinset B ω T, f p) =
      ∑ p ∈ Q, if p ∈ clusterTraj B ω T then f p else 0 := by
    calc
      _ = ∑ p ∈ clusterPlusFinset B ω T,
          if p ∈ clusterTraj B ω T then f p else 0 :=
        Finset.sum_congr rfl fun p hp => (if_pos
          (mem_clusterPlusFinset_cluster B ω T hp)).symm
      _ = _ := Finset.sum_subset hsub (fun p hp hn => by
        have hp1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).2).1
        have hnc : p ∉ clusterTraj B ω T := fun hc =>
          hn ((mem_clusterPlusFinset_iff_cluster B ω T hp1).mpr hc)
        exact if_neg hnc)
  rw [hsum]
  unfold Q slabSum
  exact (Finset.sum_product (Finset.univ : Finset B.V) (Finset.Icc (1 : ℤ) H)
    (fun p : Site B => if p ∈ clusterTraj B ω T then f p else 0)).trans Finset.sum_comm

/-- Full layers below `L` vanish, leaving exactly the occupation sum in
`L < y ≤ H`. This identity is pathwise. -/
theorem pairing_eq_slabSum (ω : TrajSeq B) (T : ℕ) (L H : ℤ)
    (hL : 0 ≤ L) (hlower : R B (L : ℝ) ⊆ clusterTraj B ω T)
    (hupper : clusterTraj B ω T ⊆ R B (H : ℝ)) (f : Site B → ℝ)
    (hf : ZeroHorizontalAverage B f) :
    pairingTraj B ω T f = slabSum B T (Finset.Ioc L H) f ω := by
  classical
  have hLH : L ≤ H := by
    have hmem : (B.pt, L) ∈ R B (L : ℝ) := by rw [mem_R]
    have hb := hupper (hlower hmem)
    rw [mem_R] at hb
    exact_mod_cast hb
  rw [pairingTraj_eq_sum_clusterPlus B ω T f hf,
    sum_clusterPlus_eq_slabSum_Icc B ω T H hupper f]
  have hsplit : Finset.Icc (1 : ℤ) H = Finset.Icc 1 L ∪ Finset.Ioc L H := by
    ext y
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdis : Disjoint (Finset.Icc (1 : ℤ) L) (Finset.Ioc L H) := by
    apply Finset.disjoint_left.mpr
    intro y hy hy'
    have := (Finset.mem_Icc.mp hy).2
    have := (Finset.mem_Ioc.mp hy').1
    omega
  unfold slabSum
  rw [hsplit, Finset.sum_union hdis]
  have hzero : (∑ y ∈ Finset.Icc (1 : ℤ) L, ∑ x : B.V,
      if (x, y) ∈ clusterTraj B ω T then f (x, y) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    have hmem (x : B.V) : (x, y) ∈ clusterTraj B ω T :=
      hlower (by change (y : ℝ) ≤ (L : ℝ); exact_mod_cast (Finset.mem_Icc.mp hy).2)
    simp only [hmem, if_true, hf y]
  rw [hzero, zero_add]

/-- On the literal shape event the pairing equals the finite-slab sum, once
the lower edge of the slab is nonnegative (`tex:791-803`). -/
theorem pairing_eq_slabSum_on_event (ω : TrajSeq B) (T : ℕ) (d : ℝ)
    (hL : 0 ≤ ⌊(T : ℝ) / (B.card : ℝ) - d⌋)
    (hω : ω ∈ eventAt B T d) (f : Site B → ℝ) (hf : ZeroHorizontalAverage B f) :
    pairingTraj B ω T f = slabSum B T (slabHeights B T d) f ω := by
  apply pairing_eq_slabSum B ω T _ _ hL hω.1 _ f hf
  intro p hp
  change (p.2 : ℝ) ≤ (⌊(T : ℝ) / (B.card : ℝ) + d⌋ : ℤ)
  exact_mod_cast Int.le_floor.mpr (hω.2 hp)

end IdlaCyl.Replace
