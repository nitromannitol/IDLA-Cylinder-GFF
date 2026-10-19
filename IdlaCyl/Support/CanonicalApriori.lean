/-
The canonical `pr:apriori` outer tail (`tex:559-619`), part (b), on the
`TrajSeq`/`idlaMeasure` carrier.

The proof has three pieces:

* the **layer-union tail bound** (`tex:576-578`): if the cluster at time `T`
  is not contained in `R_h`, then some layer `m > h` is occupied, so
  `ℙ(A(T) ⊄ R_h) ≤ ∑_{m > h} (layer mass at level m)` — this file;
* the **binomial bound** `μ_{m+1}(T) ≤ N^{-m} C(T, m+1)` on each layer mass
  (`IdlaCyl.layerMean_le_binom`, `Support/LayerRecurrence.lean`);
* the **analytic sum bound** `∑_{m > βT/N} N^{-(m-1)} C(T,m) ≤ e^{-βT/N}` for
  `T ≥ K_0 N log N`, `β > e²` (the remaining step, reported below).

Everything is on the canonical carrier; no `Driver`/`driverLaw`/`cluster`.
-/
import IdlaCyl.Support.LayerRecurrence

namespace IdlaCyl

open MeasureTheory Filter
open scoped ENNReal BigOperators

/-- `idlaMeasure` is a probability measure, so it is `ofReal` of its own real
value on every set. -/
theorem idlaMeasure_ofReal_toReal (B : Base) (s : Set (TrajSeq B)) :
    ENNReal.ofReal ((idlaMeasure B s).toReal) = idlaMeasure B s :=
  ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top prob_le_one)

/-- The mass of a single layer, as an `ℝ≥0∞` sum of the per-site probabilities.
Because the sets `{(x,m) ∈ A(t)}` are disjoint in `x`, this is the measure of
"some site of layer `m` is occupied". -/
noncomputable def layerMass (B : Base) (t : ℕ) (m : ℤ) : ℝ≥0∞ :=
  ∑ x : B.V, idlaMeasure B {ω : TrajSeq B | (x, m) ∈ clusterTraj B ω t}

/-- `layerMass` is `ofReal` of `layerMean`. -/
theorem layerMass_eq_ofReal_layerMean (B : Base) (t : ℕ) (m : ℤ) :
    layerMass B t m = ENNReal.ofReal (layerMean B t m) := by
  rw [layerMass, layerMean,
    ENNReal.ofReal_sum_of_nonneg (fun x _ => ENNReal.toReal_nonneg)]
  exact Finset.sum_congr rfl fun x _ => (idlaMeasure_ofReal_toReal B _).symm

/-- **Layer-union tail bound.**  If the cluster leaves `R_h`, some layer `m > h`
is occupied, hence
`ℙ(A(T) ⊄ R_h) ≤ ∑_{m > h} (mass of layer m)`. -/
theorem idlaMeasure_not_subset_le_tsum (B : Base) (T : ℕ) (h : ℝ) :
    idlaMeasure B {ω : TrajSeq B | ¬ (clusterTraj B ω T ⊆ R B h)}
      ≤ ∑' m : ℤ,
          (if h < (m : ℝ) then layerMass B T m else 0) := by
  have hE : {ω : TrajSeq B | ¬ (clusterTraj B ω T ⊆ R B h)}
      = ⋃ m : ℤ, ({ω : TrajSeq B | h < (m : ℝ)}
          ∩ {ω : TrajSeq B | ∃ x : B.V, (x, m) ∈ clusterTraj B ω T}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hnot
      obtain ⟨p, hp, hp2⟩ := Set.not_subset.mp hnot
      rw [mem_R, not_le] at hp2
      exact ⟨p.2, hp2, p.1, hp⟩
    · rintro ⟨m, hm, x, hx⟩
      exact fun hsub => (not_le.mpr hm) (hsub hx)
  rw [hE]
  refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun m => ?_)
  by_cases hm : h < (m : ℝ)
  · rw [if_pos hm]
    calc idlaMeasure B ({ω : TrajSeq B | h < (m : ℝ)}
            ∩ {ω : TrajSeq B | ∃ x : B.V, (x, m) ∈ clusterTraj B ω T})
        ≤ idlaMeasure B {ω : TrajSeq B | ∃ x : B.V, (x, m) ∈ clusterTraj B ω T} :=
          measure_mono Set.inter_subset_right
      _ ≤ layerMass B T m := by
          rw [show {ω : TrajSeq B | ∃ x : B.V, (x, m) ∈ clusterTraj B ω T}
              = ⋃ x ∈ (Finset.univ : Finset B.V),
                  {ω : TrajSeq B | (x, m) ∈ clusterTraj B ω T} from by
            ext ω; simp]
          exact measure_biUnion_finset_le _ _
  · rw [if_neg hm]
    exact le_of_eq (measure_mono_null (fun ω hω => absurd hω.1 hm) measure_empty)

/-- **Layer-union tail bound, against the expected occupation.**  Combining the
previous lemma with `layerMass = ofReal layerMean`. -/
theorem idlaMeasure_not_subset_le_tsum_layerMean (B : Base) (T : ℕ) (h : ℝ) :
    idlaMeasure B {ω : TrajSeq B | ¬ (clusterTraj B ω T ⊆ R B h)}
      ≤ ∑' m : ℤ,
          (if h < (m : ℝ) then ENNReal.ofReal (layerMean B T m) else 0) := by
  refine (idlaMeasure_not_subset_le_tsum B T h).trans (ENNReal.tsum_le_tsum fun m => ?_)
  by_cases hm : h < (m : ℝ)
  · rw [if_pos hm, if_pos hm, layerMass_eq_ofReal_layerMean]
  · rw [if_neg hm, if_neg hm]

/-- **Layer-union tail bound, against the binomial estimate.**  Each occupied
layer above `h` contributes at most `N^{-(m-1)} C(T,m)` (`layerMean_le_binom`),
and only the finitely many layers `h < m ≤ T+1` can carry mass. -/
theorem idlaMeasure_not_subset_le_tsum_binom (B : Base) (hrec : External.LazyRwRecurrent)
    (T : ℕ) (h : ℝ) (hh : 0 ≤ h) :
    idlaMeasure B {ω : TrajSeq B | ¬ (clusterTraj B ω T ⊆ R B h)}
      ≤ ∑' m : ℤ, (if h < (m : ℝ) then
          ENNReal.ofReal ((1 / (B.card : ℝ)) ^ (m - 1).toNat
            * (Nat.choose T ((m - 1).toNat + 1) : ℝ))
          else 0) := by
  refine (idlaMeasure_not_subset_le_tsum_layerMean B T h).trans
    (ENNReal.tsum_le_tsum fun m => ?_)
  by_cases hm : h < (m : ℝ)
  · rw [if_pos hm, if_pos hm]
    refine ENNReal.ofReal_le_ofReal ?_
    have hm0 : 0 < m := by
      have : (0 : ℝ) < (m : ℝ) := lt_of_le_of_lt hh hm
      exact_mod_cast this
    have hcast : (((m - 1).toNat : ℤ) + 1) = m := by omega
    have h := layerMean_le_binom B hrec (m - 1).toNat T
    rwa [hcast] at h
  · rw [if_neg hm, if_neg hm]

end IdlaCyl
