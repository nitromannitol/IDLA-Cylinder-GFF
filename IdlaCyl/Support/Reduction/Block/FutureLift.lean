module

public import IdlaCyl.Support.Reduction.Target
public import IdlaCyl.Support.Reduction.EntranceTail
public import IdlaCyl.Support.Outer.Translation
public import IdlaCyl.Support.StoppedAe

@[expose] public section

/-!
Source: paper/idla-cylinder-gff.tex, tex:1440-1453.

# Future clusters under a shifted coupling

Two driving sequences whose clusters at times `T` and `T'` differ by a vertical shift `k`
keep that relation at every later time, provided that for each later walker index `s` the
first walker, from some splice index `τ` on, is the second walker translated up by `k`, and
its prefix before `τ` stays at height at most `k`. The shift is carried through the exit
sites: a walk that stays in the translated cluster until the splice point exits the
translated cluster at the translate of the exit site of its continuation
(`exitSite'_splice`). Induction on the walker index then gives agreement at every later time
(`clusterTraj_future_shift`), and a coupling whose later walkers are almost surely spliced
inherits the endpoint bound (`future_cluster_bound`). The finiteness of each exit comes from
the first marginal, through `idlaMeasure_ae_stopped_hyp`.
-/

namespace IdlaCyl.Reduction

open MeasureTheory

/-- A vertical shift of a cluster by a nonnegative integer is the image under `outerShift`. -/
theorem shiftCluster_eq_outerShift_image (B : Base) (k : ℕ) (A : Set (Site B)) :
    shiftCluster B k A = outerShift B (k : ℤ) '' A := rfl

/-- The exit site of a walk from a translated cluster is the translate of the exit site of its
continuation, when the walk stays in the translated cluster before a splice point `τ` and
then follows the translate of `G`. -/
theorem exitSite'_splice (B : Base) (k : ℤ) (D : Set (Site B)) (F G : ℕ → Site B) (τ : ℕ)
    (hpre : ∀ i < τ, F i ∈ outerShift B k '' D)
    (hsp : ∀ n, F (τ + n) = outerShift B k (G n))
    (hf : exitTime' B (outerShift B k '' D) F ≠ ⊤) :
    exitSite' B (outerShift B k '' D) F = outerShift B k (exitSite' B D G) := by
  rw [exitSite_skip_prefix B (outerShift B k '' D) F τ hpre hf]
  have htail : (fun n => F (τ + n)) = outerShiftPath B k G := by
    funext n
    exact hsp n
  rw [htail]
  exact exitSite'_outerShift B k D G

/-- Agreement of two driving sequences' clusters, shifted by `k`, at every later time, from the
agreement at the two starting times and a splice of the later walkers for each index. -/
theorem clusterTraj_future_shift (B : Base) (k T T' : ℕ) (ω₁ ω₂ : TrajSeq B)
    (hcl : clusterTraj B ω₁ T = shiftCluster B k (clusterTraj B ω₂ T'))
    (hsplice : ∀ s : ℕ, ∃ τ : ℕ, (∀ i < τ, (ω₁ (T + s) i).2 ≤ (k : ℤ)) ∧
      ∀ n : ℕ, ω₁ (T + s) (τ + n) = outerShift B (k : ℤ) (ω₂ (T' + s) n))
    (hfin : ∀ s : ℕ, exitTime' B (clusterTraj B ω₁ (T + s)) (ω₁ (T + s)) ≠ ⊤) :
    ∀ s : ℕ, clusterTraj B ω₁ (T + s) = shiftCluster B k (clusterTraj B ω₂ (T' + s)) := by
  have hstep : ∀ (ω : TrajSeq B) (t : ℕ), clusterTraj B ω (t + 1) =
      clusterTraj B ω t ∪ {exitSite' B (clusterTraj B ω t) (ω t)} :=
    fun ω t => clusterFrom_succ B (R B 0) ω t
  have hR0 : ∀ (ω : TrajSeq B) (t : ℕ), R B 0 ⊆ clusterTraj B ω t := by
    intro ω t
    rw [clusterTraj_eq_union]
    exact Set.subset_union_left
  have hcover : ∀ (t : ℕ) (p : Site B), p.2 ≤ (k : ℤ) →
      p ∈ outerShift B (k : ℤ) '' clusterTraj B ω₂ t := by
    intro t p hp
    refine ⟨outerShift B (-(k : ℤ)) p, hR0 ω₂ t ?_, ?_⟩
    · show ((p.2 + -(k : ℤ) : ℤ) : ℝ) ≤ 0
      exact_mod_cast (show p.2 + -(k : ℤ) ≤ 0 by omega)
    · show (p.1, p.2 + -(k : ℤ) + (k : ℤ)) = p
      exact Prod.ext rfl (by show p.2 + -(k : ℤ) + (k : ℤ) = p.2; omega)
  intro s
  induction s with
  | zero => simpa only [Nat.add_zero] using hcl
  | succ s ih =>
    have hC : clusterTraj B ω₁ (T + s) = outerShift B (k : ℤ) '' clusterTraj B ω₂ (T' + s) :=
      ih.trans (shiftCluster_eq_outerShift_image B k _)
    have hkey : exitSite' B (clusterTraj B ω₁ (T + s)) (ω₁ (T + s)) =
        outerShift B (k : ℤ) (exitSite' B (clusterTraj B ω₂ (T' + s)) (ω₂ (T' + s))) := by
      obtain ⟨τ, hpre, hsp⟩ := hsplice s
      have hf : exitTime' B (outerShift B (k : ℤ) '' clusterTraj B ω₂ (T' + s)) (ω₁ (T + s)) ≠ ⊤ := by
        rw [← hC]
        exact hfin s
      rw [hC]
      exact exitSite'_splice B (k : ℤ) (clusterTraj B ω₂ (T' + s)) (ω₁ (T + s))
        (ω₂ (T' + s)) τ (fun i hi => hcover (T' + s) _ (hpre i hi)) hsp hf
    show clusterTraj B ω₁ (T + s + 1) = shiftCluster B k (clusterTraj B ω₂ (T' + s + 1))
    rw [hstep, hstep, hkey, hC, shiftCluster_eq_outerShift_image]
    rw [Set.image_union, Set.image_singleton]

/-- A coupling of the full driving laws whose endpoint agreement fails with probability at most
`ε`, and whose later walkers are almost surely spliced at every index, agrees at all later
times except on an event of the same bound. The almost-sure finiteness of the exits comes from
the first marginal, since `idlaMeasure` gives it almost surely. -/
theorem future_cluster_bound (B : Base) (T T' k : ℕ) (ε : ℝ)
    (μ : Measure (TrajSeq B × TrajSeq B))
    (hfst : μ.map (Prod.fst : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B)
    (hsp : ∀ s : ℕ, ∀ᵐ p ∂μ, ∃ τ : ℕ, (∀ i < τ, (p.1 (T + s) i).2 ≤ (k : ℤ)) ∧
      ∀ n : ℕ, p.1 (T + s) (τ + n) = outerShift B (k : ℤ) (p.2 (T' + s) n))
    (hend : μ {p | clusterTraj B p.1 T = shiftCluster B k (clusterTraj B p.2 T')}ᶜ ≤
      ENNReal.ofReal ε) :
    μ {p | ∀ s : ℕ, clusterTraj B p.1 (T + s) = shiftCluster B k (clusterTraj B p.2 (T' + s))}ᶜ
      ≤ ENNReal.ofReal ε := by
  have hfin : ∀ᵐ p ∂μ, ∀ s : ℕ, exitTime' B (clusterTraj B p.1 (T + s)) (p.1 (T + s)) ≠ ⊤ := by
    refine ae_of_ae_map (p := fun ω : TrajSeq B => ∀ s : ℕ,
      exitTime' B (clusterTraj B ω (T + s)) (ω (T + s)) ≠ ⊤) measurable_fst.aemeasurable ?_
    rw [hfst]
    filter_upwards [idlaMeasure_ae_stopped_hyp B] with ω hω
    exact fun s => hω.2.2.2 (T + s)
  have hall : ∀ᵐ p ∂μ, (∀ s : ℕ, ∃ τ : ℕ, (∀ i < τ, (p.1 (T + s) i).2 ≤ (k : ℤ)) ∧
      ∀ n : ℕ, p.1 (T + s) (τ + n) = outerShift B (k : ℤ) (p.2 (T' + s) n)) ∧
      (∀ s : ℕ, exitTime' B (clusterTraj B p.1 (T + s)) (p.1 (T + s)) ≠ ⊤) := by
    exact ((ae_all_iff.2 hsp).and hfin)
  have hsub : {p : TrajSeq B × TrajSeq B | ∀ s : ℕ, clusterTraj B p.1 (T + s) =
      shiftCluster B k (clusterTraj B p.2 (T' + s))}ᶜ ≤ᵐ[μ]
      {p : TrajSeq B × TrajSeq B | clusterTraj B p.1 T = shiftCluster B k (clusterTraj B p.2 T')}ᶜ := by
    filter_upwards [hall] with p hp hnot hend'
    exact hnot (clusterTraj_future_shift B k T T' p.1 p.2 hend' hp.1 hp.2)
  exact (measure_mono_ae hsub).trans hend

end IdlaCyl.Reduction
