module

/-
The next settling site is independent of the past settling sites.

`paper/idla-cylinder-gff.tex:895-897`: the martingale increment
`𝒳_{k,N} = (1/√(N a_N)) ψ(X_k,Y_k)` is a martingale difference with respect to
the natural filtration `𝓕_k = σ(A(0),…,A(k))`, so the settling site
`(X_{k+1},Y_{k+1})` must be conditionally independent of `𝓕_k`, with the law of
the next walk.  The independence half of that statement, at the level of the
driving trajectories, is this lemma: under `idlaMeasure` the tuple of settling
sites `(settleSite B ω j)_{j<k}` is independent of the `k`-th walk trajectory
`ω k`.

The proof composes Mathlib's independence of the i.i.d. coordinates
(`IdlaCyl.iIndepFun_traj`) on the left with the map that reads the settling
sites from the first `k` trajectories (`IdlaCyl.measurable_settleSite_comap`,
whose extension `IdlaCyl.extendTuple` turns a `k`-tuple of trajectories into a
full `TrajSeq`).  No conditional expectation is taken here; the conditional law
of the next settle site is obtained by disintegrating this independence against
the law of `ω k`.
-/
public import IdlaCyl.Support.Independence
public import Mathlib.Probability.Independence.Basic

@[expose] public section

namespace IdlaCyl

open MeasureTheory ProbabilityTheory

theorem indep_settleSite_omega (B : Base) (k : ℕ) :
    IndepFun (fun ω : TrajSeq B => fun j : {j : ℕ // j < k} => settleSite B ω j)
      (fun ω : TrajSeq B => ω k) (idlaMeasure B) := by
  -- Independence of the first `k` coordinates from the `k`-th coordinate, which
  -- is `iIndepFun_traj` restricted to the disjoint finsets `range k` and `{k}`.
  have hraw : IndepFun
      (fun ω : TrajSeq B => fun i : {i : ℕ // i ∈ Finset.range k} => ω i)
      (fun ω : TrajSeq B => fun i : {i : ℕ // i ∈ ({k} : Finset ℕ)} => ω i)
      (idlaMeasure B) :=
    (iIndepFun_traj B).indepFun_finset (Finset.range k) {k}
      (by simp) (fun i => measurable_pi_apply i)
  -- On the left, read off the settling sites from the `k`-tuple of trajectories.
  let φ : ({i : ℕ // i ∈ Finset.range k} → (ℕ → Site B)) →
      ({j : ℕ // j < k} → Site B) :=
    fun s j => settleSite B
      (extendTuple B k (fun i : {i : ℕ // i < k} =>
        s (⟨i.1, Finset.mem_range.mpr i.2⟩ : {i : ℕ // i ∈ Finset.range k}))) j
  have hφ : Measurable φ := by
    dsimp only [φ]
    refine measurable_pi_iff.mpr fun j => ?_
    exact (measurable_settleSite B j).comp
      ((measurable_extendTuple B k).comp
        (measurable_pi_iff.mpr fun i =>
          measurable_pi_apply
            (⟨i.1, Finset.mem_range.mpr i.2⟩ : {i : ℕ // i ∈ Finset.range k})))
  -- On the right, read off the `k`-th trajectory.
  let ψ : ({i : ℕ // i ∈ ({k} : Finset ℕ)} → (ℕ → Site B)) → (ℕ → Site B) :=
    fun t => t (⟨k, by simp⟩ : {i : ℕ // i ∈ ({k} : Finset ℕ)})
  have hψ : Measurable ψ := by
    dsimp only [ψ]
    exact measurable_pi_apply (⟨k, by simp⟩ : {i : ℕ // i ∈ ({k} : Finset ℕ)})
  -- Compose, then identify the resulting functions with the statement's.
  have hleft : (φ ∘ fun ω : TrajSeq B => fun i : {i : ℕ // i ∈ Finset.range k} => ω i)
      = fun ω : TrajSeq B => fun j : {j : ℕ // j < k} => settleSite B ω j := by
    funext ω j
    dsimp only [φ, Function.comp_apply]
    show settleSite B (extendTuple B k (fun i : {i : ℕ // i < k} => ω i)) j
        = settleSite B ω j
    unfold settleSite
    have hcongr : clusterTraj B (extendTuple B k (fun i : {i : ℕ // i < k} => ω i))
          (j : ℕ) = clusterTraj B ω (j : ℕ) := by
      apply clusterTraj_congr B
      intro i hi
      exact extendTuple_apply_of_lt B _ (lt_trans hi j.2)
    rw [hcongr, extendTuple_apply_of_lt B _ j.2]
  have hright : (ψ ∘ fun ω : TrajSeq B => fun i : {i : ℕ // i ∈ ({k} : Finset ℕ)} => ω i)
      = fun ω : TrajSeq B => ω k := by
    funext ω
    dsimp only [ψ, Function.comp_apply]
  exact IndepFun.congr (hraw.comp hφ hψ) (Filter.Eventually.of_forall (fun ω => congrFun hleft ω)) (Filter.Eventually.of_forall (fun ω => congrFun hright ω))

end IdlaCyl
