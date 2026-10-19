/-
Block batches of stopped releases: pathwise growth, batch law, and queue accounting.
Source: paper/idla-cylinder-gff.tex, tex:246-265 (exit locations of stopped walks).
-/
import IdlaCyl.Support.Reduction.Block.BlockPause
import IdlaCyl.Support.Reduction.FreezeBatchLaw
import IdlaCyl.Support.Reduction.LayerCounts
import IdlaCyl.Support.Reduction.SeedGrowth
import IdlaCyl.Support.Admissible
import IdlaCyl.Support.CylGraph
import IdlaCyl.Support.StoppedAe

/-!
The block batch of `M` stopped releases is realized by independent uniform walks, one per
release, each stopped at its first exit from the occupied sites strictly below the stopping
height `h`, followed by the settle-first/duplicate-second coupon update.

The file proves three things. First, the pathwise growth `blockGrow` has the law of the
abstract batch kernel `blockBatch` under the infinite product `idlaMeasure`. Second, every
step adds one exit site: the seed grows by that site, and the queue gains it exactly when
it was already occupied. Third, when the seed starts at the rectangle `R_a` and ends at
the rectangle `R_h` with `h = a + H`, the queue gains exactly `M - N H` entries, all at
height `h`, where `N` is the number of sites per layer.
-/

attribute [local instance] Classical.propDecidable

namespace IdlaCyl.Reduction

open MeasureTheory ProbabilityTheory

/-- The visible block state after `n` independent stopped releases, each stopped at its first
exit from the occupied sites strictly below height `h`, with each exit site settled or
duplicated by `freezeCoupon`. -/
noncomputable def blockGrow (B : Base) (h : ℤ) (s : ResumeState B) (ω : TrajSeq B) :
    ℕ → ResumeState B
  | 0 => s
  | n + 1 => freezeCoupon B (blockGrow B h s ω n)
      (exitSite' B (resumeSeed B (blockGrow B h s ω n).1 ∩ R B ((h : ℝ) - 1)) (ω n))

/-- The recursion step of `blockGrow`, unfolded. -/
theorem blockGrow_succ (B : Base) (h : ℤ) (s : ResumeState B) (ω : TrajSeq B) (n : ℕ) :
    blockGrow B h s ω (n + 1) = freezeCoupon B (blockGrow B h s ω n)
      (exitSite' B (resumeSeed B (blockGrow B h s ω n).1 ∩ R B ((h : ℝ) - 1)) (ω n)) :=
  rfl

/-- One block step from a fixed state is a measurable function of the released walk. -/
theorem measurable_blockStep (B : Base) (h : ℤ) (t : ResumeState B) :
    Measurable (fun X : ℕ → Site B =>
      freezeCoupon B t (exitSite' B (resumeSeed B t.1 ∩ R B ((h : ℝ) - 1)) X)) :=
  (measurable_of_countable (freezeCoupon B t)).comp (measurable_exitSite' B _)

/-- The block state is a measurable function of the released walks. -/
theorem measurable_blockGrow (B : Base) (h : ℤ) (s : ResumeState B) (n : ℕ) :
    Measurable (fun ω => blockGrow B h s ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hu : Measurable (fun sX : ResumeState B × (ℕ → Site B) =>
          freezeCoupon B sX.1 (exitSite' B (resumeSeed B sX.1.1 ∩ R B ((h : ℝ) - 1)) sX.2)) := by
        apply measurable_from_prod_countable_right
        intro t
        exact measurable_blockStep B h t
      have hc : Measurable (fun ω : TrajSeq B => (blockGrow B h s ω n, ω n)) :=
        ih.prodMk (measurable_pi_apply n)
      have hfun : (fun ω : TrajSeq B => blockGrow B h s ω (n + 1)) =
          (fun sX : ResumeState B × (ℕ → Site B) =>
            freezeCoupon B sX.1 (exitSite' B (resumeSeed B sX.1.1 ∩ R B ((h : ℝ) - 1)) sX.2)) ∘
          (fun ω : TrajSeq B => (blockGrow B h s ω n, ω n)) :=
        funext fun ω => rfl
      rw [hfun]
      exact hu.comp hc

/-- The block state after `n` releases depends only on the first `n` walks. -/
theorem blockGrow_congr (B : Base) (h : ℤ) (s : ResumeState B) (ω η : TrajSeq B)
    (n : ℕ) (hn : ∀ i < n, ω i = η i) : blockGrow B h s ω n = blockGrow B h s η n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change freezeCoupon B (blockGrow B h s ω n)
        (exitSite' B (resumeSeed B (blockGrow B h s ω n).1 ∩ R B ((h : ℝ) - 1)) (ω n)) = _
      rw [ih (fun i hi => hn i (by omega)), hn n (by omega)]
      rfl

/-- The finite independent-walk construction has the prescribed fresh-step transition. -/
theorem blockGrow_law_succ (B : Base) (h : ℤ) (s : ResumeState B) (n : ℕ) :
    (idlaMeasure B).map (fun ω => blockGrow B h s ω (n + 1)) =
      ((idlaMeasure B).map (fun ω => blockGrow B h s ω n)).bind (freezeBlockStep B h) := by
  let step := fun sX : ResumeState B × (ℕ → Site B) =>
    freezeCoupon B sX.1 (exitSite' B (resumeSeed B sX.1.1 ∩ R B ((h : ℝ) - 1)) sX.2)
  have hs : Measurable step := by
    apply measurable_from_prod_countable_right
    intro t
    exact measurable_blockStep B h t
  have hj := IndepFun.map_prod_eq_prod_map_map
    (measurable_blockGrow B h s n).aemeasurable (measurable_pi_apply n).aemeasurable
    (resume_indep_past B (fun _ => walkLawUniform B) n _ (measurable_blockGrow B h s n)
      (fun ω η hωη => blockGrow_congr B h s ω η n hωη))
  rw [Measure.infinitePi_map_eval] at hj
  change (idlaMeasure B).map (fun ω => (blockGrow B h s ω n, ω n)) =
    ((idlaMeasure B).map (fun ω => blockGrow B h s ω n)).prod (walkLawUniform B) at hj
  calc
    _ = ((idlaMeasure B).map (fun ω => (blockGrow B h s ω n, ω n))).map step :=
      (Measure.map_map hs ((measurable_blockGrow B h s n).prodMk
        (measurable_pi_apply n))).symm
    _ = (((idlaMeasure B).map (fun ω => blockGrow B h s ω n)).prod
        (walkLawUniform B)).map step := by rw [hj]
    _ = _ := resume_prod_map _ _ step hs

/-- The first-step recursion of `blockBatch` also has a last-step recursion. -/
theorem blockBatch_succ_right (B : Base) (h : ℤ) (M : ℕ) (s : ResumeState B) :
    (blockBatch B h M s).bind (freezeBlockStep B h) = blockBatch B h (M + 1) s := by
  induction M generalizing s with
  | zero =>
      change (Measure.dirac s).bind (freezeBlockStep B h) =
        (freezeBlockStep B h s).bind Measure.dirac
      rw [Measure.dirac_bind (measurable_of_countable _), Measure.bind_dirac]
  | succ M ih =>
      change ((freezeBlockStep B h s).bind (blockBatch B h M)).bind (freezeBlockStep B h) =
        (freezeBlockStep B h s).bind (blockBatch B h (M + 1))
      rw [Measure.bind_bind (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable]
      congr 1
      funext t
      exact ih t

/-- **The pathwise block batch has the law of the abstract block batch kernel.** -/
theorem blockBatch_law (B : Base) (h : ℤ) (M : ℕ) (s : ResumeState B) :
    (idlaMeasure B).map (fun ω => blockGrow B h s ω M) = blockBatch B h M s := by
  induction M with
  | zero => simp only [blockGrow, Measure.map_const, measure_univ, one_smul, blockBatch]
  | succ M ih => rw [blockGrow_law_succ, ih, blockBatch_succ_right]

/-- A block release never removes an occupied site. -/
theorem resumeSeed_subset_blockGrow (B : Base) (h : ℤ) (s : ResumeState B) (ω : TrajSeq B)
    (n : ℕ) : resumeSeed B s.1 ⊆ resumeSeed B (blockGrow B h s ω n).1 := by
  induction n with
  | zero => exact Set.Subset.rfl
  | succ n ih => exact ih.trans (freezeCoupon_seed_mono B _ _)

/-- Each step adds the exit site to the seed. -/
theorem blockGrow_succ_seed (B : Base) (h : ℤ) (s : ResumeState B) (ω : TrajSeq B) (n : ℕ) :
    resumeSeed B (blockGrow B h s ω (n + 1)).1 = resumeSeed B (blockGrow B h s ω n).1 ∪
      {exitSite' B (resumeSeed B (blockGrow B h s ω n).1 ∩ R B ((h : ℝ) - 1)) (ω n)} := by
  rw [blockGrow_succ]
  unfold freezeCoupon
  split_ifs with hz
  · dsimp only
    exact (Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr hz)).symm
  · dsimp only
    exact resumeSeed_insert B _ _

/-- Queue gain of a single step: the queue is unchanged when the exit site is new, and gains
exactly that exit site when it was already occupied. -/
theorem freezeCoupon_queue_of_mem (B : Base) (s : ResumeState B) (z : Site B)
    (hz : z ∈ resumeSeed B s.1) : (freezeCoupon B s z).2 = s.2 ++ [z] := by
  unfold freezeCoupon
  rw [if_pos hz]

/-- A new settled site leaves the queue unchanged. -/
theorem freezeCoupon_queue_of_notMem (B : Base) (s : ResumeState B) (z : Site B)
    (hz : z ∉ resumeSeed B s.1) : (freezeCoupon B s z).2 = s.2 := by
  unfold freezeCoupon
  rw [if_neg hz]

/-- Each block step either leaves the queue unchanged (the exit site is new) or appends
exactly its exit site (the exit site was already occupied). -/
theorem blockGrow_succ_queue (B : Base) (h : ℤ) (s : ResumeState B) (ω : TrajSeq B) (n : ℕ) :
    (exitSite' B (resumeSeed B (blockGrow B h s ω n).1 ∩ R B ((h : ℝ) - 1)) (ω n) ∉
        resumeSeed B (blockGrow B h s ω n).1 ∧
      (blockGrow B h s ω (n + 1)).2 = (blockGrow B h s ω n).2) ∨
    (exitSite' B (resumeSeed B (blockGrow B h s ω n).1 ∩ R B ((h : ℝ) - 1)) (ω n) ∈
        resumeSeed B (blockGrow B h s ω n).1 ∧
      (blockGrow B h s ω (n + 1)).2 = (blockGrow B h s ω n).2 ++
        [exitSite' B (resumeSeed B (blockGrow B h s ω n).1 ∩ R B ((h : ℝ) - 1)) (ω n)]) := by
  by_cases hz : exitSite' B (resumeSeed B (blockGrow B h s ω n).1 ∩ R B ((h : ℝ) - 1))
      (ω n) ∈ resumeSeed B (blockGrow B h s ω n).1
  · exact Or.inr ⟨hz, by rw [blockGrow_succ, freezeCoupon_queue_of_mem B _ _ hz]⟩
  · exact Or.inl ⟨hz, by rw [blockGrow_succ, freezeCoupon_queue_of_notMem B _ _ hz]⟩

/-- Membership in an integer-height rectangle. -/
theorem blockMem_R_int_iff (B : Base) (p : Site B) (k : ℤ) : p ∈ R B (k : ℝ) ↔ p.2 ≤ k := by
  rw [mem_R, Int.cast_le]

/-- Membership in the rectangle strictly below an integer height. -/
theorem blockMem_R_sub_one_iff (B : Base) (h : ℤ) (p : Site B) :
    p ∈ R B ((h : ℝ) - 1) ↔ p.2 < h := by
  have e : (h : ℝ) - 1 = ((h - 1 : ℤ) : ℝ) := by push_cast; ring
  rw [e, blockMem_R_int_iff]
  omega

/-- **Pathwise accounting of the block growth.** If the walks are admissible, start in `R_0`,
and exit each shrinking set `seed ∩ R_{h-1}` in finite time, then the seed stays inside `R_h`
and the queue gains only copies at height `h`. The seed starts at `R_a` with `a < h`. -/
theorem blockGrow_queue_at_height (B : Base) (a : ℕ) (h : ℤ) (ha : (a : ℤ) < h)
    (s : ResumeState B) (hs : resumeSeed B s.1 = R B (a : ℝ)) (ω : TrajSeq B) (n : ℕ)
    (hadm : ∀ i < n, CylAdmissible B (ω i)) (hstart : ∀ i < n, ω i 0 ∈ R B 0)
    (hfin : ∀ i < n,
      exitTime' B (resumeSeed B (blockGrow B h s ω i).1 ∩ R B ((h : ℝ) - 1)) (ω i) ≠ ⊤) :
    resumeSeed B (blockGrow B h s ω n).1 ⊆ R B (h : ℝ) ∧
      ∃ extra : List (Site B), (∀ z ∈ extra, z.2 = h) ∧
        (blockGrow B h s ω n).2 = s.2 ++ extra := by
  induction n with
  | zero =>
      refine ⟨?_, [], by simp, by simp [blockGrow]⟩
      intro p hp
      have hp' : p ∈ resumeSeed B s.1 := hp
      rw [hs] at hp'
      have h1 : (a : ℝ) ≤ (h : ℝ) := by exact_mod_cast ha.le
      exact mem_R.mpr ((mem_R.mp hp').trans h1)
  | succ n ih =>
      obtain ⟨hsub, extra, hextra, hq⟩ := ih (fun i hi => hadm i (by omega))
        (fun i hi => hstart i (by omega)) (fun i hi => hfin i (by omega))
      have hfn := hfin n (by omega)
      have hstn := hstart n (by omega)
      have hS0 : ω n 0 ∈ resumeSeed B (blockGrow B h s ω n).1 ∩ R B ((h : ℝ) - 1) := by
        refine ⟨?_, ?_⟩
        · apply resumeSeed_subset_blockGrow B h s ω n
          rw [hs]
          exact mem_R.mpr ((mem_R.mp hstn).trans (Nat.cast_nonneg a))
        · have h1 : (1 : ℝ) ≤ h := by exact_mod_cast (show (1 : ℤ) ≤ h by omega)
          exact mem_R.mpr (by linarith [mem_R.mp hstn])
      obtain ⟨q, hqS, hadj⟩ := exitSite'_adj hS0 (hadm n (by omega)) hfn
      have hzout := exitSite'_mem_compl B _ hfn
      set z := exitSite' B (resumeSeed B (blockGrow B h s ω n).1 ∩ R B ((h : ℝ) - 1)) (ω n)
        with hz_def
      have hqh : q.2 < h := (blockMem_R_sub_one_iff B h q).mp hqS.2
      have hzh : z.2 ≤ h := by
        rcases (cylGraph_adj_iff B q z).mp hadj with ⟨_, h1⟩ | ⟨h2, _⟩ <;> omega
      have hzmem : z ∈ R B (h : ℝ) := mem_R.mpr (by exact_mod_cast hzh)
      have hseed : resumeSeed B (blockGrow B h s ω (n + 1)).1 ⊆ R B (h : ℝ) := by
        intro p hp
        rw [blockGrow_succ_seed] at hp
        rcases hp with hp | hp
        · exact hsub hp
        · rw [Set.mem_singleton_iff] at hp
          rw [hp]
          exact hzmem
      refine ⟨hseed, ?_⟩
      rcases blockGrow_succ_queue B h s ω n with ⟨hzn, hqn⟩ | ⟨hzn, hqn⟩
      · exact ⟨extra, hextra, by rw [hqn, hq]⟩
      · have hzeq : z.2 = h := by
          have h1 : h ≤ z.2 := by
            by_contra hlt
            exact hzout ⟨hzn, (blockMem_R_sub_one_iff B h z).mpr (by omega)⟩
          omega
        refine ⟨extra ++ [z], ?_, by rw [hqn, hq, List.append_assoc]⟩
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact hextra w hw
        · rw [List.mem_singleton] at hw
          rw [hw]
          exact hzeq

/-- Each entry of the queue added by one block growth has height exactly `h`, almost surely,
for every number of releases. -/
theorem blockGrow_queue_ae (B : Base) (a : ℕ) (h : ℤ) (ha : (a : ℤ) < h) (s : ResumeState B)
    (hs : resumeSeed B s.1 = R B (a : ℝ)) (n : ℕ) :
    ∀ᵐ ω ∂idlaMeasure B, resumeSeed B (blockGrow B h s ω n).1 ⊆ R B (h : ℝ) ∧
      ∃ extra : List (Site B), (∀ z ∈ extra, z.2 = h) ∧
        (blockGrow B h s ω n).2 = s.2 ++ extra := by
  have hae : ∀ᵐ ω ∂idlaMeasure B, ∀ i, CylAdmissible B (ω i) ∧ ω i 0 ∈ R B 0 ∧
      exitTime' B (resumeSeed B (blockGrow B h s ω i).1 ∩ R B ((h : ℝ) - 1)) (ω i) ≠ ⊤ := by
    filter_upwards [idlaMeasure_ae_admissible B, idlaMeasure_ae_start_mem B,
      idlaMeasure_ae_coord_hits_all B] with ω ha hst hh i
    refine ⟨ha i, hst i, ?_⟩
    obtain ⟨m, hm⟩ := hh i h
    exact exitTime'_ne_top_of_height B Set.inter_subset_right hm.ge
  filter_upwards [hae] with ω hω
  exact blockGrow_queue_at_height B a h ha s hs ω n (fun i _ => (hω i).1)
    (fun i _ => (hω i).2.1) (fun i _ => (hω i).2.2)

/-- **Mass of the block growth.** Each release adds exactly one particle, settled or mobile. -/
theorem blockGrow_mass (B : Base) (h : ℤ) (s : ResumeState B) (ω : TrajSeq B) (M : ℕ) :
    (blockGrow B h s ω M).1.val.card + (blockGrow B h s ω M).2.length =
      s.1.val.card + s.2.length + M := by
  induction M with
  | zero => rfl
  | succ M ih =>
      have hm := freezeCoupon_mass B (blockGrow B h s ω M)
        (exitSite' B (resumeSeed B (blockGrow B h s ω M).1 ∩ R B ((h : ℝ) - 1)) (ω M))
      rw [blockGrow_succ]
      omega

/-- A finite extension whose seed is the rectangle `R_ℓ`, `ℓ ≥ 0`, has exactly `N ℓ` sites. -/
theorem blockFinite_card (B : Base) (F : ResumeFinite B) (ℓ : ℤ)
    (hF : resumeSeed B F = R B (ℓ : ℝ)) : F.val.card = B.card * ℓ.toNat := by
  have hmem : ∀ z : Site B, z ∈ F.val ↔ 1 ≤ z.2 ∧ z.2 ≤ ℓ := by
    intro z
    constructor
    · intro hz
      have hpos : (0 : ℝ) < (z.2 : ℝ) := lt_of_not_ge (F.property z hz)
      have hposZ : (0 : ℤ) < z.2 := by exact_mod_cast hpos
      have hm : z ∈ R B (ℓ : ℝ) := hF ▸ (show z ∈ resumeSeed B F from Or.inr hz)
      have hupper : z.2 ≤ ℓ := by exact_mod_cast (mem_R.mp hm)
      exact ⟨by omega, hupper⟩
    · rintro ⟨hlo, hup⟩
      have hm : z ∈ resumeSeed B F := by
        rw [hF]
        exact mem_R.mpr (by exact_mod_cast hup)
      rcases hm with hzero | hz
      · have hz0 : z.2 ≤ 0 := by exact_mod_cast (mem_R.mp hzero)
        omega
      · exact hz
  have heq : F.val = Finset.univ ×ˢ Finset.Icc (1 : ℤ) ℓ := by
    ext z
    rw [hmem z, Finset.mem_product, Finset.mem_Icc]
    simp
  rw [heq, Finset.card_product, Finset.card_univ, Int.card_Icc, add_sub_cancel_right]
  rfl

/-- **Queue accounting at the rectangle `R_h`, `h = a + H`.** If the seed starts at `R_a` and
ends at `R_h` after `M` releases, the queue gained exactly `M - N H` entries, all at height `h`.
Here `N = B.card` is the number of sites per layer. -/
theorem blockGrow_queue_count (B : Base) (a H : ℕ) (hH : 1 ≤ H) (h : ℤ)
    (hh : h = (a : ℤ) + H) (s : ResumeState B) (hs : resumeSeed B s.1 = R B (a : ℝ))
    (ω : TrajSeq B) (M : ℕ)
    (hadm : ∀ i < M, CylAdmissible B (ω i)) (hstart : ∀ i < M, ω i 0 ∈ R B 0)
    (hfin : ∀ i < M,
      exitTime' B (resumeSeed B (blockGrow B h s ω i).1 ∩ R B ((h : ℝ) - 1)) (ω i) ≠ ⊤)
    (hend : resumeSeed B (blockGrow B h s ω M).1 = R B (h : ℝ)) :
    (∃ extra : List (Site B), (∀ z ∈ extra, z.2 = h) ∧
        (blockGrow B h s ω M).2 = s.2 ++ extra) ∧
      (blockGrow B h s ω M).2.length = s.2.length + (M - B.card * H) := by
  have ha : (a : ℤ) < h := by omega
  obtain ⟨_, extra, hextra, hq⟩ := blockGrow_queue_at_height B a h ha s hs ω M hadm hstart hfin
  refine ⟨⟨extra, hextra, hq⟩, ?_⟩
  have hmass := blockGrow_mass B h s ω M
  have hc1 := blockFinite_card B _ h hend
  have hc0 := blockFinite_card B s.1 (a : ℤ) (by rw [Int.cast_natCast]; exact hs)
  have e : B.card * h.toNat = B.card * (a : ℤ).toNat + B.card * H := by
    rw [show h.toNat = (a : ℤ).toNat + H by omega, Nat.mul_add]
  have hge : s.2.length ≤ (blockGrow B h s ω M).2.length := by
    rw [hq, List.length_append]
    omega
  omega

/-- A queue segment whose entries all sit at height `h` has the mobile count of a single layer:
it is the length on layer `h` and empty elsewhere. -/
theorem mobileOnLayer_of_all_height (B : Base) (L : List (Site B)) (h k : ℤ)
    (hL : ∀ z ∈ L, z.2 = h) : mobileOnLayer B L k = if k = h then L.length else 0 := by
  unfold mobileOnLayer
  by_cases hk : k = h
  · rw [if_pos hk]
    have hall : L.filter (fun w => decide (w.2 = k)) = L :=
      List.filter_eq_self.mpr (fun w hw => by simp [hL w hw, hk])
    rw [hall]
  · rw [if_neg hk]
    have hnone : L.filter (fun w => decide (w.2 = k)) = [] :=
      List.filter_eq_nil_iff.mpr (fun w hw => by simp [hL w hw, Ne.symm hk])
    rw [hnone]
    rfl

/-- **Per-layer queue ledger of a successful block batch.** Compared with the start, the queue
gains `M - N H` mobile copies on layer `h` and nothing on any other layer. -/
theorem blockGrow_queue_layer_count (B : Base) (a H : ℕ) (hH : 1 ≤ H) (h : ℤ)
    (hh : h = (a : ℤ) + H) (s : ResumeState B) (hs : resumeSeed B s.1 = R B (a : ℝ))
    (ω : TrajSeq B) (M : ℕ)
    (hadm : ∀ i < M, CylAdmissible B (ω i)) (hstart : ∀ i < M, ω i 0 ∈ R B 0)
    (hfin : ∀ i < M,
      exitTime' B (resumeSeed B (blockGrow B h s ω i).1 ∩ R B ((h : ℝ) - 1)) (ω i) ≠ ⊤)
    (hend : resumeSeed B (blockGrow B h s ω M).1 = R B (h : ℝ)) (k : ℤ) :
    mobileOnLayer B (blockGrow B h s ω M).2 k =
      mobileOnLayer B s.2 k + if k = h then M - B.card * H else 0 := by
  obtain ⟨⟨extra, hextra, hq⟩, hlen⟩ :=
    blockGrow_queue_count B a H hH h hh s hs ω M hadm hstart hfin hend
  have hlen' : extra.length = M - B.card * H := by
    rw [hq, List.length_append] at hlen
    omega
  have hsplit : mobileOnLayer B (s.2 ++ extra) k = mobileOnLayer B s.2 k + mobileOnLayer B extra k := by
    simp [mobileOnLayer, List.filter_append]
  rw [hq, hsplit, mobileOnLayer_of_all_height B extra h k hextra, hlen']

end IdlaCyl.Reduction
