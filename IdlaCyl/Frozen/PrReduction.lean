/-
Proposition `pr:reduction` (tex:1446-1449), as printed.

The paper's own words:

  Fix $\n > 0$ and $m \geq 1$, with $T^\sharp$ as in the statement of
  Theorem~\ref{th:max_fluct}. For every integer $T$ with $T^\sharp \leq T \leq N^m$
  and every $N$ large enough, there exist an integer $T'$ with $1 \leq T' \leq T^\sharp$
  and a non-negative integer $k$ with $T' + N k = T$, together with a coupling of
  $A(T)$ and an IDLA process $(A_*(t))_{t \geq 0}$ on $\bbG_N$ starting from
  $A_*(0) = R_0$, such that
    \[ \bbP\big( A(T) = A_*(T') + R_k \big) \geq 1 - N^{-(\n+1)}\,, \]
  where $A_*(T') + R_k \coloneqq \{(x, y+k) : (x, y) \in A_*(T')\}$.

Encoding, on the canonical model used by `th:max_fluct` (`MaxFluctV2.lean`):
* `T^♯ = N √τ_mix (log N)²` is `Defs.sharp B`, a real number, as in Theorem 1.1; `m ≥ 1` is real,
  and `N^m` is the real power.
* "every `N` large enough" is a cutoff `N₀` on the size of the base, chosen after `ν` and `m`
  and before the base and `T`, so it is uniform over all bases with at least `N₀` vertices.
  This node is therefore stronger than the print, whose "every `N` large enough" is read per base
  family in `th:max_fluct` (`MaxFluctV2.lean`, where `N₀` follows the base sequence); it has the
  shape of `pr_reduction_alpha`.
* A coupling of `A(T)` and `A_*` is a measure on pairs of walk sequences whose two marginals are
  the canonical IDLA driving law `idlaMeasure B` (walks started uniformly on layer 0 from
  `A(0) = R_0`); the clusters are `clusterTraj B ω t`, and `A_*(T') + R_k` is
  `Reduction.shiftCluster B k`.
This is `IdlaCyl.pr_reduction_alpha` (`Support/Reduction/Target.lean`) with the coefficient
`α = 1`. It is proved (`Reduction.block_pr_reduction`, `Support/Reduction/Block/`) by an argument
different from the printed one, whose proof has a gap (`ledger/ERRATA.md`, E18): the reduction fills
blocks of `H ≍ √τ_mix log N` layers with `2NH` particles stopped at the top of each block, instead of
one layer at a time, so the reduced time is at most `6NH`, which is below `T^♯` for `N` large; the
comparisons use Silvestri's Proposition 2, proved in `External/Discharge/Silvestri.lean`.

As printed, the range `T^♯ ≤ T ≤ N^m` is empty for `m = 1` once `N ≥ 3` (then `T^♯ > N`), and for
`1 ≤ m < 2` on bases whose mixing time is of order `N²`; for those parameters the statement holds
trivially, as the printed one does.
-/
import IdlaCyl.Support.Reduction.Target
import IdlaCyl.Support.Reduction.Block.BlockRoundInst

namespace IdlaCyl.Frozen

open MeasureTheory

-- FROZEN-STATEMENT-BEGIN
theorem pr_reduction (ν : ℝ) (hν : 0 < ν) (m : ℝ) (hm : 1 ≤ m) :
    ∃ N₀ : ℕ, ∀ B : Base, N₀ ≤ B.card → ∀ T : ℕ,
      Defs.sharp B ≤ (T : ℝ) → (T : ℝ) ≤ (B.card : ℝ) ^ m →
      ∃ T' k : ℕ,
        1 ≤ T' ∧ (T' : ℝ) ≤ Defs.sharp B ∧ T' + B.card * k = T ∧
        ∃ μ : Measure (TrajSeq B × TrajSeq B),
          μ.map (Prod.fst : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
          μ.map (Prod.snd : TrajSeq B × TrajSeq B → TrajSeq B) = idlaMeasure B ∧
          ENNReal.ofReal (1 - (B.card : ℝ) ^ (-(ν + 1))) ≤
            μ {p | clusterTraj B p.1 T =
              Reduction.shiftCluster B k (clusterTraj B p.2 T')}
-- FROZEN-STATEMENT-END
:=
  Reduction.block_pr_reduction ν hν m hm

end IdlaCyl.Frozen
