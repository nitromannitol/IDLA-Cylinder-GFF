# The comparator audit

The four main theorems of the paper are restated here using mathlib alone, so that a reader
can check what is proved without reading the library.

| Pair | Paper | Challenge theorem | Library theorem |
| --- | --- | --- | --- |
| `MaxFluct` | Theorem 1.1 (`th:max_fluct`) | `IdlaCylAudit.max_fluct` | `IdlaCyl.Frozen.max_fluct_v3` |
| `GFF` | Theorem 1.3 (`th:GFF`) | `IdlaCylAudit.gff` | `IdlaCyl.Frozen.gff_v3` |
| `Cycle` | the cycle (`thm:cycle`) | `IdlaCylAudit.thm_cycle` | `IdlaCyl.Frozen.thm_cycle_v3` |
| `Torus` | the torus (`thm:torus`) | `IdlaCylAudit.thm_torus` | `IdlaCyl.Frozen.thm_torus_v3` |

Each pair has a directory with three files.

- `Challenge.lean` imports `Mathlib` and nothing else. Between `VOCABULARY-BEGIN` and
  `VOCABULARY-END` it rebuilds the model of the paper from mathlib primitives: the base graph
  and its lazy walk, the cylinder walk and its law, the canonical IDLA law, the clusters, the
  mixing time, the spectral data, the test functions, the limiting variance, and the cycle and
  torus bases. The block is a token-for-token copy of the library's definitions, under the
  namespace `IdlaCylAudit` in place of `IdlaCyl`, and it is the same in all four challenges.
  The file then states the theorem and ends in a single `sorry`. This file is the object of
  trust: a reader checks what it says, not how it is proved.
- `Solution.lean` imports the library, the shared vocabulary
  [`SolutionBasic.lean`](SolutionBasic.lean) (a byte-identical copy of the vocabulary block,
  importing only `Mathlib`, so that it elaborates exactly as in the challenge) and the bridge
  in [`Support/`](Support/). It restates the challenge theorem verbatim and proves it from the
  library's registered theorem.
- `comparator.json` names the challenge module, the solution module, the theorem and the
  permitted axioms (`propext`, `Classical.choice`, `Quot.sound`), and enables the NanoDa
  replay.

The bridge identifies the vocabulary with the library. `Bridge.base` maps a vocabulary base to
the library base with the same fields; sites, driving sequences and measurable spaces then agree
definitionally, and every definition of the vocabulary is proved equal to its library
counterpart: by `rfl` where it is not recursive (the IDLA law, the cycle and torus bases), by
induction for the recursive ones (the clusters, the powers of the base kernel), and by cases
for the indexed cycle base. A solution can only supply a proof of the statement the reader saw
in the challenge; nothing it imports can change that statement.

[`tools/check_audit.py`](../tools/check_audit.py) checks the structure: the imports of each
challenge, the identity of the vocabulary blocks, the verbatim restatement in each solution
and the configurations. [leanprover/comparator](https://github.com/leanprover/comparator)
checks the rest: it requires the solution's theorem to have exactly the challenge's statement,
compares the dependency closures of the two statements, rejects any axiom outside the three
permitted ones, and replays the proof with the Lean kernel and with NanoDa. Run it with
[`scripts/run_comparators.sh`](../scripts/run_comparators.sh); see
[`CI_ARTIFACTS.md`](../CI_ARTIFACTS.md) for the hosted workflow.
