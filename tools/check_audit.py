#!/usr/bin/env python3
"""Structural checks of the comparator audit in `IdlaCylAudit/`.

    python3 tools/check_audit.py [AUDIT_BUILD_LOG]

For each pair `IdlaCylAudit/<Pair>/`:

  1. `Challenge.lean` imports `Mathlib` and nothing else, and contains exactly one block between
     `-- VOCABULARY-BEGIN` and `-- VOCABULARY-END`;
  2. that block is byte-identical to the block of `IdlaCylAudit/SolutionBasic.lean`, which also
     imports only `Mathlib`;
  3. the challenge contains exactly one `sorry`, after the vocabulary block, in its theorem;
  4. `Solution.lean` contains no `sorry` and no vocabulary block, and states the challenge
     theorem with the byte-identical text from `theorem` to `:= by`;
  5. `comparator.json` names the pair's challenge and solution modules and its theorem, permits
     exactly `propext`, `Quot.sound` and `Classical.choice`, and enables the NanoDa replay.

With a build log of `lake build IdlaCylAudit`, it also checks that the only warnings are the
four intentional `declaration uses 'sorry'` warnings of the challenges.  The comparator itself
(`scripts/run_comparators.sh`) checks the statements and their dependency closures.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
AUDIT = ROOT / "IdlaCylAudit"
PAIRS = {
    "MaxFluct": "IdlaCylAudit.max_fluct",
    "GFF": "IdlaCylAudit.gff",
    "Cycle": "IdlaCylAudit.thm_cycle",
    "Torus": "IdlaCylAudit.thm_torus",
}
BEGIN = "-- VOCABULARY-BEGIN\n"
END = "-- VOCABULARY-END\n"
AXIOMS = {"propext", "Quot.sound", "Classical.choice"}


def imports(text: str) -> list[str]:
    return [line.split()[1] for line in text.splitlines() if line.startswith("import ")]


def block(text: str, where: str, fails: list[str]) -> str | None:
    if text.count(BEGIN) != 1 or text.count(END) != 1:
        fails.append(f"{where}: needs exactly one vocabulary block")
        return None
    start = text.index(BEGIN) + len(BEGIN)
    return text[start:text.index(END)]


def statement(text: str, name: str) -> str | None:
    short = name.split(".")[-1]
    match = re.search(rf"^theorem {re.escape(short)}\b.*?:= by\n", text, re.S | re.M)
    return match.group(0) if match else None


def strip_comments(text: str) -> str:
    """Remove nested `/- ... -/` blocks and `--` line comments."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def sorry_count(text: str) -> int:
    return len(re.findall(r"\bsorry\b", strip_comments(text)))


def check() -> list[str]:
    fails: list[str] = []
    basic = (AUDIT / "SolutionBasic.lean").read_text()
    if imports(basic) != ["Mathlib"]:
        fails.append("SolutionBasic.lean must import Mathlib only")
    vocabulary = block(basic, "SolutionBasic.lean", fails)
    found = sorted(p.parent.name for p in AUDIT.glob("*/comparator.json"))
    if found != sorted(PAIRS):
        fails.append(f"comparator pairs {found} != {sorted(PAIRS)}")
    for pair, theorem in PAIRS.items():
        directory = AUDIT / pair
        missing = [f for f in ("Challenge.lean", "Solution.lean", "comparator.json")
                   if not (directory / f).is_file()]
        if missing:
            fails.append(f"{pair}: missing {', '.join(missing)}")
            continue
        challenge = (directory / "Challenge.lean").read_text()
        solution = (directory / "Solution.lean").read_text()
        if imports(challenge) != ["Mathlib"]:
            fails.append(f"{pair}/Challenge.lean must import Mathlib only")
        challenge_block = block(challenge, f"{pair}/Challenge.lean", fails)
        if challenge_block is not None and challenge_block != vocabulary:
            fails.append(f"{pair}/Challenge.lean: vocabulary differs from SolutionBasic.lean")
        if sorry_count(challenge) != 1 or (
                challenge_block is not None and sorry_count(challenge_block) != 0):
            fails.append(f"{pair}/Challenge.lean: needs exactly one sorry, in its theorem")
        if sorry_count(solution) != 0:
            fails.append(f"{pair}/Solution.lean contains sorry")
        if BEGIN in solution or END in solution:
            fails.append(f"{pair}/Solution.lean must take its vocabulary from SolutionBasic")
        stated = statement(challenge, theorem)
        if stated is None or stated != statement(solution, theorem):
            fails.append(f"{pair}: the solution does not restate the challenge theorem verbatim")
        config = json.loads((directory / "comparator.json").read_text())
        expected = {
            "challenge_module": f"IdlaCylAudit.{pair}.Challenge",
            "solution_module": f"IdlaCylAudit.{pair}.Solution",
            "theorem_names": [theorem],
            "definition_names": [],
            "enable_nanoda": True,
        }
        for key, value in expected.items():
            if config.get(key) != value:
                fails.append(f"{pair}/comparator.json: {key} is {config.get(key)!r}")
        if set(config.get("permitted_axioms", [])) != AXIOMS or len(
                config.get("permitted_axioms", [])) != len(AXIOMS):
            fails.append(f"{pair}/comparator.json: permitted axioms must be exactly {sorted(AXIOMS)}")
    return fails


def check_log(log: str) -> list[str]:
    fails: list[str] = []
    warnings = [line for line in log.splitlines() if re.search(r"(^|\s)warning:", line)]
    allowed = re.compile(
        r"IdlaCylAudit/(MaxFluct|GFF|Cycle|Torus)/Challenge\.lean:\d+:\d+: "
        r"declaration uses ['`]sorry['`]")
    unexpected = [line for line in warnings if not allowed.search(line)]
    pairs = {m.group(1) for line in warnings if (m := allowed.search(line))}
    if unexpected:
        fails.extend(f"unexpected warning: {line.strip()}" for line in unexpected)
    if pairs != set(PAIRS) or len(warnings) != len(PAIRS):
        fails.append(f"expected one sorry warning per challenge, found {len(warnings)} warnings")
    if "error:" in log:
        fails.append("the audit build reported an error")
    return fails


def main() -> int:
    fails = check()
    if len(sys.argv) > 1:
        fails += check_log(Path(sys.argv[1]).read_text())
    for fail in fails:
        print(f"FAIL  {fail}")
    if fails:
        return 1
    print(f"OK  {len(PAIRS)} comparator pairs; vocabulary identical; statements verbatim")
    return 0


if __name__ == "__main__":
    sys.exit(main())
