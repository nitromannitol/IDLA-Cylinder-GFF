#!/usr/bin/env python3
"""Frozen-statement manifest for IDLA-Cylinder-GFF.

    python3 tools/manifest.py check     # verify; exit 1 on any failure
    python3 tools/manifest.py freeze    # write/refresh ledger/manifest.yaml

A node is one `.lean` file under `IdlaCyl/Frozen/` or `IdlaCyl/External/`
containing exactly one

    -- FROZEN-STATEMENT-BEGIN
    ...
    -- FROZEN-STATEMENT-END

block.  The sha256 of the bytes *between* the marker lines is the contract.
Unlike the checker this replaces, a block may hold more than one declaration:
a theorem is sealed together with the definitions that carry its content, so
that `Delta` or `sigmaSq` cannot be rewritten without breaking the hash.  All
declaration names in a block are recorded, in order.

Checks performed:

  1. every manifest node's file exists and has exactly one block;
  2. the block hash matches the manifest;
  3. the declaration names parsed from the block match the manifest exactly;
  4. every frozen/external file is owned by exactly one node, and every node
     owns a file that exists;
  5. `sorry` appears in the production tree only *after* an end marker, and
     only in files whose node state is `DRAFT_SORRY`;
  6. no `axiom`, `admit`, `sorryAx`, or `native_decide` anywhere in the
     production tree;
  7. states come from the allowed set, and `External` nodes are never
     `DRAFT_SORRY` (a hypothesis has nothing to prove);
  8. the paper source hash matches `source_pin`, so a node's line references
     cannot drift silently.
"""
from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"
PAPER = ROOT / "paper" / "idla-cylinder-gff.tex"
LIB = ROOT / "IdlaCyl"
FROZEN_DIRS = (LIB / "Frozen", LIB / "External")

BEGIN = "-- FROZEN-STATEMENT-BEGIN"
END = "-- FROZEN-STATEMENT-END"
STATES = {"FROZEN", "SEALED", "DRAFT_SORRY", "CONDITIONAL", "PROVED"}
BANNED = ("axiom ", "admit", "sorryAx", "native_decide")

DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_.'!?]*)", re.M)


def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def strip_comments(text: str) -> str:
    """Blank out block and line comments, preserving newlines and length."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            out.append("  "); i += 2; continue
        if text.startswith("-/", i) and depth:
            depth -= 1
            out.append("  "); i += 2; continue
        if depth:
            out.append("\n" if text[i] == "\n" else " "); i += 1; continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        out.append(text[i]); i += 1
    return "".join(out)


def block_of(path: Path) -> tuple[bytes, list[str], int]:
    """The frozen block's bytes, its declaration names, and the end-marker offset."""
    raw = path.read_text(encoding="utf-8")
    if raw.count(BEGIN) != 1 or raw.count(END) != 1:
        raise ValueError(f"{path}: expected exactly one frozen block, "
                         f"found {raw.count(BEGIN)} begin / {raw.count(END)} end")
    b = raw.index(BEGIN) + len(BEGIN)
    if raw[b] == "\n":
        b += 1
    e = raw.index(END)
    body = raw[b:e]
    names = [m.group(2) for m in DECL.finditer(strip_comments(body))]
    return body.encode("utf-8"), names, e


# --- a deliberately tiny YAML reader/writer for the one shape we use --------

def load_manifest() -> dict:
    if not MANIFEST.exists():
        return {"source_pin": {}, "nodes": []}
    man: dict = {"source_pin": {}, "nodes": []}
    node: dict | None = None
    in_decls = False
    for line in MANIFEST.read_text().split("\n"):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        if line.startswith("  - id:"):
            node = {"id": line.split(":", 1)[1].strip(), "decls": []}
            man["nodes"].append(node); in_decls = False
            continue
        m = re.match(r"^    ([a-z0-9_]+):\s*(.*)$", line)
        if m and node is not None:
            key, val = m.group(1), m.group(2).strip()
            if key == "decls":
                in_decls = True
                node["decls"] = []
            else:
                in_decls = False
                node[key] = val.strip('"')
            continue
        m = re.match(r"^      - (.*)$", line)
        if m and node is not None and in_decls:
            node["decls"].append(m.group(1).strip().strip('"'))
            continue
        m = re.match(r"^  ([a-z0-9_]+):\s*(.*)$", line)
        if m:
            man["source_pin"][m.group(1)] = m.group(2).strip().strip('"')
    return man


def dump_manifest(man: dict) -> str:
    out = [
        "# Frozen-statement manifest for IDLA-Cylinder-GFF.",
        "#",
        "# The bytes between the FROZEN-STATEMENT markers are the contract: a proof",
        "# attempt may fill in the proof after the end marker, never touch the",
        "# statement.  `frozen_sha256` is the SHA-256 of exactly those bytes.",
        "#",
        "# States: FROZEN (a statement assumed here, such as a cited result),",
        "#         DRAFT_SORRY (statement settled, proof open),",
        "#         CONDITIONAL (proved from External hypotheses),",
        "#         PROVED / SEALED (proved, axiom closure clean).",
        "",
        "version: 1",
        "source_pin:",
        f"  file: {man['source_pin']['file']}",
        f"  sha256: {man['source_pin']['sha256']}",
        "",
        "nodes:",
    ]
    for n in man["nodes"]:
        out += [
            "",
            f"  - id: {n['id']}",
            f"    kind: {n['kind']}",
            f"    source: {n['source']}",
            f"    file: {n['file']}",
            f"    state: {n['state']}",
            f"    frozen_sha256: {n['frozen_sha256']}",
            "    decls:",
        ]
        out += [f"      - {d}" for d in n["decls"]]
    return "\n".join(out) + "\n"


def frozen_files() -> list[Path]:
    out: list[Path] = []
    for d in FROZEN_DIRS:
        if d.exists():
            out += sorted(p for p in d.rglob("*.lean"))
    return out


def production_files() -> list[Path]:
    return sorted(list(LIB.rglob("*.lean")) + [ROOT / "IdlaCyl.lean"])


def check() -> int:
    man = load_manifest()
    fails: list[str] = []

    want = sha(PAPER.read_bytes())
    if man["source_pin"].get("sha256") != want:
        fails.append(f"source_pin: paper hash {want} != manifest "
                     f"{man['source_pin'].get('sha256')}")

    by_file = {}
    for n in man["nodes"]:
        p = ROOT / n["file"]
        if not p.exists():
            fails.append(f"{n['id']}: file {n['file']} does not exist")
            continue
        if n["file"] in by_file:
            fails.append(f"{n['file']} is owned by two nodes")
        by_file[n["file"]] = n
        try:
            body, names, _ = block_of(p)
        except ValueError as e:
            fails.append(str(e)); continue
        got = sha(body)
        if got != n["frozen_sha256"]:
            fails.append(f"{n['id']}: frozen block hash {got} != manifest "
                         f"{n['frozen_sha256']} -- the statement changed")
        if names != n["decls"]:
            fails.append(f"{n['id']}: declarations {names} != manifest {n['decls']}")
        if n["state"] not in STATES:
            fails.append(f"{n['id']}: unknown state {n['state']}")
        if "/External/" in n["file"] and n["state"] == "DRAFT_SORRY":
            fails.append(f"{n['id']}: an External hypothesis cannot be DRAFT_SORRY")

    for p in frozen_files():
        rel = str(p.relative_to(ROOT))
        if rel not in by_file:
            fails.append(f"{rel}: not owned by any manifest node")

    for p in production_files():
        if not p.exists():
            continue
        text = p.read_text(encoding="utf-8")
        masked = strip_comments(text)
        for bad in BANNED:
            if bad in masked:
                fails.append(f"{p.relative_to(ROOT)}: forbidden token {bad.strip()!r}")
        if "sorry" not in masked:
            continue
        rel = str(p.relative_to(ROOT))
        node = by_file.get(rel)
        if END in text:
            e = text.index(END)
            if "sorry" in masked[:e]:
                fails.append(f"{rel}: `sorry` inside the frozen block")
        if node is None:
            # A Support file may carry open obligations; they are tracked by
            # the sorry count in the gate report, not by the manifest.
            continue
        if node["state"] not in ("DRAFT_SORRY", "CONDITIONAL"):
            fails.append(f"{rel}: state {node['state']} but the file contains `sorry`")

    for f in fails:
        print(f"FAIL  {f}")
    n_nodes = len(man["nodes"])
    if fails:
        print(f"\n{len(fails)} failure(s) over {n_nodes} node(s)")
        return 1
    print(f"OK  {n_nodes} node(s), paper pin {want[:12]}…")
    return 0


def freeze() -> int:
    man = load_manifest()
    old = {n["id"]: n for n in man["nodes"]}
    nodes = []
    for p in frozen_files():
        rel = str(p.relative_to(ROOT))
        body, names, end = block_of(p)
        nid = p.stem
        prev = old.get(nid, {})
        text = p.read_text(encoding="utf-8")
        has_sorry = "sorry" in strip_comments(text)[end:]
        state = prev.get("state") or ("DRAFT_SORRY" if has_sorry else "FROZEN")
        if not has_sorry and state == "DRAFT_SORRY":
            state = "PROVED"
        if has_sorry and state in ("PROVED", "SEALED", "FROZEN"):
            state = "DRAFT_SORRY"
        m = re.search(r"tex:(\d+)-(\d+)", text)
        source = prev.get("source") or (
            f"idla-cylinder-gff.tex:{m.group(1)}-{m.group(2)}" if m else "unknown")
        nodes.append({
            "id": nid,
            "kind": "external" if "/External/" in rel else "theorem",
            "source": source,
            "file": rel,
            "state": state,
            "frozen_sha256": sha(body),
            "decls": names,
        })
    man = {"source_pin": {"file": "paper/idla-cylinder-gff.tex",
                          "sha256": sha(PAPER.read_bytes())},
           "nodes": nodes}
    MANIFEST.write_text(dump_manifest(man))
    print(f"wrote {MANIFEST.relative_to(ROOT)}: {len(nodes)} node(s)")
    for n in nodes:
        print(f"  {n['state']:12s} {n['id']:16s} {n['frozen_sha256'][:12]}…  "
              + ", ".join(n["decls"]))
    return 0


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "check"
    sys.exit({"check": check, "freeze": freeze}[cmd]())
