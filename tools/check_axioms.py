#!/usr/bin/env python3
"""Check the axiom closure of every declaration registered in the manifest.

Draft theorems may depend on ``sorryAx`` while their manifest state is
``DRAFT_SORRY``.  Every other declaration must depend only on Lean's standard
axioms.  Frozen inputs are checked for unexpected axioms, but are reported as
inputs rather than counted as proofs.
"""

from __future__ import annotations

from contextlib import contextmanager
import fcntl
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
TOOLS = Path(__file__).resolve().parent
BUILD_DIR = ROOT / ".lake" / "build"
MANIFEST = ROOT / "ledger" / "manifest.yaml"
# The shared Lake lock is opt-in: with IDLA_LAKE_LOCK naming a file, Lake runs hold an
# exclusive flock on it (reusing file descriptor 3 when gate.sh holds it); otherwise no lock.
GLOBAL_LOCK = Path(os.environ["IDLA_LAKE_LOCK"]) if os.environ.get("IDLA_LAKE_LOCK") else None
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ALLOWED_STATES = {"FROZEN", "DRAFT_SORRY", "CONDITIONAL", "PROVED", "SEALED"}
IDENTIFIER_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.!?]*$")
STRING_RE = re.compile(r'"(?:\\.|[^"\\])*"')
FROZEN_DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.!?]*)", re.M
)
AXIOM_LINE_RE = re.compile(
    r"^\s*(?:'(?P<quoted>[^']+)'|(?P<plain>\S+))"
    r"\s+depends on axioms:\s*\[(?P<axioms>[^\]]*)\]\s*$"
)

sys.path.insert(0, str(TOOLS))
import manifest as manifest_module  # noqa: E402
from manifest import load_manifest  # noqa: E402  (use the repository parser)


@contextmanager
def global_build_lock():
    """Hold the shared Lake lock, reusing flock fd 3 when gate.sh supplies it."""
    if GLOBAL_LOCK is None:
        yield
        return
    fd = None
    owns_fd = False
    try:
        lock_stat = GLOBAL_LOCK.stat() if GLOBAL_LOCK.exists() else None
        try:
            inherited = os.stat("/proc/self/fd/3")
        except OSError:
            inherited = None
        if (lock_stat is not None
                and inherited is not None
                and (inherited.st_dev, inherited.st_ino)
                == (lock_stat.st_dev, lock_stat.st_ino)):
            fd = 3
        else:
            fd = os.open(GLOBAL_LOCK, os.O_CREAT | os.O_RDWR, 0o600)
            owns_fd = True
        fcntl.flock(fd, fcntl.LOCK_EX)
        yield
    finally:
        if owns_fd and fd is not None:
            fcntl.flock(fd, fcntl.LOCK_UN)
            os.close(fd)


def run_manifest_check() -> int:
    """Run the authoritative manifest census and source-pin check first."""
    try:
        result = subprocess.run(
            [sys.executable, str(TOOLS / "manifest.py"), "check"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
    except OSError as error:
        print(f"check_axioms: could not run tools/manifest.py check: {error}",
              file=sys.stderr)
        return 1
    if result.stdout:
        sys.stdout.write(result.stdout)
    if result.stderr:
        sys.stderr.write(result.stderr)
    return result.returncode


def frozen_code_text(text: str) -> str:
    """Mask strings before comments so source text cannot forge declarations."""
    strings_masked = STRING_RE.sub(
        lambda match: re.sub(r"[^\n]", " ", match.group(0)), text
    )
    return manifest_module.strip_comments(strings_masked)


def load_nodes() -> list[dict[str, Any]]:
    """Load and validate the repository's manifest using its own parser."""
    raw = MANIFEST.read_text(encoding="utf-8")
    parsed = load_manifest()
    nodes = parsed.get("nodes")
    manifest_rows = len(re.findall(r"^  - id:", raw, re.MULTILINE))
    if not isinstance(nodes, list) or not nodes or len(nodes) != manifest_rows:
        raise ValueError(
            f"manifest node census is empty or incomplete "
            f"({len(nodes) if isinstance(nodes, list) else 0} parsed, "
            f"{manifest_rows} rows)"
        )

    ids: set[str] = set()
    files: set[str] = set()
    declaration_names: set[tuple[str, str]] = set()
    for index, node in enumerate(nodes, start=1):
        if not isinstance(node, dict):
            raise ValueError(f"manifest row {index} is not a mapping")
        for field in ("id", "kind", "file", "state", "decls"):
            if field not in node:
                raise ValueError(f"manifest row {index} is missing {field!r}")

        node_id, kind, file_name, state = (
            node["id"], node["kind"], node["file"], node["state"]
        )
        if not all(isinstance(value, str) and value for value in
                   (node_id, kind, file_name, state)):
            raise ValueError(f"manifest row {index} has an empty or non-string field")
        if node_id in ids:
            raise ValueError(f"duplicate manifest node id {node_id!r}")
        ids.add(node_id)
        if file_name in files:
            raise ValueError(f"manifest file {file_name!r} occurs more than once")
        files.add(file_name)
        if state not in ALLOWED_STATES:
            raise ValueError(f"{node_id}: unknown manifest state {state!r}")
        if state == "DRAFT_SORRY" and kind != "theorem":
            raise ValueError(f"{node_id}: DRAFT_SORRY is permitted only for theorem rows")

        path = Path(file_name)
        if (path.is_absolute() or ".." in path.parts or path.suffix != ".lean"
                or len(path.parts) < 3 or path.parts[0] != "IdlaCyl"
                or path.parts[1] not in {"Frozen", "External"}):
            raise ValueError(f"{node_id}: invalid manifest Lean file {file_name!r}")
        if not (ROOT / path).is_file():
            raise ValueError(f"{node_id}: manifest Lean file does not exist: {file_name}")
        expected_kind = "theorem" if path.parts[1] == "Frozen" else "external"
        if kind != expected_kind:
            raise ValueError(
                f"{node_id}: kind {kind!r} does not match {path.parts[1]} source"
            )

        decls = node["decls"]
        if not isinstance(decls, list) or not decls:
            raise ValueError(f"{node_id}: manifest declaration list is empty or invalid")
        for declaration in decls:
            if not isinstance(declaration, str) or not IDENTIFIER_RE.fullmatch(declaration):
                raise ValueError(f"{node_id}: invalid declaration name {declaration!r}")
            key = (file_name, declaration)
            if key in declaration_names:
                raise ValueError(f"{node_id}: duplicate declaration {declaration!r}")
            declaration_names.add(key)

    return nodes


def qualified_name(node: dict[str, Any], declaration: str) -> str:
    """Qualify the manifest's short declaration name by its source namespace."""
    directory = Path(node["file"]).parts[1]
    namespace = "IdlaCyl.Frozen" if directory == "Frozen" else "IdlaCyl.External"
    return f"{namespace}.{declaration}"


def expected_declarations(nodes: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    expected: dict[str, dict[str, Any]] = {}
    for node in nodes:
        path = ROOT / node["file"]
        block, names, _ = manifest_module.block_of(path)
        masked = frozen_code_text(block.decode("utf-8"))
        declarations = [
            (match.group(2), match.group(1))
            for match in FROZEN_DECL_RE.finditer(masked)
        ]
        if [name for name, _kind in declarations] != names or names != node["decls"]:
            raise ValueError(
                f"{node['id']}: declaration kinds could not be reconciled with its Frozen block"
            )
        theorem_exports = [name for name, kind in declarations if kind == "theorem"]
        if node["state"] == "DRAFT_SORRY" and len(theorem_exports) != 1:
            raise ValueError(
                f"{node['id']}: DRAFT_SORRY row must register exactly one theorem export"
            )
        for declaration in node["decls"]:
            name = qualified_name(node, declaration)
            if name in expected:
                raise ValueError(f"duplicate fully qualified declaration {name!r}")
            declaration_kind = next(
                kind for declared_name, kind in declarations
                if declared_name == declaration
            )
            expected[name] = {
                "node": node,
                "declaration_kind": declaration_kind,
                "draft_export": (
                    node["state"] == "DRAFT_SORRY"
                    and declaration_kind == "theorem"
                    and declaration == theorem_exports[0]
                ),
            }
    return expected


def parse_axiom_output(
    output: str, expected_names: set[str]
) -> tuple[dict[str, set[str]], list[str]]:
    """Parse ``#print axioms`` output and require one line per probe name."""
    found: dict[str, set[str]] = {}
    errors: list[str] = []
    for line in output.splitlines():
        if "depends on axioms:" not in line:
            continue
        match = AXIOM_LINE_RE.fullmatch(line)
        if match is None:
            errors.append(f"unparseable axiom report line: {line}")
            continue
        name = match.group("quoted") or match.group("plain")
        if name not in expected_names:
            errors.append(f"unregistered declaration in axiom output: {name}")
            continue
        if name in found:
            errors.append(f"duplicate axiom report for {name}")
            continue
        raw_axioms = match.group("axioms").strip()
        axioms = set() if not raw_axioms else {
            item.strip() for item in raw_axioms.split(",")
        }
        if "" in axioms:
            errors.append(f"empty axiom name in report for {name}")
        found[name] = axioms

    for name in sorted(expected_names - found.keys()):
        errors.append(f"no axiom report for {name}")
    return found, errors


def axiom_policy_errors(
    expected: dict[str, dict[str, Any]], reports: dict[str, set[str]]
) -> list[str]:
    """Enforce standard axioms and the one registered ``sorryAx`` exception."""
    errors: list[str] = []
    for name, entry in expected.items():
        node = entry["node"]
        axioms = reports.get(name)
        if axioms is None:
            continue
        extra_axioms = axioms - STANDARD_AXIOMS - {"sorryAx"}
        if extra_axioms:
            errors.append(
                f"{name}: unregistered axiom(s): {', '.join(sorted(extra_axioms))}"
            )
        if "sorryAx" in axioms and not entry["draft_export"]:
            errors.append(
                f"{name}: sorryAx is not allowed for frozen declaration kind "
                f"{entry['declaration_kind']} in {node['id']}"
            )
    return errors


def run_lake_build() -> int:
    """Ensure the imported artifacts correspond to the current library sources."""
    env = os.environ.copy()
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    try:
        result = subprocess.run(
            ["lake", "build", "IdlaCyl"],
            cwd=ROOT,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=3600,
            env=env,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        print(f"check_axioms: could not run lake build IdlaCyl: {error}", file=sys.stderr)
        return 1
    if result.stdout:
        sys.stdout.write(result.stdout)
    if result.stderr:
        sys.stderr.write(result.stderr)
    if result.returncode != 0:
        print(f"check_axioms: FAIL (lake build IdlaCyl exited {result.returncode})",
              file=sys.stderr)
        return 1
    return 0


def probe_source(nodes: list[dict[str, Any]]) -> tuple[str, dict[str, dict[str, Any]]]:
    expected = expected_declarations(nodes)
    modules = sorted({
        Path(node["file"]).with_suffix("").as_posix().replace("/", ".")
        for node in nodes
    })
    source = "".join(f"import {module}\n" for module in modules)
    source += "".join(f"#print axioms {name}\n" for name in expected)
    return source, expected


def _main_locked(argv: list[str] | None = None) -> int:
    args = sys.argv[1:] if argv is None else argv
    if args:
        print("usage: check_axioms.py", file=sys.stderr)
        return 2

    manifest_code = run_manifest_check()
    if manifest_code != 0:
        print(f"check_axioms: FAIL (tools/manifest.py check exited {manifest_code})",
              file=sys.stderr)
        return 1

    try:
        nodes = load_nodes()
        source, expected = probe_source(nodes)
    except (OSError, KeyError, TypeError, ValueError) as error:
        print(f"check_axioms: could not read manifest: {error}", file=sys.stderr)
        return 1

    if BUILD_DIR.is_symlink() or (BUILD_DIR.exists() and not BUILD_DIR.is_dir()):
        print("check_axioms: .lake/build must not be a symlink or non-directory",
              file=sys.stderr)
        return 1
    if run_lake_build() != 0:
        return 1
    if not BUILD_DIR.is_dir() or BUILD_DIR.is_symlink() or BUILD_DIR.resolve() != BUILD_DIR:
        print("check_axioms: lake build did not create a physical local .lake/build directory",
              file=sys.stderr)
        return 1

    try:
        with tempfile.NamedTemporaryFile(
            "w", suffix=".lean", dir=BUILD_DIR, encoding="utf-8", delete=False
        ) as handle:
            handle.write(source)
            probe = Path(handle.name)
        env = os.environ.copy()
        env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
        result = subprocess.run(
            ["lake", "env", "lean", str(probe)],
            cwd=ROOT,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=3600,
            env=env,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        print(f"check_axioms: Lean axiom probe failed to run: {error}", file=sys.stderr)
        return 1
    finally:
        if "probe" in locals():
            probe.unlink(missing_ok=True)

    if result.returncode != 0:
        if result.stdout:
            sys.stdout.write(result.stdout)
        if result.stderr:
            sys.stderr.write(result.stderr)
        print(f"check_axioms: FAIL (Lean axiom probe exited {result.returncode})",
              file=sys.stderr)
        return 1

    reports, parse_errors = parse_axiom_output(result.stdout, set(expected))
    violations = list(parse_errors)
    violations.extend(axiom_policy_errors(expected, reports))
    draft_names_with_sorry = 0
    proved_exports = 0
    frozen_inputs = 0
    for name, entry in expected.items():
        node = entry["node"]
        axioms = reports.get(name)
        if axioms is None:
            continue
        if "sorryAx" in axioms:
            if entry["draft_export"]:
                draft_names_with_sorry += 1
                print(f"  DRAFT_SORRY {node['id']}: {name} depends on sorryAx")
            else:
                print(f"  FAIL {name}: unexpected sorryAx dependency")
        elif node["state"] in {"PROVED", "SEALED"} and node["kind"] == "theorem":
            proved_exports += 1
            print(f"  {node['state']:6s} {node['id']}: {name} has standard axiom closure")
        elif node["state"] == "DRAFT_SORRY":
            print(f"  DRAFT_SORRY {node['id']}: {name} has no sorryAx dependency")
        elif node["state"] == "FROZEN":
            frozen_inputs += 1
            print(f"  FROZEN input {node['id']}: {name} (not counted as a proof)")

    for error in violations:
        print(f"  FAIL {error}", file=sys.stderr)
    draft_rows = sum(node["state"] == "DRAFT_SORRY" for node in nodes)
    print(
        f"check_axioms: {len(nodes)} nodes, {len(expected)} declarations; "
        f"{draft_rows} registered draft rows, {draft_names_with_sorry} declarations "
        f"with allowed sorryAx, {proved_exports} clean PROVED/SEALED exports, "
        f"{frozen_inputs} frozen input declarations"
    )
    return 1 if violations else 0


def main(argv: list[str] | None = None) -> int:
    try:
        with global_build_lock():
            return _main_locked(argv)
    except OSError as error:
        print(f"check_axioms: could not acquire global Lake lock: {error}",
              file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
