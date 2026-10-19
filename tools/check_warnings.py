#!/usr/bin/env python3
"""Check Lake warnings and every production ``sorry`` against the manifest."""

from __future__ import annotations

from collections import Counter
from contextlib import contextmanager
import fcntl
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
TOOLS = Path(__file__).resolve().parent
MANIFEST = ROOT / "ledger" / "manifest.yaml"
BUILD_DIR = ROOT / ".lake" / "build"
TRACE_DIR = BUILD_DIR / "lib" / "lean"
# The shared Lake lock is opt-in: with IDLA_LAKE_LOCK naming a file, Lake runs hold an
# exclusive flock on it (reusing file descriptor 3 when gate.sh holds it); otherwise no lock.
GLOBAL_LOCK = Path(os.environ["IDLA_LAKE_LOCK"]) if os.environ.get("IDLA_LAKE_LOCK") else None
BEGIN = "-- FROZEN-STATEMENT-BEGIN"
END = "-- FROZEN-STATEMENT-END"
ANSI_RE = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
DIAGNOSTIC_RE = re.compile(
    r"^(?P<path>.+?\.lean):(?P<line>[0-9]+):(?P<column>[0-9]+):\s*(?P<message>.*)$"
)
SORRY_MESSAGE_RE = re.compile(r"declaration uses [`']sorry[`']\s*$")
SORRY_TOKEN_RE = re.compile(r"\bsorry\b")
IDENTIFIER_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.!?]*$")
ALLOWED_STATES = {"FROZEN", "DRAFT_SORRY", "CONDITIONAL", "PROVED", "SEALED"}
FROZEN_DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.!?]*)",
    re.M,
)
NEXT_COMMAND_RE = re.compile(
    r"(?m)^[ \t]*(?:@[\[][^\]]*[\]]\s*)*"
    r"(?:noncomputable\s+|private\s+|protected\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|instance|namespace|section|end)\b"
)
TOKEN_RE = re.compile(r":=|[A-Za-z_][A-Za-z0-9_'.!?]*|[^\s]")

sys.path.insert(0, str(TOOLS))
import manifest as manifest_module  # noqa: E402
from manifest import load_manifest  # noqa: E402


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
        print(f"check_warnings: could not run tools/manifest.py check: {error}",
              file=sys.stderr)
        return 1
    if result.stdout:
        sys.stdout.write(result.stdout)
    if result.stderr:
        sys.stderr.write(result.stderr)
    return result.returncode


def load_nodes() -> list[dict[str, Any]]:
    """Load and defensively validate the manifest after its authoritative check."""
    raw = MANIFEST.read_text(encoding="utf-8")
    manifest = load_manifest()
    nodes = manifest.get("nodes")
    row_count = len(re.findall(r"^  - id:", raw, re.MULTILINE))
    if not isinstance(nodes, list) or not nodes or len(nodes) != row_count:
        raise ValueError(
            f"manifest node census is empty or incomplete "
            f"({len(nodes) if isinstance(nodes, list) else 0} parsed, {row_count} rows)"
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
        expected_kind = "theorem" if path.parts[1] == "Frozen" else "external"
        if kind != expected_kind:
            raise ValueError(
                f"{node_id}: kind {kind!r} does not match {path.parts[1]} source"
            )
        if not isinstance(node["decls"], list) or not node["decls"]:
            raise ValueError(f"{node_id}: manifest declaration list is empty or invalid")
        for declaration in node["decls"]:
            if not isinstance(declaration, str) or not IDENTIFIER_RE.fullmatch(declaration):
                raise ValueError(f"{node_id}: invalid declaration name {declaration!r}")
            key = (file_name, declaration)
            if key in declaration_names:
                raise ValueError(f"{node_id}: duplicate declaration {declaration!r}")
            declaration_names.add(key)
        if not (ROOT / path).is_file():
            raise ValueError(f"{node_id}: manifest Lean file does not exist: {file_name}")
    return nodes


def mask_strings(text: str) -> str:
    """Blank Lean string literals while preserving offsets and line numbers."""
    return re.sub(
        r'"(?:\\.|[^"\\])*"',
        lambda match: re.sub(r"[^\n]", " ", match.group(0)),
        text,
    )


def code_text(text: str) -> str:
    return manifest_module.strip_comments(mask_strings(text))


def source_location(path: Path, offset: int) -> tuple[str, int]:
    return path.relative_to(ROOT).as_posix(), path.read_text(encoding="utf-8").count(
        "\n", 0, offset
    ) + 1


def draft_source_locations(
    nodes: list[dict[str, Any]],
) -> tuple[Counter[tuple[str, int]], Counter[tuple[str, int]], list[str]]:
    """Bind each draft warning to its sole theorem declaration and exact hole."""
    expected: Counter[tuple[str, int]] = Counter()
    allowed_tokens: Counter[tuple[str, int]] = Counter()
    errors: list[str] = []
    for node in nodes:
        if node["state"] != "DRAFT_SORRY":
            continue
        path = ROOT / node["file"]
        try:
            raw = path.read_text(encoding="utf-8")
            _block, names, end = manifest_module.block_of(path)
        except (OSError, ValueError) as error:
            errors.append(f"{node['id']}: cannot inspect frozen theorem source: {error}")
            continue
        begin = raw.index(BEGIN) + len(BEGIN)
        if raw[begin:begin + 1] == "\n":
            begin += 1
        block_code = code_text(raw[begin:end])
        declarations = list(FROZEN_DECL_RE.finditer(block_code))
        declared_names = [match.group(2) for match in declarations]
        if declared_names != names or names != node["decls"]:
            errors.append(f"{node['id']}: declaration list does not match its frozen block")
            continue
        exports = [match for match in declarations if match.group(1) == "theorem"]
        if len(exports) != 1:
            errors.append(
                f"{node['id']}: DRAFT_SORRY row must have exactly one theorem export"
            )
            continue

        marker_end = end + len(END)
        tail_code = code_text(raw[marker_end:])
        prefix = re.match(r"\s*:=\s*by\s+sorry\b", tail_code, re.S)
        if prefix is None:
            errors.append(
                f"{node['file']}: registered draft theorem must have exact `:= by sorry` body"
            )
            continue
        next_command = NEXT_COMMAND_RE.search(tail_code, prefix.end())
        proof_region = tail_code[:next_command.start()] if next_command else tail_code
        if TOKEN_RE.findall(proof_region) != [":=", "by", "sorry"]:
            errors.append(
                f"{node['file']}: registered draft theorem body is not exactly `:= by sorry`"
            )
            continue

        declaration = exports[0]
        absolute_declaration = begin + declaration.start()
        relative_path, declaration_line = source_location(path, absolute_declaration)
        expected[(relative_path, declaration_line)] += 1
        sorry_match = SORRY_TOKEN_RE.search(proof_region)
        if sorry_match is None:
            errors.append(f"{node['file']}: registered draft proof has no sorry token")
            continue
        relative_token_path, sorry_line = source_location(
            path, marker_end + sorry_match.start()
        )
        allowed_tokens[(relative_token_path, sorry_line)] += 1
    return expected, allowed_tokens, errors


def production_sorry_tokens() -> dict[str, list[int]]:
    """Return every non-comment, non-string sorry token in production Lean."""
    found: dict[str, list[int]] = {}
    for path in manifest_module.production_files():
        if not path.is_file():
            continue
        code = code_text(path.read_text(encoding="utf-8"))
        rel = path.relative_to(ROOT).as_posix()
        for match in SORRY_TOKEN_RE.finditer(code):
            found.setdefault(rel, []).append(code.count("\n", 0, match.start()) + 1)
    return found


def expected_trace_sources() -> dict[Path, Path]:
    sources = manifest_module.production_files()
    return {trace_path_for_source(source): source for source in sources}


def trace_path_for_source(source: Path, trace_root: Path | None = None) -> Path:
    root = TRACE_DIR if trace_root is None else trace_root
    return root / source.relative_to(ROOT).with_suffix(".trace")


def expected_module(source: Path) -> str:
    return source.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")


def normalize_repo_path(path_text: str) -> str:
    path = Path(path_text)
    if path.is_absolute():
        try:
            return path.resolve().relative_to(ROOT.resolve()).as_posix()
        except ValueError:
            return str(path)
    return path.as_posix()


def parse_diagnostic(message: str) -> tuple[str, int, int, str] | None:
    clean_message = ANSI_RE.sub("", message.strip())
    if not clean_message:
        return None
    line = clean_message.splitlines()[0]
    if line.startswith("warning:"):
        line = line[len("warning:"):].strip()
    match = DIAGNOSTIC_RE.fullmatch(line)
    if match is None:
        return None
    return (
        normalize_repo_path(match.group("path")),
        int(match.group("line")),
        int(match.group("column")),
        match.group("message").strip(),
    )


def is_sorry_diagnostic(diagnostic: tuple[str, int, int, str]) -> bool:
    return SORRY_MESSAGE_RE.fullmatch(diagnostic[3]) is not None


def lake_environment() -> dict[str, str]:
    env = os.environ.copy()
    env["PATH"] = str(Path.home() / ".elan" / "bin") + os.pathsep + env.get("PATH", "")
    return env


def option_flag(name: str, value: Any) -> str:
    """Use LeanOptionValue.asCliFlagValue's string, Bool, and Nat encodings."""
    if isinstance(value, bool):
        encoded = "true" if value else "false"
    elif isinstance(value, int) and value >= 0:
        encoded = str(value)
    elif isinstance(value, str):
        encoded = f'"{value}"'
    else:
        raise ValueError(f"unsupported Lake option value for {name!r}: {value!r}")
    return f"-D{name}={encoded}"


def current_trace_inputs(trace_sources: dict[Path, Path]) -> dict[str, Any]:
    """Ask Lake for current setups and use Lake.Hash for exact trace leaf hashes.

    Lake's Module.recFetchInput uses Hash.ofText for a Lean source; Run.lean
    hashes the Lean git commit; Module.traceOptions uses pureHash on each
    -D option flag. The rehash build preceding this query independently checks
    source contents without trusting cached .hash files.
    """
    sources = list(trace_sources.values())
    modules = [expected_module(source) for source in sources]
    env = lake_environment()
    query = subprocess.run(
        ["lake", "--rehash", "--json", "query",
         *(f"+{module}:setup" for module in modules)],
        cwd=ROOT, capture_output=True, text=True, encoding="utf-8",
        errors="replace", timeout=3600, env=env, check=False,
    )
    if query.returncode != 0:
        raise ValueError(f"Lake setup query exited {query.returncode}: {query.stderr[-1000:]}")
    lines = query.stdout.splitlines()
    if len(lines) != len(modules):
        raise ValueError(f"Lake setup query returned {len(lines)} records for {len(modules)} modules")
    setups = [json.loads(line) for line in lines]
    flags: set[str] = set()
    for module, setup in zip(modules, setups):
        if not isinstance(setup, dict) or setup.get("name") != module:
            raise ValueError(f"Lake setup query has wrong module identity for {module}")
        options = setup.get("options")
        if not isinstance(options, dict):
            raise ValueError(f"Lake setup query has no effective options for {module}")
        flags.update(option_flag(name, value) for name, value in options.items())

    commit = subprocess.run(
        ["lean", "--githash"], cwd=ROOT, capture_output=True, text=True,
        encoding="utf-8", errors="replace", timeout=30, env=env, check=False,
    )
    if commit.returncode != 0 or not re.fullmatch(r"[0-9a-f]{40}", commit.stdout.strip()):
        raise ValueError("could not identify current Lean commit")
    lean_commit = commit.stdout.strip()

    # This helper calls the same Lake hash functions that create trace inputs.
    helper = '''import Lake
open Lake
def main (args : List String) : IO UInt32 := do
  let mut mode := "sources"
  let mut commit := ""
  for arg in args do
    if arg == "--OPTIONS--" then
      mode := "options"
    else if arg == "--MODULES--" then
      mode := "modules"
    else if arg.startsWith "--COMMIT=" then
      commit := (arg.drop 9).toString
    else if mode == "modules" then
      let name : Lean.Name := arg.toName
      IO.println s!"M\\t{(pureHash name).hex}"
    else if mode == "options" then
      IO.println s!"O\\t{(pureHash arg).hex}"
    else
      let contents ← IO.FS.readFile arg
      IO.println s!"S\\t{(Hash.ofText contents).hex}"
  IO.println s!"V\\t{Lean.versionStringCore}\\t{(pureHash commit).hex}"
  return 0
'''
    # The final argument is the Lean commit, so the helper hashes it as Lake does.
    ordered_flags = sorted(flags)
    with tempfile.NamedTemporaryFile(
        "w", suffix=".lean", encoding="utf-8", delete=False
    ) as handle:
        handle.write(helper)
        helper_path = Path(handle.name)
    try:
        hashes = subprocess.run(
            ["lake", "env", "lean", "--run", str(helper_path),
             *(str(source.resolve()) for source in sources),
             "--OPTIONS--", *ordered_flags, "--MODULES--", *modules,
             f"--COMMIT={lean_commit}"],
            cwd=ROOT, capture_output=True, text=True, encoding="utf-8",
            errors="replace", timeout=3600, env=env, check=False,
        )
    finally:
        helper_path.unlink(missing_ok=True)
    if hashes.returncode != 0:
        raise ValueError(f"Lake trace hash helper failed: {hashes.stderr[-1000:]}")
    hash_lines = [line.split("\t") for line in hashes.stdout.splitlines()]
    expected_count = len(sources) + len(ordered_flags) + len(modules) + 1
    if len(hash_lines) != expected_count:
        raise ValueError("Lake trace hash helper returned an incomplete result")
    source_rows = hash_lines[:len(sources)]
    option_rows = hash_lines[len(sources):len(sources) + len(ordered_flags)]
    module_rows = hash_lines[len(sources) + len(ordered_flags):-1]
    version_row = hash_lines[-1]
    if (any(len(row) != 2 or row[0] != "S" for row in source_rows)
            or any(len(row) != 2 or row[0] != "O" for row in option_rows)
            or any(len(row) != 2 or row[0] != "M" for row in module_rows)
            or len(version_row) != 3 or version_row[0] != "V"):
        raise ValueError("Lake trace hash helper returned malformed hashes")
    source_hashes = {source: row[1] for source, row in zip(sources, source_rows)}
    option_hashes = dict(zip(ordered_flags, (row[1] for row in option_rows)))
    module_hashes = dict(zip(modules, (row[1] for row in module_rows)))
    expected_options = {
        module: sorted([option_flag(name, value), option_hashes[option_flag(name, value)]]
                       for name, value in setup["options"].items())
        for module, setup in zip(modules, setups)
    }
    return {
        "sources": source_hashes,
        "modules": module_hashes,
        "lean": [f"Lean {version_row[1]}, commit {lean_commit}", version_row[2]],
        "options": expected_options,
    }


def trace_identity_errors(
    trace_path: Path, trace: Any, source: Path, provenance: dict[str, Any]
) -> list[str]:
    """Require exact Lake module, source, Lean commit, and option inputs."""
    rel_trace = trace_path.relative_to(ROOT).as_posix()
    module = expected_module(source)
    errors: list[str] = []
    if not isinstance(trace, dict):
        return [f"{rel_trace}: Lake trace root is not an object"]
    if trace.get("synthetic") is not False:
        errors.append(f"{rel_trace}: Lake trace is synthetic or lacks synthetic=false")
    if not isinstance(trace.get("depHash"), str) or not trace.get("depHash"):
        errors.append(f"{rel_trace}: Lake trace has no dependency hash")
    if not isinstance(trace.get("outputs"), dict):
        errors.append(f"{rel_trace}: Lake trace has no output record")

    inputs = trace.get("inputs")
    if not isinstance(inputs, list):
        errors.append(f"{rel_trace}: Lake trace has no input list")
        return errors
    dependency_roots = [
        item[0] for item in inputs
        if isinstance(item, list) and len(item) == 2
        and isinstance(item[0], str) and item[0].endswith(":deps")
    ]
    if dependency_roots != [f"{module}:deps"]:
        errors.append(
            f"{rel_trace}: input module identity {dependency_roots!r} "
            f"does not match {module}"
        )
    module_inputs = [
        item
        for item in inputs
        if isinstance(item, list) and len(item) == 2
        and isinstance(item[0], str) and item[0].startswith("Module.name: ")
    ]
    if module_inputs != [[f"Module.name: {module}", provenance["modules"][module]]]:
        errors.append(
            f"{rel_trace}: Module.name identity/hash does not match current Lake module {module}"
        )

    source_inputs = [
        item for item in inputs
        if isinstance(item, list) and len(item) == 2
        and isinstance(item[0], str) and item[0].endswith(".lean")
    ]
    expected_path = str(source)
    if (len(source_inputs) != 1 or source_inputs[0][0] != expected_path
            or not isinstance(source_inputs[0][1], str)
            or not re.fullmatch(r"[0-9a-fA-F]{16}", source_inputs[0][1])):
        actual_paths = [item[0] for item in source_inputs]
        errors.append(
            f"{rel_trace}: source input {actual_paths!r} does not identify "
            f"{source.relative_to(ROOT).as_posix()} in this checkout"
        )
    elif source_inputs[0][1] != provenance["sources"][source]:
        errors.append(f"{rel_trace}: source content hash does not match current Lean file")
    lean_inputs = [item for item in inputs if isinstance(item, list) and len(item) == 2
                   and isinstance(item[0], str) and item[0].startswith("Lean ")]
    if lean_inputs != [provenance["lean"]]:
        errors.append(f"{rel_trace}: Lean version/commit trace input does not match current Lean")
    option_inputs = [item for item in inputs if isinstance(item, list) and len(item) == 2
                     and item[0] == "options"]
    if (len(option_inputs) != 1 or not isinstance(option_inputs[0][1], list)
            or sorted(option_inputs[0][1]) != provenance["options"][module]):
        errors.append(f"{rel_trace}: effective options trace input does not match current Lake setup")
    return errors


def read_trace_warnings(
    trace_sources: dict[Path, Path],
    provenance: dict[str, Any],
) -> tuple[list[tuple[str, int, int, str]], list[str]]:
    warnings: list[tuple[str, int, int, str]] = []
    errors: list[str] = []
    for trace_path, source in sorted(trace_sources.items()):
        rel_trace = trace_path.relative_to(ROOT).as_posix()
        if not trace_path.is_file():
            errors.append(
                f"{rel_trace}: missing Lake trace after successful build; rebuild required"
            )
            continue
        try:
            trace = json.loads(trace_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            errors.append(f"{rel_trace}: could not read Lake trace: {error}; rebuild required")
            continue
        identity_errors = trace_identity_errors(trace_path, trace, source, provenance)
        if identity_errors:
            errors.extend(f"{error}; clean rebuild required" for error in identity_errors)
        log = trace.get("log") if isinstance(trace, dict) else None
        if not isinstance(log, list):
            errors.append(f"{rel_trace}: Lake trace has no diagnostic log; rebuild required")
            continue
        expected_path = source.relative_to(ROOT).as_posix()
        for entry in log:
            if not isinstance(entry, dict) or entry.get("level") != "warning":
                continue
            message = entry.get("message")
            if not isinstance(message, str):
                errors.append(f"{rel_trace}: invalid warning record; rebuild required")
                continue
            diagnostic = parse_diagnostic(message)
            if diagnostic is None:
                errors.append(f"{rel_trace}: unparseable warning {message!r}; rebuild required")
                continue
            if diagnostic[0] != expected_path:
                errors.append(
                    f"{rel_trace}: warning source {diagnostic[0]} does not match "
                    f"module source {expected_path}; clean rebuild required"
                )
                continue
            warnings.append(diagnostic)
    return warnings, errors


def run_lake_build() -> tuple[int, str]:
    env = lake_environment()
    try:
        result = subprocess.run(
            ["lake", "--rehash", "build", "IdlaCyl"],
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=3600,
            env=env,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        return 1, f"check_warnings: could not run lake build IdlaCyl: {error}\n"
    return result.returncode, result.stdout


def _main_locked() -> int:
    manifest_code = run_manifest_check()
    if manifest_code != 0:
        print(f"check_warnings: FAIL (tools/manifest.py check exited {manifest_code})",
              file=sys.stderr)
        return 1

    try:
        nodes = load_nodes()
        expected, allowed_tokens, source_errors = draft_source_locations(nodes)
        source_tokens = production_sorry_tokens()
    except (OSError, KeyError, TypeError, ValueError) as error:
        print(f"check_warnings: could not inspect manifest/source: {error}", file=sys.stderr)
        return 1

    actual_tokens = Counter(
        (path, line)
        for path, lines in source_tokens.items()
        for line in lines
    )
    source_violations = list(source_errors)
    for location, count in sorted((actual_tokens - allowed_tokens).items()):
        source_violations.append(
            f"unregistered sorry token at {location[0]}:{location[1]} ({count} occurrence(s))"
        )
    for location, count in sorted((allowed_tokens - actual_tokens).items()):
        source_violations.append(
            f"registered draft sorry token missing at {location[0]}:{location[1]} "
            f"({count} occurrence(s))"
        )
    if BUILD_DIR.is_symlink() or (BUILD_DIR.exists() and not BUILD_DIR.is_dir()):
        for error in source_violations:
            print(f"check_warnings: FAIL {error}", file=sys.stderr)
        print("check_warnings: .lake/build must not be a symlink or non-directory",
              file=sys.stderr)
        return 1

    build_code, build_output = run_lake_build()
    if build_output:
        sys.stdout.write(build_output)
    if build_code != 0:
        for error in source_violations:
            print(f"check_warnings: FAIL {error}", file=sys.stderr)
        print(f"check_warnings: FAIL (lake build IdlaCyl exited {build_code})",
              file=sys.stderr)
        return 1
    if not BUILD_DIR.is_dir() or BUILD_DIR.is_symlink() or BUILD_DIR.resolve() != BUILD_DIR:
        for error in source_violations:
            print(f"check_warnings: FAIL {error}", file=sys.stderr)
        print(
            "check_warnings: lake build did not create a physical local .lake/build directory",
            file=sys.stderr,
        )
        return 1

    trace_sources = expected_trace_sources()
    try:
        provenance = current_trace_inputs(trace_sources)
    except (OSError, ValueError, subprocess.TimeoutExpired, json.JSONDecodeError) as error:
        print(f"check_warnings: FAIL (could not validate Lake trace inputs: {error})",
              file=sys.stderr)
        return 1
    trace_warnings, trace_errors = read_trace_warnings(trace_sources, provenance)
    if trace_errors:
        for error in source_violations:
            print(f"check_warnings: FAIL {error}", file=sys.stderr)
        for error in trace_errors:
            print(f"check_warnings: FAIL {error}", file=sys.stderr)
        print(
            f"check_warnings: {len(nodes)} nodes, "
            f"{sum(len(n['decls']) for n in nodes)} declarations, "
            f"{len(trace_sources)} IdlaCyl traces; rebuild required for warning provenance"
        )
        return 1

    actual: Counter[tuple[str, int]] = Counter()
    unexpected: list[str] = []
    for diagnostic in trace_warnings:
        path, line, _column, message = diagnostic
        if is_sorry_diagnostic(diagnostic):
            actual[(path, line)] += 1
        else:
            unexpected.append(f"{path}:{line}: {message}")

    trace_locations: Counter[tuple[str, int, int, str]] = Counter(trace_warnings)
    for raw_line in build_output.splitlines():
        clean_line = ANSI_RE.sub("", raw_line).strip()
        if not clean_line.startswith("warning:"):
            continue
        diagnostic = parse_diagnostic(clean_line)
        if diagnostic is None:
            unexpected.append(clean_line)
            continue
        if trace_locations[diagnostic]:
            trace_locations[diagnostic] -= 1
            continue
        path, line, _column, message = diagnostic
        if is_sorry_diagnostic(diagnostic):
            actual[(path, line)] += 1
        else:
            unexpected.append(f"{path}:{line}: {message}")

    missing = expected - actual
    extra = actual - expected
    if source_violations or unexpected or missing or extra:
        print("check_warnings: FAIL", file=sys.stderr)
        for error in source_violations:
            print(f"  source violation: {error}", file=sys.stderr)
        for line in unexpected:
            print(f"  unexpected warning: {line}", file=sys.stderr)
        for (path, line), count in sorted(missing.items()):
            print(
                f"  missing {count} registered sorry warning(s): {path}:{line}",
                file=sys.stderr,
            )
        for (path, line), count in sorted(extra.items()):
            print(f"  extra {count} sorry warning(s): {path}:{line}", file=sys.stderr)
        print(
            f"check_warnings: {len(nodes)} nodes, "
            f"{sum(len(n['decls']) for n in nodes)} declarations, "
            f"{len(trace_sources)} IdlaCyl module traces, "
            f"{sum(actual.values())} observed sorry warning(s), "
            f"{sum(expected.values())} registered draft warning(s), "
            f"{len(unexpected)} other warning(s)"
        )
        return 1

    print(
        f"check_warnings: OK ({len(nodes)} nodes, "
        f"{sum(len(n['decls']) for n in nodes)} declarations; "
        f"{len(trace_sources)} IdlaCyl module traces; "
        f"{sum(actual.values())} registered sorry warnings)"
    )
    return 0


def main() -> int:
    try:
        with global_build_lock():
            return _main_locked()
    except OSError as error:
        print(f"check_warnings: could not acquire global Lake lock: {error}",
              file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
