"""Mutation tests for the executable manifest, axiom, warning, and shell gates."""

from __future__ import annotations

from contextlib import ExitStack, redirect_stderr, redirect_stdout
from collections import Counter
from hashlib import sha256
from io import StringIO
import json
import copy
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_axioms
import check_warnings


REPO = Path(__file__).resolve().parents[2]
TOOLS_TO_COPY = (
    "manifest.py",
    "check_axioms.py",
    "check_warnings.py",
    "gate.sh",
)
BEGIN = "-- FROZEN-STATEMENT-BEGIN"
END = "-- FROZEN-STATEMENT-END"


def inherited_global_lock_fd() -> tuple[int, ...]:
    """Let child checker processes reuse the enclosing test run's Lake lock."""
    try:
        if Path(os.readlink("/proc/self/fd/3")) == check_warnings.GLOBAL_LOCK:
            return (3,)
    except OSError:
        pass
    return ()


def write_fixture(
    root: Path,
    *,
    block: str = "theorem foo : True",
    proof: str = ":= by\n  sorry\n",
    declarations: tuple[str, ...] = ("foo",),
    manifest_declarations: tuple[str, ...] | None = None,
    state: str = "DRAFT_SORRY",
) -> Path:
    """Create a tiny manifest-valid Lean tree for mutation tests."""
    (root / "tools").mkdir(parents=True, exist_ok=True)
    for name in TOOLS_TO_COPY:
        shutil.copy2(REPO / "tools" / name, root / "tools" / name)
    (root / "paper").mkdir(parents=True, exist_ok=True)
    paper = root / "paper" / "idla-cylinder-gff.tex"
    paper.write_text("fixture paper pin\n", encoding="utf-8")
    frozen = root / "IdlaCyl" / "Frozen" / "Foo.lean"
    frozen.parent.mkdir(parents=True, exist_ok=True)
    (root / "IdlaCyl.lean").write_text("-- fixture root module\n", encoding="utf-8")
    frozen.write_text(
        "namespace IdlaCyl\nnamespace Frozen\n"
        f"{BEGIN}\n{block}\n{END}\n{proof}"
        "end Frozen\nend IdlaCyl\n",
        encoding="utf-8",
    )
    body = (block + "\n").encode("utf-8")
    row_declarations = declarations if manifest_declarations is None else manifest_declarations
    decl_lines = "".join(f"      - {name}\n" for name in row_declarations)
    manifest_text = (
        "version: 1\n"
        "source_pin:\n"
        "  file: paper/idla-cylinder-gff.tex\n"
        f"  sha256: {sha256(paper.read_bytes()).hexdigest()}\n"
        "nodes:\n\n"
        "  - id: Foo\n"
        "    kind: theorem\n"
        "    source: unknown\n"
        "    file: IdlaCyl/Frozen/Foo.lean\n"
        f"    state: {state}\n"
        f"    frozen_sha256: {sha256(body).hexdigest()}\n"
        "    decls:\n"
        f"{decl_lines}"
    )
    (root / "ledger").mkdir(parents=True, exist_ok=True)
    (root / "ledger" / "manifest.yaml").write_text(manifest_text, encoding="utf-8")
    (root / ".lake" / "build").mkdir(parents=True, exist_ok=True)
    return frozen


def patch_checker_root(stack: ExitStack, root: Path) -> None:
    """Redirect imported production entry points and manifest logic to a fixture."""
    for checker in (check_axioms, check_warnings):
        stack.enter_context(patch.object(checker, "ROOT", root))
        stack.enter_context(patch.object(checker, "TOOLS", root / "tools"))
        stack.enter_context(patch.object(checker, "BUILD_DIR", root / ".lake" / "build"))
        stack.enter_context(patch.object(
            checker, "MANIFEST", root / "ledger" / "manifest.yaml"
        ))
    stack.enter_context(patch.object(check_warnings, "TRACE_DIR",
                                      root / ".lake" / "build" / "lib" / "lean"))
    manifest = check_axioms.manifest_module
    stack.enter_context(patch.object(manifest, "ROOT", root))
    stack.enter_context(patch.object(manifest, "MANIFEST", root / "ledger" / "manifest.yaml"))
    stack.enter_context(patch.object(manifest, "PAPER", root / "paper" / "idla-cylinder-gff.tex"))
    stack.enter_context(patch.object(manifest, "LIB", root / "IdlaCyl"))
    stack.enter_context(patch.object(
        manifest,
        "FROZEN_DIRS",
        (root / "IdlaCyl" / "Frozen", root / "IdlaCyl" / "External"),
    ))


def trace_record(module: str, source: Path, warning: str | None = None) -> dict:
    inputs = [
        [f"{module}:deps", [["deps", []]]],
        ["Lean 4.32.0, commit fixture", "0123456789abcdef"],
        [str(source), "0123456789abcdef"],
        ["options", []],
        [f"Module.name: {module}", "0123456789abcdef"],
    ]
    log = [] if warning is None else [{"level": "warning", "message": warning}]
    return {
        "synthetic": False,
        "schemaVersion": "fixture",
        "outputs": {"o": ["fixture.olean"], "m": False},
        "log": log,
        "inputs": inputs,
        "depHash": "0123456789abcdef",
    }


class ProductionMutationTests(unittest.TestCase):
    def test_omitted_manifest_declaration_fails_both_standalone_checks(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            write_fixture(root, manifest_declarations=())
            for script in ("check_axioms.py", "check_warnings.py"):
                with self.subTest(script=script):
                    result = subprocess.run(
                        [sys.executable, str(root / "tools" / script)],
                        cwd=root,
                        capture_output=True,
                        text=True,
                        pass_fds=inherited_global_lock_fd(),
                        check=False,
                    )
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("tools/manifest.py check exited", result.stderr)
                    self.assertIn("declarations ['foo'] != manifest []", result.stdout)
                    self.assertNotIn("lake build", result.stderr)

    def test_omitted_manifest_row_fails_both_standalone_checks(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            write_fixture(root)
            manifest_path = root / "ledger" / "manifest.yaml"
            manifest_path.write_text(
                manifest_path.read_text(encoding="utf-8").split("  - id: Foo\n")[0],
                encoding="utf-8",
            )
            for script in ("check_axioms.py", "check_warnings.py"):
                with self.subTest(script=script):
                    result = subprocess.run(
                        [sys.executable, str(root / "tools" / script)],
                        cwd=root, capture_output=True, text=True,
                        pass_fds=inherited_global_lock_fd(), check=False,
                    )
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("tools/manifest.py check exited", result.stderr)
                    self.assertIn("IdlaCyl/Frozen/Foo.lean", result.stdout)

    def test_draft_row_definition_sorryax_fails_axiom_checker_main(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            write_fixture(
                root,
                block="def helper : True := True\ntheorem foo : True",
                declarations=("helper", "foo"),
            )
            output = "\n".join(
                [
                    "IdlaCyl.Frozen.helper depends on axioms: [sorryAx]",
                    "IdlaCyl.Frozen.foo depends on axioms: [sorryAx]",
                ]
            )
            original_run = subprocess.run

            def fake_run(command, **kwargs):
                if command[:3] == ["lake", "env", "lean"]:
                    return subprocess.CompletedProcess(command, 0, output, "")
                return original_run(command, **kwargs)

            stdout, stderr = StringIO(), StringIO()
            with ExitStack() as stack:
                patch_checker_root(stack, root)
                stack.enter_context(patch.object(check_axioms, "run_lake_build", return_value=0))
                stack.enter_context(patch.object(check_axioms.subprocess, "run", side_effect=fake_run))
                stack.enter_context(redirect_stdout(stdout))
                stack.enter_context(redirect_stderr(stderr))
                status = check_axioms.main([])
            self.assertEqual(status, 1)
            self.assertIn("sorryAx is not allowed for frozen declaration kind def", stderr.getvalue())
            self.assertIn("DRAFT_SORRY", stdout.getvalue())

    def test_proved_draft_export_cannot_substitute_helper_sorry(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            frozen = write_fixture(
                root,
                proof=(
                    ":= by\n  trivial\n\n"
                    "theorem helper : True := by\n  sorry\n"
                ),
            )
            self.assertTrue(frozen.is_file())
            stdout, stderr = StringIO(), StringIO()
            with ExitStack() as stack:
                patch_checker_root(stack, root)
                stack.enter_context(patch.object(
                    check_warnings, "run_lake_build", return_value=(0, "")
                ))
                stack.enter_context(patch.object(
                    check_warnings, "current_trace_inputs", return_value={
                        "sources": {}, "lean": [], "options": {},
                    }
                ))
                stack.enter_context(redirect_stdout(stdout))
                stack.enter_context(redirect_stderr(stderr))
                status = check_warnings.main()
            self.assertEqual(status, 1)
            self.assertIn("exact `:= by sorry` body", stderr.getvalue())
            self.assertIn("unregistered sorry token at IdlaCyl/Frozen/Foo.lean", stderr.getvalue())

    def test_mismatched_trace_module_and_source_path_fail_warning_main(self) -> None:
        for mutation in ("module", "module_hash", "input_path",
                         "same_path_spelling", "diagnostic_path"):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                source = write_fixture(root)
                build_dir = root / ".lake" / "build" / "lib" / "lean"
                module = "IdlaCyl.Frozen.Foo"
                line = source.read_text(encoding="utf-8").splitlines().index("theorem foo : True") + 1
                diag_source = source
                input_source = source
                trace_module = module
                if mutation == "module":
                    trace_module = "IdlaCyl.Support.Foo"
                elif mutation == "input_path":
                    input_source = Path("/other/checkout/IdlaCyl/Frozen/Foo.lean")
                elif mutation == "diagnostic_path":
                    diag_source = root / "IdlaCyl" / "Support" / "Foo.lean"
                root_trace = build_dir / "IdlaCyl.trace"
                foo_trace = build_dir / "IdlaCyl" / "Frozen" / "Foo.trace"
                root_trace.parent.mkdir(parents=True, exist_ok=True)
                foo_trace.parent.mkdir(parents=True, exist_ok=True)
                root_trace.write_text(
                    json.dumps(trace_record("IdlaCyl", root / "IdlaCyl.lean")),
                    encoding="utf-8",
                )
                warning = (
                    f"{diag_source}:{line}:8: declaration uses `sorry`"
                )
                record = trace_record(trace_module, input_source, warning)
                if mutation == "module_hash":
                    next(item for item in record["inputs"]
                         if item[0].startswith("Module.name: "))[1] = "0000000000000000"
                elif mutation == "same_path_spelling":
                    next(item for item in record["inputs"]
                         if item[0] == str(source))[0] = str(source.parent) + "/./" + source.name
                foo_trace.write_text(json.dumps(record), encoding="utf-8")

                stdout, stderr = StringIO(), StringIO()
                with ExitStack() as stack:
                    patch_checker_root(stack, root)
                    stack.enter_context(patch.object(
                        check_warnings, "run_lake_build", return_value=(0, "")
                    ))
                    stack.enter_context(patch.object(
                        check_warnings, "current_trace_inputs", return_value={
                            "sources": {root / "IdlaCyl.lean": "0123456789abcdef",
                                        source: "0123456789abcdef"},
                            "modules": {"IdlaCyl": "0123456789abcdef",
                                        module: "0123456789abcdef"},
                            "lean": ["Lean 4.32.0, commit fixture", "0123456789abcdef"],
                            "options": {"IdlaCyl": [], module: []},
                        }
                    ))
                    stack.enter_context(redirect_stdout(stdout))
                    stack.enter_context(redirect_stderr(stderr))
                    status = check_warnings.main()
                self.assertEqual(status, 1)
                self.assertIn("rebuild required", stderr.getvalue())
                if mutation == "module":
                    self.assertIn("module identity", stderr.getvalue())
                elif mutation == "module_hash":
                    self.assertIn("Module.name identity/hash", stderr.getvalue())
                elif mutation in ("input_path", "same_path_spelling"):
                    self.assertIn("source input", stderr.getvalue())
                else:
                    self.assertIn("warning source", stderr.getvalue())

    def test_gate_propagates_each_isolated_checker_failure(self) -> None:
        for failing in ("check_axioms.py", "check_warnings.py"):
            with self.subTest(failing=failing), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                write_fixture(root)
                shim_dir = root / "bin"
                shim_dir.mkdir()
                python_shim = shim_dir / "python3"
                python_shim.write_text(
                    "#!/usr/bin/env bash\n"
                    "case ${1:-} in\n"
                    "  tools/check_axioms.py|tools/check_warnings.py)\n"
                    "    if [[ $1 == \"$FAIL_CHECKER\" ]]; then exit 23; fi\n"
                    "    exit 0;;\n"
                    "  tools/manifest.py) exit 0;;\n"
                    "  *) exec \"$REAL_PYTHON\" \"$@\";;\n"
                    "esac\n", encoding="utf-8",
                )
                python_shim.chmod(0o755)
                lake_shim = shim_dir / "lake"
                lake_shim.write_text("#!/usr/bin/env bash\nexit 0\n", encoding="utf-8")
                lake_shim.chmod(0o755)
                report = root / "gate-report.md"
                env = {**os.environ, "PATH": str(shim_dir) + os.pathsep + os.environ["PATH"],
                       "IDLA_GATE_REPORT": str(report), "FAIL_CHECKER": f"tools/{failing}",
                       "REAL_PYTHON": sys.executable, "HOME": str(root)}
                result = subprocess.run(
                    ["bash", str(root / "tools" / "gate.sh")], cwd=root, env=env,
                    capture_output=True, text=True, check=False, timeout=30,
                )
                self.assertNotEqual(result.returncode, 0)
                gate_report = report.read_text(encoding="utf-8")
                self.assertIn(f"{('axiom' if failing == 'check_axioms.py' else 'warning')} checker failed (exit 23)", gate_report)
                other = "warning" if failing == "check_axioms.py" else "axiom"
                self.assertIn(f"{other} checker passed", gate_report)
                self.assertIn("GATE FAILED", gate_report)

    def test_real_trace_rejects_hash_version_and_options_mutations(self) -> None:
        source = REPO / "IdlaCyl" / "Frozen" / "ClmQOnEcV3.lean"
        trace_path = check_warnings.trace_path_for_source(source)
        with check_warnings.global_build_lock():
            provenance = check_warnings.current_trace_inputs({trace_path: source})
            trace = json.loads(trace_path.read_text(encoding="utf-8"))
        self.assertEqual(check_warnings.trace_identity_errors(
            trace_path, trace, source, provenance), [])
        module = check_warnings.expected_module(source)

        def input_row(rows, matches):
            found = [item for item in rows if isinstance(item, list) and len(item) == 2
                     and isinstance(item[0], str) and matches(item[0])]
            self.assertEqual(len(found), 1, [item[0] for item in rows if isinstance(item, list)])
            return found[0]

        def is_source(key):
            return key.endswith(".lean") and Path(key).resolve() == source.resolve()

        for mutation, expected in (
            ("source", "source content hash"),
            ("module_hash", "Module.name identity/hash"),
            ("same_path_spelling", "source input"),
            ("version", "Lean version/commit"),
            ("options", "effective options"),
        ):
            with self.subTest(mutation=mutation):
                changed = copy.deepcopy(trace)
                rows = changed["inputs"]
                if mutation == "source":
                    row = input_row(rows, is_source)
                    row[1] = "0000000000000000"
                elif mutation == "module_hash":
                    row = input_row(rows, lambda key: key == f"Module.name: {module}")
                    row[1] = "0000000000000000"
                elif mutation == "same_path_spelling":
                    row = input_row(rows, is_source)
                    row[0] = str(Path(row[0]).parent) + "/./" + Path(row[0]).name
                    self.assertEqual(Path(row[0]).resolve(), source.resolve())
                elif mutation == "version":
                    row = input_row(rows, lambda key: key.startswith("Lean "))
                    row[0] = "Lean 0.0.0, commit " + "0" * 40
                else:
                    row = input_row(rows, lambda key: key == "options")
                    row[1][0][1] = "0000000000000000"
                errors = check_warnings.trace_identity_errors(
                    trace_path, changed, source, provenance)
                self.assertTrue(any(expected in error for error in errors), errors)


class ExistingGateBehaviorTests(unittest.TestCase):
    def test_actual_manifest_census_is_complete(self) -> None:
        nodes = check_axioms.load_nodes()
        self.assertEqual(len(nodes), 41)
        self.assertEqual(sum(len(node["decls"]) for node in nodes), 57)
        self.assertEqual(nodes, check_warnings.load_nodes())

    def test_axiom_probe_contains_all_registered_declarations(self) -> None:
        nodes = check_axioms.load_nodes()
        source, expected = check_axioms.probe_source(nodes)
        self.assertEqual(len(expected), 57)
        self.assertIn("import IdlaCyl.Frozen.PrInnerStoppedV2", source)
        self.assertIn("import IdlaCyl.External.Discharge.Bernstein", source)
        self.assertIn("import IdlaCyl.Frozen.GFFV3", source)
        self.assertIn("#print axioms IdlaCyl.Frozen.pr_inner", source)
        self.assertIn("#print axioms IdlaCyl.External.thm_martingale_clt", source)
        self.assertEqual(expected["IdlaCyl.External.silvestriTV"]["declaration_kind"], "def")
        self.assertFalse(expected["IdlaCyl.External.silvestriTV"]["draft_export"])
        self.assertFalse(expected["IdlaCyl.Frozen.pr_reduction"]["draft_export"])

    def test_axiom_output_requires_every_requested_name_once(self) -> None:
        output = "\n".join([
            "'IdlaCyl.Frozen.done' depends on axioms: [propext, Quot.sound]",
            "IdlaCyl.Frozen.draft depends on axioms: [sorryAx]",
        ])
        reports, errors = check_axioms.parse_axiom_output(
            output, {"IdlaCyl.Frozen.done", "IdlaCyl.Frozen.draft"}
        )
        self.assertEqual(errors, [])
        self.assertEqual(reports["IdlaCyl.Frozen.done"], {"propext", "Quot.sound"})
        self.assertEqual(reports["IdlaCyl.Frozen.draft"], {"sorryAx"})

    def test_source_census_has_only_registered_drafts(self) -> None:
        nodes = check_warnings.load_nodes()
        expected, allowed, errors = check_warnings.draft_source_locations(nodes)
        tokens = check_warnings.production_sorry_tokens()
        actual = Counter(
            (path, line) for path, lines in tokens.items() for line in lines
        )
        self.assertEqual(errors, [])
        self.assertEqual(sum(expected.values()), 0)
        self.assertEqual(sum(allowed.values()), 0)
        self.assertEqual(sum(actual.values()), 0)
        self.assertEqual(actual - allowed, Counter())


if __name__ == "__main__":
    unittest.main()
