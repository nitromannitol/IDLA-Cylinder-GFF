#!/usr/bin/env bash
# Run the manifest, build, axiom, warning and audit checks.  With IDLA_LAKE_LOCK naming a
# file, the whole gate runs under an exclusive flock on it, so that no other Lake process
# writes the build directories meanwhile.
set -uo pipefail

if [[ -n "${IDLA_LAKE_LOCK:-}" ]]; then
  # The checkers reuse the lock held on file descriptor 3 instead of taking it again.
  exec 3>>"$IDLA_LAKE_LOCK" || exit 1
  /usr/bin/flock -x 3 || exit 1
fi

cd "$(dirname "$0")/.." || exit 1
export PATH="${HOME:?}/.elan/bin:$PATH"
if [[ -L .lake/build || ( -e .lake/build && ! -d .lake/build ) ]]; then
  printf '%s\n' 'gate: .lake/build must be a physical directory' >&2
  exit 1
fi
mkdir -p .lake/build || exit 1
if [[ "$(readlink -f .lake/build)" != "$(pwd -P)/.lake/build" ]]; then
  printf '%s\n' 'gate: .lake/build is outside this checkout' >&2
  exit 1
fi

SHA=$(git rev-parse --short HEAD 2>/dev/null || echo nogit)
REPORT=${IDLA_GATE_REPORT:-".lake/build/reports/gate-${SHA}.md"}
mkdir -p "$(dirname "$REPORT")"
FAIL=0

say() { printf '%s\n' "$*" | tee -a "$REPORT"; }

: > "$REPORT"
say "# Gate report \`${SHA}\`"
say ""
say "Run $(date -u '+%Y-%m-%d %H:%M:%SZ')."
say ""

run_check() {
  local heading=$1
  local description=$2
  shift 2
  say "## ${heading}"
  say ""
  say '```'
  "$@" 2>&1 | tee -a "$REPORT"
  local status=${PIPESTATUS[0]}
  say '```'
  if [ "$status" -ne 0 ]; then
    FAIL=1
    say "**${description} failed (exit ${status}).**"
  else
    say "**${description} passed.**"
  fi
  say ""
}

run_check "Manifest" "manifest check" python3 tools/manifest.py check
run_check "Build" "lake build IdlaCyl" lake build IdlaCyl
run_check "Axiom closure" "axiom checker" python3 tools/check_axioms.py
run_check "Warnings" "warning checker" python3 tools/check_warnings.py
AUDIT_LOG=$(mktemp)
run_check "Comparator audit build" "lake build IdlaCylAudit" bash -c \
  "set -o pipefail; lake build IdlaCylAudit 2>&1 | tee '$AUDIT_LOG'"
run_check "Comparator audit structure" "audit checker" python3 tools/check_audit.py "$AUDIT_LOG"
rm -f "$AUDIT_LOG"

say "## Open obligations"
say ""
say "| file | sorry tokens |"
say "|---|---:|"
OBLIGATION_DATA=$(python3 - <<'PY'
import sys
sys.path.insert(0, "tools")
import check_warnings

found = check_warnings.production_sorry_tokens()
for path, lines in sorted(found.items(), key=lambda item: (-len(item[1]), item[0])):
    print(f"{path}\t{len(lines)}")
print(f"TOTAL\t{sum(len(lines) for lines in found.values())}")
PY
)
OBLIGATION_STATUS=$?
if [ "$OBLIGATION_STATUS" -ne 0 ]; then
  FAIL=1
  say "**Could not count open obligations (exit ${OBLIGATION_STATUS}).**"
else
  while IFS=$'\t' read -r file count; do
    [ -z "$file" ] && continue
    if [ "$file" = "TOTAL" ]; then
      TOTAL=$count
    else
      say "| \`${file}\` | ${count} |"
    fi
  done <<< "$OBLIGATION_DATA"
  say ""
  say "**${TOTAL:-0} open obligation(s).**"
fi
say ""

say "---"
if [ "$FAIL" -eq 0 ]; then
  say "**GATE PASSED** — ${TOTAL:-0} open obligation(s) remain."
else
  say "**GATE FAILED**"
fi
exit "$FAIL"
