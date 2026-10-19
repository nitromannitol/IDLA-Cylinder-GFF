#!/usr/bin/env bash
# Run the comparator on the challenge/solution pairs of `IdlaCylAudit/`.
#
#   scripts/run_comparators.sh TOOL_ROOT [PAIR ...]
#
# TOOL_ROOT holds builds of the pinned verification tools, laid out as
#   TOOL_ROOT/comparator/.lake/build/bin/comparator     (leanprover/comparator)
#   TOOL_ROOT/lean4export/.lake/build/bin/lean4export   (leanprover/lean4export)
#   TOOL_ROOT/nanoda_lib/target/release/nanoda_bin      (ammkrn/nanoda_lib)
#   TOOL_ROOT/bin/landrun                               (Zouuup/landrun)
# at the revisions recorded in `.github/workflows/comparator.yml`.  With no PAIR, all four
# pairs run.  Each pair passes when the comparator exits 0, prints its success verdict exactly
# once, and reports no warning other than the intentional `sorry` of the challenge.  Logs are
# kept under `.lake/comparator-logs/<PAIR>/`.  If IDLA_LAKE_LOCK names a file, every Lake
# invocation runs under an exclusive `flock` on it.
set -uo pipefail

if [ $# -lt 1 ]; then
  echo "usage: $0 TOOL_ROOT [PAIR ...]" >&2
  exit 2
fi
TOOLS=$(cd "$1" && pwd) || exit 2
shift
cd "$(dirname "$0")/.." || exit 2
PAIRS=("$@")
[ ${#PAIRS[@]} -eq 0 ] && PAIRS=(MaxFluct GFF Cycle Torus)

export COMPARATOR_LANDRUN="$TOOLS/bin/landrun"
export COMPARATOR_LEAN4EXPORT="$TOOLS/lean4export/.lake/build/bin/lean4export"
export COMPARATOR_NANODA="$TOOLS/nanoda_lib/target/release/nanoda_bin"
COMPARATOR="$TOOLS/comparator/.lake/build/bin/comparator"
for tool in "$COMPARATOR" "$COMPARATOR_LEAN4EXPORT" "$COMPARATOR_NANODA" "$COMPARATOR_LANDRUN"; do
  if [ ! -x "$tool" ]; then
    echo "missing tool: $tool" >&2
    exit 2
  fi
done

lake_run() {
  if [ -n "${IDLA_LAKE_LOCK:-}" ]; then
    /usr/bin/flock -x "$IDLA_LAKE_LOCK" lake "$@"
  else
    lake "$@"
  fi
}

FAIL=0
for pair in "${PAIRS[@]}"; do
  config="IdlaCylAudit/$pair/comparator.json"
  if [ ! -f "$config" ]; then
    echo "unknown pair: $pair" >&2
    FAIL=1
    continue
  fi
  logs=".lake/comparator-logs/$pair"
  mkdir -p "$logs"
  echo "== $pair: building the challenge and the solution"
  if ! lake_run build "IdlaCylAudit.$pair.Challenge" "IdlaCylAudit.$pair.Solution" \
      > "$logs/build.log" 2>&1; then
    tail -40 "$logs/build.log"
    echo "== $pair: FAILED (build)"
    FAIL=1
    continue
  fi
  echo "== $pair: running the comparator"
  start=$(date +%s)
  lake_run env "$COMPARATOR" "$config" > "$logs/stdout.log" 2> "$logs/stderr.log"
  status=$?
  echo "exit $status, $(( $(date +%s) - start )) s" > "$logs/result.txt"
  verdicts=$(cat "$logs/stdout.log" "$logs/stderr.log" | grep -c '^Your solution is okay!$')
  other=$(cat "$logs/stdout.log" "$logs/stderr.log" | grep -E '(^|[[:space:]])(warning|error):' |
    grep -v -E "IdlaCylAudit/$pair/Challenge\.lean:[0-9]+:[0-9]+: declaration uses ['\`]sorry['\`]" || true)
  if [ "$status" -eq 0 ] && [ "$verdicts" -eq 1 ] && [ -z "$other" ]; then
    echo "== $pair: PASSED ($(cat "$logs/result.txt"))"
  else
    tail -40 "$logs/stdout.log" "$logs/stderr.log"
    echo "== $pair: FAILED ($(cat "$logs/result.txt"), $verdicts verdicts)"
    FAIL=1
  fi
done
exit "$FAIL"
