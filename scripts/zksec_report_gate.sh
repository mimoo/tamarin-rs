#!/usr/bin/env bash
# Cross-fork gate for the ZKSec report modes (`--state-audit`,
# `--proof-diagnostics`): run BOTH binaries over the same theories in each
# mode and check that a consumer reading either one sees the same thing — the
# same report content and the same exit code.
#
# This gate's reference side is NOT the pristine upstream oracle the other
# gates use.  Both modes are ZKSec-branch additions, so the only reference is
# our HASKELL FORK's build of them (the `zksec` branch of the tamarin-prover
# fork).  Point HS_PATH at it; a pristine 1.12/1.13 binary rejects the flags
# and this gate says so rather than passing vacuously.
#
# WHAT IS COMPARED, and what deliberately is not:
#   * compared: the whole report bar the fields below — for `--state-audit`
#     the `summary` and every lemma's name/quantifier/prover_status/
#     audit_outcome/steps; for `--proof-diagnostics` the `summary` and every
#     open state's lemma/path/kind/reason/requested_method/formulas/
#     open_goals/applicable_methods/constraint_system.  Plus the exit code.
#   * NOT compared: `processing_time_seconds` (wall clock — the Rust side is
#     the faster one, which is the point), the `input_file` / `trace_file`
#     paths (run-local), and the serialised BYTES.  Object-key order is not
#     part of the schema: aeson does not preserve the written order and
#     serde_json sorts, so both sides are read through a JSON parser, never
#     diffed as text.
#
# Env: RS_PATH, HS_PATH, MODE (state-audit | proof-diagnostics | both;
#      default both), CORPUS (a file listing theories, one per line),
#      FILE_TIMEOUT, RESULTS_TSV.
# A corpus list should hold theories BOTH binaries can load as invoked here:
# this gate passes no per-file flags, so a `--diff` model (or anything else
# needing them) is refused by both sides, compares nothing, and reports
# SKIP_NOREPORT — a failing status, as a no-compare is in every other gate.
#
# A report DIFF is re-checked against the plain LOAD before it is reported as
# one: both modes read the proof tree the load produces, and outside
# scripts/parity_corpus.txt the port does not claim that tree is byte-identical
# (the SAPIC manual-proof theories are not in the corpus, and their replay does
# differ).  Such a file reports DIFF_PREEXISTING — still a failure, but not the
# report mode's.
#
# Output TSV (4 col): relpath  mode  MATCH|DIFF|DIFF_PREEXISTING|SKIP_*  detail
set -u
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root=$(dirname "$script_dir")
[ -r "$script_dir/gate_common.sh" ] || { echo "zksec_report_gate: missing $script_dir/gate_common.sh (owns the shared gate helpers)" >&2; exit 2; }
. "$script_dir/gate_common.sh"
oom_prologue
# Both provers resolve `maude` by NAME from PATH when no --with-maude is
# passed; the resolver honours the operator's MAUDE_PATH/PATH first.
MAUDE=$(resolve_maude) || exit 2
maude_on_path "$MAUDE"

RS_PATH="${RS_PATH:-$repo_root/target/release/tamarin-rs}"
FILE_TIMEOUT="${FILE_TIMEOUT:-300}"
RESULTS_TSV="${RESULTS_TSV:-$script_dir/results/zksec_report_gate_results.tsv}"
MODE="${MODE:-both}"
# Default corpus: the two in-repo fixtures.  `state_audit.spthy` carries all
# four conclusive audit outcomes and no stored proof (so every lemma is an
# open `sorry` under the other mode); `proof_diagnostics.spthy` carries a
# partial proof and a stale `solve(...)` step.  Point CORPUS at a file list to
# gate real models.
CORPUS="${CORPUS:-}"

case "$MODE" in
    state-audit)       modes=(state-audit) ;;
    proof-diagnostics) modes=(proof-diagnostics) ;;
    both)              modes=(state-audit proof-diagnostics) ;;
    *) echo "zksec_report_gate: MODE must be state-audit, proof-diagnostics or both (got '$MODE')" >&2; exit 2 ;;
esac

[ -x "$RS_PATH" ] || { echo "zksec_report_gate: no RS binary at $RS_PATH (cargo build --release)" >&2; exit 2; }

# The Haskell FORK's binary — not the pristine oracle the other gates find
# under tamarin-prover-testing/.  Looked for next to this checkout by default.
find_hs_fork_bin() {
    local c
    for c in "$repo_root"/../tamarin-prover-fork/.stack-work/install/*/*/*/bin/tamarin-prover \
             "$repo_root"/../tamarin-prover-fork/.stack-work/dist/*/ghc-*/build/tamarin-prover/tamarin-prover; do
        [ -x "$c" ] && { echo "$c"; return 0; }
    done; return 1
}
HS_PATH="${HS_PATH:-$(find_hs_fork_bin)}" || true
[ -x "${HS_PATH:-/nonexistent}" ] || {
    echo "zksec_report_gate: no Haskell-fork binary (set HS_PATH to a build of the fork's zksec branch)" >&2
    exit 2
}
# A pristine binary has neither flag; catching that here keeps the gate from
# reporting every file as a DIFF against an empty report.
hs_help=$("$HS_PATH" --help 2>&1)
for m in "${modes[@]}"; do
    case "$hs_help" in
        *"--$m"*) ;;
        *) echo "zksec_report_gate: $HS_PATH does not implement --$m — point HS_PATH at a build of the fork's zksec branch" >&2; exit 2 ;;
    esac
done

mkdir -p "$(dirname "$RESULTS_TSV")"
: > "$RESULTS_TSV"
work=$(mktemp -d) || exit 2
trap 'rm -rf "$work"' EXIT

# Strip the run-local fields, then compare the rest structurally.  Exits 0 on
# agreement, 1 on a difference (printing it), 2 if either file is unreadable.
compare_reports() {
    python3 - "$1" "$2" <<'PY'
import json, sys

def norm(path):
    with open(path) as f:
        d = json.load(f)
    for t in d.get("theories", []):
        # Wall clock and run-local paths: not part of what a consumer reads.
        t.pop("processing_time_seconds", None)
        t["input_file"] = "<in>"
        if "trace_file" in t:                    # --state-audit only
            t["trace_file"] = "<traces>" if t["trace_file"] else None
    return d

try:
    a, b = norm(sys.argv[1]), norm(sys.argv[2])
except Exception as e:                      # noqa: BLE001 - reported, not raised
    print(f"unreadable report: {e}")
    sys.exit(2)

if a == b:
    sys.exit(0)
print("HS:", json.dumps(a, sort_keys=True))
print("RS:", json.dumps(b, sort_keys=True))
sys.exit(1)
PY
}

# Do the two forks already disagree on the plain LOAD of this theory — the
# replayed proof tree both report modes read?  Paid only when a report DIFFs,
# so the happy path costs nothing.  The env-volatile lines are dropped the way
# the other gates drop them; anything left is a genuine load difference.
plain_load_differs() {
    local f="$1" strip='/processing time\|Git revision\|Compiled at\|Maude version\|analyzed:/d'
    timeout "$FILE_TIMEOUT" "$HS_PATH" "$f" 2>/dev/null | sed "$strip" > "$work/plain_hs.txt" || return 1
    timeout "$FILE_TIMEOUT" "$RS_PATH" "$f" 2>/dev/null | sed "$strip" > "$work/plain_rs.txt" || return 1
    ! cmp -s "$work/plain_hs.txt" "$work/plain_rs.txt"
}

files=()
if [ -n "$CORPUS" ]; then
    [ -r "$CORPUS" ] || { echo "zksec_report_gate: cannot read CORPUS list $CORPUS" >&2; exit 2; }
    # A read loop rather than the `mapfile` the older gates use: this one is
    # also run from a dev box, and macOS ships bash 3.2, where `mapfile` is
    # missing and `set -u` then dies on an unset array — a silent vacuous run.
    while IFS= read -r line || [ -n "$line" ]; do
        case "$line" in ''|'#'*) continue;; esac
        files+=("$line")
    done < "$CORPUS"
else
    files=("$repo_root/crates/tamarin-prover/tests/fixtures/state_audit.spthy" \
           "$repo_root/crates/tamarin-prover/tests/fixtures/proof_diagnostics.spthy")
fi
[ "${#files[@]}" -gt 0 ] || { echo "zksec_report_gate: CORPUS $CORPUS listed no theories" >&2; exit 2; }

fail=0
runs=0
for mode in "${modes[@]}"; do
    for f in "${files[@]}"; do
        [ -n "$f" ] || continue
        runs=$((runs + 1))
        rel="${f#"$repo_root"/}"
        if [ ! -r "$f" ]; then
            printf '%s\t%s\tSKIP_NOFILE\t-\n' "$rel" "$mode" >> "$RESULTS_TSV"; fail=1; continue
        fi
        hs_json="$work/hs.json"; rs_json="$work/rs.json"
        rm -f "$hs_json" "$rs_json"

        timeout "$FILE_TIMEOUT" "$HS_PATH" "--$mode=$hs_json" "$f" >/dev/null 2>&1
        hs_rc=$?
        timeout "$FILE_TIMEOUT" "$RS_PATH" "--$mode=$rs_json" "$f" >/dev/null 2>&1
        rs_rc=$?

        # 124 is timeout(1)'s own code: a run that never produced a verdict
        # must not be read as a verdict that happened to match.
        if [ "$hs_rc" = 124 ] || [ "$rs_rc" = 124 ]; then
            printf '%s\t%s\tSKIP_TIMEOUT\ths_rc=%s rs_rc=%s\n' "$rel" "$mode" "$hs_rc" "$rs_rc" >> "$RESULTS_TSV"; fail=1; continue
        fi
        if [ "$hs_rc" != "$rs_rc" ]; then
            printf '%s\t%s\tDIFF\texit code hs=%s rs=%s\n' "$rel" "$mode" "$hs_rc" "$rs_rc" >> "$RESULTS_TSV"; fail=1; continue
        fi
        # Neither side wrote a report: both refused the file the same way
        # (typically a theory needing flags this gate does not pass, e.g. a
        # `--diff` model).  That is agreement on the REFUSAL, not on the mode
        # — nothing was compared — so it reports as its own status and fails,
        # the same way the other gates treat a no-compare.  One side writing a
        # report and the other not IS a real DIFF, and falls through below.
        if [ ! -s "$hs_json" ] && [ ! -s "$rs_json" ]; then
            printf '%s\t%s\tSKIP_NOREPORT\tboth refused the file, rc=%s\n' "$rel" "$mode" "$rs_rc" >> "$RESULTS_TSV"; fail=1; continue
        fi
        if detail=$(compare_reports "$hs_json" "$rs_json"); then
            printf '%s\t%s\tMATCH\trc=%s\n' "$rel" "$mode" "$rs_rc" >> "$RESULTS_TSV"
        elif plain_load_differs "$f"; then
            # The report modes read a proof tree the LOAD produced.  When the
            # two forks already disagree on that tree — the port does not
            # claim byte parity outside scripts/parity_corpus.txt, and the
            # SAPIC manual-proof theories are not in it — the reports must
            # disagree too, and the report mode is not the thing at fault.
            # Says so instead of reading as a report-mode regression.  Still
            # fails: it is a real cross-fork difference, just not this
            # gate's to fix.
            printf '%s\t%s\tDIFF_PREEXISTING\tthe plain load already differs; not a report-mode divergence\n' "$rel" "$mode" >> "$RESULTS_TSV"; fail=1
        else
            printf '%s\t%s\tDIFF\t%s\n' "$rel" "$mode" "$(echo "$detail" | head -2 | tr '\n' ' ')" >> "$RESULTS_TSV"; fail=1
        fi
    done
done

cat "$RESULTS_TSV"
matched=$(grep -c $'\tMATCH\t' "$RESULTS_TSV" || true)
echo "zksec_report_gate: $matched/$runs match"
exit "$fail"
