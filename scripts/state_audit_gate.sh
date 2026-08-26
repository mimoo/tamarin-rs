#!/usr/bin/env bash
# Cross-fork gate for `--state-audit`: run BOTH binaries over the same
# theories and check that a consumer reading either one sees the same thing —
# the same report content and the same exit code.
#
# This gate's reference side is NOT the pristine upstream oracle the other
# gates use.  `--state-audit` is a ZKSec-branch addition, so the only
# reference is our HASKELL FORK's build of the same mode (the `zksec` branch
# of the tamarin-prover fork).  Point HS_PATH at it; a pristine 1.12/1.13
# binary rejects the flag and this gate will say so rather than pass
# vacuously.
#
# WHAT IS COMPARED, and what deliberately is not:
#   * compared: `summary`, every lemma's name/quantifier/prover_status/
#     audit_outcome/steps, and the process exit code.
#   * NOT compared: `processing_time_seconds` (wall clock — the Rust side is
#     the faster one, which is the point), the `input_file` / `trace_file`
#     paths (run-local), and the serialised BYTES.  Object-key order is not
#     part of the schema: aeson does not preserve the written order and
#     serde_json sorts, so both sides are read through a JSON parser, never
#     diffed as text.
#
# Env: RS_PATH, HS_PATH, CORPUS (a file listing theories, one per line),
#      FILE_TIMEOUT.
# Output TSV (3 col): relpath  MATCH|DIFF|SKIP_*  detail
set -u
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root=$(dirname "$script_dir")
[ -r "$script_dir/gate_common.sh" ] || { echo "state_audit_gate: missing $script_dir/gate_common.sh (owns the shared gate helpers)" >&2; exit 2; }
. "$script_dir/gate_common.sh"
oom_prologue
# Both provers resolve `maude` by NAME from PATH when no --with-maude is
# passed; the resolver honours the operator's MAUDE_PATH/PATH first.
MAUDE=$(resolve_maude) || exit 2
maude_on_path "$MAUDE"

RS_PATH="${RS_PATH:-$repo_root/target/release/tamarin-rs}"
FILE_TIMEOUT="${FILE_TIMEOUT:-300}"
RESULTS_TSV="${RESULTS_TSV:-$script_dir/results/state_audit_gate_results.tsv}"
# Default corpus: the in-repo fixture, whose four lemmas cover all four
# conclusive outcomes.  Point CORPUS at a file list to gate real models.
CORPUS="${CORPUS:-}"

[ -x "$RS_PATH" ] || { echo "state_audit_gate: no RS binary at $RS_PATH (cargo build --release)" >&2; exit 2; }

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
    echo "state_audit_gate: no Haskell-fork binary (set HS_PATH to a build of the fork's zksec branch)" >&2
    exit 2
}
# A pristine binary has no --state-audit; catching that here keeps the gate
# from reporting every file as a DIFF against an empty report.
if ! "$HS_PATH" --help 2>&1 | grep -q -- '--state-audit'; then
    echo "state_audit_gate: $HS_PATH does not implement --state-audit — point HS_PATH at a build of the fork's zksec branch" >&2
    exit 2
fi

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
        t["trace_file"] = "<traces>" if t.get("trace_file") else None
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

files=()
if [ -n "$CORPUS" ]; then
    [ -r "$CORPUS" ] || { echo "state_audit_gate: cannot read CORPUS list $CORPUS" >&2; exit 2; }
    # A read loop rather than the `mapfile` the older gates use: this one is
    # also run from a dev box, and macOS ships bash 3.2, where `mapfile` is
    # missing and `set -u` then dies on an unset array — a silent vacuous run.
    while IFS= read -r line || [ -n "$line" ]; do
        case "$line" in ''|'#'*) continue;; esac
        files+=("$line")
    done < "$CORPUS"
else
    files=("$repo_root/crates/tamarin-prover/tests/fixtures/state_audit.spthy")
fi
[ "${#files[@]}" -gt 0 ] || { echo "state_audit_gate: CORPUS $CORPUS listed no theories" >&2; exit 2; }

fail=0
for f in "${files[@]}"; do
    [ -n "$f" ] || continue
    rel="${f#"$repo_root"/}"
    if [ ! -r "$f" ]; then
        printf '%s\tSKIP_NOFILE\t-\n' "$rel" >> "$RESULTS_TSV"; fail=1; continue
    fi
    hs_json="$work/hs.json"; rs_json="$work/rs.json"
    rm -f "$hs_json" "$rs_json"

    timeout "$FILE_TIMEOUT" "$HS_PATH" "--state-audit=$hs_json" "$f" >/dev/null 2>&1
    hs_rc=$?
    timeout "$FILE_TIMEOUT" "$RS_PATH" "--state-audit=$rs_json" "$f" >/dev/null 2>&1
    rs_rc=$?

    # 124 is timeout(1)'s own code: a run that never produced a verdict must
    # not be read as a verdict that happened to match.
    if [ "$hs_rc" = 124 ] || [ "$rs_rc" = 124 ]; then
        printf '%s\tSKIP_TIMEOUT\ths_rc=%s rs_rc=%s\n' "$rel" "$hs_rc" "$rs_rc" >> "$RESULTS_TSV"; fail=1; continue
    fi
    if [ "$hs_rc" != "$rs_rc" ]; then
        printf '%s\tDIFF\texit code hs=%s rs=%s\n' "$rel" "$hs_rc" "$rs_rc" >> "$RESULTS_TSV"; fail=1; continue
    fi
    if detail=$(compare_reports "$hs_json" "$rs_json"); then
        printf '%s\tMATCH\trc=%s\n' "$rel" "$rs_rc" >> "$RESULTS_TSV"
    else
        printf '%s\tDIFF\t%s\n' "$rel" "$(echo "$detail" | head -2 | tr '\n' ' ')" >> "$RESULTS_TSV"; fail=1
    fi
done

cat "$RESULTS_TSV"
matched=$(grep -c $'\tMATCH\t' "$RESULTS_TSV" || true)
echo "state_audit_gate: $matched/${#files[@]} match"
exit "$fail"
