//! `--state-audit` end-to-end pins.
//!
//! `--state-audit` is a ZKSec-branch addition with no counterpart in the
//! pristine submodule, so there is no upstream oracle to capture bytes from.
//! What it DOES have is our Haskell fork, which implements the same mode; the
//! contract these tests pin is the one a consumer reads off either binary —
//! the report schema, the console lines, and the exit code — so an audit can
//! be run on either and the results compared.  (`scripts/state_audit_gate.sh`
//! runs that comparison against a built Haskell fork; these tests do not need
//! one.)
//!
//! The fixture is the Haskell fork's own `examples/features/state-audit.spthy`
//! verbatim, chosen because its four lemmas cover all four CONCLUSIVE
//! outcomes at once — including the pair the mode exists for, where the same
//! solved trace is a counterexample under `all-traces` and a witness under
//! `exists-trace`.
//!
//! Maude: [`maude_available`] resolves through the common harness ladder and
//! PANICS when nothing resolves, so a bare `cargo test` cannot skip these
//! pins silently; `TAM_ALLOW_NO_MAUDE=1` is the only opt-in to the skip.

mod common;

use std::path::PathBuf;

use common::{fixture, maude_available, run_binary};

/// The Haskell fork's audit example: `transition_is_executable`
/// (exists-trace, satisfied), `missing_transition_witness` (exists-trace,
/// unsatisfiable), `transitioned_state_was_initialized` (all-traces, holds),
/// `transition_is_unreachable` (all-traces, falsified).
const THEORY: &str = "state_audit.spthy";

/// A fresh per-test temp dir, so the derived trace targets of concurrent
/// tests cannot collide.
fn case(test: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tamarin_rs_state_audit_{test}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("mkdir");
    dir
}

fn read_report(path: &std::path::Path) -> serde_json::Value {
    let body =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    serde_json::from_str(&body).expect("the report is JSON")
}

/// Index a theory's lemma rows by name — declaration order is the prover's
/// business, not the audit's contract.
fn outcomes(report: &serde_json::Value) -> Vec<(String, String)> {
    report["theories"][0]["lemmas"]
        .as_array()
        .expect("lemmas array")
        .iter()
        .map(|l| {
            (
                l["name"].as_str().expect("name").to_string(),
                l["audit_outcome"].as_str().expect("outcome").to_string(),
            )
        })
        .collect()
}

/// The headline pin: one run, all four conclusive outcomes, and the exit code
/// that makes the mode usable in CI.  Note `transition_is_executable` and
/// `transition_is_unreachable` are the SAME underlying solved trace read
/// under the two quantifiers.
#[test]
fn a_falsified_property_is_reported_and_exits_two() {
    if !maude_available() {
        return;
    }
    let dir = case("falsified");
    let report_path = dir.join("audit.json");
    let (rc, stdout, _) = run_binary(
        &[&format!("--state-audit={}", report_path.display())],
        &[&fixture(THEORY)],
    );

    assert_eq!(rc, 2, "a falsified selected property exits 2\n{stdout}");
    assert!(
        stdout.contains(
            "state audit: 2 clean, 1 counterexample(s), 1 missing witness(es), 0 inconclusive"
        ),
        "{stdout}"
    );
    // The console names what the audit could NOT clear, and only that.
    assert!(
        stdout.contains("counterexample  ") && stdout.contains("transition_is_unreachable"),
        "{stdout}"
    );
    assert!(
        stdout.contains("no_witness      ") && stdout.contains("missing_transition_witness"),
        "{stdout}"
    );
    assert!(
        !stdout.contains("transitioned_state_was_initialized"),
        "a clean lemma belongs in the report, not the console:\n{stdout}"
    );

    let report = read_report(&report_path);
    assert_eq!(report["schema_version"], 1);
    assert_eq!(report["mode"], "state-transition-audit");
    assert_eq!(report["summary"]["property_verified"], 1);
    assert_eq!(report["summary"]["witness_found"], 1);
    assert_eq!(report["summary"]["counterexamples"], 1);
    assert_eq!(report["summary"]["no_witness"], 1);
    assert_eq!(report["summary"]["inconclusive"], 0);

    let mut got = outcomes(&report);
    got.sort();
    assert_eq!(
        got,
        vec![
            (
                "missing_transition_witness".to_string(),
                "no_witness".to_string()
            ),
            (
                "transition_is_executable".to_string(),
                "witness_found".to_string()
            ),
            (
                "transition_is_unreachable".to_string(),
                "counterexample".to_string()
            ),
            (
                "transitioned_state_was_initialized".to_string(),
                "property_verified".to_string()
            ),
        ]
    );
}

/// The mode is COMPACT: the closed-theory dump the same run would otherwise
/// print is replaced by the report, and so is the `summary of summaries:`
/// block.  A CI consumer reads the JSON, not megabytes of theory.
#[test]
fn the_theory_dump_and_summary_block_are_replaced_by_the_report() {
    if !maude_available() {
        return;
    }
    let dir = case("compact");
    let report_path = dir.join("audit.json");
    let (_, stdout, _) = run_binary(
        &[&format!("--state-audit={}", report_path.display())],
        &[&fixture(THEORY)],
    );

    assert!(
        !stdout.contains("summary of summaries:"),
        "the report replaces the summary block:\n{stdout}"
    );
    assert!(
        !stdout.contains("theory State_Audit begin"),
        "the report replaces the theory dump:\n{stdout}"
    );
    // Exactly the four audit lines: headline, two diagnostics, report path.
    assert_eq!(stdout.lines().count(), 4, "{stdout}");
}

/// `--state-audit` implies `--prove` — the mode is useless if it reports on
/// unproved `sorry` placeholders, and the Haskell fork folds the same
/// implication into `proveMode`.
#[test]
fn the_audit_proves_without_an_explicit_prove_flag() {
    if !maude_available() {
        return;
    }
    let dir = case("implies_prove");
    let report_path = dir.join("audit.json");
    // No `--prove` anywhere in the argv.
    let (rc, _, _) = run_binary(
        &[&format!("--state-audit={}", report_path.display())],
        &[&fixture(THEORY)],
    );
    assert_eq!(rc, 2);

    let report = read_report(&report_path);
    // Every lemma decided: nothing left at the 1-step `sorry` placeholder an
    // unproved run would report.
    for lemma in report["theories"][0]["lemmas"].as_array().expect("lemmas") {
        assert_ne!(lemma["audit_outcome"], "incomplete", "{lemma}");
    }
}

/// `--lemma` narrows the audit the way it narrows the prover.  The lemmas it
/// excludes are ABSENT, not "inconclusive" — the prove loop leaves their
/// stored `sorry` proofs in place, so reporting on the verdict alone would
/// make every narrowed audit exit 3.
#[test]
fn a_lemma_selector_narrows_the_audit_to_a_clean_exit() {
    if !maude_available() {
        return;
    }
    let dir = case("narrowed");
    let report_path = dir.join("audit.json");
    let (rc, stdout, _) = run_binary(
        &[
            &format!("--state-audit={}", report_path.display()),
            "--lemma=transitioned_state_was_initialized",
        ],
        &[&fixture(THEORY)],
    );

    assert_eq!(rc, 0, "every selected lemma holds\n{stdout}");
    assert!(
        stdout.contains(
            "state audit: 1 clean, 0 counterexample(s), 0 missing witness(es), 0 inconclusive"
        ),
        "{stdout}"
    );
    let report = read_report(&report_path);
    assert_eq!(
        outcomes(&report),
        vec![(
            "transitioned_state_was_initialized".to_string(),
            "property_verified".to_string()
        )]
    );
}

/// A search that cannot finish is `incomplete` and exits 3 — distinct from
/// both "holds" (0) and "falsified" (2), so CI can tell an unproven audit
/// from a passing one.
#[test]
fn an_unfinished_search_is_inconclusive_and_exits_three() {
    if !maude_available() {
        return;
    }
    let dir = case("inconclusive");
    let report_path = dir.join("audit.json");
    let (rc, stdout, _) = run_binary(
        &[
            &format!("--state-audit={}", report_path.display()),
            "--bound=1",
            "--lemma=transitioned_state_was_initialized",
        ],
        &[&fixture(THEORY)],
    );

    assert_eq!(rc, 3, "{stdout}");
    assert!(stdout.contains("1 inconclusive"), "{stdout}");
    let report = read_report(&report_path);
    assert_eq!(
        outcomes(&report),
        vec![(
            "transitioned_state_was_initialized".to_string(),
            "incomplete".to_string()
        )]
    );
}

/// The audit defaults a trace target on, so a reported counterexample always
/// has a serialised trace to point at, and the report names it.  The path is
/// per-theory, so a multi-file audit's files do not overwrite each other.
#[test]
fn the_report_points_at_a_trace_file_the_run_wrote() {
    if !maude_available() {
        return;
    }
    let dir = case("traces");
    let report_path = dir.join("audit.json");
    run_binary(
        &[&format!("--state-audit={}", report_path.display())],
        &[&fixture(THEORY)],
    );

    let report = read_report(&report_path);
    let named = report["theories"][0]["trace_file"]
        .as_str()
        .expect("the audit names a trace file");
    assert_eq!(
        named,
        format!("{}.state_audit.traces.json", report_path.display())
    );
    let body = std::fs::read_to_string(named).expect("the named trace file exists");
    assert!(body.contains("\"graphs\""), "{body:.200}");
}

/// An explicit `--output-json` wins over the derived default: the audit
/// borrows the existing flag rather than fighting it.
#[test]
fn an_explicit_output_json_wins_over_the_derived_target() {
    if !maude_available() {
        return;
    }
    let dir = case("explicit_traces");
    let report_path = dir.join("audit.json");
    let traces = dir.join("mine.json");
    run_binary(
        &[
            &format!("--state-audit={}", report_path.display()),
            &format!("--output-json={}", traces.display()),
        ],
        &[&fixture(THEORY)],
    );

    let report = read_report(&report_path);
    assert_eq!(
        report["theories"][0]["trace_file"],
        serde_json::Value::String(traces.display().to_string())
    );
    assert!(traces.exists(), "the explicit target was written");
    assert!(
        !dir.join("audit.json.state_audit.traces.json").exists(),
        "no derived file when the target was given"
    );
}

/// The report path's directory is created on demand — a CI job writing to
/// `reports/audit.json` should not have to `mkdir` first.
#[test]
fn a_missing_report_directory_is_created() {
    if !maude_available() {
        return;
    }
    let dir = case("mkdir");
    let report_path = dir.join("nested").join("deeper").join("audit.json");
    let (rc, stdout, _) = run_binary(
        &[
            &format!("--state-audit={}", report_path.display()),
            "--lemma=transitioned_state_was_initialized",
        ],
        &[&fixture(THEORY)],
    );
    assert_eq!(rc, 0, "{stdout}");
    assert!(report_path.exists());
}

/// Two theories in one run land as two `theories` entries with their own
/// trace targets, and the exit code is the whole run's.
#[test]
fn a_multi_theory_run_reports_each_file() {
    if !maude_available() {
        return;
    }
    let dir = case("multi");
    let report_path = dir.join("audit.json");
    // A second copy under a different stem, so the derived trace targets
    // differ and neither overwrites the other.
    let second = dir.join("second.spthy");
    std::fs::copy(fixture(THEORY), &second).expect("copy fixture");

    let (rc, _, _) = run_binary(
        &[
            &format!("--state-audit={}", report_path.display()),
            "--lemma=transitioned_state_was_initialized",
        ],
        &[&fixture(THEORY), &second],
    );
    assert_eq!(rc, 0);

    let report = read_report(&report_path);
    let theories = report["theories"].as_array().expect("theories");
    assert_eq!(theories.len(), 2);
    assert_eq!(report["summary"]["property_verified"], 2);
    let a = theories[0]["trace_file"].as_str().expect("trace a");
    let b = theories[1]["trace_file"].as_str().expect("trace b");
    assert_ne!(a, b, "each theory gets its own trace target");
    assert!(std::path::Path::new(a).exists() && std::path::Path::new(b).exists());
}
