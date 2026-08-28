//! `--proof-diagnostics` end-to-end pins.
//!
//! A ZKSec-branch addition, so there is no upstream oracle to capture bytes
//! from; the reference is our Haskell fork, which implements the same mode.
//! What these pin is the contract a consumer reads off either binary — the
//! report schema, the console rendering, and the exit code.
//! (`scripts/zksec_report_gate.sh` runs the comparison against a built
//! Haskell fork; these tests do not need one.)
//!
//! The fixture is the Haskell fork's own
//! `examples/features/proof-diagnostics.spthy` verbatim: one lemma with an
//! explicit `sorry`, and one whose stored `solve(...)` step names a goal the
//! current system does not have — the two kinds the mode exists to
//! distinguish.
//!
//! Maude: [`maude_available`] resolves through the common harness ladder and
//! PANICS when nothing resolves, so a bare `cargo test` cannot skip these
//! pins silently; `TAM_ALLOW_NO_MAUDE=1` is the only opt-in to the skip.

mod common;

use std::path::PathBuf;

use common::{fixture, maude_available, run_binary};

/// `partial_reachability` (exists-trace, `by sorry`) and
/// `deliberately_false_secrecy` (all-traces, `simplify` then a stale
/// `solve(!KU('wrong-value') @ #wrong_node)`).
const THEORY: &str = "proof_diagnostics.spthy";

/// A theory with no stored proof at all: every lemma is an open `sorry` at
/// its own start system.
const PROOFLESS: &str = "state_audit.spthy";

fn case(test: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tamarin_rs_proof_diagnostics_{test}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("mkdir");
    dir
}

fn read_report(path: &std::path::Path) -> serde_json::Value {
    let body =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    serde_json::from_str(&body).expect("the report is JSON")
}

/// `(lemma, kind)` for each reported state, in report order.
fn states(report: &serde_json::Value) -> Vec<(String, String)> {
    report["theories"][0]["diagnostics"]
        .as_array()
        .expect("diagnostics array")
        .iter()
        .map(|d| {
            (
                d["lemma"].as_str().expect("lemma").to_string(),
                d["kind"].as_str().expect("kind").to_string(),
            )
        })
        .collect()
}

/// The headline pin: both kinds in one run, and the exit code that makes the
/// mode usable in CI.
#[test]
fn open_and_invalid_states_are_reported_and_exit_four() {
    if !maude_available() {
        return;
    }
    let dir = case("open_states");
    let report_path = dir.join("diag.json");
    let (rc, stdout, _) = run_binary(
        &[&format!("--proof-diagnostics={}", report_path.display())],
        &[&fixture(THEORY)],
    );

    assert_eq!(rc, 4, "open proof states exit 4\n{stdout}");
    assert!(
        stdout.contains("proof diagnostics: 2 open proof state(s)"),
        "{stdout}"
    );

    let report = read_report(&report_path);
    assert_eq!(report["schema_version"], 1);
    assert_eq!(report["mode"], "proof-diagnostics");
    assert_eq!(report["summary"]["open_proof_states"], 2);
    assert_eq!(report["summary"]["sorries"], 1);
    assert_eq!(report["summary"]["invalid_steps"], 1);
    assert_eq!(report["summary"]["unhandled_cases"], 0);

    assert_eq!(
        states(&report),
        vec![
            ("partial_reachability".to_string(), "sorry".to_string()),
            (
                "deliberately_false_secrecy".to_string(),
                "invalid_step".to_string()
            ),
        ]
    );
}

/// The point of the `invalid_step` kind: it names the STORED step that no
/// longer applies, and the methods that do — which is what a reader needs to
/// repair a proof after a source edit.
#[test]
fn an_invalid_step_names_what_was_asked_for_and_what_applies() {
    if !maude_available() {
        return;
    }
    let dir = case("invalid_step");
    let report_path = dir.join("diag.json");
    let (_, stdout, _) = run_binary(
        &[&format!("--proof-diagnostics={}", report_path.display())],
        &[&fixture(THEORY)],
    );

    let report = read_report(&report_path);
    let invalid = report["theories"][0]["diagnostics"]
        .as_array()
        .expect("diagnostics")
        .iter()
        .find(|d| d["kind"] == "invalid_step")
        .expect("the stale solve( … ) step");

    assert_eq!(invalid["reason"], "invalid proof step encountered");
    // The stored step, verbatim from the source's `solve(...)`.
    assert_eq!(
        invalid["requested_method"],
        "solve( !KU( 'wrong-value' ) @ #wrong_node )"
    );
    // The goal the system actually has — a DIFFERENT one, which is why the
    // stored step failed.
    assert_eq!(invalid["open_goals"][0], "!KU( ~value ) @ #vk");
    assert_eq!(
        invalid["applicable_methods"][0],
        "solve( !KU( ~value ) @ #vk )"
    );
    // Reached under the root's single unnamed case.
    assert_eq!(invalid["path"][0], "(single-case)");
    // The full system is in the file...
    assert!(invalid["constraint_system"]
        .as_str()
        .expect("constraint system")
        .contains("unsolved constraints:"));
    // ...and not on the console.
    assert!(!stdout.contains("unsolved constraints:"), "{stdout}");
    // The console does carry the locating line and the repair hints.
    assert!(stdout.contains("requested: solve( !KU( 'wrong-value' ) @ #wrong_node )"));
    assert!(stdout.contains("solve( !KU( ~value ) @ #vk )"));
}

/// A theory with no stored proof reports one open `sorry` per lemma, at the
/// lemma's own start system — "this lemma has no proof" is exactly what the
/// mode should say about it.
#[test]
fn a_proofless_theory_reports_every_lemma() {
    if !maude_available() {
        return;
    }
    let dir = case("proofless");
    let report_path = dir.join("diag.json");
    let (rc, stdout, _) = run_binary(
        &[&format!("--proof-diagnostics={}", report_path.display())],
        &[&fixture(PROOFLESS)],
    );

    assert_eq!(rc, 4, "{stdout}");
    let report = read_report(&report_path);
    assert_eq!(report["summary"]["open_proof_states"], 4);
    assert_eq!(report["summary"]["sorries"], 4);
    for (_, kind) in states(&report) {
        assert_eq!(kind, "sorry");
    }
    // Each carries its own lemma's formula, so the states are per-lemma and
    // not four copies of one.
    let formulas: Vec<String> = report["theories"][0]["diagnostics"]
        .as_array()
        .expect("diagnostics")
        .iter()
        .map(|d| d["formulas"][0].as_str().unwrap_or("").to_string())
        .collect();
    assert_eq!(formulas.len(), 4);
    assert_eq!(
        formulas
            .iter()
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        4,
        "four distinct formulas: {formulas:?}"
    );
}

/// A complete proof has nothing open, and says so with rc 0 — the green case
/// a CI job is actually gating on.
#[test]
fn a_complete_proof_reports_nothing_and_exits_zero() {
    if !maude_available() {
        return;
    }
    let dir = case("complete");
    let proved = dir.join("proved.spthy");
    let report_path = dir.join("diag.json");

    // Produce a fully-proved theory with the port itself, then check it.
    let (prove_rc, _, _) = run_binary(
        &["--prove", &format!("-o={}", proved.display())],
        &[&fixture(PROOFLESS)],
    );
    assert_eq!(prove_rc, 0);
    let text = std::fs::read_to_string(&proved).expect("proved theory");
    assert!(!text.contains("sorry"), "the proof should be complete");

    let (rc, stdout, _) = run_binary(
        &[&format!("--proof-diagnostics={}", report_path.display())],
        &[&proved],
    );
    assert_eq!(rc, 0, "{stdout}");
    assert!(
        stdout.contains("proof diagnostics: 0 open proof state(s)"),
        "{stdout}"
    );
    let report = read_report(&report_path);
    assert_eq!(report["summary"]["open_proof_states"], 0);
    // The file is still listed, with an empty list.
    assert_eq!(report["theories"].as_array().expect("theories").len(), 1);
    assert_eq!(states(&report), Vec::<(String, String)>::new());
}

/// `--lemma` narrows the report the way it narrows the prover.
#[test]
fn a_lemma_selector_narrows_the_report() {
    if !maude_available() {
        return;
    }
    let dir = case("narrowed");
    let report_path = dir.join("diag.json");
    let (rc, stdout, _) = run_binary(
        &[
            &format!("--proof-diagnostics={}", report_path.display()),
            "--lemma=partial_reachability",
        ],
        &[&fixture(THEORY)],
    );

    assert_eq!(rc, 4, "{stdout}");
    assert!(
        stdout.contains("proof diagnostics: 1 open proof state(s)"),
        "{stdout}"
    );
    assert_eq!(
        states(&read_report(&report_path)),
        vec![("partial_reachability".to_string(), "sorry".to_string())]
    );
}

/// `--prove` fills in the very `sorry` nodes the mode reports, so the
/// combination is refused rather than silently reporting a complete proof.
/// Same message and rc 1 as the Haskell fork's `die`.
#[test]
fn prove_is_refused() {
    if !maude_available() {
        return;
    }
    let dir = case("with_prove");
    let (rc, stdout, stderr) = run_binary(
        &[
            &format!("--proof-diagnostics={}", dir.join("diag.json").display()),
            "--prove",
        ],
        &[&fixture(THEORY)],
    );
    assert_eq!(rc, 1, "{stdout}{stderr}");
    assert!(
        stderr.contains(
            "--proof-diagnostics checks the supplied partial proof; use --lemma to select \
             lemmas instead of --prove"
        ),
        "{stderr}"
    );
    assert!(
        !dir.join("diag.json").exists(),
        "a refused run writes no report"
    );
}

/// The two ZKSec report modes each replace the theory dump with their own
/// document and answer opposite questions, so they cannot both run.
#[test]
fn the_two_report_modes_are_mutually_exclusive() {
    if !maude_available() {
        return;
    }
    let dir = case("both_modes");
    let (rc, _, stderr) = run_binary(
        &[
            &format!("--proof-diagnostics={}", dir.join("d.json").display()),
            &format!("--state-audit={}", dir.join("a.json").display()),
        ],
        &[&fixture(THEORY)],
    );
    assert_eq!(rc, 1);
    assert!(
        stderr.contains("--state-audit and --proof-diagnostics cannot be used together"),
        "{stderr}"
    );
}

/// Compact mode: the report replaces the closed-theory dump and the
/// `summary of summaries:` block.
#[test]
fn the_theory_dump_and_summary_block_are_replaced_by_the_report() {
    if !maude_available() {
        return;
    }
    let dir = case("compact");
    let (_, stdout, _) = run_binary(
        &[&format!(
            "--proof-diagnostics={}",
            dir.join("diag.json").display()
        )],
        &[&fixture(THEORY)],
    );
    assert!(
        !stdout.contains("summary of summaries:"),
        "the report replaces the summary block:\n{stdout}"
    );
    assert!(
        !stdout.contains("theory Proof_Diagnostics begin"),
        "the report replaces the theory dump:\n{stdout}"
    );
}

/// The report path's directory is created on demand.
#[test]
fn a_missing_report_directory_is_created() {
    if !maude_available() {
        return;
    }
    let dir = case("mkdir");
    let report_path = dir.join("nested").join("deeper").join("diag.json");
    run_binary(
        &[&format!("--proof-diagnostics={}", report_path.display())],
        &[&fixture(THEORY)],
    );
    assert!(report_path.exists());
}
