//! `--lemma-timeout` end-to-end pins.
//!
//! `--lemma-timeout` is a ZKSec-branch addition with no counterpart in either
//! the pristine submodule or our Haskell fork: HS has no per-lemma wall-clock
//! budget, so there is no oracle to capture bytes from.  What these tests pin
//! is the contract an automated consumer depends on:
//!
//!   1. absent, the flag changes nothing — the HS-faithful default;
//!   2. a spent budget cuts the search short and reports `analysis
//!      incomplete` rather than a verdict, so an overrunning lemma can never
//!      be mistaken for a proved one;
//!   3. the run CONTINUES — the whole point.  Before this flag a single
//!      non-converging lemma blocked the file and every other result was
//!      lost;
//!   4. under `--state-audit` a cut lemma lands in the `inconclusive` bucket
//!      and the process exits 3, which is the exit code that already means
//!      "not conclusive" there.
//!
//! The budget used throughout is `=0`: a budget of zero seconds is already
//! spent when the search starts, so the cut is deterministic and these pins do
//! not depend on machine speed.  A wall-clock fixture ("a lemma that takes
//! longer than 2s") would be inherently flaky, and would get flakier as the
//! prover gets faster.
//!
//! Maude: [`maude_available`] resolves through the common harness ladder and
//! PANICS when nothing resolves, so a bare `cargo test` cannot skip these pins
//! silently; `TAM_ALLOW_NO_MAUDE=1` is the only opt-in to the skip.

mod common;

use std::path::PathBuf;

use common::{fixture, maude_available, run_binary};

/// The Haskell fork's audit example, reused here: four lemmas covering both
/// quantifiers and both verdicts, so the pins below show a timeout overriding
/// each of them rather than only the easy case.
const THEORY: &str = "state_audit.spthy";

fn case(test: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tamarin_rs_lemma_timeout_{test}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("mkdir");
    dir
}

fn read_report(path: &std::path::Path) -> serde_json::Value {
    let body =
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    serde_json::from_str(&body).expect("the report is JSON")
}

/// Absent, the flag is inert: the same four verdicts the theory has without
/// it.  This is the pin that keeps the default HS-faithful — a budget nobody
/// asked for must never turn a verdict into `analysis incomplete`.
#[test]
fn absent_the_flag_changes_nothing() {
    if !maude_available() {
        return;
    }
    let (_, with_flag_absent, _) = run_binary(&["--prove"], &[&fixture(THEORY)]);
    // A budget far larger than this theory needs must agree with it exactly.
    let (_, with_ample_budget, _) =
        run_binary(&["--prove", "--lemma-timeout=600"], &[&fixture(THEORY)]);

    let verdicts = |s: &str| -> Vec<String> {
        s.lines()
            .filter(|l| l.contains("(all-traces):") || l.contains("(exists-trace):"))
            .map(|l| l.trim().to_string())
            .collect()
    };
    let base = verdicts(&with_flag_absent);
    assert_eq!(base.len(), 4, "four lemmas expected\n{with_flag_absent}");
    assert!(
        base.iter().all(|l| !l.contains("analysis incomplete")),
        "unbudgeted run must reach a verdict for every lemma:\n{with_flag_absent}"
    );
    assert_eq!(
        base,
        verdicts(&with_ample_budget),
        "an ample budget must not change any verdict"
    );
}

/// A spent budget cuts every targeted lemma short.  The verdict line says
/// `analysis incomplete`, never `verified` or `falsified`: a lemma whose
/// search did not finish must not be reported as decided in either direction.
#[test]
fn a_spent_budget_reports_incomplete_instead_of_a_verdict() {
    if !maude_available() {
        return;
    }
    let (_, stdout, _) = run_binary(&["--prove", "--lemma-timeout=0"], &[&fixture(THEORY)]);

    let lines: Vec<&str> = stdout
        .lines()
        .filter(|l| l.contains("(all-traces):") || l.contains("(exists-trace):"))
        .collect();
    assert_eq!(lines.len(), 4, "every lemma is still reported\n{stdout}");
    for l in &lines {
        assert!(
            l.contains("analysis incomplete"),
            "a cut lemma must not claim a verdict: {l}"
        );
    }
}

/// The reason the flag exists: the run does not stop at the first lemma it
/// cannot finish.  Before it, one non-converging lemma blocked the file and
/// the other results were never printed.
#[test]
fn the_run_continues_past_a_cut_lemma() {
    if !maude_available() {
        return;
    }
    let (rc, stdout, _) = run_binary(&["--prove", "--lemma-timeout=0"], &[&fixture(THEORY)]);

    assert_eq!(rc, 0, "a cut lemma is not a batch-mode failure\n{stdout}");
    // All four names appear, not just the first.
    for name in [
        "transition_is_executable",
        "missing_transition_witness",
        "transitioned_state_was_initialized",
        "transition_is_unreachable",
    ] {
        assert!(stdout.contains(name), "{name} missing from:\n{stdout}");
    }
}

/// Under `--state-audit` a cut lemma is `inconclusive`, and the process exits
/// 3 — the code that bucket already carries.  An automated consumer can then
/// tell "this property does not hold" (exit 2) from "the prover ran out of
/// budget" (exit 3), which is the distinction that makes a budget safe to set
/// by default in CI.
#[test]
fn a_cut_lemma_is_inconclusive_in_the_audit_and_exits_three() {
    if !maude_available() {
        return;
    }
    let dir = case("audit");
    let report_path = dir.join("audit.json");
    let (rc, stdout, _) = run_binary(
        &[
            &format!("--state-audit={}", report_path.display()),
            "--lemma-timeout=0",
        ],
        &[&fixture(THEORY)],
    );

    assert_eq!(rc, 3, "inconclusive, not falsified\n{stdout}");
    assert!(
        stdout.contains("state audit: 0 clean, 0 counterexample(s), 0 missing witness(es), 4 inconclusive"),
        "{stdout}"
    );

    let report = read_report(&report_path);
    assert_eq!(report["summary"]["inconclusive"], 4);
    assert_eq!(report["summary"]["property_verified"], 0);
    assert_eq!(report["summary"]["counterexamples"], 0);
    assert_eq!(report["summary"]["no_witness"], 0);
    assert_eq!(report["summary"]["witness_found"], 0);

    for lemma in report["theories"][0]["lemmas"]
        .as_array()
        .expect("lemmas array")
    {
        assert_eq!(
            lemma["audit_outcome"], "incomplete",
            "every cut lemma is incomplete: {lemma}"
        );
    }
}

/// The budget is per-lemma, not per-run: `--lemma=NAME` narrows what the
/// budget applies to, and the untargeted lemmas keep the stored-skeleton
/// behaviour they have without `--prove`.  A per-run budget would make the
/// last lemma in a long file unprovable purely because of its position.
#[test]
fn the_budget_is_per_lemma_not_per_run() {
    if !maude_available() {
        return;
    }
    let (_, stdout, _) = run_binary(
        &[
            "--prove=transition_is_executable",
            "--lemma-timeout=0",
        ],
        &[&fixture(THEORY)],
    );

    let cut: Vec<&str> = stdout
        .lines()
        .filter(|l| l.contains("transition_is_executable") && l.contains("analysis incomplete"))
        .collect();
    assert_eq!(cut.len(), 1, "the targeted lemma was cut\n{stdout}");

    // The other three were never targeted, so the budget never applied to
    // them: they report their stored status, not `analysis incomplete`
    // attributable to this run's budget.
    assert!(
        stdout.contains("missing_transition_witness"),
        "untargeted lemmas are still listed\n{stdout}"
    );
}
