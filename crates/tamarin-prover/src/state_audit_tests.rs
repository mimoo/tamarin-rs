//! Tests for the `--state-audit` classification, tallies, exit code, and
//! report shape.
//!
//! The audit adds no analysis of its own — it re-reads the `(verdict,
//! quantifier)` pair the prove loop already folded — so what is OURS to get
//! wrong is exactly that re-reading (a found trace means opposite things
//! under the two quantifiers), the selection boundary (a filtered lemma is
//! absent, not "inconclusive"), and the exit-code precedence.  Those are what
//! these cover; whether the underlying verdict is right is `run`'s and the
//! solver's business.

use super::*;

/// No `--prove=`/`--lemma=` narrowing — every lemma is selected.
const NO_FILTER: &[String] = &[];

fn lemma(name: &str, verdict: LemmaVerdict, exists_trace: bool) -> LemmaResult {
    LemmaResult {
        name: name.to_string(),
        verdict,
        proof_steps: 7,
        exists_trace,
    }
}

fn file(in_file: &str, results: Vec<LemmaResult>) -> FileResult {
    FileResult {
        in_file: in_file.to_string(),
        out_file: None,
        results,
        elapsed_ms: 1500,
        wf_count: 0,
    }
}

// =========================================================================
// Classification
// =========================================================================

/// The whole point of the mode: the SAME prover verdict means opposite
/// things under the two quantifiers, and the audit outcome must say which.
#[test]
fn a_found_trace_is_a_counterexample_for_safety_and_a_witness_for_executability() {
    // `--prove` folds a found trace to Falsified under all-traces and to
    // Verified under exists-trace (see `run::lemma_verdict`), so these two
    // rows are the same underlying `TraceFound`.
    assert_eq!(
        classify(&lemma("secrecy", LemmaVerdict::Falsified, false)),
        Some(AuditOutcome::Counterexample)
    );
    assert_eq!(
        classify(&lemma("executable", LemmaVerdict::Verified, true)),
        Some(AuditOutcome::WitnessFound)
    );
}

/// The mirror image: a COMPLETE proof verifies a safety property but means
/// the sought witness does not exist.
#[test]
fn a_complete_proof_verifies_safety_and_denies_a_witness() {
    assert_eq!(
        classify(&lemma("secrecy", LemmaVerdict::Verified, false)),
        Some(AuditOutcome::PropertyVerified)
    );
    assert_eq!(
        classify(&lemma("executable", LemmaVerdict::Falsified, true)),
        Some(AuditOutcome::NoWitness)
    );
}

/// Only the four decided outcomes are conclusive, and only the two that
/// falsify a selected property are failures.  A `witness_found` is a clean
/// result — the executability lemma it comes from is meant to succeed.
#[test]
fn conclusive_and_failure_partition_the_outcomes() {
    for outcome in [
        AuditOutcome::PropertyVerified,
        AuditOutcome::WitnessFound,
        AuditOutcome::Counterexample,
        AuditOutcome::NoWitness,
    ] {
        assert!(outcome.is_conclusive(), "{}", outcome.text());
    }
    for outcome in [
        AuditOutcome::Incomplete,
        AuditOutcome::Undetermined,
        AuditOutcome::Unfinishable,
        AuditOutcome::Invalidated,
    ] {
        assert!(!outcome.is_conclusive(), "{}", outcome.text());
        assert!(!outcome.is_failure(), "{}", outcome.text());
    }
    assert!(AuditOutcome::Counterexample.is_failure());
    assert!(AuditOutcome::NoWitness.is_failure());
    assert!(!AuditOutcome::WitnessFound.is_failure());
    assert!(!AuditOutcome::PropertyVerified.is_failure());
}

/// A lemma `--lemma=NAME` excluded is absent from the report, NOT reported
/// as inconclusive — otherwise every narrowed audit would exit 3 and list the
/// lemmas the user deliberately left out.
///
/// The prove loop does NOT mark those lemmas `Filtered`: it leaves their
/// stored `sorry` proof alone, which folds to the same `Analyzed` an
/// unfinished search yields.  Only the NAME filter separates the two, so
/// that is what the audit selects on.
#[test]
fn a_lemma_outside_the_filter_is_excluded_rather_than_inconclusive() {
    let files = [file(
        "m.spthy",
        vec![
            lemma("wanted", LemmaVerdict::Verified, false),
            // Unselected, and indistinguishable from an unfinished search by
            // verdict alone.
            lemma("other", LemmaVerdict::Analyzed, false),
        ],
    )];
    let filter = vec!["wanted".to_string()];

    let t = tally(&filter, &files);
    assert_eq!(t.property_verified, 1);
    assert_eq!(t.inconclusive, 0);
    assert_eq!(t.clean, 1);
    assert_eq!(exit_code(&t), 0);
    assert!(diagnostic_lines(&filter, &files).is_empty());

    let r = report(&filter, &files, &[None], &t);
    let lemmas = r["theories"][0]["lemmas"].as_array().expect("lemmas");
    assert_eq!(lemmas.len(), 1);
    assert_eq!(lemmas[0]["name"], "wanted");

    // Without the filter the same lemma IS reported, and the run is
    // inconclusive — the filter is doing the work, not the verdict.
    let unfiltered = tally(NO_FILTER, &files);
    assert_eq!(unfiltered.inconclusive, 1);
    assert_eq!(exit_code(&unfiltered), 3);
}

/// A `--prove=PREFIX*` selector narrows the audit the same way it narrows
/// the prover — the audit reuses `lemma_matches` rather than reimplementing
/// the glob.
#[test]
fn a_prefix_selector_narrows_the_audit() {
    let files = [file(
        "m.spthy",
        vec![
            lemma("state_a", LemmaVerdict::Verified, false),
            lemma("state_b", LemmaVerdict::Falsified, false),
            lemma("unrelated", LemmaVerdict::Analyzed, false),
        ],
    )];
    let t = tally(&["state_*".to_string()], &files);
    assert_eq!(t.property_verified, 1);
    assert_eq!(t.counterexamples, 1);
    assert_eq!(t.inconclusive, 0);
}

/// The no-prove paths DO mark unselected lemmas `Filtered`; that verdict is
/// excluded too, so the two selection signals agree.
#[test]
fn a_filtered_verdict_is_excluded_as_well() {
    assert_eq!(
        classify(&lemma("other", LemmaVerdict::Filtered, false)),
        None
    );
}

// =========================================================================
// Tally and exit code
// =========================================================================

#[test]
fn tally_counts_each_outcome_and_derives_clean_and_failures() {
    let t = tally(
        NO_FILTER,
        &[
            file(
                "a.spthy",
                vec![
                    lemma("safe", LemmaVerdict::Verified, false),
                    lemma("attack", LemmaVerdict::Falsified, false),
                    lemma("reachable", LemmaVerdict::Verified, true),
                ],
            ),
            file(
                "b.spthy",
                vec![
                    lemma("dead", LemmaVerdict::Falsified, true),
                    lemma("hard", LemmaVerdict::Analyzed, false),
                ],
            ),
        ],
    );
    assert_eq!(t.property_verified, 1);
    assert_eq!(t.witness_found, 1);
    assert_eq!(t.counterexamples, 1);
    assert_eq!(t.no_witness, 1);
    assert_eq!(t.inconclusive, 1);
    // Conclusive and not a failure: `safe` + `reachable`.
    assert_eq!(t.clean, 2);
    assert_eq!(t.failures, 2);
}

/// A falsified property is the finding the mode exists to surface, so it
/// outranks an unfinished sibling lemma.
#[test]
fn a_falsification_outranks_an_inconclusive_result() {
    let t = tally(
        NO_FILTER,
        &[file(
            "m.spthy",
            vec![
                lemma("attack", LemmaVerdict::Falsified, false),
                lemma("hard", LemmaVerdict::Analyzed, false),
            ],
        )],
    );
    assert_eq!(exit_code(&t), 2);
}

#[test]
fn inconclusive_is_three_and_all_clear_is_zero() {
    let inconclusive = tally(
        NO_FILTER,
        &[file(
            "m.spthy",
            vec![
                lemma("safe", LemmaVerdict::Verified, false),
                lemma("hard", LemmaVerdict::Analyzed, false),
            ],
        )],
    );
    assert_eq!(exit_code(&inconclusive), 3);

    let clean = tally(
        NO_FILTER,
        &[file(
            "m.spthy",
            vec![
                lemma("safe", LemmaVerdict::Verified, false),
                lemma("reachable", LemmaVerdict::Verified, true),
            ],
        )],
    );
    assert_eq!(exit_code(&clean), 0);
}

// =========================================================================
// Console lines
// =========================================================================

#[test]
fn headline_reads_the_tally() {
    let t = tally(
        NO_FILTER,
        &[file(
            "m.spthy",
            vec![
                lemma("safe", LemmaVerdict::Verified, false),
                lemma("attack", LemmaVerdict::Falsified, false),
                lemma("dead", LemmaVerdict::Falsified, true),
                lemma("hard", LemmaVerdict::Analyzed, false),
            ],
        )],
    );
    assert_eq!(
        headline(&t),
        "state audit: 1 clean, 1 counterexample(s), 1 missing witness(es), 1 inconclusive"
    );
}

/// The console lists only what the audit could not clear; the clean lemmas
/// live in the report file.
#[test]
fn diagnostic_lines_name_only_the_unclear_lemmas() {
    let lines = diagnostic_lines(
        NO_FILTER,
        &[file(
            "models/m.spthy",
            vec![
                lemma("safe", LemmaVerdict::Verified, false),
                lemma("attack", LemmaVerdict::Falsified, false),
                lemma("hard", LemmaVerdict::Analyzed, false),
            ],
        )],
    );
    assert_eq!(
        lines,
        vec![
            "  counterexample  models/m.spthy :: attack".to_string(),
            "  incomplete      models/m.spthy :: hard".to_string(),
        ]
    );
}

// =========================================================================
// Report document
// =========================================================================

#[test]
fn report_carries_the_schema_the_haskell_fork_emits() {
    let files = vec![file(
        "models/m.spthy",
        vec![
            lemma("safe", LemmaVerdict::Verified, false),
            lemma("attack", LemmaVerdict::Falsified, false),
            lemma("other", LemmaVerdict::Filtered, false),
        ],
    )];
    let t = tally(NO_FILTER, &files);
    let r = report(NO_FILTER, &files, &[Some("t.traces.json".to_string())], &t);

    assert_eq!(r["schema_version"], 1);
    assert_eq!(r["mode"], "state-transition-audit");
    assert_eq!(r["summary"]["property_verified"], 1);
    assert_eq!(r["summary"]["counterexamples"], 1);
    assert_eq!(r["summary"]["witness_found"], 0);
    assert_eq!(r["summary"]["no_witness"], 0);
    assert_eq!(r["summary"]["inconclusive"], 0);

    let theory = &r["theories"][0];
    assert_eq!(theory["input_file"], "models/m.spthy");
    assert_eq!(theory["processing_time_seconds"], 1.5);
    assert_eq!(theory["wellformedness_warnings"], 0);
    assert_eq!(theory["trace_file"], "t.traces.json");

    // The filtered lemma is absent — two rows, not three.
    let lemmas = theory["lemmas"].as_array().expect("lemmas array");
    assert_eq!(lemmas.len(), 2);
    assert_eq!(lemmas[0]["name"], "safe");
    assert_eq!(lemmas[0]["quantifier"], "all-traces");
    // The prover's own phrase, so a reader can cross-check the audit's
    // re-reading against the summary line the plain run would have printed.
    assert_eq!(lemmas[0]["prover_status"], "verified");
    assert_eq!(lemmas[0]["audit_outcome"], "property_verified");
    assert_eq!(lemmas[0]["steps"], 7);
    assert!(lemmas[0]["side"].is_null());
    assert_eq!(lemmas[1]["audit_outcome"], "counterexample");
    assert_eq!(lemmas[1]["prover_status"], "falsified - found trace");
}

/// An exists-trace row records the quantifier that made the re-reading go
/// the other way, so the report is self-explaining.
#[test]
fn an_exists_trace_row_records_its_quantifier() {
    let files = vec![file(
        "m.spthy",
        vec![lemma("reachable", LemmaVerdict::Verified, true)],
    )];
    let t = tally(NO_FILTER, &files);
    let r = report(NO_FILTER, &files, &[None], &t);
    let row = &r["theories"][0]["lemmas"][0];
    assert_eq!(row["quantifier"], "exists-trace");
    assert_eq!(row["audit_outcome"], "witness_found");
    assert_eq!(row["prover_status"], "verified");
    assert!(r["theories"][0]["trace_file"].is_null());
}

// =========================================================================
// Derived trace target
// =========================================================================

/// Each theory gets its own trace file, so a multi-file audit does not have
/// its files overwrite each other's traces.
#[test]
fn the_derived_trace_target_is_per_theory() {
    assert_eq!(
        default_trace_target("state-audit.json", "models/vault.spthy"),
        "state-audit.json.vault.traces.json"
    );
    assert_eq!(
        default_trace_target("out/audit.json", "a.spthy"),
        "out/audit.json.a.traces.json"
    );
    assert_ne!(
        default_trace_target("audit.json", "dir/a.spthy"),
        default_trace_target("audit.json", "dir/b.spthy")
    );
}
