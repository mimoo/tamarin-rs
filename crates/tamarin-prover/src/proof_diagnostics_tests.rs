//! Tests for the `--proof-diagnostics` tallies, exit code, console rendering
//! and report shape.
//!
//! The open states themselves are found in `tamarin-theory`, against a real
//! proof tree and a real `ProofContext`; what is OURS here is the shaping —
//! the counts a CI job reads, the exit code that separates "unfinished proof"
//! from "false property", and the console/JSON split (the constraint system
//! is far too large for a terminal and belongs only in the file).

use super::*;

use tamarin_theory::proof_diagnostics::{OpenProofKind, OpenProofState};

fn state(kind: OpenProofKind, path: &[&str]) -> OpenProofState {
    OpenProofState {
        path: path.iter().map(|s| s.to_string()).collect(),
        kind,
        reason: None,
        requested_method: None,
        formulas: vec!["∃ x #i. (A( x ) @ #i)".to_string()],
        open_goals: vec!["!KU( ~k ) @ #vk".to_string()],
        applicable_methods: vec!["simplify".to_string()],
        constraint_system: "last: none\n\nformulas: …".to_string(),
    }
}

fn lemma(name: &str, states: Vec<OpenProofState>) -> LemmaDiagnostics {
    LemmaDiagnostics {
        lemma: name.to_string(),
        states,
    }
}

fn file(in_file: &str) -> FileResult {
    FileResult {
        in_file: in_file.to_string(),
        out_file: None,
        results: Vec::new(),
        elapsed_ms: 2500,
        wf_count: 1,
    }
}

// =========================================================================
// Tally and exit code
// =========================================================================

#[test]
fn tally_counts_every_kind_across_files_and_lemmas() {
    let files = vec![
        vec![
            lemma(
                "a",
                vec![
                    state(OpenProofKind::Sorry, &[]),
                    state(OpenProofKind::InvalidStep, &["case_1"]),
                ],
            ),
            lemma("b", vec![state(OpenProofKind::Sorry, &[])]),
        ],
        vec![lemma("c", vec![state(OpenProofKind::UnhandledCase, &[])])],
    ];
    let t = tally(&files);
    assert_eq!(t.open_proof_states, 4);
    assert_eq!(t.sorries, 2);
    assert_eq!(t.invalid_steps, 1);
    assert_eq!(t.unhandled_cases, 1);
}

/// A complete proof is the only thing that exits 0 — the mode's whole job is
/// to fail a CI run whose proofs are not actually finished.
#[test]
fn a_complete_proof_exits_zero_and_any_open_state_exits_four() {
    let empty = tally(&[]);
    assert_eq!(empty.open_proof_states, 0);
    assert_eq!(exit_code(&empty), 0);

    // A theory present but with nothing open is also complete.
    let no_states = tally(&[vec![lemma("a", Vec::new())]]);
    assert_eq!(exit_code(&no_states), 0);

    let open = tally(&[vec![lemma("a", vec![state(OpenProofKind::Sorry, &[])])]]);
    assert_eq!(exit_code(&open), 4);
}

/// 4 is deliberately not the audit's 2 or 3: "this proof is unfinished" is a
/// different fact from "this property is false", and a CI job must be able to
/// tell them apart from the exit code alone.
#[test]
fn the_exit_code_does_not_collide_with_the_audit_codes() {
    let open = tally(&[vec![lemma(
        "a",
        vec![state(OpenProofKind::InvalidStep, &[])],
    )]]);
    let rc = exit_code(&open);
    assert_eq!(rc, 4);
    assert_ne!(rc, 2, "2 is the audit's falsified");
    assert_ne!(rc, 3, "3 is the audit's inconclusive");
}

#[test]
fn headline_reads_the_tally() {
    let t = tally(&[vec![lemma(
        "a",
        vec![
            state(OpenProofKind::Sorry, &[]),
            state(OpenProofKind::InvalidStep, &[]),
        ],
    )]]);
    assert_eq!(headline(&t), "proof diagnostics: 2 open proof state(s)");
}

// =========================================================================
// Console rendering
// =========================================================================

/// The locating line, then only the sections that have content — and never
/// the constraint system, which would bury the terminal.
#[test]
fn console_lines_locate_the_state_and_omit_the_constraint_system() {
    let mut s = state(OpenProofKind::InvalidStep, &["case_1", "case_2"]);
    s.requested_method = Some("solve( !KU( 'stale' ) @ #x )".to_string());
    let lines = console_lines("m.spthy", "secrecy", &s);
    assert_eq!(
        lines,
        vec![
            "  invalid_step    m.spthy :: secrecy :: case_1/case_2".to_string(),
            "    requested: solve( !KU( 'stale' ) @ #x )".to_string(),
            "    formulas:".to_string(),
            "      ∃ x #i. (A( x ) @ #i)".to_string(),
            "    open goals:".to_string(),
            "      !KU( ~k ) @ #vk".to_string(),
            "    applicable:".to_string(),
            "      simplify".to_string(),
        ]
    );
    assert!(
        !lines.iter().any(|l| l.contains("last: none")),
        "the constraint system belongs in the report file only: {lines:?}"
    );
}

/// A root-level state has no case path, and no ` :: ` separator for one.
#[test]
fn a_root_state_renders_without_a_path_suffix() {
    let lines = console_lines("m.spthy", "reach", &state(OpenProofKind::Sorry, &[]));
    assert_eq!(lines[0], "  sorry           m.spthy :: reach");
}

/// Sections with nothing in them are dropped rather than printed empty.
#[test]
fn empty_sections_are_omitted() {
    let mut s = state(OpenProofKind::Sorry, &[]);
    s.open_goals.clear();
    s.applicable_methods.clear();
    let lines = console_lines("m.spthy", "reach", &s);
    assert!(!lines.iter().any(|l| l.contains("open goals")), "{lines:?}");
    assert!(!lines.iter().any(|l| l.contains("applicable")), "{lines:?}");
    assert!(lines.iter().any(|l| l.contains("formulas")), "{lines:?}");
    // No `requested:` line either — only an invalid step has one.
    assert!(!lines.iter().any(|l| l.contains("requested")), "{lines:?}");
}

// =========================================================================
// Report document
// =========================================================================

#[test]
fn report_carries_the_schema_the_haskell_fork_emits() {
    let file_results = vec![file("models/m.spthy")];
    let mut s = state(OpenProofKind::InvalidStep, &["(single-case)"]);
    s.reason = Some("invalid proof step encountered".to_string());
    s.requested_method = Some("solve( !KU( 'stale' ) @ #x )".to_string());
    let files = vec![vec![lemma("secrecy", vec![s])]];
    let t = tally(&files);
    let r = report(&file_results, &files, &t);

    assert_eq!(r["schema_version"], 1);
    assert_eq!(r["mode"], "proof-diagnostics");
    assert_eq!(r["summary"]["open_proof_states"], 1);
    assert_eq!(r["summary"]["invalid_steps"], 1);
    assert_eq!(r["summary"]["sorries"], 0);
    assert_eq!(r["summary"]["unhandled_cases"], 0);

    let theory = &r["theories"][0];
    assert_eq!(theory["input_file"], "models/m.spthy");
    assert_eq!(theory["processing_time_seconds"], 2.5);
    assert_eq!(theory["wellformedness_warnings"], 1);

    let d = &theory["diagnostics"][0];
    assert_eq!(d["lemma"], "secrecy");
    assert!(d["side"].is_null());
    assert_eq!(d["path"][0], "(single-case)");
    assert_eq!(d["kind"], "invalid_step");
    assert_eq!(d["reason"], "invalid proof step encountered");
    assert_eq!(d["requested_method"], "solve( !KU( 'stale' ) @ #x )");
    assert_eq!(d["formulas"][0], "∃ x #i. (A( x ) @ #i)");
    assert_eq!(d["open_goals"][0], "!KU( ~k ) @ #vk");
    assert_eq!(d["applicable_methods"][0], "simplify");
    // Present in the file even though the console omits it.
    assert_eq!(d["constraint_system"], "last: none\n\nformulas: …");
}

/// Several lemmas' states flatten into one per-theory list, each row naming
/// the lemma it came from — the report is keyed by state, not by lemma.
#[test]
fn a_theorys_states_flatten_with_their_lemma_names() {
    let file_results = vec![file("m.spthy")];
    let files = vec![vec![
        lemma("a", vec![state(OpenProofKind::Sorry, &[])]),
        lemma(
            "b",
            vec![
                state(OpenProofKind::Sorry, &["x"]),
                state(OpenProofKind::InvalidStep, &["y"]),
            ],
        ),
    ]];
    let t = tally(&files);
    let r = report(&file_results, &files, &t);
    let rows = r["theories"][0]["diagnostics"].as_array().expect("rows");
    assert_eq!(rows.len(), 3);
    let names: Vec<&str> = rows.iter().map(|d| d["lemma"].as_str().unwrap()).collect();
    assert_eq!(names, vec!["a", "b", "b"]);
}

/// A theory with nothing open still gets a row, with an empty list — a
/// consumer should see every file it asked about.
#[test]
fn a_clean_theory_is_still_listed() {
    let file_results = vec![file("clean.spthy")];
    let files: Vec<TheoryDiagnostics> = vec![Vec::new()];
    let t = tally(&files);
    let r = report(&file_results, &files, &t);
    let theories = r["theories"].as_array().expect("theories");
    assert_eq!(theories.len(), 1);
    assert_eq!(theories[0]["input_file"], "clean.spthy");
    assert_eq!(
        theories[0]["diagnostics"].as_array().expect("rows").len(),
        0
    );
}
