// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! `--proof-diagnostics` — Lean-style reporting of the proof states a
//! theory's stored proofs leave open.
//!
//! A ZKSec-branch addition with no upstream Haskell counterpart; it mirrors
//! the mode of the same name in our Haskell fork (`src/Main/Mode/Batch.hs` on
//! that repo's `zksec` branch) so the two binaries emit the same schema and
//! the same exit code, and a check can be run on either and diffed.
//!
//! This module is only the report shape. The states themselves are collected
//! in [`tamarin_theory::proof_diagnostics`], next to the per-lemma
//! `ProofContext` that answers "what applies here?"; see that module for what
//! counts as an open state and why.
//!
//! **Why it refuses `--prove`.** The mode reports what a stored proof leaves
//! open. `--prove` hands those very `sorry` nodes to the autoprover
//! (`replaceSorryProver`), so under it there is nothing left to report — the
//! run would exit 0 having said the proof is complete BECAUSE it completed it.
//! Selection is by `--lemma` instead, which narrows without proving. The
//! Haskell fork rejects the combination for the same reason, with the same
//! message and the same exit code.
//!
//! Object-key ORDER is not part of the shared schema — aeson does not
//! preserve the written order and `serde_json::Map` sorts. Compare the two
//! forks' reports through a JSON reader, never byte-for-byte.

use tamarin_theory::proof_diagnostics::OpenProofState;

use crate::run::FileResult;

/// One theory's open proof states, grouped by the lemma they came from.
///
/// Lemma name and side live here rather than on [`OpenProofState`] because
/// the theory crate has no notion of either: a lemma is proved by name there,
/// and `side` only exists for the diff theories this port does not have.
#[derive(Debug, Clone)]
pub struct LemmaDiagnostics {
    pub lemma: String,
    pub states: Vec<OpenProofState>,
}

/// Every open state of one input file, in lemma declaration order.
pub type TheoryDiagnostics = Vec<LemmaDiagnostics>;

/// The tallies the console line and the report's `summary` block share.
pub struct DiagnosticsTally {
    pub open_proof_states: usize,
    pub invalid_steps: usize,
    pub sorries: usize,
    pub unhandled_cases: usize,
}

pub fn tally(files: &[TheoryDiagnostics]) -> DiagnosticsTally {
    let mut t = DiagnosticsTally {
        open_proof_states: 0,
        invalid_steps: 0,
        sorries: 0,
        unhandled_cases: 0,
    };
    for state in files.iter().flatten().flat_map(|l| l.states.iter()) {
        t.open_proof_states += 1;
        match state.kind.text() {
            "invalid_step" => t.invalid_steps += 1,
            "sorry" => t.sorries += 1,
            "unhandled_case" => t.unhandled_cases += 1,
            _ => {}
        }
    }
    t
}

/// `0` when every checked proof is complete, `4` when any proof state is
/// still open.
///
/// A distinct code from the audit's `2`/`3`: "this proof is unfinished" is
/// not "this property is false", and a CI job should be able to tell them
/// apart without parsing the report.
pub fn exit_code(t: &DiagnosticsTally) -> i32 {
    if t.open_proof_states > 0 {
        4
    } else {
        0
    }
}

pub fn headline(t: &DiagnosticsTally) -> String {
    format!(
        "proof diagnostics: {} open proof state(s)",
        t.open_proof_states
    )
}

/// The console rendering of one open state: a locating line, then the
/// sections that have anything in them.
///
/// The constraint system is deliberately NOT printed here — it is the
/// largest field by far, and the report file carries it.
pub fn console_lines(in_file: &str, lemma: &str, state: &OpenProofState) -> Vec<String> {
    let mut lines = Vec::new();
    // HS `printf "  %-15s %s :: %s%s%s"`, whose third `%s` is the `side:`
    // prefix — always empty here (no diff support).
    let path = if state.path.is_empty() {
        String::new()
    } else {
        format!(" :: {}", state.path.join("/"))
    };
    lines.push(format!(
        "  {:<15} {} :: {}{}",
        state.kind.text(),
        in_file,
        lemma,
        path
    ));
    if let Some(m) = &state.requested_method {
        lines.push(format!("    requested: {m}"));
    }
    let mut section = |heading: &str, values: &[String]| {
        if values.is_empty() {
            return;
        }
        lines.push(format!("    {heading}:"));
        lines.extend(values.iter().map(|v| format!("      {v}")));
    };
    section("formulas", &state.formulas);
    section("open goals", &state.open_goals);
    section("applicable", &state.applicable_methods);
    lines
}

fn state_value(lemma: &str, state: &OpenProofState) -> serde_json::Value {
    use serde_json::{json, Value};
    json!({
        "lemma": lemma,
        // Always null: no diff support (see the module doc).
        "side": Value::Null,
        "path": state.path,
        "kind": state.kind.text(),
        "reason": state.reason,
        "requested_method": state.requested_method,
        "formulas": state.formulas,
        "open_goals": state.open_goals,
        "applicable_methods": state.applicable_methods,
        "constraint_system": state.constraint_system,
    })
}

/// Build the report document. `files` is parallel to `file_results`.
pub(crate) fn report(
    file_results: &[FileResult],
    files: &[TheoryDiagnostics],
    t: &DiagnosticsTally,
) -> serde_json::Value {
    use serde_json::{json, Value};

    let theories: Vec<Value> = file_results
        .iter()
        .enumerate()
        .map(|(i, file)| {
            let diagnostics: Vec<Value> = files
                .get(i)
                .map(|theory| {
                    theory
                        .iter()
                        .flat_map(|l| l.states.iter().map(|s| state_value(&l.lemma, s)))
                        .collect()
                })
                .unwrap_or_default();
            json!({
                "input_file": file.in_file,
                "processing_time_seconds": file.elapsed_ms as f64 / 1000.0,
                "wellformedness_warnings": file.wf_count,
                "diagnostics": diagnostics,
            })
        })
        .collect();

    json!({
        "schema_version": 1,
        "mode": "proof-diagnostics",
        "summary": {
            "open_proof_states": t.open_proof_states,
            "invalid_steps": t.invalid_steps,
            "sorries": t.sorries,
            "unhandled_cases": t.unhandled_cases,
        },
        "theories": theories,
    })
}

#[cfg(test)]
#[path = "proof_diagnostics_tests.rs"]
mod proof_diagnostics_tests;
