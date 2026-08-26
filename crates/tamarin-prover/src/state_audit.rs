// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! `--state-audit` — a compact, machine-readable batch report for auditing
//! security properties over on-chain state transitions.
//!
//! This is a ZKSec-branch addition with no upstream Haskell counterpart in
//! the pristine submodule; it mirrors the `--state-audit` mode of our Haskell
//! fork (`src/Main/Mode/Batch.hs` on that repo's `zksec` branch) so the two
//! binaries emit the same schema and the same exit codes, and an audit can be
//! run on either and diffed.  Nothing here touches the solver or any
//! parity-gated output: the mode proves exactly the lemmas `--prove` /
//! `--lemma` already select, and only replaces the theory dump and the
//! `summary of summaries:` block with the report.
//!
//! **Where it deliberately differs from the Haskell fork.**  Observational
//! equivalence (`--diff`) is unported here, so the diff-lemma half of the
//! Haskell mode — the `observational-equivalence` quantifier and the per-side
//! `"side"` discriminator — has no reachable source.  The `"side"` key is
//! still emitted (always `null`) so one consumer reads both binaries.
//!
//! Object-key ORDER is not part of the shared schema.  Haskell's `aeson`
//! `object [...]` does not preserve the written order, and `serde_json::Map`
//! here sorts keys; compare the two with a key-normalising reader
//! (`jq -S`), never byte-for-byte.

use crate::cli::lemma_matches;
use crate::run::{proof_status_text, FileResult, LemmaResult, LemmaVerdict};

/// Security-oriented classification of one audited lemma.
///
/// The distinction the plain prover verdict cannot make: a solved trace
/// FALSIFIES an all-traces safety property but WITNESSES an exists-trace
/// executability property.  Collapsing those two into "falsified" / "verified"
/// is what makes a raw prover summary unreadable as an audit result, so they
/// stay apart here.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AuditOutcome {
    /// An `all-traces` safety property was proved.
    PropertyVerified,
    /// An `exists-trace` executability / attack witness was found.
    WitnessFound,
    /// An `all-traces` safety property was falsified by a trace.
    Counterexample,
    /// An `exists-trace` property was conclusively falsified.
    NoWitness,
    /// The search did not finish (bound, deadline, or a `sorry`).
    Incomplete,
    /// The proof tree folded to a status that could not be determined.
    Undetermined,
    /// No open goals, but reducible operators remain in subterms.
    Unfinishable,
    /// A stored proof step was invalidated.
    Invalidated,
}

impl AuditOutcome {
    /// The stable string that reaches the report and the console lines.
    /// These are schema, not prose — do not reword them.
    pub fn text(self) -> &'static str {
        match self {
            AuditOutcome::PropertyVerified => "property_verified",
            AuditOutcome::WitnessFound => "witness_found",
            AuditOutcome::Counterexample => "counterexample",
            AuditOutcome::NoWitness => "no_witness",
            AuditOutcome::Incomplete => "incomplete",
            AuditOutcome::Undetermined => "undetermined",
            AuditOutcome::Unfinishable => "unfinishable",
            AuditOutcome::Invalidated => "invalidated",
        }
    }

    /// Did the audit establish anything about this lemma, either way?
    pub fn is_conclusive(self) -> bool {
        matches!(
            self,
            AuditOutcome::PropertyVerified
                | AuditOutcome::WitnessFound
                | AuditOutcome::Counterexample
                | AuditOutcome::NoWitness
        )
    }

    /// Did the audit establish that a SELECTED property does not hold?  These
    /// are the outcomes that make the run exit 2.
    pub fn is_failure(self) -> bool {
        matches!(self, AuditOutcome::Counterexample | AuditOutcome::NoWitness)
    }
}

/// Classify one proved lemma.  `None` means the lemma does not belong in the
/// report at all — see [`selected`] for what the audit reports on.
///
/// The four conclusive outcomes are a re-reading of the SAME
/// `(verdict, quantifier)` pair `run::lemma_verdict` already folded, not a
/// second classification of the proof tree: `Verified` under `exists-trace`
/// is HS's `TraceFound`, `Falsified` under `exists-trace` is HS's
/// `CompleteProof`, and so on — see `run::lemma_verdict`.
pub fn classify(result: &LemmaResult) -> Option<AuditOutcome> {
    match &result.verdict {
        LemmaVerdict::Verified if result.exists_trace => Some(AuditOutcome::WitnessFound),
        LemmaVerdict::Verified => Some(AuditOutcome::PropertyVerified),
        LemmaVerdict::Falsified if result.exists_trace => Some(AuditOutcome::NoWitness),
        LemmaVerdict::Falsified => Some(AuditOutcome::Counterexample),
        LemmaVerdict::Unfinishable => Some(AuditOutcome::Unfinishable),
        LemmaVerdict::Undetermined => Some(AuditOutcome::Undetermined),
        LemmaVerdict::Invalidated => Some(AuditOutcome::Invalidated),
        LemmaVerdict::Analyzed => Some(AuditOutcome::Incomplete),
        // Reachable only if some path builds a verdict without proving: the
        // audit forces `prove_mode`, so every SELECTED lemma is attempted.
        LemmaVerdict::Skipped => Some(AuditOutcome::Incomplete),
        // Already marked unselected by the verdict builder.
        LemmaVerdict::Filtered => None,
    }
}

/// Is this lemma one the audit reports on?  HS `auditClosedTheory` filters
/// with `lemmaSelector opts` — the SAME name filter `--prove=NAME` /
/// `--lemma=NAME` feed the prover — before it builds a single result.
///
/// Filtering by NAME, not by verdict, is load-bearing.  The prove loop leaves
/// an unselected lemma's stored `sorry` proof in place, which folds to
/// `Incomplete`, indistinguishable from a selected lemma the search could not
/// finish.  Reporting on the verdict alone would therefore make every
/// narrowed audit exit 3 and list the lemmas the user deliberately excluded.
fn selected(lemma_filter: &[String], result: &LemmaResult) -> bool {
    lemma_matches(lemma_filter, &result.name)
}

/// One audited lemma, paired with the file it came from so the console lines
/// and the per-theory JSON can both be built from one pass.
struct AuditedLemma<'a> {
    result: &'a LemmaResult,
    outcome: AuditOutcome,
}

fn audited<'a>(lemma_filter: &[String], file: &'a FileResult) -> Vec<AuditedLemma<'a>> {
    file.results
        .iter()
        .filter(|r| selected(lemma_filter, r))
        .filter_map(|r| classify(r).map(|outcome| AuditedLemma { result: r, outcome }))
        .collect()
}

/// The tallies the console line and the report's `summary` block share.
pub struct AuditTally {
    pub property_verified: usize,
    pub witness_found: usize,
    pub counterexamples: usize,
    pub no_witness: usize,
    pub inconclusive: usize,
    /// Conclusive AND not a failure — what the console calls "clean".
    pub clean: usize,
    /// `counterexamples + no_witness`.
    pub failures: usize,
}

pub fn tally(lemma_filter: &[String], file_results: &[FileResult]) -> AuditTally {
    let mut t = AuditTally {
        property_verified: 0,
        witness_found: 0,
        counterexamples: 0,
        no_witness: 0,
        inconclusive: 0,
        clean: 0,
        failures: 0,
    };
    for file in file_results {
        for lemma in audited(lemma_filter, file) {
            match lemma.outcome {
                AuditOutcome::PropertyVerified => t.property_verified += 1,
                AuditOutcome::WitnessFound => t.witness_found += 1,
                AuditOutcome::Counterexample => t.counterexamples += 1,
                AuditOutcome::NoWitness => t.no_witness += 1,
                _ => {}
            }
            if !lemma.outcome.is_conclusive() {
                t.inconclusive += 1;
            } else if !lemma.outcome.is_failure() {
                t.clean += 1;
            }
        }
    }
    t.failures = t.counterexamples + t.no_witness;
    t
}

/// The exit code the audit run reports.
///
/// * `2` — a selected property is falsified (an all-traces counterexample or
///   a missing exists-trace witness).  This is the finding the mode exists to
///   surface, so it outranks an unfinished sibling lemma.
/// * `3` — everything ran, but the audit established nothing for at least one
///   selected lemma.
/// * `0` — every selected lemma holds.
///
/// There is no run-level-failure arm: parse, I/O, Maude, guarded-conversion
/// and ranking failures all return before the batch loop reaches the audit,
/// so the tally is the only thing left to decide the code.
pub fn exit_code(t: &AuditTally) -> i32 {
    if t.failures > 0 {
        return 2;
    }
    if t.inconclusive > 0 {
        return 3;
    }
    0
}

/// The headline console line, mirroring the Haskell fork's `printf`.
pub fn headline(t: &AuditTally) -> String {
    format!(
        "state audit: {} clean, {} counterexample(s), {} missing witness(es), {} inconclusive",
        t.clean, t.counterexamples, t.no_witness, t.inconclusive
    )
}

/// One console line per lemma the audit could not clear — every failure and
/// every inconclusive result.  Clean lemmas are intentionally silent; the
/// report file carries them.
pub fn diagnostic_lines(lemma_filter: &[String], file_results: &[FileResult]) -> Vec<String> {
    let mut lines = Vec::new();
    for file in file_results {
        for lemma in audited(lemma_filter, file) {
            if lemma.outcome.is_failure() || !lemma.outcome.is_conclusive() {
                // HS `printf "  %-15s %s :: %s%s"`, whose third `%s` is the
                // `side:` prefix — always empty here (see the module doc).
                lines.push(format!(
                    "  {:<15} {} :: {}",
                    lemma.outcome.text(),
                    file.in_file,
                    lemma.result.name
                ));
            }
        }
    }
    lines
}

/// Build the report document.  `trace_files` is parallel to `file_results`
/// and carries each theory's resolved `--output-json` target, which the audit
/// defaults on so a counterexample always has a trace to point at.
pub fn report(
    lemma_filter: &[String],
    file_results: &[FileResult],
    trace_files: &[Option<String>],
    t: &AuditTally,
) -> serde_json::Value {
    use serde_json::{json, Value};

    let theories: Vec<Value> = file_results
        .iter()
        .enumerate()
        .map(|(i, file)| {
            let lemmas: Vec<Value> = audited(lemma_filter, file)
                .iter()
                .map(|lemma| {
                    json!({
                        "name": lemma.result.name,
                        // Always null: no diff support (see the module doc).
                        "side": Value::Null,
                        "quantifier": if lemma.result.exists_trace {
                            "exists-trace"
                        } else {
                            "all-traces"
                        },
                        "prover_status": proof_status_text(lemma.result),
                        "audit_outcome": lemma.outcome.text(),
                        "steps": lemma.result.proof_steps,
                    })
                })
                .collect();
            json!({
                "input_file": file.in_file,
                "processing_time_seconds": file.elapsed_ms as f64 / 1000.0,
                "wellformedness_warnings": file.wf_count,
                "trace_file": trace_files.get(i).cloned().flatten(),
                "lemmas": lemmas,
            })
        })
        .collect();

    json!({
        "schema_version": 1,
        "mode": "state-transition-audit",
        "summary": {
            "property_verified": t.property_verified,
            "witness_found": t.witness_found,
            "counterexamples": t.counterexamples,
            "no_witness": t.no_witness,
            "inconclusive": t.inconclusive,
        },
        "theories": theories,
    })
}

/// The per-theory trace target an audit run writes solved constraint systems
/// to.  An explicit `--output-json` wins; otherwise the audit derives one
/// from the report path and the theory's base name, so a multi-file run does
/// not have its files overwrite each other's traces.
///
/// Mirrors the Haskell fork's
/// `findArg "traceJSON" <|> Just (stateAuditFile ++ "." ++ takeBaseName inFile ++ ".traces.json")`.
pub fn default_trace_target(audit_file: &str, in_file: &str) -> String {
    let base = std::path::Path::new(in_file)
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("theory");
    format!("{audit_file}.{base}.traces.json")
}

#[cfg(test)]
#[path = "state_audit_tests.rs"]
mod state_audit_tests;
