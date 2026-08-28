// Currently GPL 3.0 until granted permission by the upstream authors
// of the tamarin-prover sources this file cites; list them with:
//   scripts/gen_license_headers.py --authors <this file>

//! Lean-style snapshots of the proof obligations a stored proof leaves open.
//!
//! This backs the batch driver's `--proof-diagnostics`, a ZKSec-branch
//! addition with no upstream counterpart; it mirrors the mode of the same name
//! in our Haskell fork (`src/Main/Mode/Batch.hs` on that repo's `zksec`
//! branch), so the two binaries report the same states.
//!
//! Nothing here proves anything. It reads a proof tree that
//! [`crate::replay::check_and_extend`] has already replayed — HS's close-time
//! `checkAndExtendProver` pass, which every load runs with or without
//! `--prove` — and describes each node the replay could not close.
//!
//! **Which nodes those are.** HS matches `(psMethod step, psInfo step)`
//! against `(Sorry reason, Just sys)`: a `Sorry` step that still carries an
//! annotated constraint system. The `Just` is load-bearing — `checkProof`
//! marks a stored step it could NOT replay with `Nothing` (rendered
//! `/* unannotated */`) and keeps the stale subtree verbatim beneath an
//! `invalid proof step encountered` sorry, so the unannotated nodes are the
//! stale text, not the open obligation. RS's [`ProofNode::annotated`] is that
//! `Just`/`Nothing`, so the same filter applies.
//!
//! **Systems are always live here.** The process-wide [`SysRetention`] that
//! drops per-node systems under `--prove` only governs `run_proof_search`;
//! the replay path this mode reads constructs its nodes with their systems
//! attached regardless (see [`crate::constraint::solver::search::SysRetention`]).
//! `--proof-diagnostics` therefore needs no retention change, and refuses
//! `--prove` anyway.
//!
//! [`SysRetention`]: crate::constraint::solver::search::SysRetention

use crate::constraint::solver::context::ProofContext;
use crate::constraint::solver::goals::GoalRanking;
use crate::constraint::solver::proof_method::{is_applicable_for_display, ProofMethod};
use crate::constraint::solver::search::{candidate_methods_with_expl, ProofNode};
use crate::constraint::system::System;
use crate::prove::ProveError;

/// HS's `"invalid proof step encountered"` sorry reason — the annotation
/// `checkProof` puts on a stored step that could not be replayed
/// (Theory/Proof.hs:447-467, see line 459). Matched, not merely displayed, so
/// keep it byte-identical to `replay.rs`'s.
const INVALID_STEP: &str = "invalid proof step encountered";

/// HS `checkAndExtendProver`'s `unhandledCase` reason
/// (Theory/Proof.hs:624-630, see line 628).
const UNHANDLED_CASE: &str = "unhandled case";

/// Why a proof state is still open.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpenProofKind {
    /// A stored proof step that could not be replayed against the current
    /// system. Its verbatim subtree is kept beneath the node.
    InvalidStep,
    /// A case the method produced that the stored proof does not cover.
    ///
    /// Unreachable on this path, in RS and HS alike, and kept for schema
    /// parity: HS only mints this reason when the prover handed to
    /// `checkAndExtendProver` returns `Nothing`, and the batch close passes
    /// `sorryProver Nothing`, which always returns `Just`. RS's
    /// [`crate::replay::check_and_extend`] mirrors that with a plain
    /// annotated `sorry` for the same cases.
    UnhandledCase,
    /// An explicit `sorry` in the source, or a leaf the replay parked
    /// (bound, deadline, no applicable method).
    Sorry,
    /// Any other open node. Not reachable through [`classify_node`]'s
    /// `Sorry`-only filter; kept so the kind set matches the Haskell fork's.
    OpenProof,
}

impl OpenProofKind {
    /// The stable string that reaches the report. Schema, not prose.
    pub fn text(self) -> &'static str {
        match self {
            OpenProofKind::InvalidStep => "invalid_step",
            OpenProofKind::UnhandledCase => "unhandled_case",
            OpenProofKind::Sorry => "sorry",
            OpenProofKind::OpenProof => "open_proof",
        }
    }
}

/// One open proof obligation, rendered.
///
/// Every field is a rendered string rather than a live term: the report is
/// the product, and holding systems alive past the walk would defeat the
/// point of reading them here.
#[derive(Debug, Clone)]
pub struct OpenProofState {
    /// Case names from the lemma's proof root down to this node, with the
    /// single unnamed case spelled `(single-case)`.
    pub path: Vec<String>,
    pub kind: OpenProofKind,
    /// The `sorry` annotation verbatim, when it had one.
    pub reason: Option<String>,
    /// For [`OpenProofKind::InvalidStep`], the stored step that failed to
    /// replay — the root of the verbatim subtree kept beneath the node.
    pub requested_method: Option<String>,
    /// The system's guarded formulas.
    pub formulas: Vec<String>,
    /// The goals still to be solved.
    pub open_goals: Vec<String>,
    /// The proof methods that apply at this exact state.
    pub applicable_methods: Vec<String>,
    /// The whole constraint system, as the interactive UI's pane renders it.
    pub constraint_system: String,
}

/// Walk a replayed proof tree and describe every node it left open.
///
/// `ctx` is taken by `&mut` only to force the goal ranking: HS's diagnostics
/// call `rankProofMethods GoalNrRanking [defaultTactic] ctxt sys`, overriding
/// whatever heuristic the theory or `--heuristic` chose, so that the reported
/// method list is a property of the STATE and not of the search order that
/// happened to be configured. Everything else about `ctx` — `use_induction`,
/// the sources, the lemma name — stays as the lemma set it, and the previous
/// ranking is restored before returning.
pub fn collect_open_proof_states(
    ctx: &mut ProofContext,
    root: &ProofNode,
) -> Result<Vec<OpenProofState>, ProveError> {
    let saved = ctx.heuristic.take();
    ctx.heuristic = Some(vec![GoalRanking::GoalNr]);
    let mut out = Vec::new();
    let mut path = Vec::new();
    let walked = walk(ctx, root, &mut path, &mut out);
    // Restore before propagating: the ranking swap must not outlive this call
    // even when the walk fails partway down the tree.
    ctx.heuristic = saved;
    walked.map(|()| out)
}

fn walk(
    ctx: &mut ProofContext,
    node: &ProofNode,
    path: &mut Vec<String>,
    out: &mut Vec<OpenProofState>,
) -> Result<(), ProveError> {
    if let Some((kind, reason)) = classify_node(node) {
        out.push(OpenProofState {
            path: path.clone(),
            kind,
            reason,
            requested_method: requested_method(kind, node),
            formulas: formulas_of(&node.sys),
            open_goals: open_goals_of(&node.sys),
            applicable_methods: applicable_methods_of(ctx, &node.sys)?,
            constraint_system: crate::pretty_system::pretty_non_graph_system(&node.sys),
        });
    }
    // `M.toList children` is ascending case-name order in HS, which is
    // `BTreeMap` iteration order here — the two walks visit in lockstep.
    for (case, child) in &node.children {
        path.push(display_case_name(case));
        let walked = walk(ctx, child, path, out);
        // Pop before propagating so the path stays balanced either way.
        path.pop();
        walked?;
    }
    Ok(())
}

/// HS `(psMethod step, psInfo step)` against `(Sorry reason, Just sys)`.
/// `None` for every node that is not an open obligation.
fn classify_node(node: &ProofNode) -> Option<(OpenProofKind, Option<String>)> {
    let reason = match &node.method {
        ProofMethod::Sorry(reason) => reason.clone(),
        _ => return None,
    };
    // HS's `Just sys`: an unannotated node is the stale stored text kept
    // verbatim under an `invalid_step`, not an obligation of its own.
    if !node.annotated {
        return None;
    }
    let kind = match reason.as_deref() {
        Some(INVALID_STEP) => OpenProofKind::InvalidStep,
        Some(UNHANDLED_CASE) => OpenProofKind::UnhandledCase,
        _ => OpenProofKind::Sorry,
    };
    Some((kind, reason))
}

/// The stored step an `invalid_step` node failed to replay: HS
/// `psMethod . root <$> M.lookup "" children`, the root of the verbatim
/// subtree `sorryNode (Just "invalid proof step encountered")
/// (M.singleton "" prf)` parked there.
fn requested_method(kind: OpenProofKind, node: &ProofNode) -> Option<String> {
    if kind != OpenProofKind::InvalidStep {
        return None;
    }
    node.children
        .get("")
        .map(|child| crate::pretty_theory::pretty_proof_method_inline(&child.method))
}

/// HS `displayCaseName`: the root's single unnamed case is `""`, which would
/// otherwise render as an empty path element.
fn display_case_name(case: &str) -> String {
    if case.is_empty() {
        "(single-case)".to_string()
    } else {
        case.to_string()
    }
}

/// HS `map (renderDoc . prettyGuarded) . S.toList . L.get sFormulas`.
///
/// `sFormulas` is a Set there and a `Vec` here, so the `S.toList` order is
/// reproduced the way `pretty_system` does it: sort a view by the derived
/// `Ord Guarded` and collapse `Ord`-equal duplicates. The live field is left
/// untouched — solver iteration order is unchanged.
///
/// `renderDoc` is the WRAPPING render, so this takes
/// [`pretty_guarded_rendered`](crate::pretty_formula::pretty_guarded_rendered)
/// and not the flat `pretty_guarded`: a formula long enough to break lands
/// here as several lines in HS, and the cross-fork gate compares this field.
fn formulas_of(sys: &System) -> Vec<String> {
    let mut sorted: Vec<&crate::guarded::Guarded> =
        sys.formulas.iter().map(|f| f.as_ref()).collect();
    sorted.sort();
    sorted.dedup();
    sorted
        .into_iter()
        .map(crate::pretty_formula::pretty_guarded_rendered)
        .collect()
}

/// HS `[prettyGoal goal | (goal, status) <- M.toList sGoals, not (gsSolved status)]`.
///
/// `M.toList` is Goal-Ord; RS stores goals in creation order, so sort by
/// `Ord Goal` first — the same correction `pretty_system::pretty_goals`
/// makes.
fn open_goals_of(sys: &System) -> Vec<String> {
    let mut open: Vec<_> = sys.goals.iter().filter(|(_, st)| !st.solved).collect();
    open.sort_by(|a, b| a.0.cmp(&b.0));
    open.iter()
        .map(|(g, _)| crate::pretty_theory::pretty_goal(g))
        .collect()
}

/// HS `map (renderDoc . prettyProofMethod . fst) $ rankProofMethods
/// GoalNrRanking [defaultTactic] ctxt sys`.
///
/// `rankProofMethods` ends in `execMethods = mapMaybe execMethod`, so the
/// list is the ranked candidates FILTERED by applicability — RS's
/// `candidate_methods_with_expl` is the unfiltered rank list, and
/// `is_applicable_for_display` is the matching filter (WHNF-depth, so a
/// `SolveGoal`'s case fan-out is never forced just to list it, exactly as
/// under HS's laziness).
fn applicable_methods_of(ctx: &ProofContext, sys: &System) -> Result<Vec<String>, ProveError> {
    let mut out = Vec::new();
    for (m, _) in candidate_methods_with_expl(sys, ctx, 0)? {
        if is_applicable_for_display(ctx, &m, sys)? {
            out.push(crate::pretty_theory::pretty_proof_method_inline(&m));
        }
    }
    Ok(out)
}
