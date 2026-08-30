//! `--without-rule` / `--without-restriction` end-to-end pins.
//!
//! Both are ZKSec-branch additions with no upstream counterpart, so there is no
//! oracle to capture bytes from. What these pin is the contract that makes an
//! ablation trustworthy:
//!
//!   1. absent, the flags change nothing;
//!   2. removing a restriction that a property depends on FALSIFIES that
//!      property -- the ablation actually bites;
//!   3. a name matching nothing is a hard ERROR, never a silent no-op. This is
//!      the one that matters: an ablation that quietly removed nothing would
//!      report the UNABLATED verdict, and a reader would draw the opposite
//!      conclusion from the one the evidence supports;
//!   4. removing an unrelated rule leaves an independent property alone.
//!
//! Maude: [`maude_available`] panics when nothing resolves, so a bare
//! `cargo test` cannot skip these silently; `TAM_ALLOW_NO_MAUDE=1` opts in.

mod common;

use common::{maude_available, run_binary};

/// A theory whose safety property holds ONLY because of a restriction, so
/// ablating that restriction must flip the verdict. `Guard` is what makes
/// `dirty` unreachable; `Unrelated` exists to be ablated without effect.
const THEORY: &str = r#"theory WithoutAblation
begin

restriction Guard:
  "All x #i. Reassign(x) @i ==> x = 'clean'"

rule Create:
  [ Fr(~a) ] --[ Created(~a) ]-> [ Acct(~a, 'dirty'), Acct(~a, 'clean') ]

rule Reassign:
  [ Acct(a, state) ] --[ Reassign(state), Adopted(state) ]-> [ ]

rule Unrelated:
  [ Fr(~n) ] --[ Noise(~n) ]-> [ ]

lemma only_clean_is_adopted:
  all-traces "All s #i. Adopted(s) @i ==> s = 'clean'"

end
"#;

fn theory_file(name: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!("tamarin_rs_without_{name}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("mkdir");
    let p = dir.join("t.spthy");
    std::fs::write(&p, THEORY).expect("write");
    p
}

/// Absent, the flags are inert and the property holds.
#[test]
fn absent_the_flags_change_nothing() {
    if !maude_available() {
        return;
    }
    let t = theory_file("absent");
    let (_, stdout, _) = run_binary(&["--prove"], &[&t]);
    assert!(
        stdout.contains("only_clean_is_adopted (all-traces): verified"),
        "{stdout}"
    );
}

/// Removing the restriction the property rests on falsifies it. If this ever
/// stops holding, the flag has stopped biting and every ablation run with it
/// is worthless.
#[test]
fn ablating_the_restriction_falsifies_the_property() {
    if !maude_available() {
        return;
    }
    let t = theory_file("bites");
    let (_, stdout, _) = run_binary(&["--prove", "--without-restriction=Guard"], &[&t]);
    assert!(
        stdout.contains("only_clean_is_adopted (all-traces): falsified"),
        "ablating Guard must falsify the property it supports:\n{stdout}"
    );
}

/// A name that matches nothing is a hard error. A silent no-op would report
/// the UNABLATED verdict under a command line that claims to have ablated,
/// which is the worst possible failure for this feature.
#[test]
fn a_name_that_matches_nothing_is_an_error() {
    if !maude_available() {
        return;
    }
    let t = theory_file("typo");

    let (rc, _, stderr) = run_binary(&["--prove", "--without-restriction=Guardd"], &[&t]);
    assert_eq!(rc, 1, "a typo must fail the run, not proceed");
    assert!(stderr.contains("no such restriction"), "{stderr}");

    let (rc, _, stderr) = run_binary(&["--prove", "--without-rule=Reasign"], &[&t]);
    assert_eq!(rc, 1, "a typo must fail the run, not proceed");
    assert!(stderr.contains("no such rule"), "{stderr}");
}

/// Ablating an unrelated rule leaves the property alone: the filter removes
/// what it is asked to and nothing else.
#[test]
fn ablating_an_unrelated_rule_is_harmless() {
    if !maude_available() {
        return;
    }
    let t = theory_file("unrelated");
    let (_, stdout, _) = run_binary(&["--prove", "--without-rule=Unrelated"], &[&t]);
    assert!(
        stdout.contains("only_clean_is_adopted (all-traces): verified"),
        "{stdout}"
    );
}
