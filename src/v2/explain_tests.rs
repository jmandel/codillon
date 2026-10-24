//! Native tests for the editor-only explanations: why a `prove` holds (solver::explain).

use super::ast::Module;
use super::kernel::{check_module, check_module_with};
use super::out::{CupKind, Feed, ModuleOut};

const EXAMPLES: [&str; 8] = [
    "prove-explain",
    "parity",
    "parity-bug-gate",
    "isqrt",
    "isqrt-wrong-cup",
    "gcd",
    "primality",
    "hashtable",
];

fn example(name: &str) -> String {
    let p = format!(
        "{}/public/examples/v2/{name}.wat",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{p}: {e}"))
}

fn explained(src: &str) -> ModuleOut {
    check_module_with(&Module::parse(src), true, true)
}

/// The user's program (research 16 §3 complaint): `prove 1` after an always-taken `br_if`.
#[test]
fn prove_after_always_taken_br_if_is_explained() {
    let out = explained(&example("prove-explain"));
    let f = &out.funcs[0];
    assert!(f.verified, "{:?}", f.line_errors);
    let c = f
        .cups
        .iter()
        .find(|c| matches!(c.feed, Feed::Prove { .. }))
        .expect("a prove-fed cup");
    // the goal: False, on unreachable (line 15), fed by the prove on line 14
    assert_eq!(c.kind, CupKind::False);
    assert_eq!(c.goal, "False");
    assert_eq!(c.line, 15);
    let Feed::Prove {
        prove_line,
        hyps,
        hyp_lines,
        ..
    } = &c.feed
    else {
        unreachable!()
    };
    assert_eq!(*prove_line, 14);
    // one hypothesis, born on the br_if fall-through (line 13)
    assert_eq!(hyps.len(), 1);
    assert_eq!(hyp_lines.as_slice(), &[13]);
    let chip = &f.chips[hyps[0] as usize];
    assert_eq!(chip.origin, "br_if fall-through");
    assert_eq!(chip.text, "and(mul($x, 2), 1) ≠ 0");
    // the reason: a parity argument, ex falso
    let e = c.explain.as_ref().expect("an explanation");
    assert!(e.ex_falso);
    assert_eq!(e.used.as_slice(), &[0]);
    let why = e.lines.join(" ");
    assert!(why.contains("mul($x, 2) is even"), "{why}");
    assert!(why.contains("and(mul($x, 2), 1) = 0"), "{why}");
    assert!(why.contains("contradicts ①"), "{why}");
}

/// Every successful prove in the examples gets 1–3 lines; an explanation names only
/// hypotheses it was given.
#[test]
fn every_prove_is_explained() {
    for ex in EXAMPLES {
        let out = explained(&example(ex));
        for c in out.cups() {
            let Feed::Prove { hyps, .. } = &c.feed else {
                continue;
            };
            let e = c
                .explain
                .as_ref()
                .unwrap_or_else(|| panic!("{ex}: line {}", c.line));
            assert!(
                (1..=3).contains(&e.lines.len()),
                "{ex}: line {}: {:?}",
                c.line,
                e.lines
            );
            assert!(e.used.iter().all(|j| (*j as usize) < hyps.len()), "{ex}");
            assert!(
                e.lines.iter().all(|l| !l.is_empty() && l != "infeasible"),
                "{ex}: {:?}",
                e.lines
            );
        }
    }
}

/// Explanations are informational: the plain kernel produces none, and verdicts, feeds and
/// errors are identical with and without them.
#[test]
fn explaining_changes_no_verdict() {
    for ex in EXAMPLES {
        let m = Module::parse(&example(ex));
        let (a, b) = (check_module(&m, true), check_module_with(&m, true, true));
        assert_eq!(a.errors, b.errors, "{ex}");
        for (fa, fb) in a.funcs.iter().zip(&b.funcs) {
            assert_eq!(fa.verified, fb.verified, "{ex}");
            assert_eq!(fa.line_errors, fb.line_errors, "{ex}");
            assert_eq!(fa.dead_lines, fb.dead_lines, "{ex}");
            for (ca, cb) in fa.cups.iter().zip(&fb.cups) {
                assert!(ca.explain.is_none(), "{ex}");
                assert_eq!(
                    (ca.verdict, &ca.feed, &ca.goal),
                    (cb.verdict, &cb.feed, &cb.goal),
                    "{ex}"
                );
            }
        }
    }
}
