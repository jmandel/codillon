//! Native tests for the editor-only explanations: why a `prove` holds (solver::explain) and the
//! regions a decided branch makes unreachable (reach.rs).

use super::ast::Module;
use super::kernel::{check_module, check_module_with};
use super::out::{CupKind, Feed, ModuleOut};

const EXAMPLES: [&str; 9] = [
    "even-shift",
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

/// The user's program (research 16 §3 complaint), now with no `prove` line (R5a): unreachable's
/// cup is fed automatically from the `br_if` fall-through fact, ex falso.
#[test]
fn prove_after_always_taken_br_if_is_explained() {
    let out = explained(&example("prove-explain"));
    let f = &out.funcs[0];
    assert!(f.verified, "{:?}", f.line_errors);
    let c = f
        .cups
        .iter()
        .find(|c| matches!(c.feed, Feed::Auto { .. }))
        .expect("an automatically fed cup");
    // the goal: False, on unreachable (line 14)
    assert_eq!(c.kind, CupKind::False);
    assert_eq!(c.goal, "False");
    assert_eq!(c.line, 14);
    let Feed::Auto {
        hyps, hyp_lines, ..
    } = &c.feed
    else {
        unreachable!()
    };
    // one hypothesis, born on the br_if fall-through (line 13)
    assert_eq!(hyps.len(), 1);
    assert_eq!(hyp_lines.as_slice(), &[13]);
    let chip = &f.chips[hyps[0] as usize];
    assert_eq!(chip.origin, "br_if fall-through");
    // the reason: a parity argument, ex falso
    let e = c.explain.as_ref().expect("an explanation");
    assert!(e.ex_falso);
    assert_eq!(e.used.as_slice(), &[0]);
    assert!(!e.lines.is_empty());
    // the line after the br_if never runs
    assert_eq!(f.never_runs.len(), 1);
    let r = &f.never_runs[0];
    assert_eq!((r.from, r.to, r.cause), (14, 14, 13));
    assert_eq!(r.why, "br_if on line 13 always branches");
}

/// Every successful prove in the examples gets 1–3 lines; an explanation names only
/// hypotheses it was given.
#[test]
fn every_prove_is_explained() {
    for ex in EXAMPLES {
        let out = explained(&example(ex));
        for c in out.cups() {
            let (Feed::Prove { hyps, .. } | Feed::Auto { hyps, .. }) = &c.feed else {
                continue;
            };
            let e = c
                .explain
                .as_ref()
                .unwrap_or_else(|| panic!("{ex}: line {}", c.line));
            assert!(
                hyps.is_empty() || (1..=3).contains(&e.lines.len()),
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
            assert!(fa.never_runs.is_empty(), "{ex}");
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

fn never(src: &str) -> Vec<(u32, u32, u32, String)> {
    explained(src)
        .funcs
        .iter()
        .flat_map(|f| f.never_runs.iter())
        .map(|r| (r.from, r.to, r.cause, r.why.clone()))
        .collect()
}

#[test]
fn decided_if_arms_never_run() {
    // (x & 1) < 2 always: the else arm never runs
    let src = "(func $g (param $x i32) (result i32)
  local.get $x
  i32.const 1
  i32.and
  i32.const 2
  i32.lt_u
  if (result i32)
    i32.const 1
  else
    i32.const 2
  end
)";
    assert_eq!(
        never(src),
        vec![(
            10,
            10,
            9,
            "the condition of the if on line 7 is always true".to_string()
        )]
    );
    // a constant 0 condition: the then arm never runs
    let src = "(func $h (result i32)
  i32.const 0
  if (result i32)
    i32.const 1
    i32.const 2
    i32.add
  else
    i32.const 2
  end
)";
    assert_eq!(
        never(src),
        vec![(
            4,
            6,
            3,
            "the condition of the if on line 3 is always false".to_string()
        )]
    );
    // an input-dependent condition decides nothing
    let src = "(func $k (param $x i32)
  local.get $x
  br_if 0
  nop
)";
    assert!(never(src).is_empty());
}

/// The account of the proof cup on `line` of an example, its lines joined.
fn account(ex: &str, line: u32) -> String {
    let out = explained(&example(ex));
    let c = out
        .cups()
        .find(|c| c.line == line && c.explain.is_some())
        .unwrap_or_else(|| panic!("{ex}: no explained cup on line {line}"));
    c.explain.as_ref().unwrap().lines.join("\n")
}

/// A direct proof reads forward, from the fact to the goal (research/24 §8): the even-shift
/// benchmark, derived from the procedure's own constraints.
#[test]
fn even_shift_account_reads_forward() {
    let a = account("even-shift", 27);
    for want in [
        "x is even, so x = 2a.",
        "x>>1 = h means 2h ≤ x ≤ 2h + 1.",
        "So 2h ≤ 2a ≤ 2h + 1, which forces h = a.",
        "So (x>>1)·2 − x = 2h − x = 2h − 2a = 0.",
        "Nothing wraps: (x>>1)·2 = 2h stays below 2³²",
        "would wrap only if 2h + 1 ≤ x, but 2h = x",
    ] {
        assert!(a.contains(want), "missing {want:?} in\n{a}");
    }
    assert!(!a.contains("If ") && !a.contains("fail"), "{a}");
    // the signed variant names its other sign case
    let s = account("even-shift", 36);
    assert!(
        s.contains("forces h = a") && s.contains("x is negative"),
        "{s}"
    );
}

#[test]
fn parity_account_reads_forward() {
    let a = account("parity", 39);
    for want in [
        "is_half(x >>ₛ 1, x) means s(x >>ₛ 1) + s(x >>ₛ 1) = s(x).",
        "x is even, so x = 2a.",
        "which forces h = a",
        "The same argument covers the case x is negative.",
    ] {
        assert!(a.contains(want), "missing {want:?} in\n{a}");
    }
    assert!(!a.contains("cannot fail"), "{a}");
}

/// isqrt: a bound from a fact names the fact; conjuncts that are facts say so; a proof that
/// only closes by refutation keeps its case account.
#[test]
fn isqrt_accounts() {
    let a = account("isqrt", 55);
    assert!(a.contains("r ≤ 65534 (①), so r + 1 ≤ 65535."), "{a}");
    assert!(a.contains("r + 1 would wrap only if"), "{a}");
    let b = account("isqrt", 51);
    assert!(b.contains("is_isqrt(r, n) means sq_le(r, n) and"), "{b}");
    assert!(b.contains("sq_le(r, n) holds (②)"), "{b}");
    let c = account("isqrt", 38);
    assert!(c.starts_with("If "), "{c}");
}

#[test]
#[ignore]
fn dump_accounts() {
    for ex in EXAMPLES
        .iter()
        .chain(["isqrt-missing-invariant", "gcd-vacuous", "hashtable-stale"].iter())
    {
        let out = explained(&example(ex));
        for c in out.cups() {
            if let Some(e) = &c.explain {
                println!(
                    "== {ex} L{} goal {} ex_falso={} hyps={:?} used={:?}",
                    c.line, c.goal, e.ex_falso, e.hyp_text, e.used
                );
                for l in &e.lines {
                    println!("   {l}");
                }
            }
        }
    }
}
