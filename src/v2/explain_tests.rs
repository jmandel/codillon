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

/// Review 25 B1: a fact prints as its chip does (in the view of its birth line) wherever it
/// appears; where the account's own view names one of its values differently, it says so.
#[test]
fn a_fact_keeps_its_birth_names_in_accounts() {
    let out = explained(&example("gcd"));
    let mut seen = false;
    for f in &out.funcs {
        for c in &f.cups {
            let (Some(e), Feed::Auto { hyps, .. } | Feed::Prove { hyps, .. }) =
                (&c.explain, &c.feed)
            else {
                continue;
            };
            for (j, h) in hyps.iter().enumerate() {
                let chip = &f.chips[*h as usize];
                let t = &e.hyp_text[j];
                assert!(
                    t.starts_with(&chip.text) || t.contains(&chip.text),
                    "{t} vs {}",
                    chip.text
                );
                if chip.text == "y ≠ 0" && t.contains("[y of line") {
                    assert!(t.contains("is x here"), "{t}");
                    seen = true;
                }
            }
        }
    }
    assert!(seen, "the back edge's y ≠ 0 names its move to x");
}

fn diags(src: &str) -> Vec<(u32, String)> {
    explained(src)
        .cups()
        .filter_map(|c| c.diag.clone().map(|d| (c.line, d)))
        .collect()
}

/// Review 25 S1: a countermodel survives values the pre-pass pins to a point (any goal with an
/// `add`), and a cup with no facts at all shows the failing input.
#[test]
fn countermodels_are_shown() {
    let d = diags(&example("hashtable-stale"));
    assert!(
        d.iter().any(|(_, m)| m.contains("allows i@301 = 7")),
        "{d:?}"
    );
    let d = diags(&example("parity-missing-proof"));
    assert!(
        d.iter().any(|(_, m)| m.contains("it fails for x = 1")),
        "{d:?}"
    );
    let src = "(func $h8 (param $a (i32 | (i32.lt_u v (i32.const 8)))))
(func $f (param $x (i32 | (i32.lt_u v (i32.const 8))))
  local.get $x
  i32.const 1
  i32.add
  call $h8
)";
    let d = diags(src);
    assert!(d.iter().any(|(_, m)| m.contains("x = 7")), "{d:?}");
}

/// Review 25 S2 (its probe P1): after `i := i + 1` and `i := x`, a cup about the old `i + 1`
/// gets no stale hint naming the later set, though the new value `x` is part of it.
#[test]
fn no_stale_hint_on_a_goal_about_the_old_value() {
    let src = "(func $h8 (param $a (i32 | (i32.lt_u v (i32.const 8)))))
(func $le8 (param $a (i32 | (i32.le_u v (i32.const 8)))))
(func $f (param $x i32)
  (local $i i32)
  local.get $x
  local.set $i
  local.get $i
  i32.const 8
  i32.ge_u
  br_if 0
  local.get $i
  i32.const 1
  i32.add
  local.set $i
  local.get $i
  call $le8
  local.get $i
  call $h8
  local.get $i
  local.get $x
  local.set $i
  call $h8
)";
    let lines: Vec<&str> = src.lines().collect();
    let last_set = lines
        .iter()
        .rposition(|l| l.trim() == "local.set $i")
        .unwrap()
        + 1;
    let d = diags(src);
    assert!(
        !d.iter()
            .any(|(_, m)| m.contains(&format!("set at line {last_set})"))),
        "{d:?}"
    );
}

#[test]
#[ignore]
fn dump_diags() {
    for ex in [
        "parity-missing-proof",
        "hashtable-stale",
        "isqrt-missing-invariant",
        "gcd-bug-guard",
    ] {
        let out = explained(&example(ex));
        for c in out.cups() {
            if let Some(d) = &c.diag {
                println!("{ex} L{}: {d}", c.line);
            }
        }
    }
}

/// Parity's harness: the never-runs line is proved from the failed check alone, because the
/// proof unfolds what the called functions compute; the account names them.
#[test]
fn accounts_name_the_definitions_they_unfold() {
    let out = explained(&example("parity"));
    let c = out
        .cups()
        .find(|c| c.line == 57 && c.explain.is_some())
        .expect("the harness's unreachable");
    let e = c.explain.as_ref().unwrap();
    assert!(e.ex_falso && e.used.len() == 1, "{e:?}");
    for f in ["hon_ok", "half_or_neg1"] {
        assert!(e.unfolded.iter().any(|u| u == f), "{:?}", e.unfolded);
    }
}
