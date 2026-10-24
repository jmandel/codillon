//! Native tests for the v2 kernel: erasure against erase.py, parsing, and the expect.json oracle.

use super::ast::Module;
use super::erase::erase_text;

pub const EXAMPLES: [&str; 13] = [
    "parity",
    "parity-missing-proof",
    "parity-bug-gate",
    "isqrt",
    "isqrt-harness-bug",
    "isqrt-wrong-cup",
    "gcd",
    "gcd-bug-guard",
    "gcd-vacuous",
    "primality",
    "hashtable",
    "hashtable-stale",
    "hashtable-bug-tombstone",
];

pub fn testdata(name: &str, ext: &str) -> String {
    let p = format!("{}/src/v2/testdata/{name}.{ext}", env!("CARGO_MANIFEST_DIR"));
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{p}: {e}"))
}

#[test]
fn erasure_matches_erase_py() {
    for ex in EXAMPLES {
        let src = testdata(ex, "wat");
        let want = testdata(ex, "erased");
        let got = erase_text(&src);
        for (i, (g, w)) in got.lines().zip(want.lines()).enumerate() {
            assert_eq!(g, w, "{ex}: line {}", i + 1);
        }
        assert_eq!(got.lines().count(), want.lines().count(), "{ex}: line count");
        assert_eq!(got, want, "{ex}");
    }
}

#[test]
fn erased_examples_assemble() {
    for ex in EXAMPLES {
        let erased = erase_text(&testdata(ex, "wat"));
        let wat = format!("(module {erased})");
        wat::parse_str(&wat).unwrap_or_else(|e| panic!("{ex}: {e}"));
    }
}

#[test]
fn examples_parse_without_errors() {
    for ex in EXAMPLES {
        let m = Module::parse(&testdata(ex, "wat"));
        assert!(m.errors.is_empty(), "{ex}: {:?}", m.errors);
        assert!(m.funcs.iter().all(|f| f.end_line > 0), "{ex}");
    }
}

#[test]
fn malformed_lines_never_panic() {
    use super::ast::{LineKind, parse_line};
    for t in ["i32.trunc_", "i64.trunc_sat_", "f32.convert_", "i32.load offset=", "(param $x (i32 |", "prove 99", ")", "\"", "(i32| $p)"] {
        let k = parse_line(t, 1);
        if t != ")" {
            assert!(matches!(k, LineKind::Error(_) | LineKind::Other), "{t}: {k:?}");
        }
    }
}

// ---------------- the expect.json oracle ----------------

use super::kernel::check_module;
use super::out::{Feed, ModuleOut, Verdict};
use serde_json::Value;

/// One cup in comparable form.
#[derive(Clone, Debug, PartialEq)]
pub struct CupKey {
    pub line: u64,
    pub kind: String,
    pub operand: Option<u64>,
    pub verdict: String,
    pub by: String,
    pub feed_line: Option<u64>,
    pub checks: Vec<u64>,
    pub hyp_lines: Vec<u64>,
}

fn ours(out: &ModuleOut) -> Vec<CupKey> {
    let mut v: Vec<CupKey> = out
        .cups()
        .map(|c| {
            let (feed_line, hyp_lines) = match &c.feed {
                Feed::Lookup { origin_line, .. } => (Some(*origin_line as u64), vec![]),
                Feed::Prove { prove_line, hyp_lines, .. } => (Some(*prove_line as u64), hyp_lines.iter().map(|x| *x as u64).collect()),
                Feed::DeadCode { ended_at } => (Some(*ended_at as u64), vec![]),
                _ => (None, vec![]),
            };
            CupKey {
                line: c.line as u64,
                kind: c.kind.name().into(),
                operand: c.operand.map(|x| x as u64),
                verdict: if c.verdict == Verdict::Refuted { "refuted".into() } else { c.verdict.name().into() },
                by: c.feed.by().into(),
                feed_line,
                checks: c.depends_on_checks.iter().map(|x| *x as u64).collect(),
                hyp_lines,
            }
        })
        .collect();
    v.sort_by_key(|c| c.line);
    v
}

fn oracle(j: &Value) -> Vec<CupKey> {
    j["cups"]
        .as_array()
        .unwrap()
        .iter()
        .map(|c| {
            let f = &c["feed"];
            let by = f["by"].as_str().unwrap().to_string();
            let feed_line = match by.as_str() {
                "lookup" => f["facts"][0]["line"].as_u64(),
                "prove" | "dead" => f["line"].as_u64(),
                _ => None,
            };
            CupKey {
                line: c["line"].as_u64().unwrap(),
                kind: c["kind"].as_str().unwrap().into(),
                operand: c["operand"].as_u64(),
                verdict: c["verdict"].as_str().unwrap().into(),
                by,
                feed_line,
                checks: c.get("depends_on_checks").and_then(|x| x.as_array()).map(|a| a.iter().map(|x| x.as_u64().unwrap()).collect()).unwrap_or_default(),
                hyp_lines: f.get("hyps").and_then(|x| x.as_array()).map(|a| a.iter().map(|h| h["line"].as_u64().unwrap()).collect()).unwrap_or_default(),
            }
        })
        .collect()
}

/// Compare kernel output with the oracle: (matching cups, total oracle cups, report lines).
pub fn compare(ex: &str) -> (usize, usize, Vec<String>) {
    let src = testdata(ex, "wat");
    let j: Value = serde_json::from_str(&testdata(ex, "expect.json")).unwrap();
    let gradual = j["mode"].as_str() == Some("gradual");
    let out = check_module(&Module::parse(&src), gradual);
    let mut mine = ours(&out);
    let want = oracle(&j);
    let mut ok = 0;
    let mut report = vec![];
    for w in &want {
        let pos = mine.iter().position(|m| m.line == w.line && m.kind == w.kind);
        match pos {
            None => report.push(format!("  MISSING {w:?}")),
            Some(p) => {
                let m = mine.remove(p);
                let same = m.verdict == w.verdict && m.by == w.by && m.feed_line == w.feed_line && m.checks == w.checks && m.operand == w.operand;
                if same {
                    ok += 1;
                    if m.hyp_lines != w.hyp_lines {
                        report.push(format!("  (hyps differ) line {} {}: ours {:?} oracle {:?}", w.line, w.kind, m.hyp_lines, w.hyp_lines));
                    }
                } else {
                    let diag = out.cups().find(|c| c.line as u64 == w.line && c.kind.name() == w.kind).and_then(|c| c.diag.clone()).unwrap_or_default();
                    let goal = out.cups().find(|c| c.line as u64 == w.line && c.kind.name() == w.kind).map(|c| c.goal.clone()).unwrap_or_default();
                    report.push(format!("  DIFF line {} {} goal {goal}\n     ours   {:?} {:?} {:?} op {:?} checks {:?} hyps {:?}\n     oracle {:?} {:?} {:?} op {:?} checks {:?} hyps {:?}\n     diag {diag}",
                        w.line, w.kind, m.verdict, m.by, m.feed_line, m.operand, m.checks, m.hyp_lines, w.verdict, w.by, w.feed_line, w.operand, w.checks, w.hyp_lines));
                }
            }
        }
    }
    for m in &mine {
        report.push(format!("  EXTRA {m:?}"));
    }
    for f in &out.funcs {
        for (l, e) in &f.line_errors {
            report.push(format!("  line error {l}: {e}"));
        }
    }
    (ok, want.len(), report)
}

#[test]
fn oracle_report() {
    let mut total = (0, 0);
    let mut text = String::new();
    let only = std::env::var("V2_EX").ok();
    for ex in EXAMPLES {
        if only.as_deref().is_some_and(|o| o != ex) {
            continue;
        }
        eprintln!("checking {ex}");
        let t0 = std::time::Instant::now();
        let (ok, n, rep) = compare(ex);
        let dt = t0.elapsed();
        text.push_str(&format!("{ex}: {ok}/{n} ({:.1} ms)\n", dt.as_secs_f64() * 1000.0));
        for r in rep {
            text.push_str(&r);
            text.push('\n');
        }
        total.0 += ok;
        total.1 += n;
    }
    text.push_str(&format!("TOTAL {}/{}\n", total.0, total.1));
    let _ = std::fs::write(format!("{}/target/v2-oracle-report.txt", env!("CARGO_MANIFEST_DIR")), &text);
    println!("{text}");
}

// ---------------- decision procedure unit tests ----------------

mod solver_units {
    use crate::v2::ast::{IOp, ValTy};
    use crate::v2::solver::{Env, Outcome, Solver};
    use crate::v2::term::{Atom, Rel, TermId, Terms};

    struct NoEnv;
    impl Env for NoEnv {
        fn unfold(&mut self, _: &mut Terms, _: TermId) -> Option<TermId> {
            None
        }
        fn eval_call(&mut self, _: &Terms, _: TermId) -> Option<u64> {
            None
        }
        fn is_real(&self, _: TermId) -> bool {
            true
        }
    }

    pub fn prove(t: &mut Terms, hyps: &[Atom], goal: &Atom) -> Outcome {
        let mut env = NoEnv;
        let t0 = std::time::Instant::now();
        let r = Solver::new(t, &mut env).prove(hyps, goal);
        assert!(t0.elapsed().as_millis() < 2000, "prove took {:?}", t0.elapsed());
        r
    }

    fn lt(a: TermId, b: TermId) -> Atom {
        Atom::cmp(Rel::Lt, false, a, b)
    }
    fn le(a: TermId, b: TermId) -> Atom {
        Atom::cmp(Rel::Le, false, a, b)
    }

    /// Reviewer B1: a product of two non-constant terms used to hang Omega-lite.
    #[test]
    fn product_of_two_variables_terminates() {
        let mut t = Terms::default();
        let x = t.leaf(ValTy::I32, "$x", None);
        let y = t.leaf(ValTy::I32, "$y", None);
        let c16 = t.konst(ValTy::I32, 16);
        let c225 = t.konst(ValTy::I32, 225);
        let xy = t.op(IOp::Mul, ValTy::I32, &[x, y]);
        let r = prove(&mut t, &[lt(x, c16), lt(y, c16)], &le(xy, c225));
        // x·y is a monomial atom: bounded by its interval [0, 225]
        assert!(matches!(r, Outcome::Valid { .. }), "{r:?}");
        let c224 = t.konst(ValTy::I32, 224);
        let r = prove(&mut t, &[lt(x, c16), lt(y, c16)], &le(xy, c224));
        assert!(!matches!(r, Outcome::Valid { .. }), "{r:?}");
    }
}
