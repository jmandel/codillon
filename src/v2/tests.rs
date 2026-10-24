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

    fn eqa(t: &mut Terms, a: TermId, b: TermId) -> Atom {
        t.mk_eq(a, b, true)
    }

    #[test]
    fn wraparound_is_explicit() {
        let mut t = Terms::default();
        let x = t.leaf(ValTy::I32, "$x", None);
        let z = t.konst(ValTy::I32, 0);
        let one = t.konst(ValTy::I32, 1);
        let c8 = t.konst(ValTy::I32, 8);
        let x0 = t.op(IOp::Add, ValTy::I32, &[x, z]);
        // add(x, 0) = x needs the result-range side constraint (review issue 4)
        let g = eqa(&mut t, x0, x);
        assert!(matches!(prove(&mut t, &[], &g), Outcome::Valid { .. }));
        // x < x + 1 is false at x = 2^32 − 1 (the wrap stays in the problem)
        let x1 = t.op(IOp::Add, ValTy::I32, &[x, one]);
        match prove(&mut t, &[], &lt(x, x1)) {
            Outcome::NotImplied(m) => assert!(m.contains(&("u($x)".into(), 4294967295)), "{m:?}"),
            r => panic!("{r:?}"),
        }
        // …but holds when the interval pre-pass removes the wrap: u(x) < 8
        match prove(&mut t, &[lt(x, c8)], &lt(x, x1)) {
            Outcome::Valid { wraps } => assert!(!wraps.is_empty()),
            r => panic!("{r:?}"),
        }
        // i64 squares of i32 values do not wrap: ext(r)·ext(r) ≥ 0 trivially, and (r+1)² = r² + 2r + 1
        let r = t.leaf(ValTy::I32, "$r", None);
        let e = t.op(IOp::ExtendI32U, ValTy::I32, &[r]);
        let one64 = t.konst(ValTy::I64, 1);
        let e1 = t.op(IOp::Add, ValTy::I64, &[e, one64]);
        let sq = t.op(IOp::Mul, ValTy::I64, &[e, e]);
        let sq1 = t.op(IOp::Mul, ValTy::I64, &[e1, e1]);
        // (2^32)^2 wraps to 0 in i64, so it needs a bound on r
        assert!(!matches!(prove(&mut t, &[], &lt(sq, sq1)), Outcome::Valid { .. }));
        let c65535 = t.konst(ValTy::I32, 65535);
        assert!(matches!(prove(&mut t, &[le(r, c65535)], &lt(sq, sq1)), Outcome::Valid { .. }));
        // the same in i32 wraps at r = 65535 (the isqrt lesson): not valid
        let r1 = t.op(IOp::Add, ValTy::I32, &[r, one]);
        let sq32 = t.op(IOp::Mul, ValTy::I32, &[r, r]);
        let sq32b = t.op(IOp::Mul, ValTy::I32, &[r1, r1]);
        assert!(!matches!(prove(&mut t, &[], &lt(sq32, sq32b)), Outcome::Valid { .. }));
    }

    #[test]
    fn case_splits_and_counterexamples() {
        let mut t = Terms::default();
        let x = t.leaf(ValTy::I32, "$x", None);
        let y = t.leaf(ValTy::I32, "$y", None);
        let z = t.konst(ValTy::I32, 0);
        // ne is a two-way split: x ≠ 0 ∧ x ≤ 0 ⇒ False
        let ne = t.mk_eq(x, z, false);
        assert!(matches!(prove(&mut t, &[ne.clone(), le(x, z)], &Atom::False), Outcome::Valid { .. }));
        // select is an ite split: select(x, y, x<y) ≥ … the minimum is ≤ both
        let c = t.op(IOp::LtU, ValTy::I32, &[x, y]);
        let mn = t.intern(crate::v2::term::Key::Ite(c, x, y), ValTy::I32);
        assert!(matches!(prove(&mut t, &[], &le(mn, x)), Outcome::Valid { .. }));
        assert!(matches!(prove(&mut t, &[], &le(mn, y)), Outcome::Valid { .. }));
        // a countermodel names program values
        match prove(&mut t, &[ne], &lt(y, x)) {
            Outcome::NotImplied(m) => assert!(!m.is_empty()),
            r => panic!("{r:?}"),
        }
        // parity: and(x, 1) = 0 ⇒ x ≠ 1
        let one = t.konst(ValTy::I32, 1);
        let a = t.op(IOp::And, ValTy::I32, &[x, one]);
        let ev = t.mk_eq(a, z, true);
        let g = t.mk_eq(x, one, false);
        assert!(matches!(prove(&mut t, &[ev], &g), Outcome::Valid { .. }));
    }

    #[test]
    fn caps_are_deterministic() {
        // more than 64 terms in one atom
        let mut t = Terms::default();
        let mut sum = t.konst(ValTy::I64, 0);
        for i in 0..70 {
            let x = t.leaf(ValTy::I32, format!("$x{i}"), None);
            let e = t.op(IOp::ExtendI32U, ValTy::I32, &[x]);
            sum = t.op(IOp::Add, ValTy::I64, &[sum, e]);
        }
        let big = t.konst(ValTy::I64, 1 << 40);
        match prove(&mut t, &[], &lt(sum, big)) {
            Outcome::Cap(s) => assert!(s.contains("cap 64"), "{s}"),
            r => panic!("{r:?}"),
        }
        // more than 256 cases: a chain of unresolvable i32 wraps
        let mut t = Terms::default();
        let mut acc = t.leaf(ValTy::I32, "$a", None);
        let mut leaves = vec![];
        for i in 0..10 {
            let x = t.leaf(ValTy::I32, format!("$x{i}"), None);
            leaves.push(x);
            acc = t.op(IOp::Add, ValTy::I32, &[acc, x]);
        }
        let _ = leaves;
        // valid in every case, but 2^10 cases must be closed
        let max = t.konst(ValTy::I32, 0xffff_ffff);
        let r1 = prove(&mut t, &[], &le(acc, max));
        let r2 = prove(&mut t, &[], &le(acc, max));
        assert_eq!(r1, r2);
        match r1 {
            Outcome::Cap(s) => assert!(s.contains("cases"), "{s}"),
            r => panic!("{r:?}"),
        }
    }
}

// ---------------- Fable review §A counterexamples: none may prove ----------------

/// Check `src`; return (verdict, diag) of every cup on lines marked `;; @cup`, and line errors.
fn marked(src: &str) -> (Vec<(u32, Verdict, String)>, Vec<(u32, String)>) {
    let out = check_module(&Module::parse(src), true);
    let lines: Vec<u32> = src.lines().enumerate().filter(|(_, l)| l.contains(";; @cup")).map(|(i, _)| i as u32 + 1).collect();
    assert!(!lines.is_empty());
    let cups = out.cups().filter(|c| lines.contains(&c.line)).map(|c| (c.line, c.verdict, c.diag.clone().unwrap_or_default())).collect();
    let errs = out.funcs.iter().flat_map(|f| f.line_errors.clone()).collect();
    (cups, errs)
}

fn none_proven(src: &str) {
    let (cups, errs) = marked(src);
    assert!(!cups.is_empty(), "no cups on marked lines");
    for (l, v, d) in &cups {
        assert!(!matches!(v, Verdict::Proven | Verdict::Assumed), "line {l} is {v:?} ({d}); errors {errs:?}");
    }
}

#[test]
fn fable_a1_predicate_reading_a_mutable_global() {
    let src = r#"(global $g (mut i32) (i32.const 1))
(func $gnz (result i32)
  global.get $g
)
(func $div_by_g (param $a (i32 | (call $gnz))) (result i32)
  local.get $a
  global.get $g
  prove 1
  i32.div_u ;; @cup
)
(func $a1 (param $n i32) (result i32)
  call $gnz
  if (result i32)
    i32.const 0
    global.set $g
    local.get $n
    call $div_by_g ;; @cup
  else
    i32.const 0
  end
)"#;
    none_proven(src);
    let (_, errs) = marked(src);
    assert!(errs.iter().any(|(_, e)| e.contains("must be pure")), "{errs:?}");
}

#[test]
fn fable_a2_globals_get_phi_at_loop_heads() {
    none_proven(
        r#"(global $g (mut i32) (i32.const 7))
(func $a2 (result i32)
  global.get $g
  i32.eqz
  if (result i32)
    i32.const 0
  else
    loop $L
      i32.const 10
      global.get $g
      i32.div_u ;; @cup
      drop
      i32.const 0
      global.set $g
      br $L
    end
    unreachable
  end
)"#,
    );
}

#[test]
fn fable_a3_edge_prove_output_stays_on_the_edge() {
    none_proven(
        r#"(func $a3 (param $n i32) (param $d i32) (result i32)
  block $b (fact (i32.ne $d 0))
    local.get $d
    i32.eqz
    i32.eqz
    prove 0
    br_if $b
    local.get $n
    local.get $d
    i32.div_u ;; @cup
    return
  end
  i32.const 1
)"#,
    );
}

#[test]
fn fable_a4_virtual_rem_u_is_guarded() {
    none_proven(
        r#"(func $gcd_ref (param $a i32) (param $b i32) (result i32)
  local.get $b
  i32.eqz
  if (result i32)
    local.get $a
  else
    local.get $b
    local.get $a
    local.get $b
    i32.rem_u
    prove 0
    call $gcd_ref
  end
)
(func $gcd_ref_m (export "measure:gcd_ref") (param $a i32) (param $b i32) (result i32)
  local.get $b
)
(func $a4 (param $n i32) (param $y i32) (result i32)
  unfold $gcd_ref $n $y
  local.get $n
  local.get $y
  prove 1
  i32.div_u ;; @cup
)
(func $a4c (param $n i32) (result i32)
  local.get $n
  local.get $n
  prove 0
  i32.div_u ;; @cup
)"#,
    );
}

#[test]
fn constant_zero_divisor_in_a_proposition_is_opaque() {
    // (div_u x 0) in a fact must not make every case unsatisfiable (review A4 residue)
    none_proven(
        r#"(func $z (param $x i32) (param $y i32) (result i32)
  local.get $x
  local.get $y
  assume (fact (i32.eq (i32.div_u $x (i32.const 0)) (i32.const 3)))
  prove 1
  i32.div_u ;; @cup
)"#,
    );
}
