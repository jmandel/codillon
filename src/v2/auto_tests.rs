//! Native tests for R5a, automatic feeding (design 16 §2, research/24).

use super::ast::Module;
use super::kernel::{check_module, check_module_probing, check_module_with};
use super::out::{CupKind, CupOut, Feed, FuncOut, ModuleOut, Verdict};

fn testdata(name: &str) -> String {
    let p = format!("{}/src/v2/testdata/{name}.wat", env!("CARGO_MANIFEST_DIR"));
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{p}: {e}"))
}

/// Delete every `prove k` line (the routine ones R5a makes unnecessary).
fn strip_proves(src: &str) -> String {
    src.lines()
        .filter(|l| {
            let t = l.split(";;").next().unwrap().trim();
            !(t.starts_with("prove ") && t[6..].trim().parse::<u32>().is_ok())
        })
        .map(|l| format!("{l}\n"))
        .collect()
}

fn func<'o>(out: &'o ModuleOut, name: &str) -> &'o FuncOut {
    out.funcs.iter().find(|f| f.name == name).unwrap()
}

fn cup(f: &FuncOut, line: u32) -> &CupOut {
    f.cups.iter().find(|c| c.line == line).unwrap()
}

/// A rank for "same or strictly better": unfed < relative to checks < assumed < proven.
fn rank(c: &CupOut) -> u8 {
    match c.verdict {
        Verdict::Refuted => 0,
        Verdict::RuntimeChecked => 1,
        _ if !c.depends_on_checks.is_empty() => 2,
        Verdict::Assumed => 3,
        Verdict::Proven => 4,
    }
}

// ---- tests ----

/// The user's program (research/24 §2) with no `prove` line: `unreachable`'s False cup is fed
/// automatically by the `br_if` fall-through fact, and the lines after `br_if` never run.
#[test]
fn user_example_needs_no_prove() {
    let src = "(func $f (param $x i32)
  local.get $x
  i32.const 2
  i32.mul
  i32.const 1
  i32.and
  i32.eqz
  br_if 0
  unreachable
)
";
    let out = check_module_with(&Module::parse(src), false, true);
    let f = &out.funcs[0];
    assert!(f.verified, "{:?}", f.line_errors);
    let c = cup(f, 9);
    assert_eq!(c.kind, CupKind::False);
    let Feed::Auto {
        hyps, hyp_lines, ..
    } = &c.feed
    else {
        panic!("{:?}", c.feed)
    };
    assert_eq!(hyp_lines.as_slice(), &[8]);
    assert_eq!(f.chips[hyps[0] as usize].origin, "br_if fall-through");
    let e = c.explain.as_ref().expect("an account");
    assert!(e.ex_falso, "{e:?}");
    assert!(
        f.never_runs
            .iter()
            .any(|r| r.from <= 9 && 9 <= r.to && r.cause == 8),
        "{:?}",
        f.never_runs
    );
}

/// isqrt and primality as shipped: no routine `prove` line (isqrt has none; primality keeps one
/// commented override), and every function is still VERIFIED with no line error; the cups
/// the deleted lines fed are fed automatically. Deleting primality's override too changes nothing.
#[test]
fn isqrt_and_primality_without_proves() {
    let proves = |s: &str| {
        s.lines()
            .filter(|l| l.trim_start().starts_with("prove "))
            .count()
    };
    for (ex, kept) in [("isqrt", 0), ("primality", 1)] {
        let src = testdata(ex);
        assert_eq!(proves(&src), kept, "{ex}");
        for text in [src.clone(), strip_proves(&src)] {
            let out = check_module(&Module::parse(&text), false);
            assert!(
                out.cups()
                    .filter(|c| matches!(c.feed, Feed::Auto { .. }))
                    .count()
                    >= 6,
                "{ex}"
            );
            for f in &out.funcs {
                assert!(
                    f.line_errors.is_empty(),
                    "{ex} {}: {:?}",
                    f.name,
                    f.line_errors
                );
                assert!(f.verified, "{ex} {}", f.name);
            }
            let ranks: Vec<u8> = out.cups().map(rank).collect();
            assert!(ranks.iter().all(|r| *r >= 3), "{ex}");
        }
    }
}

/// An explicit `prove k` keeps R32's meaning: it feeds the cup, with its own hypotheses.
#[test]
fn explicit_prove_still_feeds() {
    let src = "(func $is_even (param $x i32) (result i32)
  local.get $x
  i32.const 1
  i32.and
  i32.eqz
)
(func $half (param $x (i32 | $is_even)) (result (i32 | $is_even))
  local.get $x
  i32.const 2
  i32.add
  prove 1
)
";
    let out = check_module(&Module::parse(src), false);
    let f = func(&out, "$half");
    let c = f
        .cups
        .iter()
        .find(|c| c.kind == CupKind::ResultRefinement)
        .unwrap();
    let Feed::Prove { hyp_lines, .. } = &c.feed else {
        panic!("{:?}", c.feed)
    };
    assert_eq!(hyp_lines.len(), 1);
    assert_eq!(c.verdict, Verdict::Proven);
}

const GUARD: &str = "(func $g (param $a (i32 | (i32.lt_u v (i32.const 10)))))
(func $f (param $x i32) (param $y i32)
  local.get $x
  i32.const 5
  i32.lt_u
  if
    BODY
    local.get $x
    call $g
  end
)
";

fn guard_case(body: &str) -> ModuleOut {
    check_module(&Module::parse(&GUARD.replace("BODY", body)), false)
}

/// A fact that frayed at a `local.set` is not used for the new value: the cup stays unfed and
/// the error names the stale fact. Without the rebinding, the guard feeds the cup by R5a.
#[test]
fn frayed_fact_is_not_used() {
    let ok = guard_case("nop");
    let f = func(&ok, "$f");
    let c = f.cups.iter().find(|c| c.line == 9).unwrap();
    let Feed::Auto { hyp_lines, .. } = &c.feed else {
        panic!("{:?}", c.feed)
    };
    assert_eq!(hyp_lines.as_slice(), &[6]);

    let stale = guard_case("local.get $y\n    local.set $x");
    let f = func(&stale, "$f");
    let c = f.cups.iter().find(|c| c.line == 10).unwrap();
    assert_eq!(c.feed, Feed::Unfed, "{:?}", c.diag);
    let d = c.diag.as_deref().unwrap();
    assert!(d.contains("is about the old $x"), "{d}");
}

/// A fact about the old value *is* used when the new value is computed from it: after
/// `x := x + 1` the guard on the old x bounds the new one (a loop back edge's usual shape).
#[test]
fn old_value_fact_used_when_goal_reaches_it() {
    let out = guard_case("local.get $x\n    i32.const 1\n    i32.add\n    local.set $x");
    let f = func(&out, "$f");
    let c = f.cups.iter().find(|c| c.line == 12).unwrap();
    let Feed::Auto { hyp_lines, .. } = &c.feed else {
        panic!("{:?} {:?}", c.feed, c.diag)
    };
    assert_eq!(hyp_lines.as_slice(), &[6]);
}

/// `$f` with 25 parameters and nested guards `p0 < p1`, …, `p23 < p24`; the call needs
/// `p{lo} < p24`. Relevance pulls in the whole chain (25 variables, over the 24-variable cap).
fn chain(lo: usize) -> (String, u32) {
    let n = 25;
    let mut s =
        String::from("(func $g (param $a i32) (param $b (i32 | (i32.lt_u $a v))))\n(func $f");
    for i in 0..n {
        s += &format!(" (param $p{i} i32)");
    }
    s += "\n";
    for i in 0..n - 1 {
        s += &format!(
            "  local.get $p{i}\n  local.get $p{}\n  i32.lt_u\n  if\n",
            i + 1
        );
    }
    s += &format!("  local.get $p{lo}\n  local.get $p{}\n  call $g\n", n - 1);
    let call_line = s.lines().count() as u32;
    for _ in 0..n - 1 {
        s += "  end\n";
    }
    s += ")\n";
    (s, call_line)
}

/// When the whole relevant set exceeds the caps, R5a retries with the 8 closest relevant facts
/// (by ring, ties to the most recent); if that fails too, the cup stays unfed and the message suggests `prove k`.
#[test]
fn cap_falls_back_then_suggests_prove() {
    // p20 < p24 follows from the 8 closest guards (rings 1–2 around p20 and p24)
    let (src, line) = chain(20);
    let out = check_module(&Module::parse(&src), false);
    let c = cup(func(&out, "$f"), line);
    let Feed::Auto { hyp_lines, .. } = &c.feed else {
        panic!("{:?} {:?}", c.feed, c.diag)
    };
    assert_eq!(hyp_lines.len(), 4);
    // p0 < p24 needs all 24 guards: over the cap, and the 8 closest do not suffice
    let (src, line) = chain(0);
    let out = check_module(&Module::parse(&src), false);
    let f = func(&out, "$f");
    let c = cup(f, line);
    assert_eq!(c.feed, Feed::Unfed);
    let d = c.diag.as_deref().unwrap();
    assert!(
        d.contains("exceed the solver's limits") && d.contains("prove k"),
        "{d}"
    );
    assert!(
        f.line_errors
            .iter()
            .any(|(l, e)| *l == line && e.contains("prove k"))
    );
}

fn lines(s: &str) -> Vec<String> {
    s.lines().map(String::from).collect()
}

fn replace(lines: &[String], a: usize, b: usize, with: &[&str]) -> Vec<String> {
    let mut out = lines[..a - 1].to_vec();
    out.extend(with.iter().map(|s| s.to_string()));
    out.extend(lines[b..].iter().cloned());
    out
}

/// Vericoding (research/22 B3, research/24 §6): R5a feeds the cups of a locked line that is
/// reached only with contradictory facts, but the judge still rejects the submission — with no
/// `prove` line anywhere.
#[test]
fn auto_does_not_discharge_a_locked_line_ex_falso() {
    use super::vericode::SessionStart;
    let start = lines(
        r#"(func $main
  i32.const 5
  call $f
  drop
)
(func $f (export "f") (param $x i32) (result i32)
  local.get $x
  i32.const 0
  i32.eq
  br_if 0
  block $b (fact (i32.lt_u $x 100)) ;; @own
    nop
  end
  local.get $x
)"#,
    );
    let s = SessionStart::new(&start);
    let cond = [
        "  local.get $x",
        "  i32.const 5",
        "  i32.ge_u",
        "  br_if 0",
        "  local.get $x",
        "  i32.const 10",
        "  i32.le_u",
    ];
    let sub = replace(&start, 7, 9, &cond);
    let j = s.judge(&sub);
    assert!(!j.accepted, "{}", sub.join("\n"));
    assert!(
        j.boundary.iter().any(|r| r.msg.contains("ex falso")),
        "{:?}",
        j.boundary
    );
    // and the kernel did feed the locked block's fact automatically
    let out = check_module(&Module::parse(&sub.join("\n")), false);
    let f = func(&out, "$f");
    assert!(
        f.cups
            .iter()
            .any(|c| c.kind.name() == "BlockFact" && matches!(c.feed, Feed::Auto { .. })),
        "{:?}",
        f.cups
            .iter()
            .map(|c| (&c.goal, &c.feed))
            .collect::<Vec<_>>()
    );
}

/// The probe of a locked line asks whether the whole lane (or its 8 most recent facts) proves
/// False. Here the whole lane is over the caps and the recent facts are consistent, but the cup's
/// relevant facts `x < y` and `y < x` contradict each other: the line is still reported as
/// reached only ex falso.
#[test]
fn probe_catches_contradiction_found_by_auto() {
    let n = 25;
    let mut s = String::from(
        "(func $h (param $a (i32 | (i32.lt_u v (i32.const 3)))))\n(func $f (param $x i32)",
    );
    for i in 0..n {
        s += &format!(" (param $p{i} i32)");
    }
    s += " (param $y i32)\n  local.get $x\n  local.get $y\n  i32.lt_u\n  if\n";
    s += "  local.get $y\n  local.get $x\n  i32.lt_u\n  if\n";
    for i in 0..n - 1 {
        s += &format!(
            "  local.get $p{i}\n  local.get $p{}\n  i32.lt_u\n  if\n",
            i + 1
        );
    }
    s += "  local.get $x\n";
    let line = s.lines().count() as u32 + 1;
    s += "  call $h\n  nop\n";
    for _ in 0..n + 1 {
        s += "  end\n";
    }
    s += ")\n";
    let m = Module::parse(&s);
    let out = check_module_probing(&m, false, [line].into_iter().collect());
    let f = func(&out, "$f");
    let c = cup(f, line);
    let Feed::Auto { hyp_lines, .. } = &c.feed else {
        panic!("{:?} {:?}", c.feed, c.diag)
    };
    assert_eq!(hyp_lines.len(), 2);
    assert!(f.false_ctx_lines.contains(&line), "{:?}", f.false_ctx_lines);
    // review B1: a later probed line in the same arm, with no cup of its own, is ex falso too
    let out = check_module_probing(&m, false, [line, line + 1].into_iter().collect());
    let f = func(&out, "$f");
    assert!(
        f.false_ctx_lines.contains(&(line + 1)),
        "{:?}",
        f.false_ctx_lines
    );
    // the ex-falso feed itself may sit on an unprobed (LLM-owned) line: the later locked line
    // is still flagged
    let out = check_module_probing(&m, false, [line + 1].into_iter().collect());
    let f = func(&out, "$f");
    assert!(
        f.false_ctx_lines.contains(&(line + 1)),
        "{:?}",
        f.false_ctx_lines
    );
}

/// Review B3: relevance looks through R29 unfolding, so a memory predicate reaches the loads it
/// reads. The guard is about `mem32[0]`; the cup is `$zero()`, whose body reads `mem32[0]`.
#[test]
fn relevance_looks_through_unfolding() {
    let src = "(memory 1)
(func $zero (result i32)
  i32.const 0
  i32.load
  i32.eqz
)
(func $g (param $h (fact (call $zero))))
(func $f
  i32.const 0
  i32.load
  i32.eqz
  if
    call $g
  end
)
";
    let out = check_module(&Module::parse(src), false);
    let f = func(&out, "$f");
    let c = cup(f, 13);
    let Feed::Auto { hyp_lines, .. } = &c.feed else {
        panic!("{:?} {:?}", c.feed, c.diag)
    };
    assert_eq!(hyp_lines.as_slice(), &[12]);
}

/// Review S1: when a proven fact and an assumed one both suffice, the feed uses the proven one,
/// so the cup (and the function) stays proven.
#[test]
fn minimization_prefers_proven_facts() {
    let src = "(func $ax (export \"axiom:small\") (param $x i32) (result (fact (i32.lt_u $x 4))))
(func $g (param $a (i32 | (i32.lt_u v (i32.const 16)))))
(func $f (param $x i32)
  local.get $x
  i32.const 8
  i32.lt_u
  if
    lemma $ax $x
    local.get $x
    call $g
  end
)
";
    let out = check_module(&Module::parse(src), false);
    let f = func(&out, "$f");
    let c = cup(f, 10);
    let Feed::Auto { hyp_lines, .. } = &c.feed else {
        panic!("{:?} {:?}", c.feed, c.diag)
    };
    assert_eq!(hyp_lines.as_slice(), &[7]);
    assert_eq!(c.verdict, Verdict::Proven);
    assert!(c.assumptions.is_empty());
}

/// Timing of the whole kernel on each example, with every `prove` line deleted, against the
/// original text (research/24 §7). `cargo test --release --lib auto_timing -- --ignored --nocapture`
#[test]
#[ignore]
fn auto_timing() {
    let names = [
        "parity",
        "isqrt",
        "gcd",
        "primality",
        "hashtable",
        "hashtable-stale",
    ];
    for ex in names {
        let src = testdata(ex);
        let stripped = strip_proves(&src);
        for (what, text) in [("with proves", &src), ("auto only", &stripped)] {
            let m = Module::parse(text);
            for explain in [false, true] {
                let t0 = std::time::Instant::now();
                let reps = 20;
                let mut out = None;
                for _ in 0..reps {
                    out = Some(check_module_with(&m, true, explain));
                }
                let dt = t0.elapsed().as_secs_f64() * 1000.0 / reps as f64;
                let out = out.unwrap();
                let nf = out.funcs.len();
                let auto = out
                    .cups()
                    .filter(|c| matches!(c.feed, Feed::Auto { .. }))
                    .count();
                println!(
                    "{ex:16} {what:12} explain={explain:5} {dt:7.2} ms total, {:5.2} ms/function ({nf} functions, {auto} auto cups)",
                    dt / nf as f64
                );
            }
        }
    }
}

/// Dump the kernel's cups as JSON for the oracle tools (research/v2-examples):
/// `EX_PATH=x.wat MODE=gradual cargo test --release --lib dump_cups_json -- --ignored`
#[test]
#[ignore]
fn dump_cups_json() {
    use serde_json::json;
    let Ok(p) = std::env::var("EX_PATH") else {
        return;
    };
    let gradual = std::env::var("MODE").as_deref() != Ok("strict");
    let src = std::fs::read_to_string(&p).unwrap();
    let out = check_module(&Module::parse(&src), gradual);
    let mut cups = vec![];
    for f in &out.funcs {
        for c in &f.cups {
            let hyps = |ids: &[u32], lines: &[u32]| -> Vec<serde_json::Value> {
                ids.iter()
                    .zip(lines)
                    .map(|(id, l)| json!({"line": l, "fact": f.chips[*id as usize].text}))
                    .collect()
            };
            let feed = match &c.feed {
                Feed::Lookup { fact, origin_line } => json!({"by": "lookup",
                    "facts": [{"line": origin_line, "fact": f.chips[*fact as usize].text}]}),
                Feed::Prove {
                    prove_line,
                    hyps: h,
                    hyp_lines,
                    ..
                } => {
                    json!({"by": "prove", "line": prove_line, "hyps": hyps(h, hyp_lines)})
                }
                Feed::Auto {
                    hyps: h, hyp_lines, ..
                } => {
                    json!({"by": "auto", "hyps": hyps(h, hyp_lines)})
                }
                Feed::Eval { .. } => json!({"by": "eval"}),
                Feed::DeadCode { ended_at } => json!({"by": "dead", "line": ended_at}),
                Feed::Unfed => json!({"by": "none"}),
            };
            cups.push(json!({
                "func": f.name, "line": c.line, "operand": c.operand, "kind": c.kind.name(),
                "goal": c.goal,
                "verdict": if c.verdict == Verdict::Refuted { "refuted" } else { c.verdict.name() },
                "feed": feed, "depends_on_checks": c.depends_on_checks.to_vec(),
                "assumptions": c.assumptions.iter().map(|o| o.line).collect::<Vec<_>>(),
                "diag": c.diag,
            }));
        }
    }
    let errs: Vec<_> = out
        .funcs
        .iter()
        .flat_map(|f| f.line_errors.iter())
        .chain(out.errors.iter())
        .collect();
    let funcs: Vec<_> = out
        .funcs
        .iter()
        .map(|f| json!({"name": f.name, "verified": f.verified, "strict_clean": f.strict_clean}))
        .collect();
    println!(
        "CUPS_JSON {}",
        json!({"cups": cups, "line_errors": errs, "funcs": funcs})
    );
}
