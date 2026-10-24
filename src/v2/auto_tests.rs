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

/// isqrt and primality with every routine `prove` line deleted: every cup keeps its verdict, and
/// the cups the deleted lines fed are now fed automatically.
#[test]
fn isqrt_and_primality_without_proves() {
    for ex in ["isqrt", "primality"] {
        let src = testdata(ex);
        let stripped = strip_proves(&src);
        assert!(stripped.lines().count() < src.lines().count(), "{ex}");
        let a = check_module(&Module::parse(&src), false);
        let b = check_module(&Module::parse(&stripped), false);
        let va: Vec<(&str, u8)> = a.cups().map(|c| (c.kind.name(), rank(c))).collect();
        let vb: Vec<(&str, u8)> = b.cups().map(|c| (c.kind.name(), rank(c))).collect();
        assert_eq!(va, vb, "{ex}");
        assert!(
            b.cups().any(|c| matches!(c.feed, Feed::Auto { .. })),
            "{ex}"
        );
        for f in &b.funcs {
            assert!(
                f.line_errors.is_empty(),
                "{ex} {}: {:?}",
                f.name,
                f.line_errors
            );
            assert_eq!(f.verified, func(&a, &f.name).verified, "{ex} {}", f.name);
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

/// When the whole relevant set exceeds the caps, R5a retries with the 8 most recent relevant
/// facts; if that fails too, the cup stays unfed and the message suggests `prove k`.
#[test]
fn cap_falls_back_then_suggests_prove() {
    // p16 < p24 follows from the 8 most recent guards
    let (src, line) = chain(16);
    let out = check_module(&Module::parse(&src), false);
    let c = cup(func(&out, "$f"), line);
    let Feed::Auto { hyp_lines, .. } = &c.feed else {
        panic!("{:?} {:?}", c.feed, c.diag)
    };
    assert_eq!(hyp_lines.len(), 8);
    // p0 < p24 needs all 24 guards: over the cap, and the 8 recent ones do not suffice
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
    s += "  call $h\n";
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
}
