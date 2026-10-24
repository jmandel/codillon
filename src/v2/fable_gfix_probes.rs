//! Fable's adversarial probes of the Phase G fixes (research/22-gfix-review-fable.md). Each test
//! asserts the *sound* expectation, so a failing test is a finding, not a regression.

use super::ast::Module;
use super::kernel::check_module;
use super::out::ModuleOut;
use super::vericode::SessionStart;

fn check(src: &str) -> ModuleOut {
    let m = Module::parse(src);
    assert!(m.errors.is_empty(), "{:?}", m.errors);
    check_module(&m, true)
}

fn errors(out: &ModuleOut) -> Vec<(u32, String)> {
    let mut e: Vec<(u32, String)> = out.errors.clone();
    e.extend(out.funcs.iter().flat_map(|f| f.line_errors.clone()));
    e
}

fn verified(out: &ModuleOut, name: &str) -> bool {
    out.funcs.iter().find(|f| f.name == name).unwrap().verified
}

fn dump(out: &ModuleOut) -> String {
    let mut s = String::new();
    for f in &out.funcs {
        s += &format!("func {} verified={} strict_clean={}\n", f.name, f.verified, f.strict_clean);
        for c in &f.cups {
            s += &format!(
                "  cup {} {} {:?} ⟨{}⟩ {:?} checks {:?} {:?}\n",
                c.line, c.kind.name(), c.verdict, c.goal, c.feed, c.depends_on_checks, c.diag
            );
        }
        for e in &f.line_errors {
            s += &format!("  ERR {e:?}\n");
        }
    }
    for e in &out.errors {
        s += &format!("MODERR {e:?}\n");
    }
    s
}

fn lines(src: &str) -> Vec<String> {
    src.lines().map(String::from).collect()
}

fn session_start(name: &str) -> Vec<String> {
    let p = format!(
        "{}/public/examples/v2/sessions/{name}.json",
        env!("CARGO_MANIFEST_DIR")
    );
    let s = super::llm::parse_script(&std::fs::read_to_string(p).unwrap()).unwrap();
    s.start
}

fn replace(lines: &[String], a: usize, b: usize, with: &[&str]) -> Vec<String> {
    let mut out = lines[..a - 1].to_vec();
    out.extend(with.iter().map(|s| s.to_string()));
    out.extend(lines[b..].iter().cloned());
    out
}

// ---------------- F1: lemma totality ----------------

/// A lemma may call only predicates "which R29 keeps total" — but R29 checks the predicate's own
/// body, not its callees. $p calls $spin, an ordinary function that never returns and whose
/// result refinement is False (dead-fed, so proven). The lemma erases to nop; $f then divides by 0.
/// Fixed (B1): a function a predicate calls is itself a predicate (R29), so `$spin` is rejected
/// for its loop and nothing downstream is VERIFIED.
#[test]
fn fable_f1_lemma_through_predicate_through_partial_callee() {
    let src = r#"(func $spin (result (i32 | (i32.ne v v)))
  loop $l
    br $l
  end
  unreachable
)
(func $p (param $a i32) (result (i32 | (i32.ne $a 0)))
  call $spin
  prove 1
)
(func $dummy (param $a i32) (param $h (fact (call $p $a)))
)
(func $boom (export "lemma:boom") (param $x i32) (result (fact (i32.ne $x 0)))
  local.get $x
  call $p
  drop
)
(func $f (export "f") (param $x i32) (result i32)
  lemma $boom $x
  i32.const 1
  local.get $x
  i32.div_u
)"#;
    let out = check(src);
    println!("{}", dump(&out));
    let (r, _) = super::tests::instrumented_run(src, "f", &[0]);
    println!("run f(0): {r:?}");
    assert!(
        !verified(&out, "$f") && !verified(&out, "$boom") && !verified(&out, "$p"),
        "lemma rests on a non-terminating predicate callee"
    );
    assert!(
        errors(&out)
            .iter()
            .any(|(l, e)| *l == 1 && e.contains("predicate $spin has a loop")),
        "{:?}",
        errors(&out)
    );
    // the same with unmeasured self-recursion instead of a loop
    let rec = src.replace(
        "  loop $l\n    br $l\n  end\n  unreachable",
        "  call $spin",
    );
    assert_ne!(rec, src);
    let out = check(&rec);
    println!("{}", dump(&out));
    assert!(!verified(&out, "$f") && !verified(&out, "$boom"));
    assert!(
        errors(&out)
            .iter()
            .any(|(l, e)| *l == 1 && e.contains("recursive without measure")),
        "{:?}",
        errors(&out)
    );
}

/// `lemma $self` whose measure does not decrease.
#[test]
fn fable_f1_self_lemma_with_nondecreasing_measure() {
    let src = r#"(func $m (export "measure:lem") (param $x i32) (result i32)
  local.get $x
)
(func $lem (export "lemma:lem") (param $x i32) (result (fact (i32.ne $x 0)))
  lemma $lem $x
)
(func $f (export "f") (param $x i32) (result i32)
  lemma $lem $x
  i32.const 1
  local.get $x
  prove 1
  i32.div_u
)"#;
    let out = check(src);
    println!("{}", dump(&out));
    assert!(!verified(&out, "$f"));
    assert!(!verified(&out, "$lem"));
}

/// Cycle predicate → (lemma line) → lemma → (call) → predicate.
#[test]
fn fable_f1_predicate_lemma_cycle() {
    let src = r#"(func $p (param $a i32) (result i32)
  lemma $boom $a
  i32.const 1
)
(func $dummy (param $a i32) (param $h (fact (call $p $a)))
)
(func $boom (export "lemma:boom") (param $x i32) (result (fact (i32.ne $x 0)))
  local.get $x
  call $p
  drop
)
(func $f (export "f") (param $x i32) (result i32)
  lemma $boom $x
  i32.const 1
  local.get $x
  prove 1
  i32.div_u
)"#;
    let out = check(src);
    println!("{}", dump(&out));
    assert!(!verified(&out, "$f"));
    assert!(errors(&out).iter().any(|(_, e)| e.contains("recursive through")));
}

// ---------------- F2: aliasing through tee, params, globals ----------------

const F2_TEE: &str = r#"(func $f (export "f") (param $c i32) (result i32)
  (local $n i32)
  (local $r (i32 | (i32.le_u v $n)))
  local.get $c
  if
    i32.const 10
    local.set $n
    i32.const 10
    local.set $r
    i32.const 0
    local.tee $n
    drop
  end
  i32.const 1
  i32.const 10
  local.get $r
  i32.sub
  prove 1
  i32.div_u
)"#;

#[test]
fn fable_f2_tee_owes_the_cup_too() {
    let out = check(F2_TEE);
    println!("{}", dump(&out));
    assert!(!verified(&out, "$f"));
    let (r, _) = super::tests::instrumented_run(F2_TEE, "f", &[1]);
    println!("run f(1): {r:?}");
    assert!(r.is_err(), "f(1) must not return (it divides by zero): {r:?}");
}

/// A parameter's refinement names another parameter; the body overwrites that one.
#[test]
fn fable_f2_param_refinement_naming_a_param() {
    let src = r#"(func $f (export "f") (param $a i32) (param $r (i32 | (i32.le_u v $a))) (result i32)
  i32.const 0
  local.set $a
  i32.const 1
  local.get $a
  i32.const 1
  i32.add
  local.get $r
  i32.sub
  prove 1
  i32.div_u
)
(func $main
  i32.const 10
  i32.const 10
  call $f
  drop
)"#;
    let out = check(src);
    println!("{}", dump(&out));
    assert!(!verified(&out, "$f"));
    let c = out.cups().find(|c| c.line == 3).expect("R7 cup on `local.set $a`");
    println!("param cup: {:?} {}", c.verdict, c.goal);
}

/// A local's refinement naming a mutable global.
#[test]
fn fable_f2_local_refinement_naming_a_global() {
    let src = r#"(global $g (mut i32) (i32.const 10))
(func $f (export "f") (result i32)
  (local $r (i32 | (i32.le_u v $g)))
  i32.const 10
  local.set $r
  i32.const 0
  global.set $g
  i32.const 1
  global.get $g
  i32.const 1
  i32.add
  local.get $r
  i32.sub
  prove 1
  i32.div_u
)"#;
    let m = Module::parse(src);
    println!("parse errors {:?}", m.errors);
    let out = check_module(&m, true);
    println!("{}", dump(&out));
    let (r, _) = super::tests::instrumented_run(src, "f", &[]);
    println!("run f: {r:?}");
    assert!(
        !verified(&out, "$f") || !errors(&out).is_empty(),
        "a global named by a local refinement can be rewritten unseen"
    );
}

// ---------------- F3: refined globals ----------------

#[test]
#[ignore = "HOLE (research/22 S2): a function named only by a global refinement is not a predicate"]
fn fable_f3_global_refinement_via_predicate_reading_another_global() {
    let src = r#"(global $h (mut i32) (i32.const 1))
(func $p (param $a i32) (result i32)
  local.get $a
  global.get $h
  i32.ge_u
)
(global $g (mut (i32 | (call $p v))) (i32.const 5))
(func $f (export "f") (result i32)
  i32.const 6
  global.set $h
  i32.const 1
  global.get $g
  i32.const 1
  i32.add
  global.get $h
  i32.sub
  prove 1
  i32.div_u
)"#;
    let m = Module::parse(src);
    println!("parse errors {:?}", m.errors);
    let out = check_module(&m, true);
    println!("{}", dump(&out));
    let (r, _) = super::tests::instrumented_run(src, "f", &[]);
    println!("run f: {r:?}");
    assert!(!verified(&out, "$f"));
    // and a function named only by a global's refinement is not a predicate at all (R29 never
    // looks at it): a loop and a mutable-global read pass without a word
    let src2 = r#"(global $h (mut i32) (i32.const 1))
(func $p (param $a i32) (result i32)
  loop $l
    br $l
  end
  unreachable
)
(global $g (mut (i32 | (call $p v))) (i32.const 5))
(func $f (export "f") (result i32)
  global.get $g
)"#;
    let m2 = Module::parse(src2);
    let out2 = check_module(&m2, true);
    println!("{}", dump(&out2));
    assert!(
        errors(&out2).iter().any(|(_, e)| e.contains("predicate") || e.contains("loop")),
        "a looping function serves as a global's refinement predicate: {:?}",
        errors(&out2)
    );
}

#[test]
fn fable_f3_global_set_in_a_lemma_is_an_error() {
    let src = r#"(global $g (mut (i32 | (i32.ne v 0))) (i32.const 1))
(func $l (export "lemma:l") (result (fact (i32.const 1)))
  i32.const 0
  global.set $g
)"#;
    let out = check(src);
    println!("{}", dump(&out));
    assert!(errors(&out).iter().any(|(l, _)| *l == 2), "{:?}", errors(&out));
}

// ---------------- F5: the program must run ----------------

/// The runaway is blamed only if the budget runs out *inside* an LLM-owned function. A spin loop
/// that spends most of its steps inside a student predicate is blamed on the student.
/// Fixed (B2): an LLM frame on the stack when the budget trips is blamed, wherever the counter
/// lands, so every k is rejected with `$isqrt` named.
#[test]
fn fable_f5_spin_loop_that_lives_in_a_student_predicate() {
    let start = session_start("isqrt");
    let s = SessionStart::new(&start);
    assert!(start[30].starts_with("(func $isqrt "), "{}", start[30]);
    let mut accepted_any = None;
    for k in 1..=6 {
        let mut body = vec!["  loop $spin".to_string()];
        for _ in 0..k {
            body.push("    local.get $n".into());
            body.push("    i64.extend_i32_u".into());
            body.push("    local.get $n".into());
            body.push("    i64.extend_i32_u".into());
            body.push("    call $is_isqrt".into());
            body.push("    drop".into());
        }
        body.push("    br $spin".into());
        body.push("  end".into());
        body.push("  unreachable".into());
        let b: Vec<&str> = body.iter().map(|s| s.as_str()).collect();
        let sub = replace(&start, 32, 32, &b);
        let j = s.judge(&sub);
        println!("k={k}: {} boundary={:?} strict={:?}", j.summary(), j.boundary, j.strict);
        if j.accepted {
            accepted_any = Some(k);
        }
        assert!(
            j.strict
                .iter()
                .any(|r| r.line == 31 && r.msg.starts_with("$isqrt(") && r.msg.contains("does not finish")),
            "k={k}: {:?}",
            j.strict
        );
    }
    assert!(accepted_any.is_none(), "accepted a body that never returns (k={accepted_any:?})");
}

/// A bare `unreachable` body: traps are "not this check's business".
#[test]
fn fable_f5_bare_unreachable_body() {
    let start = session_start("isqrt");
    let s = SessionStart::new(&start);
    let sub = replace(&start, 32, 32, &["  unreachable"]);
    let j = s.judge(&sub);
    println!("{} strict={:?}", j.summary(), j.strict);
    assert!(!j.accepted);
}

/// Functions that are never run by rule (5): a fact parameter, or a precondition with no witness
/// in 0..100. Neither is reachable from $main here, so nothing runs them.
#[test]
#[ignore = "HOLE (research/22 S1): fact-param and >100-precondition functions are never run"]
fn fable_f5_functions_the_termination_rule_never_runs() {
    let start = lines(
        r#"(func $main
  nop
)
(func $g (export "g") (param $x i32) (param $h (fact (i32.lt_u $x 10))) (result (i32 | (i32.eq v $x)))
  local.get $x
  prove 0
)
(func $big (export "big") (param $x (i32 | (i32.gt_u v 1000))) (result (i32 | (i32.eq v $x)))
  local.get $x
  prove 0
)"#,
    );
    let s = SessionStart::new(&start);
    let j0 = s.judge(&start);
    println!("start: {} {:?}", j0.summary(), j0.strict);
    assert!(j0.accepted, "baseline must be clean");
    let spin = ["  loop $spin", "    br $spin", "  end", "  unreachable"];
    let sub = replace(&start, 9, 10, &spin);
    let j = s.judge(&sub);
    println!("$big spins: {} {:?}", j.summary(), j.strict);
    let big_ok = !j.accepted;
    let sub = replace(&start, 5, 6, &spin);
    let j = s.judge(&sub);
    println!("$g spins: {} {:?}", j.summary(), j.strict);
    let g_ok = !j.accepted;
    assert!(big_ok && g_ok, "big_ok={big_ok} g_ok={g_ok}");
}

// ---------------- F7: locked lines made unreachable ----------------

/// The locked block sits in an `if` the LLM controls. A constant-false condition makes it
/// unreachable without making it dead in the kernel's sense (the arm is entered under `0 ≠ 0`).
#[test]
fn fable_f7_constant_if_around_a_locked_line() {
    let start = lines(
        r#"(func $main
  i32.const 5
  call $f
  drop
)
(func $f (export "f") (param $x i32) (result i32)
  local.get $x
  if
    block $b (fact (i32.lt_u $x 100)) ;; @own
      nop
    end
  end
  local.get $x
)"#,
    );
    let s = SessionStart::new(&start);
    let j0 = s.judge(&start);
    println!("start: {} {:?}", j0.summary(), j0.strict);
    assert!(!j0.accepted, "x < 100 is not provable at the start");
    let sub = replace(&start, 7, 7, &["  i32.const 0"]);
    let sub = replace(&sub, 10, 10, &["      prove 1"]);
    let j = s.judge(&sub);
    println!("const if: {} boundary={:?} strict={:?}", j.summary(), j.boundary, j.strict);
    assert!(!j.accepted, "locked line made unreachable by a constant condition");
    // fixed (B3): a constant-false arm is dead code, so the locked line is reported unreachable
    assert!(j.boundary.iter().any(|r| r.line == 9 && r.msg.contains("unreachable")), "{:?}", j.boundary);
}

#[test]
fn fable_f7_constant_br_if_before_a_locked_line() {
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
    assert!(!s.judge(&start).accepted);
    let sub = replace(&start, 7, 9, &["  local.get $x", "  i32.const 1"]);
    let sub = replace(&sub, 11, 11, &["    prove 1"]);
    println!("{}", sub.join("\n"));
    let j = s.judge(&sub);
    println!("const br_if: {} boundary={:?} strict={:?}", j.summary(), j.boundary, j.strict);
    assert!(!j.accepted, "locked line skipped by a constant br_if");
    // fixed (B3): the fall-through of an always-taken br_if is dead code
    assert!(j.boundary.iter().any(|r| r.line == 10 && r.msg.contains("unreachable")), "{:?}", j.boundary);
}

// ---------------- A14b: moves within a block ----------------

/// `else` is not a context boundary: a student line moved from the then-arm to the else-arm keeps
/// its context string.
#[test]
fn fable_a14b_then_to_else_keeps_context() {
    let start = lines(
        r#"(func $f (export "f") (param $x i32) (result i32)
  local.get $x
  if (result i32)
    block $b (fact (i32.lt_u $x 100)) ;; @own
      nop
    end
    i32.const 1
  else
    i32.const 2
  end
)"#,
    );
    let s = SessionStart::new(&start);
    let mut t = start.clone();
    let a = t.remove(3);
    let b = t.remove(3);
    let c = t.remove(3);
    t.insert(5, a);
    t.insert(6, b);
    t.insert(7, c);
    println!("{}", t.join("\n"));
    let v = s.zone_violation(&t);
    println!("violation: {v:?}");
    // record only: equivalent to the LLM negating the condition and swapping its own arms
    let _ = v;
    // two student lines of one block swapped: not expressible as LLM-only edits, must be caught
    let start2 = lines(
        r#"(func $f (export "f") (param $x i32) (result i32)
  local.get $x ;; @own
  i32.const 1 ;; @own
  i32.sub
)"#,
    );
    let s2 = SessionStart::new(&start2);
    let mut t2 = start2.clone();
    t2.swap(1, 2);
    let v2 = s2.zone_violation(&t2);
    println!("swap violation: {v2:?}");
    assert!(v2.is_some(), "swapping two locked lines in one block passed");
}

/// B3 beyond constants: a branch decided only by reasoning (a tautology, an unfolded LLM helper,
/// two contradictory facts) still leaves the locked line live in the kernel's dead-code sense,
/// but the kernel proves False there, which the judge rejects.
#[test]
fn b3_locked_line_reached_only_ex_falso_is_rejected() {
    let start = lines(
        r#"(func $main
  i32.const 5
  call $f
  drop
)
(func $g (export "g") (param $x i32) (result i32)
  local.get $x
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
    assert!(!s.judge(&start).accepted);
    let variants: Vec<(&str, Vec<&str>)> = vec![
        ("tautology x >=u 0", vec!["  local.get $x", "  i32.const 0", "  i32.ge_u"]),
        (
            "unfolded helper g(x) = x",
            vec!["  local.get $x", "  call $g", "  local.get $x", "  i32.eq"],
        ),
        (
            "x < 5 then x > 10",
            vec![
                "  local.get $x",
                "  i32.const 5",
                "  i32.ge_u",
                "  br_if 0",
                "  local.get $x",
                "  i32.const 10",
                "  i32.le_u",
            ],
        ),
    ];
    for (what, cond) in variants {
        let sub = replace(&start, 10, 12, &cond);
        let at = 10 + cond.len() + 2; // the `nop` inside the locked block
        let sub = replace(&sub, at, at, &["    prove 1"]);
        let j = s.judge(&sub);
        println!("{what}: {} boundary={:?} strict={:?}", j.summary(), j.boundary, j.strict);
        assert!(!j.accepted, "{what}: accepted\n{}", sub.join("\n"));
        assert!(
            j.boundary.iter().any(|r| r.msg.contains("ex falso")),
            "{what}: {:?}",
            j.boundary
        );
    }
    // the locked block is entered live, but its only exit is under a contradictory fact
    let sub = replace(
        &start,
        15,
        15,
        &[
            "    local.get $x",
            "    i32.const 0",
            "    i32.lt_u",
            "    if",
            "      prove 1",
            "      br $b",
            "    end",
            "    local.get $x",
            "    return",
        ],
    );
    let j = s.judge(&sub);
    println!("exit ex falso: {} boundary={:?} strict={:?}", j.summary(), j.boundary, j.strict);
    assert!(!j.accepted, "{}", sub.join("\n"));
    assert!(j.boundary.iter().any(|r| r.line == 14), "{:?}", j.boundary);
}

/// ... while a legitimate proof of the locked block fact is still accepted.
#[test]
fn b3_honest_guard_is_accepted() {
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
    let sub = replace(
        &start,
        7,
        12,
        &[
            "  local.get $x",
            "  i32.const 100",
            "  i32.ge_u",
            "  br_if 0",
            "  block $b (fact (i32.lt_u $x 100)) ;; @own",
            "    nop",
        ],
    );
    let j = s.judge(&sub);
    println!("{} boundary={:?} strict={:?}", j.summary(), j.boundary, j.strict);
    assert!(j.accepted, "{}", sub.join("\n"));
}
