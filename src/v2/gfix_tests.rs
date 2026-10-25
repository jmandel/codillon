//! Phase G regressions (research/20-gemini-review-v2.md §F): one reproducer per finding.

use super::ast::Module;
use super::kernel::check_module;
use super::out::{ModuleOut, Verdict};

fn check(src: &str) -> ModuleOut {
    let m = Module::parse(src);
    assert!(m.errors.is_empty(), "{:?}", m.errors);
    check_module(&m, true)
}

fn errors(out: &ModuleOut) -> Vec<(u32, String)> {
    out.funcs
        .iter()
        .flat_map(|f| f.line_errors.clone())
        .collect()
}

/// Every cup on `line` is neither proven nor assumed-only-by-axiom-free derivation.
fn not_proven_at(out: &ModuleOut, line: u32) {
    let cups: Vec<_> = out.cups().filter(|c| c.line == line).collect();
    assert!(!cups.is_empty(), "no cup on line {line}");
    for c in cups {
        assert_ne!(
            c.verdict,
            Verdict::Proven,
            "line {line}: {:?} {:?}; errors {:?}",
            c.kind.name(),
            c.diag,
            errors(out)
        );
    }
}

fn verified(out: &ModuleOut, name: &str) -> bool {
    out.funcs.iter().find(|f| f.name == name).unwrap().verified
}

// ---------------- F1: lemmas are ghost code and must be total (R33) ----------------

const F1_LOOP: &str = r#"(func $boom (export "lemma:boom") (result (fact (i32.const 0)))
  loop $l
    br $l
  end
)
(func $f (export "f") (param $x i32) (result i32)
  lemma $boom
  i32.const 1
  local.get $x
  prove 1
  i32.div_u
)"#;

#[test]
fn f1_a_looping_lemma_proves_nothing() {
    let out = check(F1_LOOP);
    not_proven_at(&out, 11);
    assert!(!verified(&out, "$f"));
    assert!(!verified(&out, "$boom"));
    assert!(
        errors(&out)
            .iter()
            .any(|(l, e)| *l == 1 && e.contains("loop")),
        "{:?}",
        errors(&out)
    );
}

#[test]
fn f1_a_lemma_may_not_call_partial_code() {
    // $spin is an ordinary function: partial correctness lets it "return" False; ghost code may not
    // rest on it, since the lemma is never run and nothing makes $spin terminate
    let src = r#"(func $spin (result (fact (i32.const 0)))
  loop $l
    br $l
  end
)
(func $boom (export "lemma:boom") (result (fact (i32.const 0)))
  call $spin
)
(func $f (export "f") (param $x i32) (result i32)
  lemma $boom
  i32.const 1
  local.get $x
  prove 1
  i32.div_u
)"#;
    let out = check(src);
    not_proven_at(&out, 14);
    assert!(!verified(&out, "$f"));
}

#[test]
fn f1_calling_a_lemma_as_code_is_an_error() {
    let src = r#"(func $boom (export "lemma:boom") (result (fact (i32.const 0)))
  loop $l
    br $l
  end
)
(func $f (export "f") (param $x i32) (result i32)
  call $boom
  i32.const 1
  local.get $x
  prove 1
  i32.div_u
)"#;
    let out = check(src);
    not_proven_at(&out, 11);
    assert!(
        errors(&out).iter().any(|(l, _)| *l == 7),
        "{:?}",
        errors(&out)
    );
}

#[test]
fn f1_mutually_recursive_lemmas_are_rejected() {
    let src = r#"(func $a (export "lemma:a") (result (fact (i32.const 0)))
  lemma $b
)
(func $b (export "lemma:b") (result (fact (i32.const 0)))
  lemma $a
)
(func $f (export "f") (param $x i32) (result i32)
  lemma $a
  i32.const 1
  local.get $x
  prove 1
  i32.div_u
)"#;
    let out = check(src);
    not_proven_at(&out, 12);
    assert!(!verified(&out, "$f"));
    assert!(
        errors(&out)
            .iter()
            .any(|(_, e)| e.contains("recursive through")),
        "{:?}",
        errors(&out)
    );
}

#[test]
fn f1_lemma_value_results_and_stores_are_errors() {
    let src = r#"(memory 1)
(func $v (export "lemma:v") (result i32)
  i32.const 0
)
(func $s (export "lemma:s") (result (fact (i32.const 1)))
  i32.const 0
  i32.const 0
  i32.store
)"#;
    let out = check(src);
    let e = errors(&out);
    assert!(e.iter().any(|(l, _)| *l == 2), "{e:?}");
    assert!(e.iter().any(|(l, _)| *l == 5), "{e:?}");
}

#[test]
#[ignore]
fn dump_src() {
    let src = std::fs::read_to_string(std::env::var("SRC").unwrap()).unwrap();
    let out = check_module(&Module::parse(&src), std::env::var("STRICT").is_err());
    for f in &out.funcs {
        println!(
            "func {} verified={} strict_clean={}",
            f.name, f.verified, f.strict_clean
        );
        for c in &f.cups {
            println!(
                "  cup {} {} {:?} ⟨{}⟩ {:?} checks {:?} {:?}",
                c.line,
                c.kind.name(),
                c.verdict,
                c.goal,
                c.feed,
                c.depends_on_checks,
                c.diag
            );
        }
        for e in &f.line_errors {
            println!("  ERR {e:?}");
        }
    }
}

// ---------------- F2: a refinement naming another local is that local's invariant too (R7/R8) ----------------

const F2: &str = r#"(func $f (export "f") (param $c i32) (result i32)
  (local $n i32)
  (local $r (i32 | (i32.le_u v $n)))
  local.get $c
  if
    i32.const 10
    local.set $n
    i32.const 10
    local.set $r
    i32.const 0
    local.set $n
  end
  i32.const 1
  i32.const 10
  local.get $r
  i32.sub
  prove 1
  i32.div_u
)"#;

#[test]
fn f2_writing_a_local_named_in_a_refinement_owes_its_cup() {
    let out = check(F2);
    assert!(!verified(&out, "$f"));
    let c = out
        .cups()
        .find(|c| c.line == 11)
        .expect("a refinement cup for $r on `local.set $n`");
    assert_eq!(c.verdict, Verdict::Refuted);
    // the division rests on that cup: proven only relative to it
    let d = out.cups().find(|c| c.line == 18).unwrap();
    assert!(!d.depends_on_checks.is_empty());
    // gradual run with a value the kernel cannot fold: the new cup is a runtime check on line 11
    let src = F2
        .replacen(
            "    i32.const 0\n    local.set $n",
            "    local.get $c\n    local.set $n",
            1,
        )
        .replacen(
            "  local.get $c\n  if",
            "  local.get $c\n  i32.const 1\n  i32.sub\n  if",
            1,
        );
    let (r, _) = super::tests::instrumented_run(&src, "f", &[2]);
    assert!(
        matches!(r, Err(super::eval::EvalErr::CheckFailed { line: 13, .. })),
        "{r:?}"
    );
    let (r, _) = super::tests::instrumented_run(&src, "f", &[1]);
    assert!(r.is_ok(), "{r:?}");
}

#[test]
fn f2_a_local_refinement_may_not_read_memory() {
    let src = r#"(memory 1)
(func $p (param $a i32) (result i32)
  local.get $a
  i32.load
)
(func $f (export "f") (param $c i32) (result i32)
  (local $r (i32 | (call $p v)))
  i32.const 0
)"#;
    let out = check(src);
    assert!(
        errors(&out)
            .iter()
            .any(|(l, e)| *l == 7 && e.contains("memory")),
        "{:?}",
        errors(&out)
    );
}

// ---------------- F3: refined globals: initializer, module-wide set cups, only `v` ----------------

const F3: &str = r#"(global $g (mut (i32 | (i32.ne v 0))) (i32.const 0))
(func $f (export "f") (param $x i32) (result i32)
  i32.const 1
  global.get $g
  i32.div_u
)
(global $h (mut (i32 | (i32.ne v 0))) (i32.const 1))
(func $setter (export "setter") (param $x i32)
  local.get $x
  global.set $h
)
(func $reader (export "reader") (result i32)
  i32.const 1
  global.get $h
  i32.div_u
)
(global $k (mut (i32 | (i32.lt_u v $x))) (i32.const 1))
(func $lie (export "lie") (param $x i32) (result i32)
  i32.const 1
  local.get $x
  i32.div_u
)"#;

#[test]
fn f3_refined_globals_rest_on_their_initializer_and_every_set() {
    let m = Module::parse(F3);
    let out = check_module(&m, true);
    // $g's initializer 0 violates `v ≠ 0`: a module error, and the division is not proven
    assert!(
        out.errors
            .iter()
            .any(|(l, e)| *l == 1 && e.contains("initializer")),
        "{:?}",
        out.errors
    );
    not_proven_at(&out, 5);
    assert!(!verified(&out, "$f"));
    // $setter's unproven global.set (line 10) is a check $reader's division rests on
    let c = out.cups().find(|c| c.line == 15).unwrap();
    assert_eq!(c.depends_on_checks.to_vec(), vec![10]);
    assert!(!verified(&out, "$reader"));
    // $k's refinement names a local: rejected, so $lie gets nothing from it
    assert!(
        out.errors
            .iter()
            .any(|(l, e)| *l == 17 && e.contains("only `v`")),
        "{:?}",
        out.errors
    );
    not_proven_at(&out, 21);
    // gradual: the check in $setter catches the bad write before $reader can divide by it
    let (r, _) = super::tests::instrumented_run(F3, "setter", &[0]);
    assert!(
        matches!(r, Err(super::eval::EvalErr::CheckFailed { line: 10, .. })),
        "{r:?}"
    );
}

#[test]
fn f3_a_good_initializer_and_proven_sets_stay_verified() {
    let src = r#"(global $h (mut (i32 | (i32.ne v 0))) (i32.const 1))
(func $setter (export "setter")
  i32.const 7
  global.set $h
)
(func $reader (export "reader") (result i32)
  i32.const 1
  global.get $h
  i32.div_u
)"#;
    let out = check(src);
    assert!(out.errors.is_empty(), "{:?}", out.errors);
    assert!(verified(&out, "$setter"));
    assert!(verified(&out, "$reader"));
}

// ---------------- F4: R35 captures only of values born on every path to the check ----------------

const F4: &str = r#"(func $pos (param $a i32) (result i32)
  local.get $a
  i32.const 0
  i32.gt_s
)
(func $need (param $a (i32 | (call $pos v))) (result i32)
  local.get $a
)
(func $f (export "f") (param $x i32) (result i32)
  local.get $x
  call $need
  drop
  local.get $x
  call $pos
)
(func $g (export "g") (param $x i32) (param $c i32) (result i32)
  local.get $c
  if
    local.get $x
    call $pos
    drop
  else
    local.get $x
    call $need
    drop
  end
  i32.const 0
)"#;

#[test]
fn f4_a_check_never_reads_a_capture_from_later_or_a_sibling_arm() {
    use super::eval::EvalErr;
    // $pos($x) is computed again on line 14 (later) and line 20 (the other arm): the checks on
    // lines 11 and 24 must evaluate it, not read a shadow that was never written
    let (r, _) = super::tests::instrumented_run(F4, "f", &[5]);
    assert_eq!(r.unwrap(), vec![1]);
    let (r, _) = super::tests::instrumented_run(F4, "f", &[-1]);
    assert!(
        matches!(r, Err(EvalErr::CheckFailed { line: 11, .. })),
        "{r:?}"
    );
    let (r, _) = super::tests::instrumented_run(F4, "g", &[5, 0]);
    assert_eq!(r.unwrap(), vec![0]);
    let (r, _) = super::tests::instrumented_run(F4, "g", &[-1, 0]);
    assert!(
        matches!(r, Err(EvalErr::CheckFailed { line: 24, .. })),
        "{r:?}"
    );
    // negated: a 0 shadow would make ¬$pos($x) pass for x = 5
    let neg = F4.replace("(call $pos v)", "(i32.eqz (call $pos v))");
    let (r, _) = super::tests::instrumented_run(&neg, "f", &[5]);
    assert!(
        matches!(r, Err(EvalErr::CheckFailed { line: 11, .. })),
        "{r:?}"
    );
}

// ---------------- vericoding helpers ----------------

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

// ---------------- F6: every LLM-owned function must be strict-clean, touched or not ----------------

#[test]
fn f6_an_untouched_unproven_target_blocks_acceptance() {
    use super::vericode::SessionStart;
    let start = session_start("parity");
    let s = SessionStart::new(&start);
    assert!(start[38].contains("i32.const -1"), "{}", start[38]);
    // the gate computes x >> 1 inline and never calls (or fixes) $half, which stays `i32.const 0`
    let sub = replace(
        &start,
        39,
        39,
        &[
            "  local.get $x",
            "  call $is_even",
            "  i32.eqz",
            "  if (result (i32 | $hon_ok $x))",
            "    i32.const -1",
            "    prove 1",
            "  else",
            "    local.get $x",
            "    i32.const 1",
            "    i32.shr_s",
            "    prove 1",
            "  end",
        ],
    );
    let j = s.judge(&sub);
    assert!(!j.crossed(), "{:?}", j.boundary);
    assert_eq!(j.touched, vec!["$half_or_neg1".to_string()]);
    assert!(
        !j.out
            .funcs
            .iter()
            .find(|f| f.name == "$half")
            .unwrap()
            .verified,
        "$half is still a stub"
    );
    assert!(!j.accepted, "{}", j.summary());
    assert!(j.strict.iter().any(|r| r.line == 37), "{:?}", j.strict);
    // and an empty round on the start state is not "all verified"
    assert!(!s.judge(&start).accepted);
}

// ---------------- F5: in vericoding, an implementation must also run ----------------

#[test]
fn f5_a_spinning_or_self_calling_body_is_not_accepted() {
    use super::vericode::SessionStart;
    let start = session_start("isqrt");
    let s = SessionStart::new(&start);
    assert!(start[30].starts_with("(func $isqrt "));
    for body in [
        vec!["  loop $spin", "    br $spin", "  end", "  unreachable"],
        vec!["  local.get $n", "  call $isqrt"],
    ] {
        let sub = replace(&start, 32, 32, &body);
        let j = s.judge(&sub);
        assert!(!j.crossed(), "{:?}", j.boundary);
        // the kernel alone proves it (partial correctness) ...
        assert!(
            j.out.funcs.iter().all(|f| f.verified),
            "{body:?}: {:?}",
            j.strict
        );
        // ... but the judge runs it
        assert!(!j.accepted, "{body:?}: {}", j.summary());
        assert!(
            j.strict.iter().any(|r| r.msg.contains("does not finish")),
            "{:?}",
            j.strict
        );
    }
}

#[test]
fn f5_adequacy_reports_a_harness_that_never_finishes() {
    use super::adequacy::Bench;
    let start = session_start("isqrt");
    let sub = replace(
        &start,
        32,
        32,
        &["  loop $spin", "    br $spin", "  end", "  unreachable"],
    );
    let b = Bench::new(&sub, 8);
    assert!(b.runs.is_empty());
    assert_eq!(b.runs_away.len(), 1, "{:?}", b.runs_away);
    assert!(b.runs_away[0].starts_with("$isqrt_harness("));
    // gcd's spec predicate recurses deeper than adequacy's depth on some inputs: that is not
    // the implementation running away
    let p = format!("{}/public/examples/v2/gcd.wat", env!("CARGO_MANIFEST_DIR"));
    let g: Vec<String> = std::fs::read_to_string(p)
        .unwrap()
        .lines()
        .map(String::from)
        .collect();
    assert!(Bench::new(&g, 48).runs_away.is_empty());
}

// ---------------- F7: a locked line made dead is a boundary violation ----------------

#[test]
fn f7_returning_before_a_locked_line_is_rejected() {
    use super::vericode::SessionStart;
    let start: Vec<String> = r#"(func $main
  i32.const 5
  call $f
  drop
)
(func $f (export "f") (param $x i32) (result i32)
  block $b (fact (i32.lt_u $x 100)) ;; @own
    nop
  end
  local.get $x
)"#
    .lines()
    .map(String::from)
    .collect();
    let s = SessionStart::new(&start);
    assert!(!s.judge(&start).accepted, "x < 100 is not provable");
    let sub = replace(
        &start,
        7,
        7,
        &["  local.get $x", "  return", start[6].as_str()],
    );
    let j = s.judge(&sub);
    assert!(!j.accepted, "{}", j.summary());
    assert!(
        j.boundary
            .iter()
            .any(|r| r.line == 9 && r.msg.contains("unreachable")),
        "{:?}",
        j.boundary
    );
    // a line already dead at the start is not the round's doing
    let s2 = SessionStart::new(&sub);
    assert!(s2.judge(&sub).boundary.is_empty());
}

// ---------------- A14b (review 19): a student line moved within its own block ----------------

/// Moving a student line among LLM lines of the same block is the same text as the LLM editing
/// its own lines around it (delete above, insert below), so it cannot be a boundary violation by
/// itself. What could make such a move harmful is covered elsewhere: an `assume` is never
/// accepted in LLM code (strict), a block fact is checked at every exit wherever its header sits,
/// a move into another block is a boundary violation (context), and a locked line made dead is
/// one too (F7).
#[test]
fn a14b_a_move_within_the_block_is_judged_by_its_effect() {
    use super::vericode::SessionStart;
    let p = format!("{}/public/examples/v2/gcd.wat", env!("CARGO_MANIFEST_DIR"));
    let g: Vec<String> = std::fs::read_to_string(p)
        .unwrap()
        .lines()
        .map(String::from)
        .collect();
    let mut base = g.clone();
    base.insert(120, "      assume (fact (i32.ne $y 0))".into());
    let s = SessionStart::new(&base);
    let mut t = base.clone();
    let a = t.remove(120);
    t.insert(117, a);
    let j = s.judge(&t);
    assert!(!j.crossed());
    assert!(
        !j.accepted,
        "an assume in LLM code is never accepted: {} {:?} {:?}",
        j.summary(),
        j.boundary,
        j.strict
    );
    // moved out of its loop: crossed
    let mut t = base.clone();
    let a = t.remove(120);
    t.insert(115, a);
    let j = s.judge(&t);
    assert!(j.crossed(), "{}", j.summary());
}

// ---------------- F8: loop parameters and float conversions are checked at run time ----------------

const F8: &str = r#"(func $f (export "f") (param $n i32) (result i32)
  (local $t i32)
  local.get $n
  loop $l (param i32) (result i32)
    local.set $t
    i32.const 100
    local.get $t
    i32.div_u
  end
)
(func $g (export "g") (param $x f32) (result i32)
  local.get $x
  i32.trunc_f32_s
)
(func $h (export "h") (result i32)
  f32.const -2147483648
  i32.trunc_f32_s
)
(func $k (export "k") (result i64)
  f32.const -9223372036854775808
  i64.trunc_f32_s
)"#;

#[test]
fn f8_a_check_on_a_loop_parameter_runs() {
    use super::eval::EvalErr;
    let (r, n) = super::tests::instrumented_run(F8, "f", &[4]);
    assert_eq!(r.unwrap(), vec![25]);
    assert!(n > 0, "the check ran");
    let (r, _) = super::tests::instrumented_run(F8, "f", &[0]);
    assert!(
        matches!(r, Err(EvalErr::CheckFailed { line: 8, .. })),
        "{r:?}"
    );
}

#[test]
fn f8_float_conversion_checks_evaluate() {
    use super::runtime::{CheckOutcome, RuntimePlan};
    let m = Module::parse(F8);
    let out = check_module(&m, true);
    // −2^31 and −2^63 are exact in f32 and truncate fine: the kernel evaluates both cups true
    for line in [17, 21] {
        let cups: Vec<_> = out.cups().filter(|c| c.line == line).collect();
        assert_eq!(cups.len(), 2);
        for c in cups {
            assert_eq!(c.verdict, Verdict::Proven, "line {line}: {}", c.goal);
        }
    }
    // $g's two cups are runtime checks that evaluate on the run's value
    let plan = RuntimePlan::new(&m, &out);
    let ids: Vec<u32> = (0..plan.checks.len() as u32)
        .filter(|i| plan.checks[*i as usize].line == 13)
        .collect();
    assert_eq!(ids.len(), 2);
    let run = |x: f32| -> Vec<CheckOutcome> {
        ids.iter()
            .map(|i| plan.eval_check(*i, &[x.to_bits() as u64], None))
            .collect()
    };
    assert!(run(1.5).iter().all(|o| *o == CheckOutcome::Holds));
    assert!(run(-2147483648.0).iter().all(|o| *o == CheckOutcome::Holds));
    assert!(run(3e9).iter().any(|o| matches!(o, CheckOutcome::Fails(_))));
    assert!(
        run(f32::NAN)
            .iter()
            .any(|o| matches!(o, CheckOutcome::Fails(_)))
    );
}

#[test]
fn f8_eval_fop_matches_wasm() {
    use super::eval::eval_fop;
    let f = |x: f32| x.to_bits() as u64;
    assert_eq!(eval_fop("f32.add", &[f(1.5), f(2.25)]), Ok(f(3.75)));
    assert_eq!(eval_fop("f32.lt", &[f(1.0), f(2.0)]), Ok(1));
    assert_eq!(
        eval_fop("i32.trunc_f32_s", &[f(-2147483648.0)]),
        Ok(0x8000_0000)
    );
    assert_eq!(eval_fop("i32.trunc_f32_s", &[f(2147483648.0)]), Err(true));
    assert_eq!(eval_fop("i32.trunc_sat_f32_s", &[f(f32::NAN)]), Ok(0));
    assert_eq!(
        eval_fop("f64.convert_i32_u", &[0xffff_ffff]),
        Ok(4294967295.0f64.to_bits())
    );
    assert_eq!(eval_fop("f32.min", &[f(-0.0), f(0.0)]), Ok(f(-0.0)));
    assert_eq!(eval_fop("v128.any_true", &[0]), Err(false));
}

// ---------------- F9: fact parameters and fact results in adequacy ----------------

#[test]
fn f9_fact_preconditions_and_tautological_fact_results() {
    use super::adequacy::{pre_holds, vacuity};
    let src: Vec<String> = r#"(func $f (export "f") (param $k i32) (param $h (fact (i32.lt_u $k 10))) (result (fact (i32.ge_u $k 0)))
  prove 0
)
(func $g (export "g") (param $k i32) (param $h (fact (i32.lt_u $k 0))) (result (fact (i32.lt_u $k 10)))
  local.get $k
  drop
  prove 1
)"#
    .lines()
    .map(String::from)
    .collect();
    let m = Module::parse_lines(&src);
    assert!(pre_holds(&m, 0, &[3]));
    assert!(
        !pre_holds(&m, 0, &[12]),
        "the fact parameter is a precondition"
    );
    let rows = vacuity(&src);
    let f = rows.iter().find(|r| r.func == "$f").unwrap();
    assert!(f.witnesses > 0 && f.witnesses < f.tried, "{f:?}");
    assert!(f.unconstraining, "u(k) ≥ 0 holds for every k: {f:?}");
    let g = rows.iter().find(|r| r.func == "$g").unwrap();
    assert!(g.vacuous && g.witnesses == 0, "{g:?}");
}
