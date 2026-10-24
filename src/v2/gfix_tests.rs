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
        errors(&out).iter().any(|(_, e)| e.contains("recursive through")),
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
        println!("func {} verified={} strict_clean={}", f.name, f.verified, f.strict_clean);
        for c in &f.cups {
            println!("  cup {} {} {:?} ⟨{}⟩ {:?} checks {:?} {:?}", c.line, c.kind.name(), c.verdict, c.goal, c.feed, c.depends_on_checks, c.diag);
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
    let src = F2.replacen(
        "    i32.const 0\n    local.set $n",
        "    local.get $c\n    local.set $n",
        1,
    )
    .replacen("  local.get $c\n  if", "  local.get $c\n  i32.const 1\n  i32.sub\n  if", 1);
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
        errors(&out).iter().any(|(l, e)| *l == 7 && e.contains("memory")),
        "{:?}",
        errors(&out)
    );
}
