//! Reviewer probes (not part of the branch): adversarial submissions against the judge.
use super::vericode::*;

fn example(name: &str) -> Vec<String> {
    let p = format!(
        "{}/public/examples/v2/{name}.wat",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::read_to_string(p)
        .unwrap()
        .lines()
        .map(|s| s.to_string())
        .collect()
}

fn report(tag: &str, s: &SessionStart, lines: &[String]) {
    let j = s.judge(lines);
    println!(
        "PROBE {tag}: accepted={} crossed={} :: {}",
        j.accepted,
        j.crossed(),
        j.summary()
    );
    for r in j.boundary.iter().take(3) {
        println!("    boundary @{}: {}", r.line, r.msg);
    }
    for r in j.malformed.iter().take(3) {
        println!("    malformed @{}: {}", r.line, r.msg);
    }
    for r in j.strict.iter().take(4) {
        println!("    strict @{}: {}", r.line, r.msg);
    }
    println!("    touched: {:?}", j.touched);
}

#[test]
fn fable_probes() {
    let g = example("gcd");
    let s = SessionStart::new(&g);
    report("A0 unchanged gcd", &s, &g);

    // A1 weaken the student header (line 110)
    let mut t = g.clone();
    t[109] = "(func $gcd (export \"gcd\") (param $a i32) (param $b i32) (result i32)".into();
    report("A1 weaken header", &s, &t);

    // A2 replace prove 3 (133) with an assume
    let mut t = g.clone();
    t[132] = "      assume (fact (i32.eq (call $gcd_ref $x $y) (call $gcd_ref $a $b)))".into();
    report("A2 assume in body", &s, &t);

    // A3 add an axiom in the LLM zone and use it
    let mut t = g.clone();
    t.insert(140, "(func $cheat (export \"axiom:cheat\") (param $g i32) (param $a i32) (param $b i32) (result (fact (call $is_gcd $g $a $b))))".into());
    t.insert(141, ")".into());
    report("A3 add axiom", &s, &t);

    // A4 add an unproven lemma with a fact result, use it in the harness instead of the axiom
    let mut t = g.clone();
    t[151] = "  lemma $free $g $a $b".into();
    t.push("(func $free (export \"lemma:free\") (param $g i32) (param $a i32) (param $b i32) (result (fact (call $is_gcd $g $a $b)))".into());
    t.push(")".into());
    report("A4 unproven lemma", &s, &t);

    // A5 edit the harness body: unreachable -> nop
    let mut t = g.clone();
    t[153] = "  nop".into();
    report("A5 harness body edit", &s, &t);

    // A6 add an import
    let mut t = g.clone();
    t.insert(
        1,
        "(import \"env\" \"oracle\" (func $oracle (param i32) (result i32)))".into(),
    );
    report("A6 import", &s, &t);

    // A7 add an ordinary function and call it
    let mut t = g.clone();
    t[136] = "  call $helper".into();
    t.push("(func $helper (result i32)".into());
    t.push("  i32.const 4".into());
    t.push(")".into());
    report("A7 new plain function", &s, &t);

    // A8 drop the harness proof line (153)
    let mut t = g.clone();
    t.remove(152);
    report("A8 drop harness prove", &s, &t);

    // A9 delete a student line (the axiom's closing paren, 109)
    let mut t = g.clone();
    t.remove(108);
    report("A9 delete student line", &s, &t);

    // A10 honest insertion in the LLM zone ($gcd body, before line 114) that shifts the harness down
    let mut t = g.clone();
    t.insert(113, "  nop".into());
    report("A10 honest shift", &s, &t);

    // A17 shadow the reference function $gcd_ref by a lemma placed before it; then $gcd's
    // postcondition (v = gcd_ref(a,b)) is about the LLM's function
    let mut t = g.clone();
    let orig = t
        .iter()
        .position(|l| l.starts_with("(func $gcd_ref "))
        .unwrap();
    println!(
        "    ($gcd_ref header at line {}: {})",
        orig + 1,
        &t[orig][..70.min(t[orig].len())]
    );
    let hdr = t[orig].replace(
        "(func $gcd_ref ",
        "(func $gcd_ref (export \"lemma:shadow2\") ",
    );
    t.insert(orig, ")".into());
    t.insert(orig, "  local.get $a".into());
    t.insert(orig, hdr);
    report("A17 shadow reference by lemma", &s, &t);

    // A11 trailing comment on a student header
    let mut t = g.clone();
    t[109] = format!("{} ;; hi", g[109]);
    report("A11 trailing comment", &s, &t);

    // A13 duplicate-name lemma shadowing the student predicate $is_gcd (placed before it)
    let mut t = g.clone();
    let orig = t
        .iter()
        .position(|l| l.starts_with("(func $is_gcd"))
        .unwrap();
    println!(
        "    ($is_gcd header at line {}: {})",
        orig + 1,
        &t[orig][..60.min(t[orig].len())]
    );
    let hdr = t[orig].replace("(func $is_gcd", "(func $is_gcd (export \"lemma:shadow\")");
    t.insert(orig, ")".into());
    t.insert(orig, "  i32.const 1".into());
    t.insert(orig, hdr);
    report("A13 shadow predicate by lemma", &s, &t);

    // A14 move an instructor-placed assume (synthetic: start from a module with one)
    let mut base = g.clone();
    base.insert(123, "      assume (fact (i32.ne $y 0))".into()); // after br_if $done
    let s2 = SessionStart::new(&base);
    report("A14a base with assume", &s2, &base);
    let mut t = base.clone();
    let a = t.remove(123);
    t.insert(120, a); // before the loop guard: now covers the guard too
    report("A14b moved assume", &s2, &t);

    // A14c move the assume out of the loop (different block context)
    let mut t = base.clone();
    let a = t.remove(123);
    t.insert(117, a); // before `block $done`, at function level
    report("A14c assume moved out of the loop", &s2, &t);

    // A15 a lemma that calls a student predicate and nothing else, claiming False
    let mut t = g.clone();
    t[151] = "  lemma $bogus".into();
    t.push("(func $bogus (export \"lemma:bogus\") (result (fact (i32.const 0)))".into());
    t.push("  unreachable".into());
    t.push(")".into());
    report("A15 lemma proving False", &s, &t);

    // A16 lemma with a param refinement that is unsatisfiable, used to discharge the goal
    let mut t = g.clone();
    t[151] = "  lemma $vac $g".into();
    t.push("(func $vac (export \"lemma:vac\") (param $g (i32 | (i32.lt_u v 0))) (result (fact (i32.const 0)))".into());
    t.push("  unreachable".into());
    t.push(")".into());
    report("A16 vacuous lemma", &s, &t);

    // A18 a lemma with an unreachable body used inside $gcd to discharge the result refinement
    let mut t = g.clone();
    t[137] = "  lemma $bogus2 $x $a $b".into();
    t[138] = "  nop".into();
    t.push("(func $bogus2 (export \"lemma:bogus2\") (param $x i32) (param $a i32) (param $b i32) (result (fact (i32.eq $x (call $gcd_ref $a $b))))".into());
    t.push("  unreachable".into());
    t.push(")".into());
    report("A18 unreachable lemma in body", &s, &t);

    // A19 same lemma but its False cup proven by a vacuous param refinement
    let mut t = g.clone();
    t[137] = "  lemma $vac2 $x $a $b".into();
    t[138] = "  nop".into();
    t.push("(func $vac2 (export \"lemma:vac2\") (param $x (i32 | (i32.lt_u v 0))) (param $a i32) (param $b i32) (result (fact (i32.eq $x (call $gcd_ref $a $b))))".into());
    t.push("  prove 1".into());
    t.push("  unreachable".into());
    t.push(")".into());
    report("A19 vacuous-param lemma in body", &s, &t);

    // dump A19's kernel cups
    let j = s.judge(&t);
    for f in &j.out.funcs {
        if f.name == "$gcd" || f.name == "$vac2" {
            println!(
                "    FUNC {} verified={} strict_clean={}",
                f.name, f.verified, f.strict_clean
            );
            for c in &f.cups {
                if f.name == "$vac2" || (136..=140).contains(&c.line) {
                    println!(
                        "      cup @{} {:?} ⟨{}⟩ {:?} feed={:?} assum={:?} dep={:?}",
                        c.line,
                        c.kind,
                        c.goal,
                        c.verdict,
                        c.feed,
                        c.assumptions
                            .iter()
                            .map(|o| (o.line, o.kind))
                            .collect::<Vec<_>>(),
                        c.depends_on_checks
                    );
                }
            }
            for (l, e) in &f.line_errors {
                println!("      err @{l}: {e}");
            }
        }
    }
    for l in 136..=140 {
        println!("    {}: {}", l, t[l - 1]);
    }
}

#[test]
fn fable_adequacy() {
    use super::adequacy::*;
    for ex in [
        "gcd",
        "gcd-vacuous",
        "gcd-bug-guard",
        "isqrt",
        "isqrt-harness-bug",
        "parity",
        "parity-bug-gate",
        "parity-missing-proof",
        "hashtable",
        "hashtable-bug-tombstone",
        "hashtable-stale",
        "primality",
    ] {
        let lines = example(ex);
        let t0 = std::time::Instant::now();
        let rows = vacuity(&lines);
        let vt = t0.elapsed();
        let flagged: Vec<String> = rows
            .iter()
            .filter(|r| r.vacuous || r.unconstraining || r.witnesses == 0)
            .map(|r| {
                format!(
                    "{}@{} vac={} unc={} wit={}/{}",
                    r.func, r.header_line, r.vacuous, r.unconstraining, r.witnesses, r.tried
                )
            })
            .collect();
        println!(
            "VAC {ex}: {} rows in {:?}; flagged: {:?}",
            rows.len(),
            vt,
            flagged
        );
    }
    for ex in [
        "gcd",
        "gcd-vacuous",
        "parity",
        "isqrt",
        "hashtable",
        "primality",
    ] {
        let lines = example(ex);
        let s = SessionStart::new(&lines);
        let owners = s.owners(&lines);
        let t0 = std::time::Instant::now();
        let ms = mutants(&lines, &owners);
        let bench = Bench::new(&lines, 16);
        let mut killed_bot = 0;
        let mut killed_check = 0;
        let mut killed_trap = 0;
        let mut killed_budget = 0;
        let mut surv = vec![];
        let mut surv_proven = vec![];
        let mut invalid = 0;
        let mut own_only = 0;
        let mut runs_away = 0;
        let mut check_lines: std::collections::BTreeMap<u32, usize> = Default::default();
        for mt in &ms {
            match fate(&lines, mt, &bench) {
                Fate::Killed(r) if r.contains("check at line") => {
                    killed_check += 1;
                    let l: u32 = r.rsplit(' ').nth(1).unwrap_or("0").parse().unwrap_or(0);
                    *check_lines.entry(l).or_default() += 1;
                }
                Fate::Killed(r) if r.contains("traps") => {
                    killed_trap += 1;
                    if r.contains("unreachable") {
                        killed_bot += 1;
                    }
                }
                Fate::Killed(_) => killed_budget += 1,
                Fate::OwnOnly(_) => {
                    own_only += 1;
                }
                Fate::RunsAway(_) => {
                    runs_away += 1;
                }
                Fate::Survived { proven: true } => {
                    surv_proven.push(format!("{}@{} {}→{}", mt.op, mt.line, mt.from, mt.to))
                }
                Fate::Survived { proven: false } => {
                    surv.push(format!("{}@{} {}→{}", mt.op, mt.line, mt.from, mt.to))
                }
                Fate::Invalid(_) => invalid += 1,
            }
        }
        println!(
            "MUT {ex}: {} mutants, bench {} runs, {:?}; killed by check {} (lines {:?}), trap {} (of which unreachable {}), other {}, invalid {}, OWN-ONLY {}, RUNS-AWAY {}",
            ms.len(),
            bench.runs.len(),
            t0.elapsed(),
            killed_check,
            check_lines,
            killed_trap,
            killed_bot,
            killed_budget,
            invalid,
            own_only,
            runs_away
        );
        println!(
            "    survivors proven ({}): {:?}",
            surv_proven.len(),
            surv_proven
        );
        println!(
            "    survivors ({}): {:?}",
            surv.len(),
            &surv[..surv.len().min(12)]
        );
        // which owners do the killing check lines have?
        for l in check_lines.keys() {
            println!(
                "      check line {l} owner {:?}: {}",
                owners[*l as usize - 1],
                lines[*l as usize - 1].trim()
            );
        }
    }
}

#[test]
fn fable_probes2() {
    let g = example("gcd");
    let s = SessionStart::new(&g);
    // A20 a lemma that is also a harness: the LLM adds a harness that always reaches ⊥
    let mut t = g.clone();
    t.push("(func $h2 (export \"lemma:h2\") (export \"harness:h2\") (param $a i32)".into());
    t.push("  unreachable".into());
    t.push(")".into());
    report("A20 lemma+harness", &s, &t);
    // A21 a lemma that is also a measure for $gcd_ref (dual export)
    let mut t = g.clone();
    t.push("(func $m2 (export \"lemma:m2\") (export \"measure:gcd_ref\") (param $a i32) (param $b i32) (result i32)".into());
    t.push("  i32.const 0".into());
    t.push(")".into());
    report("A21 lemma+measure", &s, &t);
    // A22 add ';; @own' to an LLM line
    let mut t = g.clone();
    t[132] = format!("{} ;; @own", g[132]);
    report("A22 fake @own", &s, &t);
    // A23 numeric call index to a student function
    let mut t = g.clone();
    t[136] = "  call 2".into();
    report("A23 numeric call", &s, &t);
    // A24 a new global declaration
    let mut t = g.clone();
    t.insert(1, "(global $g (mut i32) (i32.const 0))".into());
    report("A24 add global", &s, &t);
    // A25 a lemma with a fact param that is False, used to prove the result refinement (needs the False fact in the lane: can it be fed?)
    let mut t = g.clone();
    t[137] = "  lemma $exfalso $x $a $b".into();
    t[138] = "  nop".into();
    t.push("(func $exfalso (export \"lemma:exfalso\") (param $x i32) (param $a i32) (param $b i32) (param $h (fact (i32.const 0))) (result (fact (i32.eq $x (call $gcd_ref $a $b))))".into());
    t.push("  prove 1".into());
    t.push("  unreachable".into());
    t.push(")".into());
    report("A25 ex falso lemma", &s, &t);
}
