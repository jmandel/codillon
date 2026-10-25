//! Tests of vericoding mode: ownership, the judge, adequacy, sessions and the LLM protocol.

use super::adequacy::*;
use super::vericode::*;
use std::time::Instant;

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

fn st(lines: &[String]) -> SessionStart {
    SessionStart::new(lines)
}

#[test]
fn ownership_follows_the_table() {
    let lines = example("isqrt");
    let o = st(&lines).owners(&lines);
    let at = |l: usize| o[l - 1];
    assert_eq!(at(1), Owner::Free, "comment");
    assert_eq!(at(2), Owner::Student, "$main header");
    assert_eq!(at(3), Owner::Student, "$main body is the runner");
    assert_eq!(at(7), Owner::Student, "predicate body");
    assert_eq!(at(31), Owner::Student, "$isqrt header");
    assert_eq!(at(32), Owner::Llm, "refined local of the body");
    assert_eq!(at(34), Owner::Llm, "loop line of the body");
    assert_eq!(at(59), Owner::Llm, "body");
    assert_eq!(at(60), Owner::Student, "closing paren of a student header");
    assert_eq!(at(62), Owner::Student, "harness body");
    // gcd: helpers of predicates are spec; the axiom is the instructor's
    let g = example("gcd");
    let o = st(&g).owners(&g);
    assert_eq!(o[8 - 1], Owner::Student, "$divides (called by a predicate)");
    assert_eq!(o[106 - 1], Owner::Student, "axiom header");
    assert_eq!(o[117 - 1], Owner::Llm, "$gcd body");
    // primality: $prime is the exported implementation although a lemma names it
    let p = example("primality");
    let o = st(&p).owners(&p);
    assert_eq!(o[97 - 1], Owner::Llm, "$prime body");
}

#[test]
fn the_judge_enforces_the_boundary() {
    let lines = example("parity");
    let s = st(&lines);
    // the unchanged, fully proven module: accepted
    assert!(s.judge(&lines).accepted);
    // weakening a header
    let mut w = lines.clone();
    w[34] = "(func $half (param $x i32) (result (i32 | $is_half $x))".into();
    let j = s.judge(&w);
    assert!(!j.accepted && j.crossed(), "{:?}", j.boundary);
    assert_eq!(j.boundary[0].line, 35);
    assert!(j.boundary[0].msg.starts_with("edited locked line 35"));
    // an assume in the body
    let w = apply_edits(
        &lines,
        &[Edit {
            a: 38,
            b: 38,
            with: vec![
                "  i32.shr_s".into(),
                "  assume (fact (call $is_half (i32.shr_s $x 1) $x))".into(),
            ],
        }],
    )
    .unwrap();
    let j = s.judge(&w);
    assert!(
        j.boundary
            .iter()
            .any(|r| r.line == 39 && r.msg.contains("assume")),
        "{:?}",
        j.boundary
    );
    // an axiom, an import, an unknown call, a new ordinary function
    let mut w = lines.clone();
    w.push(
        "(func $cheat (export \"axiom:cheat\") (param $x i32) (result (fact (call $is_even $x))))"
            .into(),
    );
    w.push(")".into());
    assert!(
        s.judge(&w)
            .boundary
            .iter()
            .any(|r| r.msg.contains("adds an axiom"))
    );
    let mut w = lines.clone();
    w.insert(
        1,
        "(import \"env\" \"oracle\" (func $oracle (param i32) (result i32)))".into(),
    );
    assert!(
        s.judge(&w)
            .boundary
            .iter()
            .any(|r| r.msg.contains("import"))
    );
    let w = apply_edits(
        &lines,
        &[Edit {
            a: 38,
            b: 38,
            with: vec!["  call $nowhere".into()],
        }],
    )
    .unwrap();
    assert!(
        s.judge(&w)
            .boundary
            .iter()
            .any(|r| r.msg.contains("$nowhere"))
    );
    // not strict-clean: stays applied (not crossed), not accepted. (Deleting a `prove` line no
    // longer does this, R5a; a wrong shift amount does: x>>2 is not half of x.)
    let w = apply_edits(
        &lines,
        &[Edit {
            a: 37,
            b: 37,
            with: vec!["  i32.const 2".into()],
        }],
    )
    .unwrap();
    let j = s.judge(&w);
    assert!(!j.accepted && !j.crossed());
    assert!(
        j.strict
            .iter()
            .any(|r| r.line == 39 && r.msg.contains("nothing feeds it")),
        "{:?}",
        j.strict
    );
    assert_eq!(j.touched, vec!["$half".to_string()]);
}

#[test]
fn edits_apply_bottom_first_and_refuse_overlaps() {
    let l: Vec<String> = ["a", "b", "c", "d"].iter().map(|s| s.to_string()).collect();
    let e = |a, b, w: &[&str]| Edit {
        a,
        b,
        with: w.iter().map(|s| s.to_string()).collect(),
    };
    assert_eq!(
        apply_edits(&l, &[e(2, 2, &["B"]), e(4, 3, &["x"])]).unwrap(),
        ["a", "B", "c", "x", "d"]
    );
    assert_eq!(
        apply_edits(&l, &[e(5, 4, &["e"])]).unwrap(),
        ["a", "b", "c", "d", "e"]
    );
    assert_eq!(
        apply_edits(&l, &[e(1, 4, &[])]).unwrap(),
        Vec::<String>::new()
    );
    assert!(apply_edits(&l, &[e(1, 2, &[]), e(2, 3, &[])]).is_err());
    assert!(apply_edits(&l, &[e(0, 1, &[])]).is_err());
}

#[test]
fn vacuity_flags_gcd_vacuous_only() {
    let rows = vacuity(&example("gcd-vacuous"));
    let h = rows.iter().find(|r| r.func == "$gcd_harness").unwrap();
    assert!(h.vacuous && h.witnesses == 0 && h.tried > 0, "{h:?}");
    for ex in ["gcd", "isqrt", "parity", "hashtable", "primality"] {
        for r in vacuity(&example(ex)) {
            assert!(!r.vacuous && r.witnesses > 0, "{ex}: {r:?}");
            assert!(!r.unconstraining, "{ex}: {r:?}");
        }
    }
    // an always-true postcondition says nothing about the result
    let src =
        "(func $f (export \"f\") (param $x i32) (result (i32 | (i32.ge_u v 0)))\n  local.get $x\n)";
    let lines: Vec<String> = src.lines().map(|s| s.to_string()).collect();
    assert!(vacuity(&lines)[0].unconstraining);
}

#[test]
fn mutation_operators_rewrite_one_site() {
    let src = "(func $f (export \"f\") (param $a i32) (param $b i32) (result i32)\n  local.get $a ;; first\n  i32.const 7\n  i32.lt_u\n  nop\n  if (result i32)\n    local.get $a\n    i32.eqz\n  else\n    local.get $b\n    i64.extend_i32_u\n    i32.wrap_i64\n  end\n)";
    let lines: Vec<String> = src.lines().map(|s| s.to_string()).collect();
    let o = st(&lines).owners(&lines);
    let ms = mutants(&lines, &o);
    let got: Vec<String> = ms
        .iter()
        .map(|m| format!("{} {} {}", m.op, m.line, m.text))
        .collect();
    for want in [
        "M5 2   local.get $b ;; first",
        "M3 3   i32.const 8",
        "M3 3   i32.const 6",
        "M1 4   i32.le_u",
        "M2 4   i32.lt_s",
        "M6 5   i32.eqz",
        "M6 8     nop",
        "M2 11     i64.extend_i32_s",
    ] {
        assert!(got.contains(&want.to_string()), "missing {want}: {got:#?}");
    }
    assert!(ms.iter().all(|m| m.line != 1), "headers are never mutated");
}

fn run_mutation(ex: &str) -> Vec<(Mutant, Fate)> {
    let lines = example(ex);
    let o = st(&lines).owners(&lines);
    let bench = Bench::new(&lines, 48);
    mutants(&lines, &o)
        .into_iter()
        .map(|m| {
            let f = fate(&lines, &m, &bench);
            (m, f)
        })
        .collect()
}

#[test]
fn mutation_testing_is_deterministic_and_finds_survivors() {
    let t = Instant::now();
    let a = run_mutation("isqrt");
    let b = run_mutation("isqrt");
    assert_eq!(a, b);
    // the isqrt survivors include equivalent mutants the kernel still proves (65535 → 65536, …)
    assert!(a.iter().any(|(m, f)| m.line == 36
        && m.to == "i32.const 65536"
        && *f == Fate::Survived { proven: true }));
    // a vacuous harness kills nothing
    let v = run_mutation("gcd-vacuous");
    assert!(!v.is_empty() && v.iter().all(|(_, f)| f.survives()));
    eprintln!(
        "mutation timing (debug or release build): {:?}",
        t.elapsed()
    );
}

/// Review 19 B4 (probe `fable_adequacy`): a kill must come from the spec — a harness ⊥, a
/// contract or result refinement, a trap — never from the implementation's own block/loop
/// invariants. Prints every example's adequacy numbers.
#[test]
fn b4_kills_come_from_the_spec_not_own_invariants() {
    for ex in [
        "gcd",
        "gcd-vacuous",
        "parity",
        "isqrt",
        "hashtable",
        "primality",
    ] {
        let lines = example(ex);
        let m = super::ast::Module::parse_lines(&lines);
        let out = super::kernel::check_module(&m, true);
        eprintln!("ADEQ start {ex}");
        let res = run_mutation(ex);
        let (mut spec, mut own, mut away, mut surv, mut proven, mut invalid) = (0, 0, 0, 0, 0, 0);
        for (mt, f) in &res {
            match f {
                Fate::Killed(why) => {
                    spec += 1;
                    // a killing check is never one of the body's own invariant cups
                    if let Some(l) = why
                        .split("check at line ")
                        .nth(1)
                        .and_then(|r| r.split(' ').next())
                        .and_then(|x| x.parse::<u32>().ok())
                    {
                        let fo = out.func_at(l).unwrap();
                        let cups: Vec<_> = fo
                            .cups
                            .iter()
                            .filter(|c| {
                                c.line == l && c.verdict == super::out::Verdict::RuntimeChecked
                            })
                            .collect();
                        assert!(
                            cups.iter().any(|c| spec_cup(&m, c, fo.func as usize))
                                || cups.is_empty(),
                            "{ex} {mt:?}: killed by an own invariant at {l}"
                        );
                    }
                }
                Fate::OwnOnly(_) => own += 1,
                Fate::RunsAway(_) => away += 1,
                Fate::Survived { proven: p } => {
                    surv += 1;
                    proven += *p as u32;
                }
                Fate::Invalid(_) => invalid += 1,
            }
        }
        eprintln!(
            "ADEQ {ex}: {} mutants: killed by spec {spec}, only own invariants {own}, runs away {away}, survived {surv} ({proven} still proven), invalid {invalid}",
            res.len()
        );
        if ex == "gcd-vacuous" {
            assert_eq!(spec, 0);
        }
    }
}

#[test]
fn n4_assume_in_a_predicate_is_an_error() {
    let src = "(func $p (param $x i32) (result i32)\n  assume (fact (i32.ne $x 0))\n  i32.const 1\n)\n(func $f (export \"f\") (param $x (i32 | $p)) (result i32)\n  local.get $x\n)";
    let out = super::kernel::check_module(&super::ast::Module::parse(src), true);
    let p = out.funcs.iter().find(|f| f.name == "$p").unwrap();
    assert!(
        p.line_errors
            .iter()
            .any(|(l, e)| *l == 2 && e.contains("not allowed inside a predicate")),
        "{:?}",
        p.line_errors
    );
    assert!(!p.verified);
}

#[test]
fn n5_strict_mode_reports_unfed_cups_as_errors() {
    let src = "(func $f (export \"f\") (param $x i32) (result i32)\n  i32.const 10\n  local.get $x\n  i32.div_u\n)";
    let m = super::ast::Module::parse(src);
    let g = super::kernel::check_module(&m, true);
    let s = super::kernel::check_module(&m, false);
    assert!(g.funcs[0].line_errors.is_empty());
    assert!(
        s.funcs[0]
            .line_errors
            .iter()
            .any(|(l, e)| *l == 4 && e.starts_with("strict: needs")),
        "{:?}",
        s.funcs[0].line_errors
    );
    // the verdict itself is the same (the cup is unfed either way)
    assert_eq!(g.funcs[0].cups[0].verdict, s.funcs[0].cups[0].verdict);
}

fn session_text(name: &str) -> String {
    let p = format!(
        "{}/public/examples/v2/sessions/{name}.json",
        env!("CARGO_MANIFEST_DIR")
    );
    std::fs::read_to_string(p).unwrap()
}

/// Replay a recorded session through the real kernel; returns the verdict kind of every round.
fn replay(name: &str, verbose: bool) -> Vec<&'static str> {
    use super::llm::*;
    let s = parse_script(&session_text(name)).unwrap();
    let start = SessionStart::new(&s.start);
    let mut cur = s.start.clone();
    let mut kinds = vec![];
    for (i, t) in s.turns.iter().enumerate() {
        let o = play_round(&start, &cur, &t.edits);
        let k = verdict_kind(&o);
        if verbose {
            let j = o.judgement.as_ref();
            eprintln!(
                "{name} turn {}: {k} (expect {:?}) {:?} {}",
                i + 1,
                t.expect,
                o.error,
                j.map(|j| j.summary()).unwrap_or_default()
            );
            if let Some(j) = j {
                for r in j
                    .boundary
                    .iter()
                    .chain(&j.malformed)
                    .chain(&j.strict)
                    .take(6)
                {
                    eprintln!("    line {}: {}", r.line, r.msg);
                }
            }
        }
        cur = o.lines;
        kinds.push(k);
    }
    kinds
}

#[test]
fn sessions_replay_as_recorded() {
    for name in ["isqrt", "parity", "gcd"] {
        let s = super::llm::parse_script(&session_text(name)).unwrap();
        let kinds = replay(name, true);
        let want: Vec<String> = s.turns.iter().map(|t| t.expect.clone().unwrap()).collect();
        assert_eq!(kinds, want, "{name}");
        assert_eq!(kinds.last(), Some(&"accepted"), "{name} ends accepted");
        assert!(
            kinds.contains(&"rejected"),
            "{name} has a boundary-crossing turn"
        );
    }
}

fn chat_reply(content: &str) -> String {
    serde_json::json!({"choices": [{"message": {"role": "assistant", "content": content}}]})
        .to_string()
}

/// The live loop against a mocked transport: the "model" replays the recorded isqrt session's
/// responses, wrapped as OpenRouter replies (one fenced, one with prose around the JSON).
#[test]
fn live_loop_with_a_mock_transport() {
    use super::llm::*;
    let text = session_text("isqrt");
    let v: serde_json::Value = serde_json::from_str(&text).unwrap();
    let s = parse_script(&text).unwrap();
    let mut live = Live::new(&s.start, &s.task, MAX_ROUNDS);
    let mut sent = vec![];
    let mut kinds = vec![];
    for (i, t) in v["turns"].as_array().unwrap().iter().enumerate() {
        let body = live
            .next_body(&ModelChoice {
                model: "test/model".into(),
                fast: false,
            })
            .expect("a round");
        assert_eq!(body["model"], "test/model");
        let req: serde_json::Value =
            serde_json::from_str(body["messages"][1]["content"].as_str().unwrap()).unwrap();
        assert_eq!(req["round"], i as u64 + 1);
        assert!(req["locked"].as_array().unwrap().len() >= 2);
        assert!(
            req["module"]
                .as_str()
                .unwrap()
                .contains("  31| (func $isqrt")
        );
        sent.push(req);
        let resp = t["response"].to_string();
        let content = if i % 2 == 0 {
            format!("```json\n{resp}\n```")
        } else {
            format!("Here you go: {resp} Done.")
        };
        kinds.push(verdict_kind(&live.on_reply(&chat_reply(&content))));
    }
    assert_eq!(
        kinds,
        [
            "not-accepted",
            "rejected",
            "not-accepted",
            "rejected",
            "accepted"
        ]
    );
    assert!(live.done && live.next_body(&ModelChoice::default()).is_none());
    // after the first round the request carries the failing cups with lane snapshots
    let cups = sent[1]["cups"].as_array().unwrap();
    assert!(
        cups.iter().any(|c| c["verdict"] == "runtime-checked"),
        "{cups:?}"
    );
    // after a rejected round, the reasons go back to the model
    assert!(
        sent[2]["last_round"]["verdict"]
            .as_str()
            .unwrap()
            .starts_with("rejected: edited locked line")
    );
    // with lanes: the fourth request's failing cups (no loop invariant yet) say what the
    // relevant facts allow (R5a's countermodel), so the model sees which fact is missing
    assert!(
        sent[3]["cups"].as_array().unwrap().iter().any(|c| c["diag"]
            .as_str()
            .is_some_and(|d| d.contains("about these values allow"))),
        "{:?}",
        sent[3]["cups"]
    );
    let lanes = sent[3]["cups"]
        .as_array()
        .unwrap()
        .iter()
        .any(|c| !c["lane"].as_array().unwrap().is_empty());
    assert!(lanes);
    // the transcript can be saved as a scripted session and replays the same way
    let saved = script_json(&Script {
        title: "t".into(),
        example: "v2/isqrt".into(),
        task: s.task.clone(),
        start: s.start.clone(),
        turns: live.turns.clone(),
    });
    let again = parse_script(&saved.to_string()).unwrap();
    assert_eq!(again.turns.len(), 5);
}

#[test]
fn live_loop_handles_bad_replies() {
    use super::llm::*;
    let s = parse_script(&session_text("parity")).unwrap();
    // an API error
    let mut live = Live::new(&s.start, &s.task, 3);
    live.next_body(&ModelChoice::default()).unwrap();
    let o = live.on_reply(r#"{"error": {"message": "No auth credentials found", "code": 401}}"#);
    assert_eq!(
        o.error.as_deref(),
        Some("OpenRouter: No auth credentials found")
    );
    assert!(!o.applied && live.done && live.lines == s.start);
    // prose without JSON, and edits outside the module
    let mut live = Live::new(&s.start, &s.task, 3);
    live.next_body(&ModelChoice::default()).unwrap();
    assert!(
        live.on_reply(&chat_reply("I cannot do that."))
            .error
            .unwrap()
            .contains("no JSON")
    );
    let mut live = Live::new(&s.start, &s.task, 3);
    live.next_body(&ModelChoice::default()).unwrap();
    let o = live.on_reply(&chat_reply(
        r#"{"edits": [{"replace_lines": [900, 901], "with": []}]}"#,
    ));
    assert!(o.error.unwrap().contains("outside"));
    // max rounds
    let mut live = Live::new(&s.start, &s.task, 2);
    for _ in 0..2 {
        live.next_body(&ModelChoice::default()).unwrap();
        live.on_reply(&chat_reply(r#"{"edits": [], "note": "nothing"}"#));
    }
    assert!(live.next_body(&ModelChoice::default()).is_none());
}

// ---------------- review 19 blocking findings (probes A13, A16, A19) ----------------

/// B1 (A19): a lemma with an unsatisfiable refinement on a value parameter derived ⊥ and handed
/// its result to $gcd for free. The lemma line now owes a Refinement cup for each refined value
/// parameter (R13/R33), so the call site's cup is unfed and the submission is not accepted.
#[test]
fn b1_lemma_value_param_refinements_are_cups() {
    let g = example("gcd");
    let s = st(&g);
    let mut t = g.clone();
    assert!(t[133].contains("unfold $gcd_ref $x $y"));
    t[133] = "  lemma $vac2 $x $a $b".into();
    t.push("(func $vac2 (export \"lemma:vac2\") (param $x (i32 | (i32.lt_u v 0))) (param $a i32) (param $b i32) (result (fact (i32.eq $x (call $gcd_ref $a $b))))".into());
    t.push("  prove 1".into());
    t.push("  unreachable".into());
    t.push(")".into());
    let j = s.judge(&t);
    assert!(!j.accepted, "A19 accepted: {:?}", j.summary());
    let gcd = j.out.funcs.iter().find(|f| f.name == "$gcd").unwrap();
    assert!(!gcd.verified);
    let cup = gcd
        .cups
        .iter()
        .find(|c| c.line == 134 && matches!(c.kind, super::out::CupKind::Refinement { .. }))
        .expect("a Refinement cup on the lemma line");
    assert_eq!(cup.verdict, super::out::Verdict::RuntimeChecked, "{cup:?}");
    // A16: the same through the harness is a locked-line edit anyway
    let mut t = g.clone();
    t[145] = "  lemma $vac $g".into();
    t.push("(func $vac (export \"lemma:vac\") (param $g (i32 | (i32.lt_u v 0))) (result (fact (i32.const 0)))".into());
    t.push("  unreachable".into());
    t.push(")".into());
    assert!(!s.judge(&t).accepted);
}

/// B2 (A13): a lemma named like the student's predicate, placed before it, shadowed it.
/// Duplicate names are now a parse error, and the judge names the shadow.
#[test]
fn b2_duplicate_function_names_are_rejected() {
    let g = example("gcd");
    let s = st(&g);
    let mut t = g.clone();
    let orig = t
        .iter()
        .position(|l| l.starts_with("(func $is_gcd"))
        .unwrap();
    let hdr = t[orig].replace("(func $is_gcd", "(func $is_gcd (export \"lemma:shadow\")");
    t.insert(orig, ")".into());
    t.insert(orig, "  i32.const 1".into());
    t.insert(orig, hdr);
    let m = super::ast::Module::parse_lines(&t);
    assert!(
        m.errors
            .iter()
            .any(|(_, e)| e.contains("duplicate function name $is_gcd")),
        "{:?}",
        m.errors
    );
    let j = s.judge(&t);
    assert!(!j.accepted && j.crossed());
    assert!(
        j.boundary
            .iter()
            .any(|r| r.msg.contains("redefines $is_gcd")),
        "{:?}",
        j.boundary
    );
}

#[test]
fn default_model_is_the_chosen_one() {
    assert_eq!(super::llm::DEFAULT_MODEL, "anthropic/claude-opus-5.5");
    use super::llm::*;
    let b = chat_body(&ModelChoice::default(), &serde_json::json!({}));
    assert_eq!(b["model"], "anthropic/claude-opus-5.5");
    assert!(b.get("provider").is_none());
    // the fast preset routes for throughput and stays within its 65.5K output limit
    let (_, _, id, fast) = PRESETS[1];
    assert_eq!(id, "deepseek/deepseek-v4.1-flash-1017");
    let b = chat_body(
        &ModelChoice {
            model: id.into(),
            fast,
        },
        &serde_json::json!({}),
    );
    assert_eq!(b["provider"]["sort"], "throughput");
    assert!(b["max_tokens"].as_u64().unwrap() <= 65_500);
}

/// Review 19 A14: a student line moved among LLM lines (here an instructor `assume` moved into
/// another block) is a boundary violation: ownership holds by identity and position.
#[test]
fn a14_moving_a_student_line_is_a_violation() {
    let g = example("gcd");
    let mut base = g.clone();
    assert!(base[119].trim() == "br_if $done");
    base.insert(120, "      assume (fact (i32.ne $y 0))".into());
    let s = st(&base);
    assert!(s.judge(&base).boundary.is_empty());
    // moved within the same block: still in place
    let mut t = base.clone();
    let a = t.remove(120);
    t.insert(121, a);
    assert!(s.zone_violation(&t).is_none(), "{:?}", s.zone_violation(&t));
    // moved out of the loop, before it
    let mut t = base.clone();
    let a = t.remove(120);
    t.insert(116, a);
    let v = s.zone_violation(&t).expect("a violation");
    assert!(v.msg.contains("out of its place"), "{v:?}");
    assert!(s.judge(&t).crossed());
}

/// Review 19 A20/A21: one role per function (no lemma that is also a harness or a measure).
#[test]
fn a20_dual_role_functions_are_rejected() {
    let g = example("gcd");
    let s = st(&g);
    let mut t = g.clone();
    t.push("(func $h2 (export \"lemma:h2\") (export \"harness:h2\") (param $a i32)".into());
    t.push("  unreachable".into());
    t.push(")".into());
    let m = super::ast::Module::parse_lines(&t);
    assert!(
        m.errors.iter().any(|(_, e)| e.contains("2 roles")),
        "{:?}",
        m.errors
    );
    let j = s.judge(&t);
    assert!(j.crossed() && !j.accepted);
}

/// Review 25 S3: a reachable instructor `assume` makes a function not VERIFIED even when R5a
/// proves every cup without it; the judge must say so (no harness needed to surface it).
#[test]
fn the_judge_rejects_a_reachable_assume() {
    let start: Vec<String> =
        "(func $f (export \"f\") (param $x i32) (result (i32 | (i32.lt_u v (i32.const 8))))
  assume (fact (i32.lt_u $x 8))
  i32.const 1
)"
        .lines()
        .map(String::from)
        .collect();
    let mut sub = start.clone();
    sub[2] = "  i32.const 0".into();
    let j = SessionStart::new(&start).judge(&sub);
    let f = &j.out.funcs[0];
    assert!(!f.strict_clean && !f.verified);
    assert!(!j.accepted, "{}", j.summary());
    assert!(
        j.strict
            .iter()
            .any(|r| r.line == 2 && r.msg.contains("reachable assume")),
        "{:?}",
        j.strict
            .iter()
            .map(|r| (r.line, &r.msg))
            .collect::<Vec<_>>()
    );
}
