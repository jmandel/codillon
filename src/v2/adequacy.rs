//! Adequacy (design 16 §7.2): is the spec worth proving? Vacuity of preconditions (by the kernel,
//! and by looking for a witness among the harness inputs), unconstraining postconditions, and
//! mutation testing of the implementation. Deterministic; no LLM.

use super::ast::{Decl, Expr, IOp, Ins, LineKind, Module, ValTy, parse_line};
use super::eval::{EvalErr, Interp, eval_iop, value_locals};
use super::kernel::check_module;
use super::out::{CupKind, Feed, Verdict};
use super::runtime::RuntimePlan;
use super::vericode::Owner;

// ---------------- harness inputs (§6.3 rule 4) ----------------

const EDGES: [i64; 16] = [
    0,
    1,
    2,
    3,
    5,
    7,
    8,
    9,
    12,
    16,
    255,
    65535,
    65536,
    0x7fff_ffff,
    -0x8000_0000,
    -1,
];

fn xorshift(s: &mut u64) -> u64 {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    *s
}

/// Constants of the module (spec boundaries such as 65535), as extra edge values.
fn module_consts(m: &Module) -> Vec<i64> {
    let mut v: Vec<i64> = vec![];
    for f in &m.funcs {
        for (_, ins) in &f.body {
            if let Ins::Const(ty, bits) = ins
                && ty.is_int()
            {
                let x = if *ty == ValTy::I32 {
                    *bits as u32 as i32 as i64
                } else {
                    *bits as i64
                };
                for y in [x, x.wrapping_add(1), x.wrapping_sub(1)] {
                    if !v.contains(&y) && !EDGES.contains(&y) {
                        v.push(y);
                    }
                }
            }
        }
    }
    v.truncate(12);
    v
}

/// The fixed input list of a function with value parameters: edge values (pairwise for two
/// parameters), module constants, then a deterministic pseudo-random sample. At most `cap`.
pub fn input_list(m: &Module, f: usize, cap: usize) -> Vec<Vec<u64>> {
    let tys: Vec<ValTy> = m.funcs[f].value_params().map(|(_, _, r)| r.ty).collect();
    let mut vals: Vec<i64> = EDGES.to_vec();
    vals.extend(module_consts(m));
    let mut out: Vec<Vec<u64>> = vec![];
    let bits = |ty: ValTy, x: i64| super::ast::to_bits(ty, x as i128);
    match tys.len() {
        0 => out.push(vec![]),
        1 => out.extend(vals.iter().map(|x| vec![bits(tys[0], *x)])),
        _ => {
            let small = &vals[..vals.len().min(10)];
            for a in small {
                for b in small {
                    let mut v = vec![bits(tys[0], *a), bits(tys[1], *b)];
                    v.extend(tys[2..].iter().map(|t| bits(*t, *a)));
                    out.push(v);
                }
            }
        }
    }
    let mut s: u64 = 0x9e37_79b9_7f4a_7c15 ^ (f as u64);
    for _ in 0..cap {
        let v: Vec<u64> = tys
            .iter()
            .map(|t| {
                let r = xorshift(&mut s);
                // mostly small numbers, sometimes wide ones
                let x = if r & 3 == 0 { r } else { r % 1000 };
                x & super::term::mask(*t)
            })
            .collect();
        out.push(v);
    }
    out.dedup();
    out.truncate(cap);
    out
}

fn eval_expr(it: &mut Interp, e: &Expr, env: &[(String, u64)], v: u64) -> Result<u64, EvalErr> {
    Ok(match e {
        Expr::V => v,
        Expr::Int(i) => *i as i64 as u64,
        Expr::Var(n) => env
            .iter()
            .find(|(k, _)| k == n)
            .map(|x| x.1)
            .ok_or_else(|| EvalErr::Unsupported(format!("unknown {n}")))?,
        Expr::Op(name, args) => {
            let (op, w) =
                IOp::parse(name).ok_or_else(|| EvalErr::Unsupported(format!("op {name}")))?;
            let a: Vec<u64> = args
                .iter()
                .map(|x| eval_expr(it, x, env, v))
                .collect::<Result<_, _>>()?;
            eval_iop(op, w, &a)?
        }
        Expr::Call(fname, args) => {
            let f =
                it.m.func_index(fname)
                    .ok_or_else(|| EvalErr::Unsupported(format!("unknown {fname}")))?;
            let a: Vec<u64> = args
                .iter()
                .map(|x| eval_expr(it, x, env, v))
                .collect::<Result<_, _>>()?;
            it.steps = 0;
            it.call(f, &a)?.first().copied().unwrap_or(0)
        }
    })
}

/// Does `args` satisfy every parameter refinement of `f` (by evaluation)? Errors count as no.
pub fn pre_holds(m: &Module, f: usize, args: &[u64]) -> bool {
    let func = &m.funcs[f];
    let env: Vec<(String, u64)> = func
        .value_params()
        .zip(args)
        .filter_map(|((_, p, r), a)| p.name.clone().map(|n| (n, *a & super::term::mask(r.ty))))
        .collect();
    let mut it = Interp::new(m);
    for ((_, _, r), a) in func.value_params().zip(args) {
        if let Some(e) = &r.refine {
            match eval_expr(&mut it, e, &env, *a & super::term::mask(r.ty)) {
                Ok(x) if x & 0xffff_ffff != 0 => {}
                _ => return false,
            }
        }
    }
    true
}

/// The harness inputs that satisfy its precondition.
pub fn witnesses(m: &Module, f: usize, cap: usize) -> (Vec<Vec<u64>>, usize) {
    let all = input_list(m, f, 64);
    let tried = all.len();
    let w: Vec<Vec<u64>> = all
        .into_iter()
        .filter(|a| pre_holds(m, f, a))
        .take(cap)
        .collect();
    (w, tried)
}

// ---------------- vacuity ----------------

#[derive(Clone, Debug)]
pub struct VacuityRow {
    pub func: String,
    pub header_line: u32,
    pub harness: bool,
    /// the kernel proves False from the parameter refinements: every claim holds trivially
    pub vacuous: bool,
    /// inputs (of `tried`) that satisfy the precondition
    pub witnesses: usize,
    pub tried: usize,
    /// a result refinement the kernel proves at a fresh value: it says nothing about the result
    pub unconstraining: bool,
}

fn n_entry_facts(m: &Module, f: usize) -> usize {
    m.funcs[f]
        .header
        .params
        .iter()
        .filter(|p| match &p.decl {
            Decl::Val(r) => r.refine.is_some(),
            Decl::Fact(_) => true,
        })
        .count()
}

/// The module with `f`'s body replaced (same function, same name; later lines shift).
fn with_body<S: AsRef<str>>(lines: &[S], m: &Module, f: usize, body: &[String]) -> Vec<String> {
    let func = &m.funcs[f];
    let (h, e) = (func.header_line as usize, func.end_line as usize);
    let mut out: Vec<String> = lines[..h].iter().map(|s| s.as_ref().to_string()).collect();
    out.extend(body.iter().cloned());
    out.extend(lines[e - 1..].iter().map(|s| s.as_ref().to_string()));
    out
}

/// §7.2 vacuity, for each harness and each function with a refined parameter or result.
pub fn vacuity<S: AsRef<str>>(lines: &[S]) -> Vec<VacuityRow> {
    let m = Module::parse_lines(lines);
    let mut rows = vec![];
    for (f, func) in m.funcs.iter().enumerate() {
        if func.imported || func.end_line == 0 || func.is_lemma() || func.is_axiom() {
            continue;
        }
        let k = n_entry_facts(&m, f);
        let refined_result = func.value_results().iter().any(|r| r.refine.is_some());
        if !func.is_harness() && k == 0 && !refined_result {
            continue;
        }
        let mut row = VacuityRow {
            func: func.name(),
            header_line: func.header_line,
            harness: func.is_harness(),
            vacuous: false,
            witnesses: 0,
            tried: 0,
            unconstraining: false,
        };
        if k > 0 {
            // prove False from the parameter refinements alone
            let body = vec![format!("  prove {k}"), "  unreachable".to_string()];
            let lines2 = with_body(lines, &m, f, &body);
            let m2 = Module::parse_lines(&lines2);
            let out = check_module(&m2, true);
            row.vacuous = out.funcs.iter().any(|o| {
                o.func as usize == f
                    && o.cups.iter().any(|c| {
                        c.kind == CupKind::False
                            && c.verdict == Verdict::Proven
                            && matches!(c.feed, Feed::Prove { .. })
                    })
            });
            let (w, tried) = witnesses(&m, f, 1000);
            row.witnesses = w.len();
            row.tried = tried;
        } else {
            row.witnesses = 1;
            row.tried = 1;
        }
        let res = func.value_results();
        if refined_result && res.len() == 1 && !row.vacuous {
            // the result replaced by a fresh value: is the result refinement still proven?
            let ty = res[0].ty.name();
            let mut lines2 = with_body(
                lines,
                &m,
                f,
                &["  call $__havoc".to_string(), format!("  prove {k}")],
            );
            lines2.insert(
                0,
                format!("(import \"vc\" \"havoc\" (func $__havoc (result {ty})))"),
            );
            let m2 = Module::parse_lines(&lines2);
            let out = check_module(&m2, true);
            let f2 = f + 1; // imports come first
            row.unconstraining = out.funcs.iter().any(|o| {
                o.func as usize == f2
                    && o.cups.iter().any(|c| {
                        c.kind == CupKind::ResultRefinement && c.verdict == Verdict::Proven
                    })
            });
        }
        rows.push(row);
    }
    rows
}

// ---------------- mutation (§7.2, M1–M6) ----------------

#[derive(Clone, Debug, PartialEq)]
pub struct Mutant {
    pub op: &'static str,
    /// 1-based line
    pub line: u32,
    pub from: String,
    pub to: String,
    /// the whole mutated line (indentation and comment kept)
    pub text: String,
}

fn swap(op: IOp, pairs: &[(IOp, IOp)]) -> Option<IOp> {
    pairs.iter().find_map(|(a, b)| {
        if *a == op {
            Some(*b)
        } else if *b == op {
            Some(*a)
        } else {
            None
        }
    })
}

use IOp::*;
const M1: [(IOp, IOp); 5] = [(LtU, LeU), (LtS, LeS), (GtU, GeU), (GtS, GeS), (Eq, Ne)];
const M2: [(IOp, IOp); 8] = [
    (LtU, LtS),
    (LeU, LeS),
    (GtU, GtS),
    (GeU, GeS),
    (DivU, DivS),
    (RemU, RemS),
    (ShrU, ShrS),
    (ExtendI32U, ExtendI32S),
];
const M4: [(IOp, IOp); 3] = [(Add, Sub), (And, Or), (Shl, ShrU)];

/// The mutants of one line, by M1–M6 (`next` is the next instruction, for M6).
fn line_mutants(
    m: &Module,
    f: usize,
    ln: u32,
    text: &str,
    next: Option<&Ins>,
    out: &mut Vec<Mutant>,
) {
    let (code, comment) = super::sexpr::split_comment(text);
    let indent: String = code.chars().take_while(|c| c.is_whitespace()).collect();
    let from = code.trim().to_string();
    let mut push = |op: &'static str, to: String| {
        let sep = if comment.is_empty() { "" } else { " " };
        let text = format!("{indent}{to}{sep}{}", comment.trim_start());
        out.push(Mutant {
            op,
            line: ln,
            from: from.clone(),
            to,
            text,
        });
    };
    let LineKind::Instr(ins) = parse_line(text, ln) else {
        return;
    };
    match ins {
        Ins::Int(op, w) => {
            if let Some(o) = swap(op, &M1) {
                push("M1", o.name(w));
            }
            if let Some(o) = swap(op, &M2) {
                push("M2", o.name(w));
            }
            if let Some(o) = swap(op, &M4) {
                push("M4", o.name(w));
            }
            if op == Eqz && w == ValTy::I32 {
                push("M6", "nop".into());
            }
        }
        Ins::Const(ty, bits) if ty.is_int() => {
            let x = if ty == ValTy::I32 {
                bits as u32 as i32 as i64
            } else {
                bits as i64
            };
            push("M3", format!("{}.const {}", ty.name(), x.wrapping_add(1)));
            push("M3", format!("{}.const {}", ty.name(), x.wrapping_sub(1)));
        }
        Ins::LocalGet(n) => {
            let locs = value_locals(m, f);
            if let Some(me) = locs.iter().find(|(k, _)| k.as_deref() == Some(n.as_str())) {
                for (k, ty) in &locs {
                    if let Some(k) = k
                        && *k != n
                        && *ty == me.1
                    {
                        push("M5", format!("local.get {k}"));
                    }
                }
            }
        }
        Ins::Nop
            if matches!(
                next,
                Some(Ins::Block(super::ast::BlockKind::If, _) | Ins::BrIf(_))
            ) =>
        {
            push("M6", "i32.eqz".into());
        }
        _ => {}
    }
}

/// Every mutant of the LLM-owned bodies of ordinary (non-ghost) functions, in line order.
pub fn mutants<S: AsRef<str>>(lines: &[S], owners: &[Owner]) -> Vec<Mutant> {
    let m = Module::parse_lines(lines);
    let mut out = vec![];
    for (f, func) in m.funcs.iter().enumerate() {
        if func.imported || func.is_lemma() {
            continue;
        }
        // the next non-proof instruction after each body line (for M6)
        let body: Vec<&(u32, Ins)> = func.body.iter().filter(|(_, i)| !i.is_proof()).collect();
        for (j, (ln, _)) in body.iter().enumerate() {
            if owners.get(*ln as usize - 1) != Some(&Owner::Llm) {
                continue;
            }
            let next = body.get(j + 1).map(|x| &x.1);
            line_mutants(&m, f, *ln, lines[*ln as usize - 1].as_ref(), next, &mut out);
        }
    }
    out
}

#[derive(Clone, Debug, PartialEq)]
pub enum Fate {
    /// the SPEC rejects it: a harness reached ⊥, a spec-derived check failed (a contract
    /// refinement, a result refinement, a harness ⊥), or it trapped
    Killed(String),
    /// only the implementation's own invariants (block/loop facts, refined body locals, lemma
    /// premises) noticed: for adequacy this is a survivor, the spec cannot tell it apart
    OwnOnly(String),
    /// it ran out of steps on some input (likely a broken loop): neither killed nor survived
    RunsAway(String),
    /// no harness run told it apart; `proven`: the kernel still fully proves it (a definite gap)
    Survived { proven: bool },
    /// the mutant is not a valid program
    Invalid(String),
}

impl Fate {
    /// The spec does not tell this mutant apart (§7.2): survived, or only the body's own checks did.
    pub fn survives(&self) -> bool {
        matches!(self, Fate::Survived { .. } | Fate::OwnOnly(_))
    }
}

/// Is this cup derived from the spec (a contract or a trap), not from the implementation's own
/// proof structure? Spec: harness ⊥, result refinements, refinements of call arguments, of
/// parameters and of globals (all on student-owned headers and declarations), trap cups.
/// Own: block/loop facts, refined body locals, lemma premises, measures.
pub fn spec_cup(m: &Module, c: &super::out::CupOut, func: usize) -> bool {
    let f = &m.funcs[func];
    match c.kind {
        CupKind::False => f.is_harness(),
        CupKind::ResultRefinement => true,
        CupKind::Bounds
        | CupKind::DivByZero
        | CupKind::DivOverflow
        | CupKind::Conversion
        | CupKind::CallIndirect => true,
        CupKind::Refinement { .. } => {
            let ins = f.body.iter().find(|(l, _)| *l == c.line).map(|x| &x.1);
            let nparams = f.value_params().count();
            match ins {
                Some(Ins::Call(_) | Ins::GlobalSet(_)) => true,
                Some(Ins::LocalSet(n) | Ins::LocalTee(n)) => {
                    super::eval::resolve_local(&value_locals(m, func), n)
                        .is_some_and(|i| i < nparams)
                }
                _ => false,
            }
        }
        CupKind::BlockFact { .. }
        | CupKind::LoopEntry
        | CupKind::BackEdge
        | CupKind::LocalInit
        | CupKind::FactParam { .. }
        | CupKind::Measure => false,
    }
}

/// The harnesses and their inputs (precondition witnesses), with each run's step count on the
/// original program (the mutant gets ten times as many, at least 20 000).
pub struct Bench {
    pub runs: Vec<(String, Vec<u64>, u32)>,
}

impl Bench {
    pub fn new<S: AsRef<str>>(lines: &[S], per_harness: usize) -> Bench {
        let m = Module::parse_lines(lines);
        let out = check_module(&m, true);
        let plan = RuntimePlan::new(&m, &out);
        let mut runs = vec![];
        for (f, func) in m.funcs.iter().enumerate() {
            if !func.is_harness() || func.end_line == 0 {
                continue;
            }
            for args in witnesses(&m, f, per_harness).0 {
                let mut it = Interp::for_run(&m, Some(&plan));
                it.budget = 2_000_000;
                let r = it.call(f, &args);
                // inputs where the original already fails tell nothing about a mutant
                // (and long runs are left out to keep mutation testing fast)
                if r.is_ok() && it.steps <= 100_000 {
                    runs.push((func.name(), args, it.steps));
                }
            }
        }
        Bench { runs }
    }
}

fn show_args(a: &[u64]) -> String {
    let v: Vec<String> = a.iter().map(|x| (*x as u32 as i32).to_string()).collect();
    format!("({})", v.join(", "))
}

/// Decide one mutant: run every harness input on the instrumented mutant (gradual mode: its
/// unfed cups are checks); if none tells it apart, ask whether the kernel still proves it.
pub fn fate<S: AsRef<str>>(lines: &[S], mt: &Mutant, bench: &Bench) -> Fate {
    let mut l2: Vec<String> = lines.iter().map(|s| s.as_ref().to_string()).collect();
    l2[mt.line as usize - 1] = mt.text.clone();
    let m = Module::parse_lines(&l2);
    if let Some((l, e)) = m.errors.first() {
        return Fate::Invalid(format!("line {l}: {e}"));
    }
    let out = check_module(&m, true);
    // first with the spec's checks only (own invariants are not part of the spec, B4)
    let mut spec_out = out.clone();
    for f in spec_out.funcs.iter_mut() {
        let fi = f.func as usize;
        for c in f.cups.iter_mut() {
            if c.verdict == Verdict::RuntimeChecked && !spec_cup(&m, c, fi) {
                c.verdict = Verdict::Proven; // not compiled into this run
            }
        }
    }
    let run = |plan: &RuntimePlan| -> Option<Result<String, String>> {
        for (h, args, steps) in &bench.runs {
            let Some(f) = m.func_index(h) else { continue };
            let mut it = Interp::for_run(&m, Some(plan));
            it.budget = steps.saturating_mul(10).max(20_000);
            let at = format!("{h}{}", show_args(args));
            match it.call(f, args) {
                Ok(_) => {}
                Err(EvalErr::CheckFailed { line, .. }) => {
                    return Some(Ok(format!("{at}: check at line {line} fails")));
                }
                Err(EvalErr::Trap(t)) => return Some(Ok(format!("{at}: traps ({t})"))),
                Err(EvalErr::Budget) => return Some(Err(format!("{at}: runs away"))),
                Err(EvalErr::Unsupported(u)) => return Some(Err(u)),
            }
        }
        None
    };
    match run(&RuntimePlan::new(&m, &spec_out)) {
        Some(Ok(why)) => return Fate::Killed(why),
        Some(Err(why)) if why.ends_with("runs away") => return Fate::RunsAway(why),
        Some(Err(why)) => return Fate::Invalid(why),
        None => {}
    }
    // the spec passes every input: did only the body's own invariants notice?
    if let Some(Ok(why)) = run(&RuntimePlan::new(&m, &out)) {
        return Fate::OwnOnly(why);
    }
    let func = out.func_at(mt.line);
    let proven = func.is_some_and(|f| f.verified)
        && out
            .funcs
            .iter()
            .filter(|f| m.funcs[f.func as usize].is_harness())
            .all(|f| f.verified);
    Fate::Survived { proven }
}
