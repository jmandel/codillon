//! Vericoding mode (design 16 §7.1): the ownership boundary between the student's specification
//! and the implementation and proofs written by an LLM (or a scripted session, or the student),
//! and the kernel as the only judge of a submission. Pure Rust; the editor draws from it.

use super::ast::{Ins, LineKind, Module, parse_line};
use super::info::analyze;
use super::kernel::check_module_probing;
use super::out::{CupKind, ModuleOut, Verdict};
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Owner {
    /// the specification: locked while the LLM works
    Student,
    /// implementation and proofs: the LLM side
    Llm,
    /// blank and comment-only lines
    Free,
}

/// Whether a function has a plain export (not a `role:` export): an implementation entry point.
fn plain_export(f: &super::ast::Func) -> bool {
    f.header.exports.iter().any(|e| !e.contains(':'))
}

/// Which functions' bodies belong to the student: predicates and measures (unless they are an
/// exported implementation, like primality's `$prime`) and every function they call, harnesses,
/// axioms and `$main`.
pub fn student_bodies(m: &Module) -> BTreeSet<String> {
    let info = analyze(m);
    let spec = |i: usize| {
        let f = &m.funcs[i];
        !f.is_lemma() && (info[i].is_pred || info[i].is_measure) && !plain_export(f)
    };
    let mut set: BTreeSet<usize> = (0..m.funcs.len()).filter(|i| spec(*i)).collect();
    let mut work: Vec<usize> = set.iter().copied().collect();
    while let Some(i) = work.pop() {
        for (_, ins) in &m.funcs[i].body {
            if let Ins::Call(n) = ins
                && let Some(g) = m.func_index(n)
                && !m.funcs[g].is_lemma()
                && !plain_export(&m.funcs[g])
                && set.insert(g)
            {
                work.push(g);
            }
        }
    }
    for (i, f) in m.funcs.iter().enumerate() {
        if f.is_harness() || f.is_axiom() || f.header.name.as_deref() == Some("$main") {
            set.insert(i);
        }
    }
    set.into_iter().map(|i| m.funcs[i].name()).collect()
}

/// Why a line is owned as it is (shown in the lock commentary).
pub fn owner_reason(m: &Module, bodies: &BTreeSet<String>, line: u32) -> &'static str {
    let Some(f) = m
        .funcs
        .iter()
        .find(|f| f.header_line == line || (f.header_line < line && line <= f.end_line))
    else {
        return "a declaration of the spec";
    };
    if f.header_line == line || f.end_line == line {
        return "a function header: the spec";
    }
    if f.is_harness() {
        "a harness body: the spec"
    } else if f.is_axiom() {
        "an instructor axiom"
    } else if f.header.name.as_deref() == Some("$main") {
        "the runner $main"
    } else if bodies.contains(&f.name()) {
        "a predicate or measure body: the spec"
    } else {
        "an instructor assume or a marked spec line"
    }
}

/// Classify every line (1-based line `i + 1` is `owners[i]`). `bodies`: the student-owned
/// function bodies (frozen at session start).
pub fn classify<S: AsRef<str>>(lines: &[S], bodies: &BTreeSet<String>) -> Vec<Owner> {
    let m = Module::parse_lines(lines);
    let mut owners = vec![Owner::Free; lines.len()];
    for (i, t) in lines.iter().enumerate() {
        let k = parse_line(t.as_ref(), i as u32 + 1);
        owners[i] = match k {
            LineKind::Memory(_) | LineKind::Global { .. } | LineKind::Import { .. } => {
                Owner::Student
            }
            _ => Owner::Free,
        };
    }
    for f in &m.funcs {
        let hdr = if f.is_lemma() {
            Owner::Llm
        } else {
            Owner::Student
        };
        let idx = f.header_line as usize - 1;
        if idx < owners.len() {
            owners[idx] = hdr;
        }
        if f.end_line == 0 {
            continue;
        }
        owners[f.end_line as usize - 1] = hdr;
        let body = if !f.is_lemma() && bodies.contains(&f.name()) {
            Owner::Student
        } else {
            Owner::Llm
        };
        for l in f.header_line + 1..f.end_line {
            let t = lines[l as usize - 1].as_ref();
            let kind = parse_line(t, l);
            owners[l as usize - 1] = match kind {
                LineKind::Blank | LineKind::Other => Owner::Free,
                LineKind::Instr(Ins::Assume(_)) => Owner::Student,
                _ if t.contains(";; @own") => Owner::Student,
                _ => body,
            };
        }
    }
    owners
}

/// Where each line sits: its function and the labels of the blocks around it ("" at top level).
/// A student line is anchored by identity *and* position: moving it to another block, or to
/// another function, changes its context (review 19, probe A14).
pub fn contexts<S: AsRef<str>>(lines: &[S]) -> Vec<String> {
    let mut out = Vec::with_capacity(lines.len());
    let mut func: Option<String> = None;
    let mut stack: Vec<String> = vec![];
    for (i, t) in lines.iter().enumerate() {
        let k = parse_line(t.as_ref(), i as u32 + 1);
        let here = |func: &Option<String>, stack: &[String]| match func {
            Some(f) => format!("{f}/{}", stack.join("/")),
            None => String::new(),
        };
        match k {
            LineKind::FuncHeader(h) => {
                out.push(String::new());
                stack.clear();
                func = if h.import.is_some() {
                    None
                } else {
                    Some(h.name.unwrap_or_else(|| "<anon>".into()))
                };
            }
            LineKind::FuncEnd => {
                out.push(String::new());
                func = None;
                stack.clear();
            }
            LineKind::Instr(Ins::Block(kind, bt)) => {
                out.push(here(&func, &stack));
                let kw = match kind {
                    super::ast::BlockKind::Block => "block",
                    super::ast::BlockKind::Loop => "loop",
                    super::ast::BlockKind::If => "if",
                };
                stack.push(format!(
                    "{kw}{}",
                    bt.label.map(|l| format!(" {l}")).unwrap_or_default()
                ));
            }
            LineKind::Instr(Ins::End) => {
                stack.pop();
                out.push(here(&func, &stack));
            }
            _ => out.push(here(&func, &stack)),
        }
    }
    out
}

/// The student zone: every student-owned line (1-based line, trimmed text, context), in order.
pub fn zone<S: AsRef<str>>(lines: &[S], owners: &[Owner]) -> Vec<(u32, String, String)> {
    let ctx = contexts(lines);
    owners
        .iter()
        .enumerate()
        .filter(|(_, o)| **o == Owner::Student)
        .map(|(i, _)| {
            (
                i as u32 + 1,
                lines[i].as_ref().trim().to_string(),
                ctx[i].clone(),
            )
        })
        .collect()
}

/// Locked ranges (1-based, inclusive) for the LLM request (§7.3).
pub fn locked_ranges(owners: &[Owner]) -> Vec<(u32, u32)> {
    let mut out: Vec<(u32, u32)> = vec![];
    for (i, o) in owners.iter().enumerate() {
        if *o != Owner::Student {
            continue;
        }
        let l = i as u32 + 1;
        match out.last_mut() {
            Some((_, b)) if *b + 1 == l => *b = l,
            _ => out.push((l, l)),
        }
    }
    out
}

#[derive(Clone, Debug, PartialEq)]
pub struct Reason {
    /// 1-based line of the submission (0: the whole module)
    pub line: u32,
    pub msg: String,
}

/// The state captured when a vericoding session starts (§7.1 (1): the student zone is hashed).
#[derive(Clone, Debug)]
pub struct SessionStart {
    pub lines: Vec<String>,
    pub bodies: BTreeSet<String>,
    pub zone: Vec<(u32, String, String)>,
    pub funcs: BTreeSet<String>,
    assumes: Vec<String>,
    imports: usize,
    /// indices into `zone` of the student lines that are dead code at session start
    dead0: BTreeSet<usize>,
    /// ... and of those reached only ex falso at session start
    false0: BTreeSet<usize>,
}

/// Zone lines inside functions whose body is the LLM's: where the LLM controls the context.
fn probe_lines(
    m: &Module,
    zone: &[(u32, String, String)],
    bodies: &BTreeSet<String>,
) -> BTreeSet<u32> {
    zone.iter()
        .map(|z| z.0)
        .filter(|&l| {
            m.funcs.iter().any(|f| {
                !f.imported && f.header_line < l && l <= f.end_line && !bodies.contains(&f.name())
            })
        })
        .collect()
}

/// Indices into the zone of its lines the kernel reaches only with False in context.
fn false_zone(zone: &[(u32, String, String)], out: &ModuleOut) -> BTreeSet<usize> {
    let f: BTreeSet<u32> = out
        .funcs
        .iter()
        .flat_map(|f| f.false_ctx_lines.iter().copied())
        .collect();
    zone.iter()
        .enumerate()
        .filter(|(_, z)| f.contains(&z.0))
        .map(|(i, _)| i)
        .collect()
}

/// Indices into the zone of its lines that control never reaches, in functions whose body is the
/// LLM's (the `;; @own` lines and headers there). Student bodies are left out: a harness's
/// `unreachable` arm is *meant* to become dead once the implementation is correct (the kernel
/// unfolds pure loop-free callees), and the LLM cannot edit those bodies.
fn dead_zone(
    zone: &[(u32, String, String)],
    out: &ModuleOut,
    bodies: &BTreeSet<String>,
) -> BTreeSet<usize> {
    let dead: BTreeSet<u32> = out
        .funcs
        .iter()
        .filter(|f| !bodies.contains(&f.name))
        .flat_map(|f| f.dead_lines.iter().copied())
        .collect();
    zone.iter()
        .enumerate()
        .filter(|(_, z)| dead.contains(&z.0))
        .map(|(i, _)| i)
        .collect()
}

fn func_text(m: &Module, lines: &[String], name: &str) -> Option<Vec<String>> {
    let f = m.funcs.iter().find(|f| f.name() == name)?;
    if f.end_line == 0 {
        return Some(vec![lines[f.header_line as usize - 1].trim().to_string()]);
    }
    Some(
        (f.header_line..=f.end_line)
            .map(|l| lines[l as usize - 1].trim().to_string())
            .filter(|t| !t.is_empty())
            .collect(),
    )
}

fn assume_lines(lines: &[String]) -> Vec<String> {
    lines
        .iter()
        .enumerate()
        .filter(|(i, t)| {
            matches!(
                parse_line(t, *i as u32 + 1),
                LineKind::Instr(Ins::Assume(_))
            )
        })
        .map(|(_, t)| t.trim().to_string())
        .collect()
}

impl SessionStart {
    pub fn new(lines: &[String]) -> SessionStart {
        let m = Module::parse_lines(lines);
        let bodies = student_bodies(&m);
        let owners = classify(lines, &bodies);
        let z = zone(lines, &owners);
        let out0 = check_module_probing(&m, false, probe_lines(&m, &z, &bodies));
        let dead0 = dead_zone(&z, &out0, &bodies);
        let false0 = false_zone(&z, &out0);
        SessionStart {
            dead0,
            false0,
            lines: lines.to_vec(),
            zone: z,
            funcs: m.funcs.iter().map(|f| f.name()).collect(),
            assumes: assume_lines(lines),
            imports: lines
                .iter()
                .filter(|t| matches!(parse_line(t, 1), LineKind::Import { .. }))
                .count(),
            bodies,
        }
    }

    pub fn owners(&self, lines: &[String]) -> Vec<Owner> {
        classify(lines, &self.bodies)
    }

    /// §7.1 (1): the first difference between the frozen student zone and this text's.
    pub fn zone_violation(&self, lines: &[String]) -> Option<Reason> {
        let now = zone(lines, &self.owners(lines));
        for i in 0..self.zone.len().max(now.len()) {
            match (self.zone.get(i), now.get(i)) {
                (Some(a), Some(b)) if a.1 == b.1 && a.2 == b.2 => continue,
                (Some(a), Some(b)) if a.1 == b.1 => {
                    return Some(Reason {
                        line: b.0,
                        msg: format!(
                            "moved locked line {} (`{}`) out of its place ({} → {})",
                            b.0,
                            a.1,
                            if a.2.is_empty() { "top level" } else { &a.2 },
                            if b.2.is_empty() { "top level" } else { &b.2 }
                        ),
                    });
                }
                (Some(a), Some(b)) => {
                    // a deleted or inserted locked line shows as a shift: name the old one
                    let msg = if now.iter().any(|x| x.1 == a.1) {
                        format!("adds a line to the locked spec: `{}`", b.1)
                    } else {
                        format!("edited locked line {} (was `{}`)", b.0, a.1)
                    };
                    return Some(Reason { line: b.0, msg });
                }
                (Some(a), None) => {
                    return Some(Reason {
                        line: lines.len() as u32,
                        msg: format!("deleted a locked line (`{}`)", a.1),
                    });
                }
                (None, Some(b)) => {
                    return Some(Reason {
                        line: b.0,
                        msg: format!("adds a line to the locked spec: `{}`", b.1),
                    });
                }
                (None, None) => break,
            }
        }
        None
    }

    /// §7.1 (2): what an LLM-side line may not do.
    pub fn forbidden(&self, lines: &[String]) -> Vec<Reason> {
        let m = Module::parse_lines(lines);
        let mut out = vec![];
        let mut old = self.assumes.clone();
        for (i, t) in lines.iter().enumerate() {
            let ln = i as u32 + 1;
            match parse_line(t, ln) {
                LineKind::Instr(Ins::Assume(_)) => {
                    let t = t.trim().to_string();
                    if let Some(p) = old.iter().position(|x| *x == t) {
                        old.remove(p);
                    } else {
                        out.push(Reason {
                            line: ln,
                            msg: "adds an `assume`: the implementation may not assume (§7.1)"
                                .into(),
                        });
                    }
                }
                LineKind::Instr(Ins::Call(n) | Ins::Lemma(n, _) | Ins::Unfold(n, _)) => {
                    let known = self.funcs.contains(&n)
                        || m.funcs.iter().any(|f| f.name() == n && f.is_lemma());
                    if !known {
                        out.push(Reason {
                            line: ln,
                            msg: format!(
                                "calls {n}, which is neither in the module nor a new lemma"
                            ),
                        });
                    }
                }
                _ => {}
            }
        }
        for (i, f) in m.funcs.iter().enumerate() {
            // identity, not name membership: a second function with a known name is a shadow
            let dup = m.funcs[..i].iter().any(|g| g.name() == f.name());
            if dup {
                out.push(Reason {
                    line: f.header_line,
                    msg: format!(
                        "redefines {}: a function name may be defined once",
                        f.name()
                    ),
                });
                continue;
            }
            if self.funcs.contains(&f.name()) {
                continue;
            }
            if f.is_axiom() {
                out.push(Reason {
                    line: f.header_line,
                    msg: format!("adds an axiom ({}): only the instructor may", f.name()),
                });
            } else if f.imported {
                out.push(Reason {
                    line: f.header_line,
                    msg: format!("adds an import ({})", f.name()),
                });
            } else if !f.is_lemma() {
                out.push(Reason {
                    line: f.header_line,
                    msg: format!(
                        "adds a function ({}): only lemma functions may be added",
                        f.name()
                    ),
                });
            }
        }
        let imports = lines
            .iter()
            .filter(|t| matches!(parse_line(t, 1), LineKind::Import { .. }))
            .count();
        if imports > self.imports && !out.iter().any(|r| r.msg.contains("import")) {
            out.push(Reason {
                line: 0,
                msg: "adds an import".into(),
            });
        }
        out
    }

    /// Functions whose text differs from the session start (new lemmas included).
    pub fn touched(&self, lines: &[String]) -> Vec<String> {
        let m0 = Module::parse_lines(&self.lines);
        let m = Module::parse_lines(lines);
        m.funcs
            .iter()
            .map(|f| f.name())
            .filter(|n| func_text(&m0, &self.lines, n) != func_text(&m, lines, n))
            .collect()
    }

    /// §7.1 (5): the program must run. The kernel's theorem is partial correctness (§6), which a
    /// body that never returns satisfies vacuously; so `$main`, every harness and every LLM-owned
    /// function must finish on inputs satisfying their preconditions (review 20 F5). An LLM-owned
    /// function no input of its list satisfies (fact parameters included) counts as run if some
    /// `$main` or harness run entered it; otherwise its termination is unchecked, which is an
    /// error rather than a silent pass (research/22 S1).
    fn termination(&self, m: &Module) -> Vec<Reason> {
        let mut r = vec![];
        let blame = |g: usize| !self.bodies.contains(&m.funcs[g].name());
        let runnable = |func: &super::ast::Func| {
            !(func.imported || func.end_line == 0 || func.is_lemma() || func.is_axiom())
        };
        let entry = |func: &super::ast::Func| {
            func.is_harness() || func.header.name.as_deref() == Some("$main")
        };
        let away = |func: &super::ast::Func, args: &[u64], g: usize| {
            let shown: Vec<String> = args
                .iter()
                .map(|a| (*a as u32 as i32).to_string())
                .collect();
            Reason {
                line: func.header_line,
                msg: format!(
                    "{}({}) does not finish: {} runs past {} steps or calls: a proof of partial correctness is not an implementation",
                    func.name(),
                    shown.join(", "),
                    m.funcs[g].name(),
                    super::adequacy::FINISH_BUDGET
                ),
            }
        };
        // $main and harnesses first: what they reach counts as run
        let mut reached = vec![false; m.funcs.len()];
        for (f, func) in m.funcs.iter().enumerate() {
            if !runnable(func) || !entry(func) {
                continue;
            }
            let fin = super::adequacy::runs_away(m, f, 16, &blame);
            if let Some((args, g)) = &fin.away {
                r.push(away(func, args, *g));
            } else {
                for (g, x) in fin.reached.iter().enumerate() {
                    reached[g] |= *x;
                }
            }
        }
        for (f, func) in m.funcs.iter().enumerate() {
            if !runnable(func) || entry(func) || self.bodies.contains(&func.name()) {
                continue;
            }
            let fin = super::adequacy::runs_away(m, f, 16, &blame);
            if let Some((args, g)) = &fin.away {
                r.push(away(func, args, *g));
            } else if fin.ran == 0 && !reached[f] {
                r.push(Reason {
                    line: func.header_line,
                    msg: format!(
                        "termination of {} is unchecked: no input in its input list satisfies its precondition and no run of $main or a harness reaches it (§7.1 rule 5); a harness that calls it would let the judge run it",
                        func.name()
                    ),
                });
            }
        }
        r
    }

    /// Judge one submission (§7.1): the boundary first, then strict-cleanness of what it touched.
    pub fn judge(&self, lines: &[String]) -> Judgement {
        let m = Module::parse_lines(lines);
        let mut boundary = self.forbidden(lines);
        if let Some(z) = self.zone_violation(lines)
            && !boundary.iter().any(|r| r.line == z.line)
        {
            boundary.push(z);
        }
        let malformed: Vec<Reason> = m
            .errors
            .iter()
            .map(|(l, e)| Reason {
                line: *l,
                msg: format!("does not parse: {e}"),
            })
            .collect();
        let now = zone(lines, &self.owners(lines));
        let out = check_module_probing(&m, false, probe_lines(&m, &now, &self.bodies));
        if boundary.is_empty() {
            // a locked line the round makes unreachable is as good as deleted: its cups would be
            // fed by dead code (R22) and say nothing (review 20 F7). So is one reached only with
            // False in context (a constant or provably decided branch, a contradictory edge
            // fact): its cups are discharged ex falso and it never runs (research/22 B3). The
            // zones match here (no boundary reason yet), so indices compare.
            for i in dead_zone(&now, &out, &self.bodies).difference(&self.dead0) {
                boundary.push(Reason {
                    line: now[*i].0,
                    msg: format!(
                        "makes locked line {} (`{}`) unreachable",
                        now[*i].0, now[*i].1
                    ),
                });
            }
            for i in false_zone(&now, &out).difference(&self.false0) {
                if boundary.iter().any(|r| r.line == now[*i].0) {
                    continue;
                }
                boundary.push(Reason {
                    line: now[*i].0,
                    msg: format!(
                        "makes locked line {} (`{}`) reachable only ex falso: the kernel proves False there (or on every exit of its block), so its obligations are vacuous",
                        now[*i].0, now[*i].1
                    ),
                });
            }
        }
        let touched = self.touched(lines);
        // every function whose body is the LLM's must be strict-clean, touched or not: leaving an
        // unproven target alone is not an implementation of it (review 20 F6)
        let mut judged = touched.clone();
        judged.extend(
            m.funcs
                .iter()
                .filter(|f| !f.imported && !f.is_axiom() && !self.bodies.contains(&f.name()))
                .map(|f| f.name()),
        );
        let mut strict = strict_reasons(&m, &out, &judged);
        // rule (5) runs whenever the text is in bounds and parses, so the LLM hears about a
        // runaway in the same round as the rest (listed last; research/22 N3)
        if boundary.is_empty() && malformed.is_empty() {
            strict.extend(self.termination(&m));
        }
        Judgement {
            accepted: boundary.is_empty() && malformed.is_empty() && strict.is_empty(),
            boundary,
            malformed,
            strict,
            touched,
            out,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Judgement {
    pub accepted: bool,
    /// §7.1 (1)–(2): the round crossed the ownership boundary (it is rolled back)
    pub boundary: Vec<Reason>,
    pub malformed: Vec<Reason>,
    /// §7.1 (3)–(4): not strict-clean (the round stays applied and runs in gradual mode)
    pub strict: Vec<Reason>,
    pub touched: Vec<String>,
    /// the strict-mode kernel output
    pub out: ModuleOut,
}

impl Judgement {
    pub fn crossed(&self) -> bool {
        !self.boundary.is_empty() || !self.malformed.is_empty()
    }
    pub fn summary(&self) -> String {
        if self.accepted {
            format!("accepted: {} verified", list(&self.touched))
        } else if !self.boundary.is_empty() {
            let m = &self.boundary[0].msg;
            format!("rejected: {}", m.split(" (was `").next().unwrap_or(m))
        } else if !self.malformed.is_empty() {
            format!("rejected: {}", self.malformed[0].msg)
        } else {
            let n = self.strict.len();
            format!(
                "not accepted: {n} obligation{} not proven (strict)",
                if n == 1 { "" } else { "s" }
            )
        }
    }
}

fn list(v: &[String]) -> String {
    if v.is_empty() {
        "nothing changed; all".into()
    } else {
        v.join(", ")
    }
}

fn strict_ok(c: &super::out::CupOut) -> bool {
    matches!(c.verdict, Verdict::Proven | Verdict::Assumed)
        && c.depends_on_checks.is_empty()
        && c.assumptions.iter().all(|o| o.kind == "axiom")
}

/// §7.1 (3)–(4): every cup of a judged function (touched, or LLM-owned) strict-clean, the function
/// VERIFIED, and every harness `False` cup proven.
pub fn strict_reasons(m: &Module, out: &ModuleOut, touched: &[String]) -> Vec<Reason> {
    let mut r = vec![];
    for f in &out.funcs {
        let func = &m.funcs[f.func as usize];
        let is_touched = touched.contains(&f.name);
        if is_touched {
            for c in f.cups.iter().filter(|c| !strict_ok(c)) {
                let why = match c.verdict {
                    Verdict::RuntimeChecked => "nothing feeds it".to_string(),
                    Verdict::Refuted => "refuted".into(),
                    _ if !c.depends_on_checks.is_empty() => "rests on runtime checks".into(),
                    _ => "rests on an assume".into(),
                };
                r.push(Reason {
                    line: c.line,
                    msg: format!("⟨{}⟩ {why}", c.goal),
                });
            }
            for (l, e) in &f.line_errors {
                if !e.starts_with("strict: ") {
                    r.push(Reason {
                        line: *l,
                        msg: e.clone(),
                    });
                }
            }
            if f.strict_clean && !f.verified {
                r.push(Reason {
                    line: f.header_line,
                    msg: format!("{} calls a function that is not VERIFIED", f.name),
                });
            }
        }
        if func.is_harness() {
            for c in f
                .cups
                .iter()
                .filter(|c| c.kind == CupKind::False && !strict_ok(c))
            {
                r.push(Reason {
                    line: c.line,
                    msg: format!("harness {}: ⊥ is not proven unreachable", f.name),
                });
            }
            if !f.verified && !r.iter().any(|x| x.line == f.header_line) {
                // the ⊥ proof rests on the contracts of what it calls: those must be VERIFIED
                let callees: Vec<&str> = func
                    .body
                    .iter()
                    .filter_map(|(_, i)| match i {
                        super::ast::Ins::Call(n) => Some(n.as_str()),
                        _ => None,
                    })
                    .filter(|n| out.funcs.iter().any(|g| g.name == *n && !g.verified))
                    .collect();
                r.push(Reason {
                    line: f.header_line,
                    msg: format!(
                        "harness {} is not VERIFIED{}",
                        f.name,
                        if callees.is_empty() {
                            String::new()
                        } else {
                            format!(": {} is not", callees.join(", "))
                        }
                    ),
                });
            }
        }
    }
    r.sort_by_key(|x| x.line);
    r.dedup();
    r
}

/// One LLM edit (§7.3): replace lines `a..=b` (1-based) with `with`; `b = a − 1` inserts before `a`.
#[derive(Clone, Debug, PartialEq)]
pub struct Edit {
    pub a: u32,
    pub b: u32,
    pub with: Vec<String>,
}

/// Apply edits that all refer to the same numbering (bottom first).
pub fn apply_edits(lines: &[String], edits: &[Edit]) -> Result<Vec<String>, String> {
    let mut es = edits.to_vec();
    es.sort_by_key(|e| std::cmp::Reverse(e.a));
    let n = lines.len() as u32;
    let mut prev_a = u32::MAX;
    for e in &es {
        if e.a == 0 || e.a > n + 1 || e.b + 1 < e.a || e.b > n {
            return Err(format!("edit [{}, {}] is outside lines 1..{n}", e.a, e.b));
        }
        if e.b >= prev_a {
            return Err(format!("edit [{}, {}] overlaps another", e.a, e.b));
        }
        prev_a = e.a;
    }
    let mut out = lines.to_vec();
    for e in &es {
        let (a, b) = (e.a as usize - 1, e.b as usize);
        out.splice(a..b.max(a), e.with.iter().cloned());
    }
    Ok(out)
}
