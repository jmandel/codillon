//! Gradual mode (R35): every unfed cup on an executable line becomes a runtime check.
//!
//! The instrumented program cannot recompute the kernel's canonical ids by itself, so the kernel
//! hands it a [`RuntimePlan`]: opaque values (parameters, φs, loads, call results, …) are copied
//! into *shadow locals* where they are born ([`Capture`]), and before a line with checks the shadow
//! values each check needs are sent to the host, which evaluates the cup's atom
//! ([`RuntimePlan::eval_check`]) and stops the run if it is false. Pure terms over those values
//! (arithmetic, predicate calls) are recomputed host-side by the reference interpreter.

use super::ast::{Module, ValTy};
use super::eval::{EvalErr, Interp, eval_iop};
use super::out::{Capture, CupKind, ModuleOut, Verdict};
use super::term::{Atom, Key, Rel, TermId, Terms};
use std::collections::{BTreeMap, HashMap, HashSet};

/// Copy a captured value into shadow local `shadow` (index among this function's shadows).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShadowAct {
    pub shadow: u32,
    pub how: Capture,
}

impl FuncPlan {
    /// (shadow, type) of each value check `id` sends, in order.
    pub fn sends_of(&self, id: u32) -> Vec<(u32, ValTy)> {
        self.sends.get(&id).cloned().unwrap_or_default()
    }
}

#[derive(Clone, Debug, Default)]
pub struct FuncPlan {
    /// 1-based header line (the instrumenter checks it against the binary's function)
    pub header_line: u32,
    /// per check id of this function: (shadow, type) sent, in order
    pub sends: BTreeMap<u32, Vec<(u32, ValTy)>>,
    /// module function index
    pub func: u32,
    /// number of value locals (params + locals) in the erased function: shadows come after them
    pub n_locals: u32,
    pub shadow_tys: Vec<ValTy>,
    /// captures at function entry
    pub entry: Vec<ShadowAct>,
    /// captures right after the instruction of a line (1-based)
    pub after: BTreeMap<u32, Vec<ShadowAct>>,
    /// checks to run right before the instruction of a line (indices into `RuntimePlan::checks`)
    pub before: BTreeMap<u32, Vec<u32>>,
}

#[derive(Clone, Debug)]
pub struct CheckSpec {
    pub func: u32,
    pub line: u32,
    pub kind: CupKind,
    pub goal: String,
    pub atom: Atom,
    /// the check applies only when this edge condition holds (br_if / br_table taken edges)
    pub guard: Option<Atom>,
    /// shadow locals whose values the check needs, in send order: (term, shadow, type)
    pub sends: Vec<(TermId, u32, ValTy)>,
    /// does evaluating it read linear memory (a call of a memory-reading function)?
    pub reads_mem: bool,
}

#[derive(Clone, Debug, PartialEq)]
pub enum CheckOutcome {
    Holds,
    Fails(String),
    /// the atom could not be evaluated (no claim is made; the run continues)
    Unknown(String),
}

#[derive(Clone, Debug, Default)]
pub struct RuntimePlan {
    pub module: Module,
    pub funcs: Vec<FuncPlan>,
    pub checks: Vec<CheckSpec>,
    /// each function's value numbering, by module function index
    pub terms: Vec<Terms>,
    /// does function f read memory (directly or through callees)?
    pub reads_mem: Vec<bool>,
    /// functions whose checks the instrumenter could not compile (the kernel's view of the
    /// function disagreed with the binary's): their checks stop the run with an error
    pub uncompiled: std::cell::RefCell<Vec<u32>>,
}

fn walk(
    terms: &Terms,
    t: TermId,
    born: &HashSet<TermId>,
    out: &mut Vec<TermId>,
    seen: &mut HashSet<TermId>,
) {
    if !seen.insert(t) {
        return;
    }
    if born.contains(&t) {
        out.push(t);
        return;
    }
    match terms.key(t) {
        Key::Op(_, _, a) | Key::Float(_, a) => {
            a.iter().for_each(|x| walk(terms, *x, born, out, seen))
        }
        Key::Call(_, a, _) => a.iter().for_each(|x| walk(terms, *x, born, out, seen)),
        Key::Load(.., a, _) => walk(terms, *a, born, out, seen),
        Key::Ite(c, a, b) => {
            for x in [c, a, b] {
                walk(terms, *x, born, out, seen)
            }
        }
        _ => {}
    }
}

/// Does evaluating the atom call a memory-reading function?
fn sends_reach_mem(terms: &Terms, a: &Atom, reads_mem: &[bool]) -> bool {
    let mut work = vec![];
    atom_terms(a, &mut work);
    let mut seen = HashSet::new();
    while let Some(t) = work.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.key(t) {
            Key::Call(f, a, _) => {
                if reads_mem.get(*f as usize).copied().unwrap_or(true) {
                    return true;
                }
                work.extend(a.iter().copied());
            }
            Key::Op(_, _, a) | Key::Float(_, a) => work.extend(a.iter().copied()),
            Key::Ite(c, a, b) => work.extend([*c, *a, *b]),
            Key::Load(.., a, _) => work.push(*a),
            _ => {}
        }
    }
    false
}

fn atom_terms(a: &Atom, v: &mut Vec<TermId>) {
    match a {
        Atom::Cmp { a, b, .. } => v.extend([*a, *b]),
        Atom::Bool { t, .. } => v.push(*t),
        Atom::Or(x, y) => {
            atom_terms(x, v);
            atom_terms(y, v);
        }
        _ => {}
    }
}

/// For each body line of function `f`, the block arms open at it (outermost first): an arm is
/// named by the line that opened it (`block`/`loop`/`if`, or `else`).
fn scopes_of(m: &Module, f: usize) -> HashMap<u32, Vec<u32>> {
    use super::ast::Ins;
    let mut open: Vec<u32> = vec![];
    let mut at = HashMap::new();
    for (line, ins) in &m.funcs[f].body {
        match ins {
            Ins::Block(..) => {
                at.insert(*line, open.clone());
                open.push(*line);
            }
            Ins::Else => {
                open.pop();
                at.insert(*line, open.clone());
                open.push(*line);
            }
            Ins::End => {
                open.pop();
                at.insert(*line, open.clone());
            }
            _ => {
                at.insert(*line, open.clone());
            }
        }
    }
    at
}

impl RuntimePlan {
    /// The plan for a checked module: one check per runtime-checked cup on an executable line.
    pub fn new(m: &Module, out: &ModuleOut) -> RuntimePlan {
        let reads_mem = super::info::analyze(m)
            .iter()
            .map(|i| i.reads_mem)
            .collect();
        let mut plan = RuntimePlan {
            module: m.clone(),
            funcs: vec![],
            checks: vec![],
            terms: vec![Terms::default(); m.funcs.len()],
            reads_mem,
            uncompiled: Default::default(),
        };
        for fo in &out.funcs {
            let f = fo.func as usize;
            let scopes = scopes_of(m, f);
            let scope_at = |l: u32| -> &[u32] {
                scopes.get(&l).map(|v| v.as_slice()).unwrap_or(&[])
            };
            // a capture is usable by a check only if it is written on every path to the check:
            // its line comes first and every block arm open there is still open at the check.
            // Opaque leaves (params, φs, globals, impure results) are born only where they are
            // defined, so they always qualify; a pure call or a load of the same canonical term may
            // also occur later or in a sibling arm, where its shadow is not yet written.
            let dominated = |t: TermId, line: u32| -> bool {
                fo.births.iter().any(|b| {
                    b.term == t
                        && (b.line == fo.header_line
                            || (b.line < line && scope_at(line).starts_with(scope_at(b.line))))
                })
            };
            let mut fp = FuncPlan {
                func: fo.func,
                header_line: fo.header_line,
                n_locals: super::eval::value_locals(m, f).len() as u32,
                ..Default::default()
            };
            let mut shadow_of: HashMap<TermId, u32> = HashMap::new();
            let mut needed: Vec<TermId> = vec![];
            let mut checks = vec![];
            for c in &fo.cups {
                if c.verdict != Verdict::RuntimeChecked || c.ghost {
                    continue;
                }
                let mut roots = vec![];
                atom_terms(&c.atom, &mut roots);
                if let Some(g) = &c.guard {
                    atom_terms(g, &mut roots);
                }
                let born: HashSet<TermId> = fo
                    .births
                    .iter()
                    .map(|b| b.term)
                    .filter(|t| {
                        !matches!(fo.terms.key(*t), Key::Call(..) | Key::Load(..))
                            || dominated(*t, c.line)
                    })
                    .collect();
                let mut sends = vec![];
                let mut seen = HashSet::new();
                for r in roots {
                    walk(&fo.terms, r, &born, &mut sends, &mut seen);
                }
                needed.extend(sends.iter().copied());
                checks.push((c, sends));
            }
            for t in needed {
                if let std::collections::hash_map::Entry::Vacant(e) = shadow_of.entry(t) {
                    e.insert(fp.shadow_tys.len() as u32);
                    fp.shadow_tys.push(fo.terms.ty(t));
                }
            }
            for b in &fo.births {
                let Some(&shadow) = shadow_of.get(&b.term) else {
                    continue;
                };
                let act = ShadowAct { shadow, how: b.how };
                let at_entry = matches!(b.how, Capture::Param(_))
                    || (b.line == fo.header_line && matches!(b.how, Capture::Global(_)));
                if at_entry {
                    fp.entry.push(act);
                } else {
                    let v = fp.after.entry(b.line).or_default();
                    if !v.contains(&act) {
                        v.push(act);
                    }
                }
            }
            for (c, sends) in checks {
                let id = plan.checks.len() as u32;
                let reads_mem = sends_reach_mem(&fo.terms, &c.atom, &plan.reads_mem);
                plan.checks.push(CheckSpec {
                    reads_mem,
                    func: fo.func,
                    line: c.line,
                    kind: c.kind,
                    goal: c.goal.clone(),
                    atom: c.atom.clone(),
                    guard: c.guard.clone(),
                    sends: sends
                        .iter()
                        .map(|t| (*t, shadow_of[t], fo.terms.ty(*t)))
                        .collect(),
                });
                fp.before.entry(c.line).or_default().push(id);
                fp.sends.insert(
                    id,
                    sends
                        .iter()
                        .map(|t| (shadow_of[t], fo.terms.ty(*t)))
                        .collect(),
                );
            }
            plan.terms[f] = fo.terms.clone();
            plan.funcs.push(fp);
        }
        plan
    }

    pub fn func_plan(&self, f: u32) -> Option<&FuncPlan> {
        self.funcs.iter().find(|p| p.func == f)
    }

    /// The plan of the `k`-th defined (non-imported) function, as the binary numbers them.
    pub fn for_defined(&self, k: usize) -> Option<&FuncPlan> {
        let f = self
            .module
            .funcs
            .iter()
            .enumerate()
            .filter(|(_, f)| !f.imported)
            .nth(k)?
            .0;
        self.func_plan(f as u32)
    }

    /// Evaluate check `id` on the values sent for it (parallel to `sends`), with the memory as it
    /// is right now (for memory-reading predicates).
    pub fn eval_check(&self, id: u32, vals: &[u64], mem: Option<&[u8]>) -> CheckOutcome {
        let c = &self.checks[id as usize];
        let terms = &self.terms[c.func as usize];
        let mut env: HashMap<TermId, u64> = HashMap::new();
        for ((t, _, _), v) in c.sends.iter().zip(vals) {
            env.insert(*t, *v);
        }
        let mut ev = Evaluator {
            plan: self,
            terms,
            env,
            mem,
        };
        if let Some(g) = &c.guard {
            match ev.atom(g) {
                Ok(false) => return CheckOutcome::Holds,
                Err(e) if e == TRAPS => return CheckOutcome::Holds,
                Ok(true) => {}
                Err(e) => return CheckOutcome::Unknown(e),
            }
        }
        // the run's values of the named values the check reads ("with $x = 3, $y = 0")
        let with = {
            let mut named: Vec<String> = vec![];
            for ((t, _, ty), v) in c.sends.iter().zip(vals) {
                let name = terms.render(*t);
                if !name.starts_with('$')
                    || name.contains('(')
                    || named.iter().any(|n| n.starts_with(&format!("{name} =")))
                {
                    continue;
                }
                let shown = match ty {
                    super::ast::ValTy::I32 => (*v as u32 as i32).to_string(),
                    super::ast::ValTy::I64 => (*v as i64).to_string(),
                    super::ast::ValTy::F32 => f32::from_bits(*v as u32).to_string(),
                    super::ast::ValTy::F64 => f64::from_bits(*v).to_string(),
                };
                named.push(format!("{name} = {shown}"));
            }
            if named.is_empty() {
                String::new()
            } else {
                format!(" with {}", named.join(", "))
            }
        };
        match ev.atom(&c.atom) {
            Ok(true) => CheckOutcome::Holds,
            Ok(false) => CheckOutcome::Fails(format!("check failed: ⟨{}⟩{with}", c.goal)),
            // a fact whose evaluation traps is false (it holds iff it evaluates, without trapping, to nonzero)
            Err(e) if e == TRAPS => CheckOutcome::Fails(format!(
                "check failed: ⟨{}⟩ (its evaluation traps){with}",
                c.goal
            )),
            Err(e) => CheckOutcome::Unknown(e),
        }
    }
}

const TRAPS: &str = "evaluation traps";

struct Evaluator<'a> {
    plan: &'a RuntimePlan,
    terms: &'a Terms,
    env: HashMap<TermId, u64>,
    mem: Option<&'a [u8]>,
}

impl Evaluator<'_> {
    fn term(&mut self, t: TermId) -> Result<u64, String> {
        if let Some(v) = self.env.get(&t) {
            return Ok(*v);
        }
        let v = match self.terms.key(t).clone() {
            Key::Const(_, b) => b,
            Key::Op(op, w, a) => {
                let args: Vec<u64> = a.iter().map(|x| self.term(*x)).collect::<Result<_, _>>()?;
                eval_iop(op, w, &args).map_err(|_| TRAPS.to_string())?
            }
            Key::Ite(c, a, b) => {
                if self.term(c)? as u32 != 0 {
                    self.term(a)?
                } else {
                    self.term(b)?
                }
            }
            Key::Call(f, a, _) => {
                let args: Vec<u64> = a.iter().map(|x| self.term(*x)).collect::<Result<_, _>>()?;
                if self.mem.is_none()
                    && self.plan.reads_mem.get(f as usize).copied().unwrap_or(true)
                {
                    return Err("memory is not available to the checker".into());
                }
                let mut it = Interp::new(&self.plan.module);
                if let Some(m) = self.mem {
                    it.mem = m.to_vec();
                }
                it.budget = 1_000_000;
                match it.call(f as usize, &args) {
                    Ok(r) => r.first().copied().ok_or("no result")?,
                    Err(EvalErr::Budget) => {
                        return Err("predicate evaluation exceeded its budget".into());
                    }
                    Err(EvalErr::Trap(_)) => return Err(TRAPS.to_string()),
                    Err(e) => return Err(format!("predicate evaluation failed: {e:?}")),
                }
            }
            _ => {
                return Err(format!(
                    "value of {} was not captured",
                    self.terms.render(t)
                ));
            }
        };
        self.env.insert(t, v);
        Ok(v)
    }

    fn atom(&mut self, a: &Atom) -> Result<bool, String> {
        Ok(match a {
            Atom::True => true,
            Atom::False => false,
            Atom::Bool { t, neg } => (self.term(*t)? != 0) != *neg,
            Atom::Or(x, y) => self.atom(x)? || self.atom(y)?,
            Atom::Cmp { rel, signed, a, b } => {
                let ty = self.terms.ty(*a);
                let (x, y) = (self.term(*a)?, self.term(*b)?);
                let s = |v: u64| {
                    if ty == ValTy::I32 {
                        v as u32 as i32 as i128
                    } else {
                        v as i64 as i128
                    }
                };
                let (x, y) = if *signed {
                    (s(x), s(y))
                } else {
                    (x as i128, y as i128)
                };
                match rel {
                    Rel::Eq => x == y,
                    Rel::Ne => x != y,
                    Rel::Lt => x < y,
                    Rel::Le => x <= y,
                }
            }
        })
    }
}
