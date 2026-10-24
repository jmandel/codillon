//! The kernel: one forward pass per function (design 16 §5.2) applying the rule cards R1–R35.

use super::ast::{BlockKind, BlockType, Decl, Expr, IOp, Ins, LocalKind, Module, Refined, ValTy};
use super::eval::{EvalErr, Interp, value_locals};
use super::info::FnInfo;
use super::out::{CupKind, CupOut, Feed, FuncOut, Origin, Verdict, Witness};
use super::solver::{Env, Outcome, Solver};
use super::symex::{call_term, symex};
use super::term::{Atom, Key, NO_EPOCH, TermId, Terms};
use smallvec::SmallVec;
use std::collections::{BTreeSet, HashMap};

pub type FactId = u32;
pub type CupId = u32;

#[derive(Clone, Debug, PartialEq)]
pub enum Dep {
    Cup(CupId),
    Fact(FactId),
    Group(u32),
    /// an assumption: (origin line, is an instructor axiom)
    Assume(u32, bool),
}

#[derive(Clone, Debug)]
pub struct Fact {
    pub atom: Atom,
    pub line: u32,
    pub kind: &'static str,
    pub deps: Vec<Dep>,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Entry {
    pub fact: FactId,
    pub line: u32,
}

#[derive(Clone, Debug)]
pub struct CupReq {
    pub kind: CupKind,
    pub operand: Option<u8>,
    pub atom: Atom,
}

pub struct Pending {
    line: u32,
    hyps: Vec<Entry>,
    failed: Option<String>,
}

#[derive(Clone, Debug)]
pub struct Edge {
    lane: Vec<Entry>,
    locals: Vec<TermId>,
    globals: Vec<TermId>,
    eps: u32,
    values: Vec<TermId>,
    fact_cups: Vec<CupId>,
    result_cups: Vec<Option<CupId>>,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum FKind {
    Func,
    Block,
    Loop,
    If,
}

pub struct Frame {
    kind: FKind,
    bt: BlockType,
    line: u32,
    lane_mark: usize,
    height: usize,
    locals: Vec<TermId>,
    globals: Vec<TermId>,
    eps: u32,
    handles: Vec<Option<Entry>>,
    real_mark: usize,
    edges: Vec<Edge>,
    cond: Option<TermId>,
    in_else: bool,
    entered_dead: Option<u32>,
    /// loops: one dependency group per declared fact, then one per param
    groups: Vec<u32>,
}

/// Module-wide context shared by every function pass.
pub struct ModCtx<'m> {
    pub m: &'m Module,
    pub info: Vec<FnInfo>,
    /// memory size lower bound M (R10)
    pub mem: Option<u64>,
    /// assumption origins of each checked lemma's results (R33)
    pub lemma_assumes: HashMap<usize, Vec<Dep>>,
    pub gradual: bool,
}

/// The solver's view of the module: unfolding and evaluation.
pub struct PassEnv<'a, 'm> {
    pub cx: &'a ModCtx<'m>,
    pub real: &'a [bool],
    pub unfold_memo: &'a mut HashMap<TermId, Option<TermId>>,
}

impl Env for PassEnv<'_, '_> {
    fn unfold(&mut self, terms: &mut Terms, call: TermId) -> Option<TermId> {
        if let Some(r) = self.unfold_memo.get(&call) {
            return *r;
        }
        let r = match terms.key(call).clone() {
            Key::Call(f, args, ep) => {
                let f = f as usize;
                let i = &self.cx.info[f];
                let fun = &self.cx.m.funcs[f];
                if i.self_rec || i.impure.is_some() || i.has_loop.is_some() || fun.is_lemma() || fun.is_axiom() {
                    None
                } else {
                    symex(self.cx.m, &self.cx.info, terms, f, &args, if ep == NO_EPOCH { 0 } else { ep })
                }
            }
            _ => None,
        };
        self.unfold_memo.insert(call, r);
        r
    }
    fn eval_call(&mut self, terms: &Terms, call: TermId) -> Option<u64> {
        let Key::Call(f, args, ep) = terms.key(call) else { return None };
        if *ep != NO_EPOCH {
            return None;
        }
        let vals: Option<Vec<u64>> = args.iter().map(|a| terms.as_const(*a)).collect();
        let mut it = Interp::new(self.cx.m);
        it.call(*f as usize, &vals?).ok()?.first().copied()
    }
    fn is_real(&self, t: TermId) -> bool {
        self.real.get(t as usize).copied().unwrap_or(false)
    }
}

pub struct Pass<'a, 'm> {
    pub cx: &'a ModCtx<'m>,
    pub f: usize,
    pub terms: Terms,
    pub facts: Vec<Fact>,
    pub lane: Vec<Entry>,
    stack: Vec<TermId>,
    /// value locals (params first)
    locs: Vec<(Option<String>, ValTy)>,
    loc_ref: Vec<Option<Refined>>,
    locals: Vec<TermId>,
    entry: Vec<TermId>,
    /// fact handles by name
    handle_names: Vec<String>,
    handles: Vec<Option<Entry>>,
    globals: Vec<TermId>,
    eps: u32,
    next_eps: u32,
    frames: Vec<Frame>,
    dead: Option<u32>,
    pending: Vec<Pending>,
    pub cups: Vec<CupOut>,
    cup_deps: Vec<Vec<Dep>>,
    pub groups: Vec<Vec<Dep>>,
    local_groups: Vec<Option<u32>>,
    global_groups: Vec<Option<u32>>,
    real: Vec<bool>,
    real_log: Vec<TermId>,
    unfold_memo: HashMap<TermId, Option<TermId>>,
    pub line_errors: Vec<(u32, String)>,
    pub slot_ids: Vec<(u32, u32)>,
    ghost: bool,
    /// lines of `assume` (not instructor axioms)
    line: u32,
}

pub type Bind = Vec<(String, TermId)>;

fn ty_of_op(name: &str) -> Option<ValTy> {
    ValTy::parse(name.split('.').next()?)
}

impl<'a, 'm> Pass<'a, 'm> {
    // ---------- terms, binding, instantiation ----------

    fn mark_real(&mut self, t: TermId) {
        if self.real.len() <= t as usize {
            self.real.resize(t as usize + 1, false);
        }
        if !self.real[t as usize] {
            self.real[t as usize] = true;
            self.real_log.push(t);
        }
    }

    fn cut_real(&mut self, mark: usize) {
        while self.real_log.len() > mark {
            let t = self.real_log.pop().unwrap();
            self.real[t as usize] = false;
        }
    }

    /// Bindings of names at the current point: value locals (current values).
    fn cur_bind(&self) -> Bind {
        self.locs.iter().zip(self.locals.iter()).filter_map(|((n, _), t)| n.clone().map(|n| (n, *t))).collect()
    }

    /// Bindings with parameters at their entry values (R15, result refinements).
    fn entry_bind(&self) -> Bind {
        let mut b = self.cur_bind();
        let np = self.entry.len();
        for (i, (n, _)) in self.locs.iter().enumerate().take(np) {
            if let Some(n) = n {
                b.retain(|(x, _)| x != n);
                b.push((n.clone(), self.entry[i]));
            }
        }
        b
    }

    pub fn inst(&mut self, e: &Expr, bind: &Bind, v: Option<TermId>, want: Option<ValTy>) -> Result<TermId, String> {
        Ok(match e {
            Expr::V => v.ok_or("`v` outside a refinement")?,
            Expr::Var(n) => bind.iter().rev().find(|(x, _)| x == n).map(|x| x.1).ok_or_else(|| format!("unknown name {n}"))?,
            Expr::Int(i) => {
                let ty = want.unwrap_or(ValTy::I32);
                self.terms.konst(ty, super::ast::to_bits(ty, *i))
            }
            Expr::Op(name, args) => {
                if let Some(t) = name.strip_suffix(".const") {
                    let ty = ValTy::parse(t).ok_or("bad const")?;
                    let Some(Expr::Int(i)) = args.first() else { return Err("bad const".into()) };
                    return Ok(self.terms.konst(ty, super::ast::to_bits(ty, *i)));
                }
                let (op, w) = IOp::parse(name).ok_or_else(|| format!("`{name}` is not a pure integer operator"))?;
                if args.len() != if op.unary() { 1 } else { 2 } {
                    return Err(format!("`{name}` takes {} operands", if op.unary() { 1 } else { 2 }));
                }
                let mut a = Vec::new();
                for x in args {
                    a.push(self.inst(x, bind, v, Some(w))?);
                }
                for x in &a {
                    if self.terms.ty(*x) != w {
                        return Err(format!("`{name}` needs {} operands", w.name()));
                    }
                }
                let _ = ty_of_op;
                self.terms.op(op, w, &a)
            }
            Expr::Call(fname, args) => {
                let g = self.cx.m.func_index(fname).ok_or_else(|| format!("unknown function {fname}"))?;
                let ptys: Vec<ValTy> = self.cx.m.funcs[g].value_params().map(|(_, _, r)| r.ty).collect();
                if ptys.len() != args.len() {
                    return Err(format!("{fname} takes {} arguments", ptys.len()));
                }
                let mut a = Vec::new();
                for (x, ty) in args.iter().zip(ptys) {
                    a.push(self.inst(x, bind, v, Some(ty))?);
                }
                call_term(self.cx.m, &self.cx.info, &mut self.terms, g, &a, self.eps).ok_or_else(|| format!("{fname} has no value result"))?
            }
        })
    }

    /// Instantiate a proposition (`(fact E)` or a refinement) to its atom.
    pub fn inst_atom(&mut self, e: &Expr, bind: &Bind, v: Option<TermId>) -> Atom {
        match self.inst(e, bind, v, Some(ValTy::I32)) {
            Ok(t) => self.terms.atom_of(t, true),
            Err(msg) => {
                self.line_errors.push((self.line, msg));
                Atom::True
            }
        }
    }

    // ---------- the lane ----------

    pub fn new_fact(&mut self, atom: Atom, line: u32, kind: &'static str, deps: Vec<Dep>) -> FactId {
        self.facts.push(Fact { atom, line, kind, deps });
        (self.facts.len() - 1) as FactId
    }

    pub fn enter(&mut self, atom: Atom, line: u32, kind: &'static str, deps: Vec<Dep>) -> FactId {
        let f = self.new_fact(atom, line, kind, deps);
        self.lane.push(Entry { fact: f, line });
        f
    }

    fn lookup(&self, goal: &Atom, extra: Option<Entry>) -> Option<Entry> {
        if let Some(e) = extra
            && self.facts[e.fact as usize].atom.feeds(goal)
        {
            return Some(e);
        }
        self.lane.iter().rev().find(|e| self.facts[e.fact as usize].atom.feeds(goal)).copied()
    }

    fn solver_env<'s>(&'s mut self) -> (&'s mut Terms, PassEnv<'s, 'm>) {
        let env = PassEnv { cx: self.cx, real: &self.real, unfold_memo: &mut self.unfold_memo };
        (&mut self.terms, env)
    }

    /// R28: evaluate an all-constant atom. Some(Ok(true)) = holds, Some(Ok(false)) = refuted.
    fn eval_atom(&mut self, a: &Atom) -> Option<Result<(bool, u32), String>> {
        let args = self.terms.atom_args(a);
        if args.is_empty() || !args.iter().all(|x| self.terms.is_const(*x)) {
            return None;
        }
        if let Atom::Bool { t, .. } = a
            && let Key::Call(_, _, ep) = self.terms.key(*t)
            && *ep != NO_EPOCH
        {
            return None;
        }
        let mut it = Interp::new(self.cx.m);
        let r = self.eval_atom_with(&mut it, a);
        Some(r.map(|b| (b, it.steps)))
    }

    fn eval_term(&self, it: &mut Interp, t: TermId) -> Result<u64, String> {
        match self.terms.key(t) {
            Key::Const(_, b) => Ok(*b),
            Key::Call(f, args, _) => {
                let vals: Vec<u64> = args.iter().map(|a| self.terms.as_const(*a).unwrap_or(0)).collect();
                match it.call(*f as usize, &vals) {
                    Ok(r) => r.first().copied().ok_or_else(|| "no result".into()),
                    Err(EvalErr::Budget) => Err(format!("evaluation exceeded {} steps", super::eval::EVAL_BUDGET)),
                    Err(EvalErr::Trap(m)) => Err(format!("evaluation trapped: {m}")),
                    Err(EvalErr::Unsupported(m)) => Err(format!("cannot evaluate: {m}")),
                }
            }
            _ => Err("cannot evaluate a float atom".into()),
        }
    }

    fn eval_atom_with(&self, it: &mut Interp, a: &Atom) -> Result<bool, String> {
        use super::term::Rel;
        match a {
            Atom::True => Ok(true),
            Atom::False => Ok(false),
            Atom::Bool { t, neg } => Ok((self.eval_term(it, *t)? != 0) != *neg),
            Atom::Or(x, y) => Ok(self.eval_atom_with(it, x)? || self.eval_atom_with(it, y)?),
            Atom::Cmp { rel, signed, a, b } => {
                let ty = self.terms.ty(*a);
                if !ty.is_int() {
                    return Err("cannot evaluate a float atom".into());
                }
                let (x, y) = (self.eval_term(it, *a)?, self.eval_term(it, *b)?);
                let s = |v: u64| if ty == ValTy::I32 { v as u32 as i32 as i64 as i128 } else { v as i64 as i128 };
                let (x, y) = if *signed { (s(x), s(y)) } else { (x as i128, y as i128) };
                Ok(match rel {
                    Rel::Eq => x == y,
                    Rel::Ne => x != y,
                    Rel::Lt => x < y,
                    Rel::Le => x <= y,
                })
            }
        }
    }
}
