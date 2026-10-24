//! The kernel: one forward pass per function (design 16 §5.2) applying the rule cards R1–R35.

use super::ast::{BlockKind, BlockType, Decl, Expr, IOp, Ins, LocalKind, Module, Refined, ValTy};
use super::eval::{EvalErr, Interp, value_locals};
use super::info::FnInfo;
use super::out::{Birth, Capture, CupKind, CupOut, Feed, FuncOut, Origin, Verdict, Witness};
use super::solver::{Env, Outcome, Solver};
use super::symex::{call_term, symex};
use super::term::{Atom, Key, NO_EPOCH, TermId, Terms};
use smallvec::SmallVec;
use std::collections::{BTreeSet, HashMap};

pub type FactId = u32;
pub type CupId = u32;

const TRAPPED: &str = "evaluation traps";

#[derive(Clone, Debug, PartialEq)]
pub enum Dep {
    Cup(CupId),
    Fact(FactId),
    Group(u32),
    /// an assumption: (origin line, is an instructor axiom)
    Assume(u32, bool),
    /// a runtime check on that line of another function (a refined global's unproven `global.set`)
    Check(u32),
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
    /// per global: what its refinement rests on beyond this function's own `global.set` cups — the
    /// initializer (R14) and every other function's unproven `global.set` cups (R9); `None` when
    /// the global has no usable refinement
    pub global_deps: Vec<Option<Vec<Dep>>>,
    /// lines at which to ask whether the context is contradictory (the judge's locked lines in
    /// LLM-owned bodies, research/22 B3); empty in the editor
    pub probe: BTreeSet<u32>,
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
                if i.self_rec
                    || i.mutual_rec.is_some()
                    || i.impure.is_some()
                    || i.has_loop.is_some()
                    || fun.is_lemma()
                    || fun.is_axiom()
                {
                    None
                } else {
                    symex(
                        self.cx.m,
                        &self.cx.info,
                        terms,
                        f,
                        &args,
                        if ep == NO_EPOCH { 0 } else { ep },
                    )
                }
            }
            _ => None,
        };
        self.unfold_memo.insert(call, r);
        r
    }
    fn eval_call(&mut self, terms: &Terms, call: TermId) -> Option<u64> {
        let Key::Call(f, args, ep) = terms.key(call) else {
            return None;
        };
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
    /// body lines control never reaches (R22)
    dead_lines: Vec<u32>,
    false_ctx_lines: Vec<u32>,
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
    pub births: Vec<Birth>,
    /// local rebindings: (local, old id, new id, line), in pass order (R7 stale hints)
    sets: Vec<(usize, TermId, TermId, u32)>,
    /// the line where a fact frays (R7, R11)
    fray: HashMap<FactId, u32>,
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
        self.locs
            .iter()
            .zip(self.locals.iter())
            .filter_map(|((n, _), t)| n.clone().map(|n| (n, *t)))
            .collect()
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

    pub fn inst(
        &mut self,
        e: &Expr,
        bind: &Bind,
        v: Option<TermId>,
        want: Option<ValTy>,
    ) -> Result<TermId, String> {
        Ok(match e {
            Expr::V => v.ok_or("`v` outside a refinement")?,
            Expr::Var(n) => bind
                .iter()
                .rev()
                .find(|(x, _)| x == n)
                .map(|x| x.1)
                .ok_or_else(|| format!("unknown name {n}"))?,
            Expr::Int(i) => {
                let ty = want.unwrap_or(ValTy::I32);
                self.terms.konst(ty, super::ast::to_bits(ty, *i))
            }
            Expr::Op(name, args) => {
                if let Some(t) = name.strip_suffix(".const") {
                    let ty = ValTy::parse(t).ok_or("bad const")?;
                    let Some(Expr::Int(i)) = args.first() else {
                        return Err("bad const".into());
                    };
                    return Ok(self.terms.konst(ty, super::ast::to_bits(ty, *i)));
                }
                let (op, w) = IOp::parse(name)
                    .ok_or_else(|| format!("`{name}` is not a pure integer operator"))?;
                if args.len() != if op.unary() { 1 } else { 2 } {
                    return Err(format!(
                        "`{name}` takes {} operands",
                        if op.unary() { 1 } else { 2 }
                    ));
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
                let g = self
                    .cx
                    .m
                    .func_index(fname)
                    .ok_or_else(|| format!("unknown function {fname}"))?;
                let ptys: Vec<ValTy> = self.cx.m.funcs[g]
                    .value_params()
                    .map(|(_, _, r)| r.ty)
                    .collect();
                if ptys.len() != args.len() {
                    return Err(format!("{fname} takes {} arguments", ptys.len()));
                }
                let mut a = Vec::new();
                for (x, ty) in args.iter().zip(ptys) {
                    a.push(self.inst(x, bind, v, Some(ty))?);
                }
                call_term(self.cx.m, &self.cx.info, &mut self.terms, g, &a, self.eps)
                    .ok_or_else(|| format!("{fname} has no value result"))?
            }
        })
    }

    /// Instantiate a proposition (`(fact E)` or a refinement) to its atom.
    pub fn inst_atom(&mut self, e: &Expr, bind: &Bind, v: Option<TermId>) -> Atom {
        match self.inst(e, bind, v, Some(ValTy::I32)) {
            Ok(t) => self.terms.atom_of(t, true),
            Err(msg) => {
                // an ill-formed proposition: an opaque atom about a fresh value, which no fact
                // matches and no proof establishes (and which, as a fact, constrains nothing else)
                self.line_errors.push((self.line, msg));
                let t = self.terms.leaf(ValTy::I32, "ill-formed proposition", None);
                Atom::Bool { t, neg: false }
            }
        }
    }

    // ---------- the lane ----------

    pub fn new_fact(
        &mut self,
        atom: Atom,
        line: u32,
        kind: &'static str,
        deps: Vec<Dep>,
    ) -> FactId {
        self.facts.push(Fact {
            atom,
            line,
            kind,
            deps,
        });
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
        self.lane
            .iter()
            .rev()
            .find(|e| self.facts[e.fact as usize].atom.feeds(goal))
            .copied()
    }

    fn solver_env<'s>(&'s mut self) -> (&'s mut Terms, PassEnv<'s, 'm>) {
        let env = PassEnv {
            cx: self.cx,
            real: &self.real,
            unfold_memo: &mut self.unfold_memo,
        };
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
        // a fact whose evaluation traps is false
        Some(match r {
            Err(e) if e == TRAPPED => Ok((false, it.steps)),
            r => r.map(|b| (b, it.steps)),
        })
    }

    fn eval_term(&self, it: &mut Interp, t: TermId) -> Result<u64, String> {
        match self.terms.key(t) {
            Key::Const(_, b) => Ok(*b),
            Key::Call(f, args, _) => {
                let vals: Vec<u64> = args
                    .iter()
                    .map(|a| self.terms.as_const(*a).unwrap_or(0))
                    .collect();
                match it.call(*f as usize, &vals) {
                    Ok(r) => r.first().copied().ok_or_else(|| "no result".into()),
                    Err(EvalErr::Budget) => Err(format!(
                        "evaluation exceeded {} steps",
                        super::eval::EVAL_BUDGET
                    )),
                    Err(EvalErr::Trap(_)) => Err(TRAPPED.into()),
                    Err(EvalErr::Unsupported(m)) => Err(format!("cannot evaluate: {m}")),
                    Err(EvalErr::CheckFailed { msg, .. }) => Err(msg),
                }
            }
            Key::Float(name, args) => {
                let vals: Vec<u64> = args
                    .iter()
                    .map(|a| self.eval_term(it, *a))
                    .collect::<Result<_, _>>()?;
                super::eval::eval_fop(name, &vals).map_err(|trap| {
                    if trap {
                        TRAPPED.to_string()
                    } else {
                        format!("cannot evaluate {name}")
                    }
                })
            }
            _ => Err("cannot evaluate this atom".into()),
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
                let s = |v: u64| {
                    if ty == ValTy::I32 {
                        v as u32 as i32 as i64 as i128
                    } else {
                        v as i64 as i128
                    }
                };
                let (x, y) = if *signed {
                    (s(x), s(y))
                } else {
                    (x as i128, y as i128)
                };
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

impl<'a, 'm> Pass<'a, 'm> {
    fn hyp_list(&self, hyps: &[Entry]) -> String {
        let v: Vec<String> = hyps
            .iter()
            .map(|e| {
                format!(
                    "{} @{}",
                    self.terms.render_atom(&self.facts[e.fact as usize].atom),
                    e.line
                )
            })
            .collect();
        format!("[{}]", v.join(", "))
    }

    fn new_cup(&mut self, line: u32, r: &CupReq) -> CupId {
        let goal = self.terms.render_atom(&r.atom);
        self.cups.push(CupOut {
            line,
            operand: r.operand,
            kind: r.kind,
            goal,
            verdict: Verdict::RuntimeChecked,
            feed: Feed::Unfed,
            assumptions: SmallVec::new(),
            depends_on_checks: SmallVec::new(),
            witness: None,
            diag: None,
            atom: r.atom.clone(),
            ghost: self.ghost,
            guard: None,
            lane: vec![],
        });
        self.cup_deps.push(vec![]);
        (self.cups.len() - 1) as CupId
    }

    /// R5: feed the cups of one line. `edge` is the taken-edge fact of a br_if/br_table cup, which is
    /// looked up first and given to a feeding `prove` as an extra hypothesis. Returns the cup ids
    /// and the facts produced by prove/evaluation (not yet entered).
    pub fn feed(
        &mut self,
        line: u32,
        reqs: &[CupReq],
        edge: Option<Entry>,
        lemma_line: bool,
    ) -> (Vec<CupId>, Vec<FactId>) {
        let ids: Vec<CupId> = reqs.iter().map(|r| self.new_cup(line, r)).collect();
        if let Some(e) = edge {
            for &c in &ids {
                self.cups[c as usize].guard = Some(self.facts[e.fact as usize].atom.clone());
            }
        }
        let mut fed = vec![false; ids.len()];
        let mut produced: Vec<(usize, FactId)> = vec![];
        if let Some(end) = self.dead {
            for &c in &ids {
                self.cups[c as usize].feed = Feed::DeadCode { ended_at: end };
                self.cups[c as usize].verdict = Verdict::Proven;
            }
            self.pending.clear();
            return (ids, vec![]);
        }
        // lookup, then evaluation
        for (i, r) in reqs.iter().enumerate() {
            let c = ids[i] as usize;
            if let Some(e) = self.lookup(&r.atom, edge) {
                let origin_line = self.facts[e.fact as usize].line;
                self.cups[c].feed = Feed::Lookup {
                    fact: e.fact,
                    origin_line,
                };
                self.cups[c].verdict = Verdict::Proven;
                self.cup_deps[c] = vec![Dep::Fact(e.fact)];
                fed[i] = true;
                continue;
            }
            match self.eval_atom(&r.atom) {
                Some(Ok((true, steps))) => {
                    self.cups[c].feed = Feed::Eval { steps };
                    self.cups[c].verdict = Verdict::Proven;
                    fed[i] = true;
                    if !lemma_line {
                        let f = self.new_fact(
                            r.atom.clone(),
                            line,
                            "evaluation",
                            vec![Dep::Cup(c as CupId)],
                        );
                        produced.push((i, f));
                    }
                }
                Some(Ok((false, _))) => {
                    let g = self.cups[c].goal.clone();
                    self.cups[c].verdict = Verdict::Refuted;
                    self.cups[c].witness = Some(Witness::Eval { value: 0 });
                    self.cups[c].diag = Some(format!("⟨{g}⟩ is false (evaluated)"));
                    fed[i] = true;
                }
                Some(Err(msg)) => self.cups[c].diag = Some(msg),
                None => {}
            }
        }
        // pending prove outputs feed the first cups that neither lookup nor evaluation fed (R32)
        for (i, r) in reqs.iter().enumerate() {
            if fed[i] || self.pending.is_empty() {
                continue;
            }
            let p = self.pending.remove(0);
            let c = ids[i] as usize;
            if let Some(msg) = &p.failed {
                self.cups[c].diag = Some(format!("the prove at line {} failed: {msg}", p.line));
                continue;
            }
            let mut hyps = p.hyps.clone();
            if let Some(e) = edge {
                hyps.push(e);
            }
            let atoms: Vec<Atom> = hyps
                .iter()
                .map(|e| self.facts[e.fact as usize].atom.clone())
                .collect();
            let (terms, mut env) = self.solver_env();
            let mut s = Solver::new(terms, &mut env);
            let out = s.prove(&atoms, &r.atom);
            match out {
                Outcome::Valid { wraps } => {
                    self.cups[c].feed = Feed::Prove {
                        prove_line: p.line,
                        hyps: hyps.iter().map(|e| e.fact).collect(),
                        hyp_lines: hyps.iter().map(|e| e.line).collect(),
                        wraps_removed: wraps.into_iter().collect(),
                    };
                    self.cups[c].verdict = Verdict::Proven;
                    self.cup_deps[c] = hyps.iter().map(|e| Dep::Fact(e.fact)).collect();
                    fed[i] = true;
                    let f =
                        self.new_fact(r.atom.clone(), line, "prove", vec![Dep::Cup(c as CupId)]);
                    produced.push((i, f));
                }
                other => {
                    let hl = self.hyp_list(&hyps);
                    let msg = match other {
                        Outcome::NotImplied(m) => {
                            let cm: Vec<String> =
                                m.iter().map(|(n, v)| format!("{n}={v}")).collect();
                            format!(
                                "not implied by {hl}: {}",
                                if cm.is_empty() {
                                    "no constraint on the inputs".into()
                                } else {
                                    cm.join(", ")
                                }
                            )
                        }
                        Outcome::Inexact(s) | Outcome::Cap(s) => format!("{s}; hypotheses {hl}"),
                        Outcome::Valid { .. } => unreachable!(),
                    };
                    self.line_errors.push((p.line, msg.clone()));
                    self.cups[c].diag = Some(format!("the prove at line {} failed: {msg}", p.line));
                }
            }
        }
        if !lemma_line {
            for p in self.pending.drain(..) {
                if p.failed.is_none() {
                    self.line_errors
                        .push((p.line, "prove has nothing to feed".into()));
                }
            }
        }
        // unfed cups: runtime checks (gradual) or errors (strict, ghost)
        for (i, r) in reqs.iter().enumerate() {
            if fed[i] {
                continue;
            }
            let c = ids[i] as usize;
            let g = self.cups[c].goal.clone();
            let base = format!("needs ⟨{g}⟩; nothing feeds it");
            let what = match r.kind {
                CupKind::ResultRefinement => format!("result {base}"),
                CupKind::LoopEntry => format!("loop entry {base}"),
                CupKind::BackEdge => format!("back-edge {base}"),
                CupKind::False => "reachable: needs False; nothing feeds it".into(),
                _ => base,
            };
            let mut d = match self.cups[c].diag.take() {
                Some(x) => format!("{what} ({x})"),
                None => what,
            };
            // the stale-fact hint first: it names the lines to look at, and a pinned note on a
            // wide line is ellipsized at its end (review 20 D.2.5)
            if let Some(h) = self.stale_hint(&r.atom) {
                d = format!("{h}; {d}");
            }
            // strict mode (§4.1): every unfed cup is an error, as in ghost code
            if self.ghost || !self.cx.gradual {
                let e = if self.ghost {
                    d.clone()
                } else {
                    format!("strict: {d}")
                };
                self.line_errors.push((line, e));
            }
            // the lane snapshot (§7.3): in-scope facts, top first, with birth lines
            self.cups[c].lane = self
                .lane
                .iter()
                .rev()
                .take(8)
                .map(|e| {
                    (
                        e.line,
                        self.terms.render_atom(&self.facts[e.fact as usize].atom),
                    )
                })
                .collect();
            self.cups[c].diag = Some(d);
        }
        produced.sort_by_key(|x| x.0);
        (ids, produced.into_iter().map(|x| x.1).collect())
    }

    /// Feed the cups of a line and enter what prove/evaluation produced (the common case).
    pub fn feed_enter(&mut self, line: u32, reqs: &[CupReq]) -> Vec<CupId> {
        let (ids, produced) = self.feed(line, reqs, None, false);
        for f in produced {
            self.lane.push(Entry { fact: f, line });
        }
        ids
    }

    fn fresh_eps(&mut self) -> u32 {
        self.next_eps += 1;
        self.next_eps
    }

    fn pop(&mut self) -> TermId {
        let h = self.frames.last().map(|f| f.height).unwrap_or(0);
        if self.stack.len() > h {
            return self.stack.pop().unwrap();
        }
        // stack-polymorphic dead code (or an invalid program): a fresh value
        self.terms.leaf(ValTy::I32, "#dead", None)
    }

    fn popn(&mut self, n: usize) -> Vec<TermId> {
        let mut v: Vec<TermId> = (0..n).map(|_| self.pop()).collect();
        v.reverse();
        v
    }

    fn push(&mut self, t: TermId) {
        self.mark_real(t);
        self.slot_ids.push((self.line, t));
        if self.dead.is_none()
            && matches!(
                self.terms.key(t),
                Key::Leaf(_) | Key::Load(..) | Key::Float(..) | Key::Call(..)
            )
        {
            self.births.push(Birth {
                term: t,
                line: self.line,
                how: Capture::Top,
            });
        }
        self.stack.push(t);
    }

    fn birth(&mut self, t: TermId, line: u32, how: Capture) {
        if self.dead.is_none() {
            self.births.push(Birth { term: t, line, how });
        }
    }

    /// An arm or branch edge whose condition is false on its own (it folds to the constant
    /// False). Control never takes it, so it is dead code, not code entered under a False fact
    /// (research/22 B3). Deciding it needs no fact, so nothing a dead-code verdict rests on is lost.
    /// Conditions false only by reasoning are left to the probe of [`Pass::lane_is_false`].
    fn impossible(&mut self, a: &Atom) -> bool {
        *a == Atom::False
    }

    /// Does the current lane (plus `extra`) prove False? Asked with the whole lane, and if that
    /// does not decide it, with its 8 most recent entries (what a `prove 8` here could use).
    fn lane_is_false(&mut self, extra: &[Entry]) -> bool {
        let atoms: Vec<Atom> = self
            .lane
            .iter()
            .chain(extra)
            .map(|e| self.facts[e.fact as usize].atom.clone())
            .collect();
        if atoms.contains(&Atom::False) {
            return true;
        }
        let mut tries = vec![atoms.clone()];
        if atoms.len() > 8 {
            tries.push(atoms[atoms.len() - 8..].to_vec());
        }
        for hyps in tries {
            let (terms, mut env) = self.solver_env();
            let mut s = Solver::new(terms, &mut env);
            if let Outcome::Valid { .. } = s.prove(&hyps, &Atom::False) {
                return true;
            }
        }
        false
    }

    fn go_dead(&mut self, line: u32) {
        if self.dead.is_none() {
            self.dead = Some(line);
            self.enter(Atom::False, line, "dead code", vec![]);
        }
    }

    fn local_index(&self, n: &str) -> Option<usize> {
        super::eval::resolve_local(&self.locs, n)
    }

    fn handle_index(&self, n: &str) -> Option<usize> {
        self.handle_names.iter().position(|x| x == n)
    }

    fn global_index(&self, n: &str) -> Option<usize> {
        let gs = &self.cx.m.globals;
        gs.iter()
            .position(|g| g.name.as_deref() == Some(n))
            .or_else(|| n.parse().ok().filter(|i: &usize| *i < gs.len()))
    }

    /// A refined global's refinement about its current value, and what it rests on (R9, R14).
    fn global_fact(&mut self, i: usize) -> Option<(Atom, Vec<Dep>)> {
        let mut deps = self.cx.global_deps.get(i)?.clone()?;
        let r = self.cx.m.globals[i].ty.refine.clone()?;
        let a = self.inst_atom(&r, &vec![], Some(self.globals[i]));
        if let Some(g) = self.global_groups[i] {
            deps.push(Dep::Group(g));
        }
        Some((a, deps))
    }

    /// R14 for globals: does the initializer satisfy the refinement (evaluated, R28)?
    fn global_init_holds(&mut self, i: usize) -> bool {
        let g = &self.cx.m.globals[i];
        let (Some(r), Some(init)) = (g.ty.refine.clone(), g.init) else {
            return false;
        };
        let v = self.terms.konst(g.ty.ty, init);
        match self.inst_atom(&r, &vec![], Some(v)) {
            Atom::True => true,
            Atom::False => false,
            a => matches!(self.eval_atom(&a), Some(Ok((true, _)))),
        }
    }

    fn fresh_globals(&mut self, line: u32) {
        for (i, g) in self.cx.m.globals.iter().enumerate() {
            if g.mutable {
                let name = g.name.clone().unwrap_or_else(|| format!("global {i}"));
                self.globals[i] = self.terms.leaf(g.ty.ty, name, None);
                self.birth(self.globals[i], line, Capture::Global(i as u32));
                if let Some((a, deps)) = self.global_fact(i) {
                    self.enter(a, line, "global refinement", deps);
                }
            }
        }
    }

    pub fn new(cx: &'a ModCtx<'m>, f: usize) -> Self {
        let func = &cx.m.funcs[f];
        let locs = value_locals(cx.m, f);
        let mut loc_ref: Vec<Option<Refined>> = vec![];
        for (_, _, r) in func.value_params() {
            loc_ref.push(r.refine.as_ref().map(|_| r.clone()));
        }
        let mut handle_names = vec![];
        for p in &func.header.params {
            if let (Decl::Fact(_), Some(n)) = (&p.decl, &p.name) {
                handle_names.push(n.clone());
            }
        }
        for l in &func.locals {
            match &l.kind {
                LocalKind::Val(r) => loc_ref.push(r.refine.as_ref().map(|_| r.clone())),
                LocalKind::Fact => handle_names.extend(l.name.clone()),
            }
        }
        let fnames = cx.m.funcs.iter().map(|g| g.name()).collect();
        let ghost =
            func.is_lemma() || func.is_axiom() || cx.info[f].is_pred || cx.info[f].is_measure;
        let nh = handle_names.len();
        Pass {
            dead_lines: vec![],
            false_ctx_lines: vec![],
            cx,
            f,
            terms: Terms::new(fnames),
            facts: vec![],
            lane: vec![],
            stack: vec![],
            locs,
            loc_ref,
            locals: vec![],
            entry: vec![],
            handle_names,
            handles: vec![None; nh],
            globals: vec![],
            eps: 0,
            next_eps: 0,
            frames: vec![],
            dead: None,
            pending: vec![],
            cups: vec![],
            cup_deps: vec![],
            groups: vec![],
            local_groups: vec![],
            global_groups: vec![],
            real: vec![],
            real_log: vec![],
            unfold_memo: HashMap::new(),
            line_errors: vec![],
            slot_ids: vec![],
            births: vec![],
            sets: vec![],
            fray: HashMap::new(),
            ghost,
            line: func.header_line,
        }
    }

    /// R14: function entry.
    fn entry(&mut self) {
        let cx = self.cx;
        let func = &cx.m.funcs[self.f];
        let hl = func.header_line;
        self.line = hl;
        for (i, r) in self.loc_ref.clone().iter().enumerate() {
            let _ = i;
            self.local_groups.push(r.as_ref().map(|_| {
                self.groups.push(vec![]);
                (self.groups.len() - 1) as u32
            }));
        }
        for g in &cx.m.globals {
            self.global_groups.push(g.ty.refine.as_ref().map(|_| {
                self.groups.push(vec![]);
                (self.groups.len() - 1) as u32
            }));
        }
        // parameters
        let mut vi = 0;
        let mut hi = 0;
        let mut bind: Bind = vec![];
        for p in &func.header.params {
            match &p.decl {
                Decl::Val(r) => {
                    let name = p.name.clone().unwrap_or_else(|| format!("param {vi}"));
                    let t = self.terms.leaf(r.ty, name.clone(), None);
                    self.birth(t, hl, Capture::Param(vi as u32));
                    self.entry.push(t);
                    self.locals.push(t);
                    bind.push((name, t));
                    if let Some(e) = &r.refine {
                        let a = self.inst_atom(e, &bind, Some(t));
                        self.enter(a, hl, "entry (parameter refinement)", vec![]);
                    }
                    vi += 1;
                }
                Decl::Fact(e) => {
                    let a = self.inst_atom(e, &bind, None);
                    let fct = self.enter(a, hl, "entry (fact parameter)", vec![]);
                    if p.name.is_some() {
                        self.handles[hi] = Some(Entry {
                            fact: fct,
                            line: hl,
                        });
                        hi += 1;
                    }
                }
            }
        }
        // ordinary locals start at 0; refined ones have a cup (R14)
        let nparams = self.locals.len();
        for (i, (_, ty)) in self.locs.clone().iter().enumerate().skip(nparams) {
            let z = self.terms.konst(*ty, 0);
            self.locals.push(z);
            if let Some(r) = self.loc_ref[i].clone() {
                let line = func
                    .locals
                    .iter()
                    .filter(|l| matches!(l.kind, LocalKind::Val(_)))
                    .nth(i - nparams)
                    .map(|l| l.line)
                    .unwrap_or(hl);
                self.line = line;
                if expr_reads_mem(cx, r.refine.as_ref().unwrap()) {
                    self.line_errors.push((
                        line,
                        "a local's refinement may not read memory: a store would falsify it unseen (R7)"
                            .into(),
                    ));
                }
                let b = self.cur_bind();
                let a = self.inst_atom(r.refine.as_ref().unwrap(), &b, Some(z));
                let ids = self.feed_enter(
                    line,
                    &[CupReq {
                        kind: CupKind::LocalInit,
                        operand: None,
                        atom: a,
                    }],
                );
                if let Some(g) = self.local_groups[i] {
                    self.groups[g as usize].push(Dep::Cup(ids[0]));
                }
            }
        }
        // globals
        for g in &cx.m.globals {
            let t = match (g.mutable, g.init) {
                (false, Some(b)) => self.terms.konst(g.ty.ty, b),
                _ => self.terms.leaf(
                    g.ty.ty,
                    g.name.clone().unwrap_or_else(|| "global".into()),
                    None,
                ),
            };
            if g.mutable {
                let gi = self.globals.len() as u32;
                self.birth(t, hl, Capture::Global(gi));
            }
            self.globals.push(t);
        }
        for i in 0..cx.m.globals.len() {
            if let Some((a, deps)) = self.global_fact(i) {
                self.enter(a, hl, "global refinement", deps);
            }
        }
        let results: Vec<Refined> = func.value_results().into_iter().cloned().collect();
        let bt = BlockType {
            label: None,
            facts: vec![],
            params: vec![],
            results,
        };
        self.frames.push(self.frame(FKind::Func, bt, hl));
    }

    fn frame(&self, kind: FKind, bt: BlockType, line: u32) -> Frame {
        Frame {
            kind,
            bt,
            line,
            lane_mark: self.lane.len(),
            height: self.stack.len(),
            locals: self.locals.clone(),
            globals: self.globals.clone(),
            eps: self.eps,
            handles: self.handles.clone(),
            real_mark: self.real_log.len(),
            edges: vec![],
            cond: None,
            in_else: false,
            entered_dead: self.dead,
            groups: vec![],
        }
    }
}

/// R27: a trapping truncation `name` from `fty` is defined iff lo < x < hi, with lo and hi as
/// `fty` bit patterns: the nearest representable values just outside the target's range. In f32
/// the value below −2^31 is −2^31 − 256 (and below −2^63, −2^63 − 2^40): −2^31 itself is valid.
fn trunc_bounds(name: &str, fty: ValTy) -> Option<(u64, u64)> {
    let (to, op) = name.split_once('.')?;
    let signed = op.ends_with("_s");
    let f32_ = fty == ValTy::F32;
    let (lo, hi): (f64, f64) = match (to, signed, f32_) {
        ("i32", true, false) => (-2147483649.0, 2147483648.0),
        ("i32", true, true) => (-2147483904.0, 2147483648.0),
        ("i32", false, _) => (-1.0, 4294967296.0),
        ("i64", true, false) => (-9223372036854777856.0, 9223372036854775808.0),
        ("i64", true, true) => (-9223373136366403584.0, 9223372036854775808.0),
        _ => (-1.0, 18446744073709551616.0),
    };
    Some(if f32_ {
        ((lo as f32).to_bits() as u64, (hi as f32).to_bits() as u64)
    } else {
        (lo.to_bits(), hi.to_bits())
    })
}

impl<'a, 'm> Pass<'a, 'm> {
    fn call_atom_bind(&self, g: usize, args: &[TermId]) -> Bind {
        let func = &self.cx.m.funcs[g];
        func.value_params()
            .zip(args.iter())
            .filter_map(|((_, p, _), a)| p.name.clone().map(|n| (n, *a)))
            .collect()
    }

    /// The measure cup of R31 at a recursive call/lemma site with arguments `args`. Never dropped:
    /// without a usable measure the cup is still there, as an unprovable obligation, with an error.
    fn measure_cup(&mut self, args: &[TermId]) -> CupReq {
        let atom = match self.measure_atom(args) {
            Ok(a) => a,
            Err(msg) => {
                self.line_errors.push((self.line, msg));
                let t = self.terms.leaf(ValTy::I32, "μ↓ (no usable measure)", None);
                Atom::Bool { t, neg: false }
            }
        };
        CupReq {
            kind: CupKind::Measure,
            operand: None,
            atom,
        }
    }

    fn measure_atom(&mut self, args: &[TermId]) -> Result<Atom, String> {
        let cx = self.cx;
        let name = cx.m.funcs[self.f].name();
        let mf = cx.info[self.f].measure.ok_or_else(|| {
            format!(
                "{name} is recursive without measure:{}",
                name.trim_start_matches('$')
            )
        })?;
        measure_shape(cx.m, self.f, mf)?;
        let a = call_term(cx.m, &cx.info, &mut self.terms, mf, args, self.eps)
            .ok_or("measure has no result")?;
        let entry = self.entry.clone();
        let b = call_term(cx.m, &cx.info, &mut self.terms, mf, &entry, self.eps)
            .ok_or("measure has no result")?;
        Ok(Atom::cmp(super::term::Rel::Lt, false, a, b))
    }

    fn bounds_cup(&mut self, addr: TermId, offset: u64, bytes: u32) -> CupReq {
        let m = self.cx.mem.unwrap_or(0) as i128;
        let k = m - offset as i128 - bytes as i128;
        let atom = if k < 0 {
            Atom::False
        } else {
            let kc = self.terms.konst(ValTy::I32, k as u64);
            Atom::cmp(super::term::Rel::Le, false, addr, kc)
        };
        CupReq {
            kind: CupKind::Bounds,
            operand: Some(0),
            atom,
        }
    }

    fn do_call(&mut self, line: u32, g: usize) {
        let cx = self.cx;
        let callee = &cx.m.funcs[g];
        let np = callee.value_params().count();
        let args = self.popn(np);
        let bind = self.call_atom_bind(g, &args);
        let mut reqs = vec![];
        let mut vi = 0usize;
        for (pi, p) in callee.header.params.iter().enumerate() {
            match &p.decl {
                Decl::Val(r) => {
                    if let Some(e) = &r.refine {
                        let a = self.inst_atom(e, &bind, Some(args[vi]));
                        reqs.push(CupReq {
                            kind: CupKind::Refinement { param: pi as u32 },
                            operand: Some(vi as u8),
                            atom: a,
                        });
                    }
                    vi += 1;
                }
                Decl::Fact(e) => {
                    let a = self.inst_atom(e, &bind, None);
                    reqs.push(CupReq {
                        kind: CupKind::FactParam { param: pi as u32 },
                        operand: None,
                        atom: a,
                    });
                }
            }
        }
        if g == self.f
            && (cx.info[g].is_pred || cx.info[g].is_measure || cx.info[g].measure.is_some())
        {
            reqs.push(self.measure_cup(&args));
        }
        let ids = self.feed_enter(line, &reqs);
        let impure = cx.info[g].impure.is_some();
        if impure {
            self.eps = self.fresh_eps();
            self.fresh_globals(line);
        }
        let results = callee.value_results();
        let r = if let Some(rt) = results.first() {
            let t = if impure {
                self.terms
                    .leaf(rt.ty, format!("{}(…)@{line}", callee.name()), None)
            } else {
                call_term(cx.m, &cx.info, &mut self.terms, g, &args, self.eps).unwrap()
            };
            self.push(t);
            Some(t)
        } else {
            None
        };
        let mut deps: Vec<Dep> = ids.iter().map(|c| Dep::Cup(*c)).collect();
        if callee.imported {
            deps.push(Dep::Assume(callee.header_line, false));
        }
        for d in &callee.header.results {
            let a = match d {
                Decl::Val(rf) => match (&rf.refine, r) {
                    (Some(e), Some(rv)) => self.inst_atom(e, &bind, Some(rv)),
                    _ => continue,
                },
                Decl::Fact(e) => self.inst_atom(e, &bind, None),
            };
            self.enter(a, line, "call result", deps.clone());
        }
    }

    fn set_local(&mut self, line: u32, i: usize, t: TermId) {
        let mut reqs = vec![];
        let mut groups = vec![];
        if let Some(r) = self.loc_ref[i].clone() {
            let b = self.cur_bind();
            let a = self.inst_atom(r.refine.as_ref().unwrap(), &b, Some(t));
            reqs.push(CupReq {
                kind: CupKind::Refinement { param: i as u32 },
                operand: Some(0),
                atom: a,
            });
            groups.push(self.local_groups[i]);
        }
        // R7: a refined local's refinement is its invariant; writing another local it names
        // must keep it true too, or R8 would re-enter it at a join against the new value
        if let Some(n) = self.locs[i].0.clone() {
            for j in 0..self.loc_ref.len() {
                let Some(r) = self.loc_ref[j].clone() else {
                    continue;
                };
                if j == i || !expr_names(r.refine.as_ref().unwrap(), &n) {
                    continue;
                }
                let mut b = self.cur_bind();
                b.push((n.clone(), t));
                let a = self.inst_atom(r.refine.as_ref().unwrap(), &b, Some(self.locals[j]));
                reqs.push(CupReq {
                    kind: CupKind::Refinement { param: j as u32 },
                    operand: None,
                    atom: a,
                });
                groups.push(self.local_groups[j]);
            }
        }
        let ids = self.feed_enter(line, &reqs);
        for (id, g) in ids.iter().zip(groups) {
            if let Some(g) = g {
                self.groups[g as usize].push(Dep::Cup(*id));
            }
        }
        let old = self.locals[i];
        if old != t && self.dead.is_none() {
            self.sets.push((i, old, t, line));
            for e in self.lane.clone() {
                if !self.fray.contains_key(&e.fact)
                    && self.atom_mentions(&self.facts[e.fact as usize].atom, &|_, x| x == old)
                {
                    self.fray.insert(e.fact, line);
                }
            }
        }
        self.locals[i] = t;
    }

    fn mentions(
        &self,
        t: TermId,
        p: &dyn Fn(&Key, TermId) -> bool,
        seen: &mut Vec<TermId>,
    ) -> bool {
        if seen.contains(&t) {
            return false;
        }
        seen.push(t);
        let k = self.terms.key(t);
        if p(k, t) {
            return true;
        }
        match k {
            Key::Op(_, _, a) | Key::Float(_, a) => a.iter().any(|x| self.mentions(*x, p, seen)),
            Key::Call(_, a, _) => a.iter().any(|x| self.mentions(*x, p, seen)),
            Key::Load(.., a, _) => self.mentions(*a, p, seen),
            Key::Ite(c, a, b) => [c, a, b].iter().any(|x| self.mentions(**x, p, seen)),
            _ => false,
        }
    }

    fn atom_mentions(&self, a: &Atom, p: &dyn Fn(&Key, TermId) -> bool) -> bool {
        let mut seen = vec![];
        match a {
            Atom::Cmp { a, b, .. } => {
                self.mentions(*a, p, &mut seen) || self.mentions(*b, p, &mut seen)
            }
            Atom::Bool { t, .. } => self.mentions(*t, p, &mut seen),
            Atom::Or(x, y) => self.atom_mentions(x, p) || self.atom_mentions(y, p),
            _ => false,
        }
    }

    /// R5's stale-fact hint: a lane fact about the value a local held before a rebinding that the
    /// goal's value replaced.
    fn stale_hint(&self, goal: &Atom) -> Option<String> {
        for &(i, old, new, line) in self.sets.iter().rev() {
            if !self.atom_mentions(goal, &|_, x| x == new) {
                continue;
            }
            if let Some(e) =
                self.lane.iter().rev().find(|e| {
                    self.atom_mentions(&self.facts[e.fact as usize].atom, &|_, x| x == old)
                })
            {
                let f = &self.facts[e.fact as usize];
                let name = self.locs[i]
                    .0
                    .clone()
                    .unwrap_or_else(|| format!("local {i}"));
                return Some(format!(
                    "⟨{}⟩ (line {}) is about the old {name} (set at line {line})",
                    self.terms.render_atom(&f.atom),
                    f.line
                ));
            }
        }
        None
    }

    /// One body line.
    fn step(&mut self, pc: usize, line: u32, ins: &Ins, tab: &[(usize, usize)]) {
        self.line = line;
        match ins {
            Ins::Prove(k) => {
                if self.dead.is_some() {
                    return;
                }
                let k = *k as usize;
                if k > self.lane.len() {
                    let msg = format!("only {} facts in scope", self.lane.len());
                    self.line_errors.push((line, msg.clone()));
                    self.pending.push(Pending {
                        line,
                        hyps: vec![],
                        failed: Some(msg),
                    });
                } else {
                    let hyps: Vec<Entry> = self.lane.iter().rev().take(k).copied().collect();
                    self.pending.push(Pending {
                        line,
                        hyps,
                        failed: None,
                    });
                }
            }
            Ins::Lemma(name, args) => self.lemma_line(line, name, args),
            Ins::Unfold(name, args) => self.unfold_line(line, name, args),
            Ins::Assume(e) if self.cx.info[self.f].is_pred || self.cx.info[self.f].is_measure => {
                // N4: a predicate must be total; an assumed fact could discharge its trap cups
                let _ = e;
                self.line_errors.push((
                    line,
                    "assume is not allowed inside a predicate or measure (R34)".into(),
                ));
            }
            Ins::Assume(e) => {
                let b = self.cur_bind();
                let a = self.inst_atom(e, &b, None);
                self.enter(a, line, "assume", vec![Dep::Assume(line, false)]);
            }
            Ins::LocalGet(n) | Ins::LocalSet(n) | Ins::LocalTee(n)
                if self.local_index(n).is_none() =>
            {
                let Some(h) = self.handle_index(n) else {
                    self.line_errors.push((line, format!("unknown local {n}")));
                    return;
                };
                match ins {
                    Ins::LocalGet(_) => match self.handles[h] {
                        Some(e) if self.lane.iter().any(|x| x.fact == e.fact) => {
                            self.lane.push(Entry { fact: e.fact, line })
                        }
                        Some(e) => self.line_errors.push((
                            line,
                            format!("{n} holds a fact that ended (born at line {})", e.line),
                        )),
                        None => self.line_errors.push((line, format!("{n} holds no fact"))),
                    },
                    _ => self.handles[h] = self.lane.last().copied(),
                }
            }
            Ins::Block(..)
            | Ins::Else
            | Ins::End
            | Ins::Br(_)
            | Ins::BrIf(_)
            | Ins::BrTable(_)
            | Ins::Return => self.control(pc, line, ins, tab),
            Ins::Nop => {
                self.feed_enter(line, &[]);
            }
            Ins::Unreachable => {
                self.feed_enter(
                    line,
                    &[CupReq {
                        kind: CupKind::False,
                        operand: None,
                        atom: Atom::False,
                    }],
                );
                self.go_dead(line);
            }
            Ins::Drop => {
                self.feed_enter(line, &[]);
                self.pop();
            }
            Ins::Select => {
                self.feed_enter(line, &[]);
                let c = self.pop();
                let b = self.pop();
                let a = self.pop();
                let ty = self.terms.ty(a);
                let t = self.terms.intern(Key::Ite(c, a, b), ty);
                self.push(t);
            }
            Ins::Const(ty, b) => {
                self.feed_enter(line, &[]);
                let t = self.terms.konst(*ty, *b);
                self.push(t);
            }
            Ins::Int(op, w) => {
                let n = if op.unary() { 1 } else { 2 };
                let args = self.popn(n);
                let mut reqs = vec![];
                if matches!(op, IOp::DivU | IOp::DivS | IOp::RemU | IOp::RemS) {
                    let z = self.terms.konst(*w, 0);
                    let a = self.terms.mk_eq(args[1], z, false);
                    reqs.push(CupReq {
                        kind: CupKind::DivByZero,
                        operand: Some(1),
                        atom: a,
                    });
                    if *op == IOp::DivS {
                        let m1 = self.terms.konst(*w, u64::MAX);
                        let min = self.terms.konst(
                            *w,
                            if *w == ValTy::I32 {
                                0x8000_0000
                            } else {
                                1 << 63
                            },
                        );
                        let x = self.terms.mk_eq(args[1], m1, false);
                        let y = self.terms.mk_eq(args[0], min, false);
                        reqs.push(CupReq {
                            kind: CupKind::DivOverflow,
                            operand: None,
                            atom: Atom::Or(Box::new(x), Box::new(y)),
                        });
                    }
                }
                self.feed_enter(line, &reqs);
                let t = self.terms.op(*op, *w, &args);
                self.push(t);
            }
            Ins::Float {
                name,
                ins: tys,
                out,
                trap,
            } => {
                let args = self.popn(tys.len());
                let mut reqs = vec![];
                if *trap && let Some((lo, hi)) = trunc_bounds(name, tys[0]) {
                    let fty = tys[0];
                    let (l, h) = (self.terms.konst(fty, lo), self.terms.konst(fty, hi));
                    let gt = self.terms.intern(
                        Key::Float(
                            format!("{}.gt", fty.name()),
                            [args[0], l].into_iter().collect(),
                        ),
                        ValTy::I32,
                    );
                    let lt = self.terms.intern(
                        Key::Float(
                            format!("{}.lt", fty.name()),
                            [args[0], h].into_iter().collect(),
                        ),
                        ValTy::I32,
                    );
                    reqs.push(CupReq {
                        kind: CupKind::Conversion,
                        operand: Some(0),
                        atom: Atom::Bool { t: gt, neg: false },
                    });
                    reqs.push(CupReq {
                        kind: CupKind::Conversion,
                        operand: Some(0),
                        atom: Atom::Bool { t: lt, neg: false },
                    });
                }
                self.feed_enter(line, &reqs);
                let t = self
                    .terms
                    .intern(Key::Float(name.clone(), args.into_iter().collect()), *out);
                self.push(t);
            }
            Ins::LocalGet(n) => {
                self.feed_enter(line, &[]);
                let i = self.local_index(n).unwrap();
                let t = self.locals[i];
                self.slot_ids.push((line, t));
                self.stack.push(t);
            }
            Ins::LocalSet(n) | Ins::LocalTee(n) => {
                let i = self.local_index(n).unwrap();
                let t = self.pop();
                self.set_local(line, i, t);
                if matches!(ins, Ins::LocalTee(_)) {
                    self.stack.push(t);
                }
            }
            Ins::GlobalGet(n) => {
                self.feed_enter(line, &[]);
                match self.global_index(n) {
                    Some(i) => {
                        let t = self.globals[i];
                        self.stack.push(t);
                    }
                    None => self.line_errors.push((line, format!("unknown global {n}"))),
                }
            }
            Ins::GlobalSet(n) => {
                let t = self.pop();
                let Some(i) = self.global_index(n) else {
                    self.line_errors.push((line, format!("unknown global {n}")));
                    return;
                };
                let mut reqs = vec![];
                if let Some(e) = self.cx.m.globals[i].ty.refine.clone()
                    && self.cx.global_deps[i].is_some()
                {
                    let a = self.inst_atom(&e, &vec![], Some(t));
                    reqs.push(CupReq {
                        kind: CupKind::Refinement { param: i as u32 },
                        operand: Some(0),
                        atom: a,
                    });
                }
                let ids = self.feed_enter(line, &reqs);
                if let (Some(g), Some(c)) = (self.global_groups[i], ids.first()) {
                    self.groups[g as usize].push(Dep::Cup(*c));
                }
                self.globals[i] = t;
            }
            Ins::Load(ma) => {
                let a = self.pop();
                let req = self.bounds_cup(a, ma.offset, ma.bytes);
                self.feed_enter(line, &[req]);
                let t = self.terms.intern(
                    Key::Load(ma.ty, ma.bytes, ma.signed, ma.offset, a, self.eps),
                    ma.ty,
                );
                self.push(t);
            }
            Ins::Store(ma) => {
                let _v = self.pop();
                let a = self.pop();
                let req = self.bounds_cup(a, ma.offset, ma.bytes);
                self.feed_enter(line, &[req]);
                let old = self.eps;
                let epoch_of = move |k: &Key, _: TermId| matches!(k, Key::Call(_, _, e) | Key::Load(.., e) if *e == old);
                for e in self.lane.clone() {
                    if !self.fray.contains_key(&e.fact)
                        && self.atom_mentions(&self.facts[e.fact as usize].atom, &epoch_of)
                    {
                        self.fray.insert(e.fact, line);
                    }
                }
                self.eps = self.fresh_eps();
            }
            Ins::MemorySize => {
                self.feed_enter(line, &[]);
                let t = self
                    .terms
                    .leaf(ValTy::I32, format!("memory.size@{line}"), None);
                self.push(t);
                let min = self
                    .terms
                    .konst(ValTy::I32, self.cx.mem.unwrap_or(0) / 65536);
                self.enter(
                    Atom::cmp(super::term::Rel::Le, false, min, t),
                    line,
                    "memory.size",
                    vec![],
                );
            }
            Ins::MemoryGrow => {
                self.feed_enter(line, &[]);
                self.pop();
                self.eps = self.fresh_eps();
                let t = self
                    .terms
                    .leaf(ValTy::I32, format!("memory.grow@{line}"), None);
                self.push(t);
            }
            Ins::MemoryFill | Ins::MemoryCopy => {
                self.feed_enter(line, &[]);
                self.popn(3);
                self.eps = self.fresh_eps();
            }
            Ins::Call(name) => match self.cx.m.func_index(name) {
                Some(g) if self.cx.m.funcs[g].is_lemma() || self.cx.m.funcs[g].is_axiom() => {
                    self.line_errors.push((
                        line,
                        format!("{name} is ghost code: write `lemma {name} …`, not `call`"),
                    ));
                }
                Some(g) => self.do_call(line, g),
                None => self
                    .line_errors
                    .push((line, format!("unknown function {name}"))),
            },
            Ins::CallIndirect => {
                self.feed_enter(
                    line,
                    &[CupReq {
                        kind: CupKind::CallIndirect,
                        operand: None,
                        atom: Atom::False,
                    }],
                );
                self.pop();
                self.eps = self.fresh_eps();
                self.fresh_globals(line);
                if let Some(c) = self.cups.last_mut() {
                    c.diag = Some("call_indirect is outside v2".into());
                }
            }
        }
    }

    fn lemma_line(&mut self, line: u32, name: &str, args: &[Expr]) {
        let cx = self.cx;
        let Some(g) = cx.m.func_index(name) else {
            self.line_errors
                .push((line, format!("unknown lemma {name}")));
            return;
        };
        let lf = &cx.m.funcs[g];
        if !lf.is_lemma() && !lf.is_axiom() {
            self.line_errors.push((
                line,
                format!("{name} is not a lemma: export it as \"lemma:…\" or \"axiom:…\""),
            ));
            return;
        }
        let ptys: Vec<ValTy> = lf.value_params().map(|(_, _, r)| r.ty).collect();
        if ptys.len() != args.len() {
            self.line_errors
                .push((line, format!("{name} takes {} arguments", ptys.len())));
            return;
        }
        let b = self.cur_bind();
        let mut vals = vec![];
        for (e, ty) in args.iter().zip(ptys) {
            match self.inst(e, &b, None, Some(ty)) {
                Ok(t) => vals.push(t),
                Err(msg) => {
                    self.line_errors.push((line, msg));
                    return;
                }
            }
        }
        let bind = self.call_atom_bind(g, &vals);
        let mut reqs = vec![];
        let mut vi = 0usize;
        for (pi, p) in lf.header.params.iter().enumerate() {
            match &p.decl {
                // a refined value parameter is sugar for a fact parameter (§1.3): the lemma line
                // owes it a cup exactly as `call` does (R13, R33) — never assumed for free
                Decl::Val(r) => {
                    if let Some(e) = &r.refine {
                        let a = self.inst_atom(e, &bind, Some(vals[vi]));
                        reqs.push(CupReq {
                            kind: CupKind::Refinement { param: pi as u32 },
                            operand: None,
                            atom: a,
                        });
                    }
                    vi += 1;
                }
                Decl::Fact(e) => {
                    let a = self.inst_atom(e, &bind, None);
                    reqs.push(CupReq {
                        kind: CupKind::FactParam { param: pi as u32 },
                        operand: None,
                        atom: a,
                    });
                }
            }
        }
        if g == self.f {
            reqs.push(self.measure_cup(&vals));
        }
        let (ids, produced) = self.feed(line, &reqs, None, true);
        for f in produced {
            self.lane.push(Entry { fact: f, line });
        }
        let mut deps: Vec<Dep> = ids.iter().map(|c| Dep::Cup(*c)).collect();
        if lf.is_axiom() {
            deps.push(Dep::Assume(lf.header_line, true));
        } else if g != self.f {
            match cx.lemma_assumes.get(&g) {
                Some(a) => deps.extend(a.iter().cloned()),
                None => deps.push(Dep::Assume(lf.header_line, false)),
            }
        }
        for d in &lf.header.results {
            if let Decl::Fact(e) = d {
                let a = self.inst_atom(e, &bind, None);
                self.enter(
                    a,
                    line,
                    if lf.is_axiom() { "axiom" } else { "lemma" },
                    deps.clone(),
                );
            }
        }
    }

    fn unfold_line(&mut self, line: u32, name: &str, args: &[Expr]) {
        let cx = self.cx;
        let Some(g) = cx.m.func_index(name) else {
            self.line_errors
                .push((line, format!("unknown predicate {name}")));
            return;
        };
        if !cx.info[g].self_rec {
            self.line_errors.push((
                line,
                format!("{name} is not recursive; it unfolds automatically"),
            ));
            return;
        }
        let ptys: Vec<ValTy> = cx.m.funcs[g].value_params().map(|(_, _, r)| r.ty).collect();
        if ptys.len() != args.len() {
            self.line_errors
                .push((line, format!("{name} takes {} arguments", ptys.len())));
            return;
        }
        let b = self.cur_bind();
        let mut vals = vec![];
        for (e, ty) in args.iter().zip(ptys) {
            match self.inst(e, &b, None, Some(ty)) {
                Ok(t) => vals.push(t),
                Err(msg) => {
                    self.line_errors.push((line, msg));
                    return;
                }
            }
        }
        let Some(call) = call_term(cx.m, &cx.info, &mut self.terms, g, &vals, self.eps) else {
            return;
        };
        let ep = self.eps;
        match symex(cx.m, &cx.info, &mut self.terms, g, &vals, ep) {
            Some(body) => {
                let a = self.terms.mk_eq(call, body, true);
                self.enter(a, line, "unfold", vec![]);
            }
            None => self.line_errors.push((
                line,
                format!("{name}'s body cannot be unfolded (only straight-line code and if/else)"),
            )),
        }
    }
}

impl<'a, 'm> Pass<'a, 'm> {
    fn resolve_label(&self, l: &str) -> Option<usize> {
        if l.starts_with('$') {
            self.frames
                .iter()
                .rposition(|f| f.bt.label.as_deref() == Some(l))
        } else {
            let d: usize = l.parse().ok()?;
            self.frames.len().checked_sub(1 + d)
        }
    }

    fn arity(&self, fi: usize) -> usize {
        let f = &self.frames[fi];
        if f.kind == FKind::Loop {
            f.bt.params.len()
        } else {
            f.bt.results.len()
        }
    }

    /// Cups an edge to frame `fi` carries, given the branch values. Returns the requests and, for
    /// block/if targets, which request belongs to each declared fact and each result.
    fn edge_reqs(
        &mut self,
        fi: usize,
        values: &[TermId],
    ) -> (Vec<CupReq>, Vec<usize>, Vec<Option<usize>>) {
        let kind = self.frames[fi].kind;
        let bt = self.frames[fi].bt.clone();
        let mut reqs = vec![];
        let mut fact_ix = vec![];
        let mut res_ix = vec![];
        if kind == FKind::Func {
            let func = &self.cx.m.funcs[self.f];
            let b = self.entry_bind();
            let mut vi = 0;
            for d in &func.header.results {
                match d {
                    Decl::Val(r) => {
                        if let (Some(e), Some(v)) = (&r.refine, values.get(vi)) {
                            let a = self.inst_atom(e, &b, Some(*v));
                            reqs.push(CupReq {
                                kind: CupKind::ResultRefinement,
                                operand: Some(vi as u8),
                                atom: a,
                            });
                        }
                        vi += 1;
                    }
                    Decl::Fact(e) => {
                        let a = self.inst_atom(e, &b, None);
                        reqs.push(CupReq {
                            kind: CupKind::ResultRefinement,
                            operand: None,
                            atom: a,
                        });
                    }
                }
            }
            return (reqs, fact_ix, res_ix);
        }
        let b = self.cur_bind();
        let ck = match kind {
            FKind::Loop => CupKind::BackEdge,
            _ => CupKind::BlockFact { label: fi as u32 },
        };
        for e in &bt.facts {
            let a = self.inst_atom(e, &b, None);
            fact_ix.push(reqs.len());
            reqs.push(CupReq {
                kind: ck,
                operand: None,
                atom: a,
            });
        }
        let typs = if kind == FKind::Loop {
            &bt.params
        } else {
            &bt.results
        };
        for (j, r) in typs.iter().enumerate() {
            match (&r.refine, values.get(j)) {
                (Some(e), Some(v)) => {
                    let a = self.inst_atom(e, &b, Some(*v));
                    res_ix.push(Some(reqs.len()));
                    reqs.push(CupReq {
                        kind: ck,
                        operand: Some(j as u8),
                        atom: a,
                    });
                }
                _ => res_ix.push(None),
            }
        }
        (reqs, fact_ix, res_ix)
    }

    /// An edge from the current point to frame `fi` (R16–R21), with an optional taken-edge fact.
    fn branch(&mut self, line: u32, fi: usize, edge: Option<Entry>) {
        let n = self.arity(fi);
        let values: Vec<TermId> = self.stack[self.stack.len().saturating_sub(n)..].to_vec();
        let (reqs, fact_ix, res_ix) = self.edge_reqs(fi, &values);
        let (ids, produced) = self.feed(line, &reqs, edge, false);
        let kind = self.frames[fi].kind;
        if kind == FKind::Loop {
            let groups = self.frames[fi].groups.clone();
            for (k, &c) in ids.iter().enumerate() {
                if let Some(g) = groups.get(k) {
                    self.groups[*g as usize].push(Dep::Cup(c));
                }
            }
            return;
        }
        if kind == FKind::Func || self.dead.is_some() {
            return;
        }
        let mark = self.frames[fi].lane_mark;
        let mut lane: Vec<Entry> = self.lane[mark.min(self.lane.len())..].to_vec();
        lane.extend(edge);
        lane.extend(produced.into_iter().map(|f| Entry { fact: f, line }));
        let e = Edge {
            lane,
            locals: self.locals.clone(),
            globals: self.globals.clone(),
            eps: self.eps,
            values,
            fact_cups: fact_ix.iter().map(|i| ids[*i]).collect(),
            result_cups: res_ix.iter().map(|i| i.map(|i| ids[i])).collect(),
        };
        self.frames[fi].edges.push(e);
    }

    fn restore_to(&mut self, fi: usize) {
        let f = &self.frames[fi];
        let (h, mark, rm) = (f.height, f.lane_mark, f.real_mark);
        self.locals = f.locals.clone();
        self.globals = f.globals.clone();
        self.eps = f.eps;
        self.handles = f.handles.clone();
        self.dead = f.entered_dead;
        self.stack.truncate(h);
        self.lane.truncate(mark);
        self.cut_real(rm);
    }

    /// At `else` (or an `end` without `else`): close the then-arm and open the else-arm.
    fn close_then(&mut self, line: u32) {
        let fi = self.frames.len() - 1;
        self.branch(line, fi, None);
        self.restore_to(fi);
        self.frames[fi].in_else = true;
        if let Some(c) = self.frames[fi].cond {
            let a = self.terms.atom_of(c, false);
            if self.impossible(&a) {
                self.go_dead(line);
                return;
            }
            // born where the else-arm starts (the `else` line), so its chip's ribbon never runs
            // through the then-arm, where the fact is false
            self.enter(a, line, "if else-arm", vec![]);
        }
    }

    fn join(&mut self, line: u32) {
        let fr = self.frames.pop().unwrap();
        let edges = fr.edges.clone();
        // restore to the frame's entry first
        self.frames.push(fr);
        let fi = self.frames.len() - 1;
        self.restore_to(fi);
        let fr = self.frames.pop().unwrap();
        let nres = fr.bt.results.len();
        // a probed (locked) block or `end` must be left on some edge that is not contradictory:
        // otherwise its block facts are discharged ex falso, or never checked (research/22 B3)
        let probed = [fr.line, line]
            .into_iter()
            .find(|l| self.cx.probe.contains(l));
        if let Some(pl) = probed
            && fr.entered_dead.is_none()
            && edges.iter().all(|e| self.lane_is_false(&e.lane))
        {
            self.false_ctx_lines.push(pl);
        }
        if edges.is_empty() {
            self.go_dead(line);
            for r in &fr.bt.results {
                let t = self.terms.leaf(r.ty, "#dead", None);
                self.stack.push(t);
            }
            return;
        }
        let same = |xs: Vec<TermId>| -> Option<TermId> {
            if xs.iter().all(|x| *x == xs[0]) {
                Some(xs[0])
            } else {
                None
            }
        };
        // R8: locals, globals, epoch, results
        let mut phis: Vec<usize> = vec![];
        for i in 0..self.locals.len() {
            match same(edges.iter().map(|e| e.locals[i]).collect()) {
                Some(t) => self.locals[i] = t,
                None => {
                    let name = self.locs[i]
                        .0
                        .clone()
                        .unwrap_or_else(|| format!("local {i}"));
                    self.locals[i] = self.terms.leaf(self.locs[i].1, name, None);
                    self.birth(self.locals[i], line, Capture::Local(i as u32));
                    phis.push(i);
                }
            }
        }
        let mut gphis = vec![];
        for i in 0..self.globals.len() {
            match same(edges.iter().map(|e| e.globals[i]).collect()) {
                Some(t) => self.globals[i] = t,
                None => {
                    let g = &self.cx.m.globals[i];
                    self.globals[i] = self.terms.leaf(
                        g.ty.ty,
                        g.name.clone().unwrap_or_else(|| "global".into()),
                        None,
                    );
                    self.birth(self.globals[i], line, Capture::Global(i as u32));
                    gphis.push(i);
                }
            }
        }
        self.eps = match same(edges.iter().map(|e| e.eps).collect()) {
            Some(e) => e,
            None => self.fresh_eps(),
        };
        let mut values = vec![];
        for j in 0..nres {
            let t = match same(edges.iter().map(|e| e.values[j]).collect()) {
                Some(t) => t,
                None => {
                    let t = self.terms.leaf(fr.bt.results[j].ty, "#φ", None);
                    if nres == 1 {
                        self.birth(t, line, Capture::Top);
                    }
                    t
                }
            };
            values.push(t);
            self.slot_ids.push((line, t));
            self.stack.push(t);
        }
        // lane: facts on every incoming edge (intersection)
        for e in &edges[0].lane {
            let atom = self.facts[e.fact as usize].atom.clone();
            let mut matched = vec![e.fact];
            let ok = edges[1..].iter().all(|ed| {
                match ed
                    .lane
                    .iter()
                    .find(|x| self.facts[x.fact as usize].atom == atom)
                {
                    Some(x) => {
                        matched.push(x.fact);
                        true
                    }
                    None => false,
                }
            });
            if !ok {
                continue;
            }
            if matched.iter().all(|f| *f == e.fact) {
                self.lane.push(*e);
            } else {
                let ol = self.facts[e.fact as usize].line;
                let f = self.new_fact(
                    atom,
                    ol,
                    "join",
                    matched.into_iter().map(Dep::Fact).collect(),
                );
                self.lane.push(Entry { fact: f, line: ol });
            }
        }
        for i in phis {
            if let (Some(r), Some(g)) = (self.loc_ref[i].clone(), self.local_groups[i]) {
                let b = self.cur_bind();
                let a = self.inst_atom(r.refine.as_ref().unwrap(), &b, Some(self.locals[i]));
                self.enter(a, line, "refined local at join (R8)", vec![Dep::Group(g)]);
            }
        }
        for i in gphis {
            if let Some((a, deps)) = self.global_fact(i) {
                self.enter(a, line, "refined global at join (R8)", deps);
            }
        }
        let b = self.cur_bind();
        for (k, e) in fr.bt.facts.iter().enumerate() {
            let a = self.inst_atom(e, &b, None);
            let deps = edges.iter().map(|ed| Dep::Cup(ed.fact_cups[k])).collect();
            self.enter(a, line, "block fact at join", deps);
        }
        for (j, r) in fr.bt.results.iter().enumerate() {
            if let Some(e) = &r.refine {
                let a = self.inst_atom(e, &b, Some(values[j]));
                let deps = edges
                    .iter()
                    .filter_map(|ed| ed.result_cups[j].map(Dep::Cup))
                    .collect();
                self.enter(a, line, "block result at join", deps);
            }
        }
    }

    fn control(&mut self, pc: usize, line: u32, ins: &Ins, tab: &[(usize, usize)]) {
        match ins {
            Ins::Block(kind, bt) => {
                let np = bt.params.len();
                match kind {
                    BlockKind::Block => {
                        self.feed_enter(line, &[]);
                        let params = self.popn(np);
                        let fr = self.frame(FKind::Block, bt.clone(), line);
                        self.frames.push(fr);
                        self.stack.extend(params);
                    }
                    BlockKind::If => {
                        self.feed_enter(line, &[]);
                        let c = self.pop();
                        let params = self.popn(np);
                        let mut fr = self.frame(FKind::If, bt.clone(), line);
                        fr.cond = Some(c);
                        self.frames.push(fr);
                        self.stack.extend(params);
                        let a = self.terms.atom_of(c, true);
                        if self.impossible(&a) {
                            self.go_dead(line);
                        } else {
                            self.enter(a, line, "if then-arm", vec![]);
                        }
                    }
                    BlockKind::Loop => self.loop_head(pc, line, bt, tab),
                }
            }
            Ins::Else => {
                if self.frames.last().map(|f| f.kind) == Some(FKind::If) {
                    self.close_then(line);
                } else {
                    self.line_errors.push((line, "else without if".into()));
                }
            }
            Ins::End => {
                let Some(fr) = self.frames.last() else { return };
                match fr.kind {
                    FKind::Func => self.line_errors.push((line, "unmatched end".into())),
                    FKind::Loop => {
                        let fi = self.frames.len() - 1;
                        // loop results: refinement cups on the fall-through (no join)
                        let n = fr.bt.results.len();
                        let values: Vec<TermId> =
                            self.stack[self.stack.len().saturating_sub(n)..].to_vec();
                        let b = self.cur_bind();
                        let mut reqs = vec![];
                        for (j, r) in self.frames[fi].bt.results.clone().iter().enumerate() {
                            if let (Some(e), Some(v)) = (&r.refine, values.get(j)) {
                                let a = self.inst_atom(e, &b, Some(*v));
                                reqs.push(CupReq {
                                    kind: CupKind::BlockFact { label: fi as u32 },
                                    operand: Some(j as u8),
                                    atom: a,
                                });
                            }
                        }
                        self.feed_enter(line, &reqs);
                        let fr = self.frames.pop().unwrap();
                        let _ = fr;
                    }
                    FKind::Block | FKind::If => {
                        if fr.kind == FKind::If && !fr.in_else {
                            self.close_then(line);
                        }
                        let fi = self.frames.len() - 1;
                        self.branch(line, fi, None);
                        self.join(line);
                    }
                }
            }
            Ins::Br(l) | Ins::BrIf(l) => {
                let Some(fi) = self.resolve_label(l) else {
                    self.line_errors.push((line, format!("unknown label {l}")));
                    return;
                };
                if matches!(ins, Ins::Br(_)) {
                    self.branch(line, fi, None);
                    self.go_dead(line);
                } else {
                    let c = self.pop();
                    let a = self.terms.atom_of(c, true);
                    let na = self.terms.atom_of(c, false);
                    // an edge that is never taken is not an edge; a fall-through that never
                    // happens is dead code (as after `br`)
                    if !self.impossible(&a) {
                        let f = self.new_fact(a, line, "br_if taken edge", vec![]);
                        self.branch(line, fi, Some(Entry { fact: f, line }));
                    }
                    if self.impossible(&na) {
                        self.go_dead(line);
                    } else {
                        self.enter(na, line, "br_if fall-through", vec![]);
                    }
                }
            }
            Ins::BrTable(ls) => {
                let i = self.pop();
                if ls.is_empty() {
                    self.line_errors
                        .push((line, "br_table needs at least one label".into()));
                    self.go_dead(line);
                    return;
                }
                let n = ls.len() - 1;
                for (j, l) in ls.iter().enumerate() {
                    let Some(fi) = self.resolve_label(l) else {
                        self.line_errors.push((line, format!("unknown label {l}")));
                        continue;
                    };
                    let a = if j < n {
                        let k = self.terms.konst(ValTy::I32, j as u64);
                        self.terms.mk_eq(i, k, true)
                    } else {
                        let k = self.terms.konst(ValTy::I32, n as u64);
                        Atom::cmp(super::term::Rel::Le, false, k, i)
                    };
                    if self.impossible(&a) {
                        continue;
                    }
                    let f = self.new_fact(a, line, "br_table edge", vec![]);
                    self.branch(line, fi, Some(Entry { fact: f, line }));
                }
                self.go_dead(line);
            }
            Ins::Return => {
                self.branch(line, 0, None);
                self.go_dead(line);
            }
            _ => {}
        }
    }

    /// R17: a loop head. Invariants are the loop's block type.
    fn loop_head(&mut self, pc: usize, line: u32, bt: &BlockType, tab: &[(usize, usize)]) {
        let b = self.cur_bind();
        let mut reqs = vec![];
        for e in &bt.facts {
            let a = self.inst_atom(e, &b, None);
            reqs.push(CupReq {
                kind: CupKind::LoopEntry,
                operand: None,
                atom: a,
            });
        }
        let np = bt.params.len();
        let params: Vec<TermId> = self.stack[self.stack.len().saturating_sub(np)..].to_vec();
        for (j, r) in bt.params.iter().enumerate() {
            if let (Some(e), Some(v)) = (&r.refine, params.get(j)) {
                let a = self.inst_atom(e, &b, Some(*v));
                reqs.push(CupReq {
                    kind: CupKind::LoopEntry,
                    operand: Some(j as u8),
                    atom: a,
                });
            }
        }
        let ids = self.feed_enter(line, &reqs);
        self.popn(np);
        let mut fr = self.frame(FKind::Loop, bt.clone(), line);
        // one group per declared fact (then per refined param), seeded with the entry cup
        let mut k = 0;
        for _ in &bt.facts {
            self.groups.push(vec![Dep::Cup(ids[k])]);
            fr.groups.push((self.groups.len() - 1) as u32);
            k += 1;
        }
        // pre-scan of the body (R8, R12)
        let body = &self.cx.m.funcs[self.f].body;
        let end = tab[pc].1.min(body.len());
        let mut set_locals = vec![];
        let mut set_globals = vec![];
        let mut bumps = false;
        let mut impure_call = false;
        for (_, ins) in &body[pc + 1..end] {
            match ins {
                Ins::LocalSet(n) | Ins::LocalTee(n) => {
                    if let Some(i) = self.local_index(n)
                        && !set_locals.contains(&i)
                    {
                        set_locals.push(i);
                    }
                }
                Ins::GlobalSet(n) => set_globals.extend(self.global_index(n)),
                Ins::Store(_)
                | Ins::MemoryFill
                | Ins::MemoryCopy
                | Ins::MemoryGrow
                | Ins::CallIndirect => bumps = true,
                Ins::Call(c) => {
                    if let Some(g) = self.cx.m.func_index(c)
                        && self.cx.info[g].impure.is_some()
                    {
                        bumps = true;
                        impure_call = true;
                    }
                }
                _ => {}
            }
        }
        if impure_call {
            set_globals = (0..self.globals.len())
                .filter(|i| self.cx.m.globals[*i].mutable)
                .collect();
        }
        self.frames.push(fr);
        // φ for the loop parameters; the top one is captured right after the `loop` line (on
        // entry and on every back edge) for runtime checks (R35); deeper ones are not capturable
        // with a single top-of-stack copy, and checks reading them are reported as unevaluable
        let np = bt.params.len();
        for (j, r) in bt.params.iter().enumerate() {
            let t = self.terms.leaf(r.ty, "#φ", None);
            self.stack.push(t);
            if j + 1 == np {
                self.birth(t, line, Capture::Top);
            }
            if let Some(e) = &r.refine {
                self.groups.push(vec![Dep::Cup(ids[k])]);
                let g = (self.groups.len() - 1) as u32;
                self.frames.last_mut().unwrap().groups.push(g);
                k += 1;
                let b = self.cur_bind();
                let a = self.inst_atom(e, &b, Some(t));
                self.enter(a, line, "loop parameter", vec![Dep::Group(g)]);
            }
            let _ = j;
        }
        for i in set_locals {
            let name = self.locs[i]
                .0
                .clone()
                .unwrap_or_else(|| format!("local {i}"));
            self.locals[i] = self.terms.leaf(self.locs[i].1, name, None);
            self.birth(self.locals[i], line, Capture::Local(i as u32));
            if let (Some(r), Some(g)) = (self.loc_ref[i].clone(), self.local_groups[i]) {
                let b = self.cur_bind();
                let a = self.inst_atom(r.refine.as_ref().unwrap(), &b, Some(self.locals[i]));
                self.enter(
                    a,
                    line,
                    "refined local at loop head (R8)",
                    vec![Dep::Group(g)],
                );
            }
        }
        for i in set_globals {
            let gl = &self.cx.m.globals[i];
            self.globals[i] = self.terms.leaf(
                gl.ty.ty,
                gl.name.clone().unwrap_or_else(|| "global".into()),
                None,
            );
            self.birth(self.globals[i], line, Capture::Global(i as u32));
            if let Some((a, deps)) = self.global_fact(i) {
                self.enter(a, line, "refined global at loop head (R8)", deps);
            }
        }
        if bumps {
            self.eps = self.fresh_eps();
        }
        let b = self.cur_bind();
        let groups = self.frames.last().unwrap().groups.clone();
        for (i, e) in bt.facts.iter().enumerate() {
            let a = self.inst_atom(e, &b, None);
            self.enter(a, line, "loop invariant", vec![Dep::Group(groups[i])]);
        }
    }
}

impl<'a, 'm> Pass<'a, 'm> {
    /// Run the pass over the whole body.
    pub fn run(&mut self) {
        let cx = self.cx;
        let func = &cx.m.funcs[self.f];
        if func.is_axiom() {
            if !func.body.is_empty() {
                self.line_errors
                    .push((func.header_line, "an axiom has an empty body".into()));
            }
            return;
        }
        self.entry();
        let tab = super::eval::block_table(&func.body);
        for (pc, (line, ins)) in func.body.iter().enumerate() {
            let before = self.dead.is_some();
            // `end`/`else` are judged by their incoming edges (in `join`), not the fall-through
            if !before
                && self.cx.probe.contains(line)
                && !matches!(ins, Ins::End | Ins::Else)
                && self.lane_is_false(&[])
            {
                self.false_ctx_lines.push(*line);
            }
            self.step(pc, *line, ins, &tab);
            // `end`/`else` are reached when some edge reaches them; any other line when control
            // falls into it
            let dead = match ins {
                Ins::End | Ins::Else => self.dead.is_some(),
                _ => before,
            };
            if dead {
                self.dead_lines.push(*line);
            }
        }
        // R15 at the closing `)`
        let line = func.end_line;
        self.line = line;
        while self.frames.len() > 1 {
            self.line_errors.push((
                self.frames.last().unwrap().line,
                "block is not closed with end".into(),
            ));
            self.frames.pop();
        }
        self.branch(line, 0, None);
        self.predicate_checks();
    }

    /// R29 / R31: shape of predicates and measures (errors on the header line).
    fn predicate_checks(&mut self) {
        let cx = self.cx;
        let i = &cx.info[self.f];
        let func = &cx.m.funcs[self.f];
        let hl = func.header_line;
        let name = func.name();
        if func.is_lemma() {
            self.lemma_checks();
            return;
        }
        if !(i.is_pred || i.is_measure) {
            return;
        }
        let what = if i.is_pred { "predicate" } else { "measure" };
        if let Some((l, why)) = &i.impure {
            self.line_errors
                .push((hl, format!("{what} {name} must be pure: line {l} {why}")));
        }
        if let Some(l) = i.has_loop {
            self.line_errors
                .push((hl, format!("{what} {name} has a loop (line {l})")));
        }
        if i.is_pred {
            let rs = func.value_results();
            if rs.len() != 1 || rs[0].ty != ValTy::I32 {
                self.line_errors
                    .push((hl, format!("predicate {name} must return one i32")));
            }
            if func
                .header
                .params
                .iter()
                .any(|p| !matches!(&p.decl, Decl::Val(r) if r.refine.is_none()))
            {
                self.line_errors.push((
                    hl,
                    format!("predicate {name} may not have refined or fact parameters"),
                ));
            }
            if let Some(g) = i.mutual_rec {
                self.line_errors.push((hl, format!("predicate {name} is recursive through {} (only direct self-recursion with a measure is allowed)", cx.m.funcs[g].name())));
            }
            if let Some(mf) = i.measure
                && let Err(e) = measure_shape(cx.m, self.f, mf)
            {
                self.line_errors.push((hl, e));
            }
            if i.self_rec && i.measure.is_none() {
                self.line_errors.push((
                    hl,
                    format!(
                        "predicate {name} is recursive without measure:{}",
                        name.trim_start_matches('$')
                    ),
                ));
            }
        } else if i.self_rec {
            self.line_errors
                .push((hl, format!("measure {name} may not be recursive")));
        }
    }

    /// R33: a lemma is ghost code, never run, so it must be total: no loops, no stores or impure
    /// calls, no value results, calls only to predicates (which R29 keeps total), and recursion only
    /// direct and measured (R31). Otherwise a lemma could "prove" False by never returning.
    fn lemma_checks(&mut self) {
        let cx = self.cx;
        let i = &cx.info[self.f];
        let func = &cx.m.funcs[self.f];
        let hl = func.header_line;
        let name = func.name();
        if let Some((l, why)) = &i.impure {
            self.line_errors
                .push((hl, format!("lemma {name} must be pure: line {l} {why}")));
        }
        if let Some(l) = i.has_loop {
            self.line_errors.push((
                hl,
                format!("lemma {name} has a loop (line {l}); ghost code must terminate"),
            ));
        }
        if !func.value_results().is_empty() {
            self.line_errors
                .push((hl, format!("lemma {name} may have only fact results")));
        }
        for (l, ins) in &func.body {
            if let Ins::Call(c) = ins
                && let Some(g) = cx.m.func_index(c)
                && !cx.info[g].is_pred
            {
                self.line_errors.push((
                    *l,
                    format!("a lemma may call only predicates: {c} is not total (ghost code must terminate)"),
                ));
            }
        }
        if let Some(g) = i.mutual_rec {
            self.line_errors.push((
                hl,
                format!(
                    "lemma {name} is recursive through {} (only direct self-recursion with a measure is allowed)",
                    cx.m.funcs[g].name()
                ),
            ));
        }
        if let Some(mf) = i.measure
            && let Err(e) = measure_shape(cx.m, self.f, mf)
        {
            self.line_errors.push((hl, e));
        }
    }

    /// Runtime-checked cup lines and assumptions a dependency list rests on (§4.1).
    pub fn closure(&self, start: &[Dep]) -> (BTreeSet<u32>, BTreeSet<(u32, bool)>) {
        let mut checks = BTreeSet::new();
        let mut assumes = BTreeSet::new();
        let mut seen_c = vec![false; self.cups.len()];
        let mut seen_f = vec![false; self.facts.len()];
        let mut seen_g = vec![false; self.groups.len()];
        let mut work: Vec<Dep> = start.to_vec();
        while let Some(d) = work.pop() {
            match d {
                Dep::Cup(c) => {
                    let c = c as usize;
                    if std::mem::replace(&mut seen_c[c], true) {
                        continue;
                    }
                    if self.cups[c].feed == Feed::Unfed {
                        if !self.cups[c].ghost {
                            checks.insert(self.cups[c].line);
                        }
                    } else {
                        work.extend(self.cup_deps[c].iter().cloned());
                    }
                }
                Dep::Fact(f) => {
                    if !std::mem::replace(&mut seen_f[f as usize], true) {
                        work.extend(self.facts[f as usize].deps.iter().cloned());
                    }
                }
                Dep::Group(g) => {
                    if !std::mem::replace(&mut seen_g[g as usize], true) {
                        work.extend(self.groups[g as usize].iter().cloned());
                    }
                }
                Dep::Assume(l, ax) => {
                    assumes.insert((l, ax));
                }
                Dep::Check(l) => {
                    checks.insert(l);
                }
            }
        }
        (checks, assumes)
    }

    /// Final verdicts and the function's output. Also returns the assumption deps of the whole
    /// function (for a lemma's callers, R33).
    pub fn finish(mut self) -> (FuncOut, Vec<Dep>) {
        let func = &self.cx.m.funcs[self.f];
        let mut all_assumes: BTreeSet<(u32, bool)> = BTreeSet::new();
        let mut unproven = !self.line_errors.is_empty();
        for c in 0..self.cups.len() {
            if self.cups[c].feed == Feed::Unfed {
                unproven = true;
                continue;
            }
            let (checks, assumes) = self.closure(&self.cup_deps[c].clone());
            let cup = &mut self.cups[c];
            cup.depends_on_checks = checks.into_iter().collect();
            cup.assumptions = assumes
                .iter()
                .map(|(l, ax)| Origin {
                    line: *l,
                    kind: if *ax { "axiom" } else { "assume" },
                })
                .collect();
            if !assumes.is_empty() && cup.verdict == Verdict::Proven {
                cup.verdict = Verdict::Assumed;
            }
            all_assumes.extend(assumes);
        }
        let strict_clean = self.line_errors.is_empty()
            && self.cups.iter().all(|c| {
                matches!(c.verdict, Verdict::Proven | Verdict::Assumed)
                    && c.depends_on_checks.is_empty()
                    && c.assumptions.iter().all(|o| o.kind == "axiom")
            });
        let mut deps: Vec<Dep> = all_assumes
            .into_iter()
            .map(|(l, ax)| Dep::Assume(l, ax))
            .collect();
        if unproven {
            deps.push(Dep::Assume(func.header_line, false));
        }
        let chips = self
            .facts
            .iter()
            .enumerate()
            .map(|(i, f)| super::out::ChipOut {
                line: f.line,
                text: self.terms.render_atom(&f.atom),
                origin: f.kind,
                frayed_at: self.fray.get(&(i as FactId)).copied(),
            })
            .collect();
        let out = FuncOut {
            name: func.name(),
            header_line: func.header_line,
            end_line: func.end_line,
            verified: false,
            strict_clean,
            cups: self.cups,
            line_errors: self.line_errors,
            chips,
            terms: self.terms,
            slot_ids: self.slot_ids,
            births: self.births,
            func: self.f as u32,
            dead_lines: self.dead_lines,
            false_ctx_lines: self.false_ctx_lines,
        };
        (out, deps)
    }
}

/// Check a whole module (design 16 §5): one pass per function, lemmas first so their callers know
/// which assumptions their results rest on.
pub fn check_module(m: &Module, gradual: bool) -> super::out::ModuleOut {
    check_module_probing(m, gradual, BTreeSet::new())
}

/// [`check_module`], also reporting which `probe` lines are reached only ex falso
/// ([`FuncOut::false_ctx_lines`]).
pub fn check_module_probing(
    m: &Module,
    gradual: bool,
    probe: BTreeSet<u32>,
) -> super::out::ModuleOut {
    let info = super::info::analyze(m);
    let mem = m.memory_min.map(|p| p.saturating_mul(65536).min(1 << 32));
    let mut cx = ModCtx {
        m,
        info,
        mem,
        lemma_assumes: HashMap::new(),
        gradual,
        global_deps: vec![None; m.globals.len()],
        probe,
    };
    let mut errors = m.errors.clone();
    global_preflight(&mut cx, &mut errors);
    // lemma order: callees first (depth-first over lemma lines)
    let mut order: Vec<usize> = vec![];
    fn visit(m: &Module, f: usize, seen: &mut Vec<bool>, order: &mut Vec<usize>) {
        if std::mem::replace(&mut seen[f], true) {
            return;
        }
        for (_, ins) in &m.funcs[f].body {
            if let Ins::Lemma(n, _) = ins
                && let Some(g) = m.func_index(n)
            {
                visit(m, g, seen, order);
            }
        }
        order.push(f);
    }
    let mut seen = vec![false; m.funcs.len()];
    for (f, func) in m.funcs.iter().enumerate() {
        if func.is_lemma() || func.is_axiom() {
            visit(m, f, &mut seen, &mut order);
        }
    }
    let lemmas: Vec<usize> = order
        .iter()
        .copied()
        .filter(|f| m.funcs[*f].is_lemma() || m.funcs[*f].is_axiom())
        .collect();
    let mut outs: Vec<Option<super::out::FuncOut>>;
    loop {
        outs = vec![None; m.funcs.len()];
        cx.lemma_assumes.clear();
        for f in lemmas
            .iter()
            .copied()
            .chain((0..m.funcs.len()).filter(|f| !lemmas.contains(f)))
        {
            if m.funcs[f].imported {
                continue;
            }
            let mut p = Pass::new(&cx, f);
            p.run();
            let (out, deps) = p.finish();
            if m.funcs[f].is_lemma() {
                cx.lemma_assumes.insert(f, deps);
            }
            outs[f] = Some(out);
        }
        // R9 across functions: a refined global's refinement rests on every unproven `global.set`
        // of it anywhere in the module (monotone: repeat until nothing new is learned)
        if !global_sets_feed_back(&mut cx, &outs) {
            break;
        }
    }
    // VERIFIED: strict-clean and every callee verified (greatest fixed point)
    let mut ver: Vec<bool> = outs
        .iter()
        .map(|o| o.as_ref().is_some_and(|o| o.strict_clean))
        .collect();
    loop {
        let mut changed = false;
        for f in 0..m.funcs.len() {
            if !ver[f] {
                continue;
            }
            let callees = m.funcs[f].body.iter().filter_map(|(_, ins)| match ins {
                Ins::Call(n) | Ins::Lemma(n, _) => m.func_index(n),
                _ => None,
            });
            let uses = cx.info[f].uses.iter().copied();
            let ok = callees
                .into_iter()
                .chain(uses)
                .all(|g| ver[g] || m.funcs[g].is_axiom());
            if !ok {
                ver[f] = false;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let mut res = super::out::ModuleOut {
        funcs: vec![],
        errors,
    };
    for (f, o) in outs.into_iter().enumerate() {
        if let Some(mut o) = o {
            o.verified = ver[f];
            res.funcs.push(o);
        }
    }
    res
}

/// R9/R14 for globals, before any pass: a refinement may name only `v` (it is a module-wide
/// invariant, not about any function's locals) and may not read memory; the initializer must
/// satisfy it, or every function's copy of it is an assumption.
fn global_preflight(cx: &mut ModCtx, errors: &mut Vec<(u32, String)>) {
    let any = (0..cx.m.funcs.len()).find(|f| !cx.m.funcs[*f].imported);
    let mut deps = vec![None; cx.m.globals.len()];
    for (i, g) in cx.m.globals.iter().enumerate() {
        let Some(r) = &g.ty.refine else { continue };
        let name = g.name.clone().unwrap_or_else(|| format!("global {i}"));
        if let Some(n) = expr_vars(r).first() {
            errors.push((
                g.line,
                format!("{name}'s refinement names {n}: a global's refinement may name only `v`"),
            ));
            continue;
        }
        if expr_reads_mem(cx, r) {
            errors.push((
                g.line,
                format!("{name}'s refinement may not read memory: a store would falsify it unseen"),
            ));
            continue;
        }
        // a predicate that fails R29 (impure, a loop) is reported on its own header; the
        // refinement is ignored here rather than "evaluated" into a misleading initializer error
        let mut called = vec![];
        super::info::expr_calls(r, &mut called);
        if let Some(p) = called.iter().find(|p| {
            cx.m
                .func_index(p)
                .is_some_and(|f| cx.info[f].impure.is_some() || cx.info[f].has_loop.is_some())
        }) {
            errors.push((
                g.line,
                format!("{name}'s refinement calls {p}, which is not a valid predicate (R29: see its header)"),
            ));
            continue;
        }
        deps[i] = Some(vec![]);
    }
    cx.global_deps = deps.clone();
    if let Some(f) = any {
        let mut p = Pass::new(cx, f);
        for (i, g) in cx.m.globals.iter().enumerate() {
            if deps[i].is_none() {
                continue;
            }
            if !p.global_init_holds(i) {
                let name = g.name.clone().unwrap_or_else(|| format!("global {i}"));
                if g.init.is_some() {
                    errors.push((
                        g.line,
                        format!("{name}'s initializer does not satisfy its refinement (R14)"),
                    ));
                }
                deps[i] = Some(vec![Dep::Assume(g.line, false)]);
            }
        }
    }
    cx.global_deps = deps;
}

/// Add every function's unproven `global.set` cups to that global's dependencies; true if any
/// were new.
fn global_sets_feed_back(cx: &mut ModCtx, outs: &[Option<super::out::FuncOut>]) -> bool {
    let mut changed = false;
    for o in outs.iter().flatten() {
        let func = &cx.m.funcs[o.func as usize];
        for c in &o.cups {
            let CupKind::Refinement { param } = c.kind else {
                continue;
            };
            let is_set = func.body.iter().any(|(l, ins)| {
                *l == c.line
                    && matches!(ins, Ins::GlobalSet(n) if global_index_of(cx.m, n) == Some(param as usize))
            });
            if !is_set {
                continue;
            }
            let Some(Some(deps)) = cx.global_deps.get_mut(param as usize) else {
                continue;
            };
            let mut new: Vec<Dep> = vec![];
            if c.feed == Feed::Unfed {
                new.push(Dep::Check(c.line));
            }
            new.extend(c.depends_on_checks.iter().map(|l| Dep::Check(*l)));
            new.extend(
                c.assumptions
                    .iter()
                    .map(|o| Dep::Assume(o.line, o.kind == "axiom")),
            );
            for d in new {
                if !deps.iter().any(|x| same_dep(x, &d)) {
                    deps.push(d);
                    changed = true;
                }
            }
        }
    }
    changed
}

fn same_dep(a: &Dep, b: &Dep) -> bool {
    match (a, b) {
        (Dep::Check(x), Dep::Check(y)) => x == y,
        (Dep::Assume(x, p), Dep::Assume(y, q)) => x == y && p == q,
        _ => false,
    }
}

fn global_index_of(m: &Module, n: &str) -> Option<usize> {
    m.globals
        .iter()
        .position(|g| g.name.as_deref() == Some(n))
        .or_else(|| n.parse::<usize>().ok())
}

fn expr_vars(e: &Expr) -> Vec<String> {
    match e {
        Expr::Var(x) => vec![x.clone()],
        Expr::Op(_, a) | Expr::Call(_, a) => a.iter().flat_map(expr_vars).collect(),
        _ => vec![],
    }
}

/// Does the proposition call a function that reads memory (R12)?
fn expr_reads_mem(cx: &ModCtx, e: &Expr) -> bool {
    match e {
        Expr::Call(f, a) => {
            cx.m.func_index(f).is_none_or(|g| cx.info[g].reads_mem)
                || a.iter().any(|x| expr_reads_mem(cx, x))
        }
        Expr::Op(_, a) => a.iter().any(|x| expr_reads_mem(cx, x)),
        _ => false,
    }
}

/// Does the proposition name `$n`?
fn expr_names(e: &Expr, n: &str) -> bool {
    match e {
        Expr::Var(x) => x == n,
        Expr::Op(_, a) | Expr::Call(_, a) => a.iter().any(|x| expr_names(x, n)),
        _ => false,
    }
}

/// R31: a measure has exactly the value parameters of its function and one i32/i64 result.
pub fn measure_shape(m: &Module, f: usize, mf: usize) -> Result<(), String> {
    let (func, meas) = (&m.funcs[f], &m.funcs[mf]);
    let p1: Vec<ValTy> = func.value_params().map(|(_, _, r)| r.ty).collect();
    let p2: Vec<ValTy> = meas.value_params().map(|(_, _, r)| r.ty).collect();
    let rs = meas.value_results();
    if p1 != p2 || meas.header.params.len() != p2.len() {
        return Err(format!(
            "measure {} must have the value parameters of {}",
            meas.name(),
            func.name()
        ));
    }
    if rs.len() != 1 || !rs[0].ty.is_int() || meas.header.results.len() != 1 {
        return Err(format!(
            "measure {} must return exactly one i32 or i64",
            meas.name()
        ));
    }
    Ok(())
}
