// Verification conditions: proofs of the specifications, one function at a time.
//
// Each function is executed symbolically over the stack machine, starting from its
// contract: params, globals, memory and ghost state are arbitrary, subject to the
// function's requires and param refinements. (The first function is the program's entry
// point: it starts from the initial state, with memory zero and globals at their
// initializers.) Loops are cut at their `@invariant`s: the invariant must hold on entry;
// then the state the body writes is made arbitrary, the invariant is assumed, and the
// body runs once to each back edge, where the invariant must hold again and the
// `@decreases` measure must have decreased. Calls go through the callee's contract: its
// requires is an obligation, its ensures a fact, and what it may write is made arbitrary.
// `@assert` is an obligation and then a fact; `@assume` is a fact; `@set` updates ghosts.
// Instructions that can trap (division, memory access) carry no-trap obligations.
//
// Encoding (SMT-LIB 2, for Z3): machine values are bitvectors with exact Wasm semantics;
// spec terms are 64-bit bitvectors whose value ranges are tracked so that they never
// wrap (a term that could exceed 64 bits is not encoded: unknown). When bit-blasting
// gives no answer (nonlinear facts), the query is translated to integer arithmetic
// (vc_int.rs) and tried again. Memory is an array of 32-bit words. A ghost map is a domain array, a
// value array and a size. Bounded quantifiers with constant bounds (≤ 64 values) are
// expanded; others become SMT quantifiers. Pure `@define`s are SMT functions (recursive
// ones with define-fun-rec); those that read state are unfolded in place.
//
// Each obligation is one self-contained query: its path's facts, and the negated goal.
// unsat means proven; sat gives a model, decoded into the state at the obligation's
// cut point (function entry, or the head of the innermost loop): a state the contract
// allows, which a run may or may not reach.

use crate::{
    checker::{Check, CheckKind, FuncPlan, GhostSet, SpecPlan},
    spec::{self, BinOp, CmpOp, Define, Domain, Env, Expr, GhostType, QuantKind, Val},
    utils::{TypedModule, ValidModule},
};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fmt::Write,
    rc::Rc,
};
use wasmparser::{BlockType, Operator, ValType};

/// The solver's budget per obligation (Z3 resource units, so results are reproducible).
pub const RLIMIT: u64 = 2_000_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TrapKind {
    DivideByZero,
    Overflow,
    OutOfBounds,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ObKind {
    Requires,       // the callee's precondition, at a call
    Ensures,        // the function's postcondition, at a return
    InvariantEntry, // a loop invariant, on entry
    InvariantKept,  // a loop invariant, after an iteration
    MeasureEntry,   // a loop measure is not negative on entry
    Measure,        // a loop measure decreases and stays non-negative
    Assert,
    LocalRefinement,
    NoTrap(TrapKind),
    Unreachable,
}

impl ObKind {
    pub fn describe(&self) -> &'static str {
        match self {
            ObKind::Requires => "precondition at the call",
            ObKind::Ensures => "postcondition",
            ObKind::InvariantEntry => "invariant on entry",
            ObKind::InvariantKept => "invariant preserved",
            ObKind::MeasureEntry => "measure on entry",
            ObKind::Measure => "measure decreases",
            ObKind::Assert => "assertion",
            ObKind::LocalRefinement => "refinement of the local",
            ObKind::NoTrap(TrapKind::DivideByZero) => "no trap (division by zero)",
            ObKind::NoTrap(TrapKind::Overflow) => "no trap (division overflow)",
            ObKind::NoTrap(TrapKind::OutOfBounds) => "no trap (memory access in bounds)",
            ObKind::Unreachable => "unreachable is not reached",
        }
    }
}

/// Where the state of a model is taken: at function entry (replayable), or at a loop head.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Cut {
    Entry,
    LoopHead(usize), // the loop's line
}

/// A value to read from a model, to show the state it describes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Read {
    Var { name: String, bits: u32 },    // a param or local (bitvector)
    Global { index: usize, name: String, bits: u32 },
    Ghost(String),                      // an integer ghost
    Word(u32),                          // a 32-bit word of memory
    MapHas { map: String, key: usize }, // key: index of the read giving the key
    MapVal { map: String, key: usize },
}

#[derive(Debug, Clone)]
pub struct Obligation {
    pub func: usize,
    pub kind: ObKind,
    pub check_kind: Option<CheckKind>,
    pub spec_line: Option<usize>,
    pub at_line: usize,
    pub smt: String,
    pub hash: u64,
    /// Something was over-approximated: a model may be spurious (sat → unknown).
    pub approximate: bool,
    /// The obligation could not be encoded (always unknown).
    pub unsupported: Option<String>,
    pub cut: Cut,
    pub reads: Vec<Read>,
    /// The SMT terms of the reads (the query's get-value).
    pub terms: Vec<String>,
}

// ---------------------------------------------------------------------------------------
// SMT terms

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum W {
    B32,
    B64,
    Opaque, // floats: not modelled
}

#[derive(Debug, Clone)]
struct V {
    t: String,
    w: W,
}

#[derive(Debug, Clone)]
enum S {
    Int(String, (i128, i128)), // a term of width wid(range), and the range its value lies in
    Bool(String),
    Map { dom: String, val: String, size: String },
}

#[derive(Debug, Clone)]
enum G {
    Int(String),
    Map { dom: String, val: String, size: String },
}

fn bv(v: i128, w: u32) -> String {
    let m = if w >= 128 { v as u128 } else { v.rem_euclid(1i128 << w) as u128 };
    format!("(_ bv{m} {w})")
}


const PREAMBLE: &str = "\
(define-fun ld32 ((m (Array (_ BitVec 30) (_ BitVec 32))) (a (_ BitVec 32))) (_ BitVec 32) (let ((i ((_ extract 31 2) a)) (o ((_ extract 1 0) a))) (ite (= o #b00) (select m i) ((_ extract 31 0) (bvlshr (concat (select m (bvadd i #b000000000000000000000000000001)) (select m i)) ((_ zero_extend 59) (concat o #b000)))))))
(define-fun ld8 ((m (Array (_ BitVec 30) (_ BitVec 32))) (a (_ BitVec 32))) (_ BitVec 8) ((_ extract 7 0) (bvlshr (select m ((_ extract 31 2) a)) ((_ zero_extend 27) (concat ((_ extract 1 0) a) #b000)))))
(define-fun ld16 ((m (Array (_ BitVec 30) (_ BitVec 32))) (a (_ BitVec 32))) (_ BitVec 16) (concat (ld8 m (bvadd a (_ bv1 32))) (ld8 m a)))
(define-fun ld64 ((m (Array (_ BitVec 30) (_ BitVec 32))) (a (_ BitVec 32))) (_ BitVec 64) (concat (ld32 m (bvadd a (_ bv4 32))) (ld32 m a)))
(define-fun st32 ((m (Array (_ BitVec 30) (_ BitVec 32))) (a (_ BitVec 32)) (v (_ BitVec 32))) (Array (_ BitVec 30) (_ BitVec 32)) (let ((i ((_ extract 31 2) a)) (o ((_ extract 1 0) a))) (ite (= o #b00) (store m i v) (let ((sh ((_ zero_extend 59) (concat o #b000))) (j (bvadd i #b000000000000000000000000000001))) (let ((nb (bvor (bvand (concat (select m j) (select m i)) (bvnot (bvshl #x00000000ffffffff sh))) (bvshl ((_ zero_extend 32) v) sh)))) (store (store m i ((_ extract 31 0) nb)) j ((_ extract 63 32) nb)))))))
(define-fun st8 ((m (Array (_ BitVec 30) (_ BitVec 32))) (a (_ BitVec 32)) (v (_ BitVec 8))) (Array (_ BitVec 30) (_ BitVec 32)) (let ((i ((_ extract 31 2) a)) (sh ((_ zero_extend 27) (concat ((_ extract 1 0) a) #b000)))) (store m i (bvor (bvand (select m i) (bvnot (bvshl #x000000ff sh))) (bvshl ((_ zero_extend 24) v) sh)))))
(define-fun st16 ((m (Array (_ BitVec 30) (_ BitVec 32))) (a (_ BitVec 32)) (v (_ BitVec 16))) (Array (_ BitVec 30) (_ BitVec 32)) (st8 (st8 m a ((_ extract 7 0) v)) (bvadd a (_ bv1 32)) ((_ extract 15 8) v)))
(define-fun st64 ((m (Array (_ BitVec 30) (_ BitVec 32))) (a (_ BitVec 32)) (v (_ BitVec 64))) (Array (_ BitVec 30) (_ BitVec 32)) (st32 (st32 m a ((_ extract 31 0) v)) (bvadd a (_ bv4 32)) ((_ extract 63 32) v)))
";

// Memory is an array of 32-bit words indexed by address / 4; unaligned and narrow
// accesses combine or mask neighbouring words, so the semantics stay exact while aligned
// word accesses (the common case) are a single select or store.
const MEM_SORT: &str = "(Array (_ BitVec 30) (_ BitVec 32))";

// ---------------------------------------------------------------------------------------
// Symbolic state

#[derive(Debug, Clone)]
struct Snapshot {
    locals: Vec<V>,
    globals: Vec<V>,
    mem: String,
    ghosts: BTreeMap<String, G>,
    ghost_locals: BTreeMap<String, G>,
}

#[derive(Debug, Clone)]
enum Ctl {
    Block { end: usize, arity: usize, height: usize },
    If { end: usize, arity: usize, height: usize },
    Loop { pc: usize, end: usize, height: usize, measure: Option<String> },
    Func,
}

#[derive(Debug, Clone)]
struct St {
    pc: usize,
    stack: Vec<V>,
    locals: Vec<V>,
    globals: Vec<V>,
    mem: String,
    ghosts: BTreeMap<String, G>,       // ghost globals
    ghost_locals: BTreeMap<String, G>, // this function's ghost locals
    path: Vec<String>,                 // facts (Bool terms)
    ctl: Vec<Ctl>,
    entry: Rc<Snapshot>,
    cut: Cut,
    cut_state: Rc<Snapshot>,
    approx: bool,
    returned: Option<Vec<V>>,
}

impl St {
    fn snapshot(&self) -> Snapshot {
        Snapshot {
            locals: self.locals.clone(),
            globals: self.globals.clone(),
            mem: self.mem.clone(),
            ghosts: self.ghosts.clone(),
            ghost_locals: self.ghost_locals.clone(),
        }
    }
}

struct FuncInfo {
    writes_mem: bool,
    writes_globals: BTreeSet<u32>,
    sets_ghosts: BTreeSet<String>,
}

struct Gen<'a> {
    plan: &'a SpecPlan,
    module: &'a ValidModule<'a>,
    func: usize,
    fp: &'a FuncPlan,
    ops: Vec<&'a Operator<'a>>,
    lines: Vec<usize>,
    op_types: Vec<(usize, Vec<W>)>, // inputs popped, outputs pushed (for unmodelled ops)
    matching: HashMap<usize, (Option<usize>, usize)>, // structured op -> (else, end)
    decls: Vec<String>,
    counter: usize,
    // (obligation, decls in scope, facts, goal, the state at its cut point)
    obligations: Vec<(Obligation, usize, Vec<String>, String, Rc<Snapshot>)>,
    addresses: BTreeSet<u32>,
    infos: &'a [FuncInfo],
    recursive_defines: &'a HashSet<String>,
    unsupported: Option<String>,
    mem_bytes: u64,
    // widths at which spec arithmetic (sadd_W …) is used
    spec_widths: BTreeSet<u32>,
}

type R<T> = Result<T, String>;

fn block_arity(module: &ValidModule, bt: &BlockType) -> R<(usize, usize)> {
    Ok(match bt {
        BlockType::Empty => (0, 0),
        BlockType::Type(_) => (0, 1),
        BlockType::FuncType(i) => {
            let ft = module.types.get(*i as usize).ok_or("bad block type")?;
            (ft.params().len(), ft.results().len())
        }
    })
}

fn width(ty: &ValType) -> W {
    match ty {
        ValType::I32 => W::B32,
        ValType::I64 => W::B64,
        _ => W::Opaque,
    }
}

fn sort_of(w: W) -> &'static str {
    match w {
        W::B32 => "(_ BitVec 32)",
        W::B64 => "(_ BitVec 64)",
        W::Opaque => "(_ BitVec 64)",
    }
}



impl<'a> Gen<'a> {
    fn fresh(&mut self, prefix: &str) -> String {
        self.counter += 1;
        format!("{prefix}{}", self.counter)
    }

    fn declare(&mut self, prefix: &str, sort: &str) -> String {
        let n = self.fresh(prefix);
        self.decls.push(format!("(declare-const {n} {sort})"));
        n
    }

    fn define(&mut self, prefix: &str, sort: &str, term: String) -> String {
        let n = self.fresh(prefix);
        self.decls.push(format!("(define-fun {n} () {sort} {term})"));
        n
    }

    fn value(&mut self, w: W, term: String) -> V {
        let t = self.define("v", sort_of(w), term);
        V { t, w }
    }

    fn fresh_value(&mut self, w: W, prefix: &str) -> V {
        let t = self.declare(prefix, sort_of(w));
        V { t, w }
    }

    // An arbitrary ghost value (its facts, e.g. that it is an i32, go onto `path`).
    fn fresh_ghost(&mut self, ty: &GhostType, name: &str, path: &mut Vec<String>) -> G {
        match ty {
            GhostType::Map => {
                let dom = self.declare(&format!("{name}_dom"), DOM_SORT);
                let val = self.declare(&format!("{name}_val"), VAL_SORT);
                let size = self.declare(&format!("{name}_size"), "(_ BitVec 64)");
                path.push(format!(
                    "(and (bvsge {size} (_ bv0 64)) (bvsle {size} {}))",
                    bv(1i128 << 32, 64)
                ));
                G::Map { dom, val, size }
            }
            GhostType::Scalar(_) => G::Int(self.declare(name, "(_ BitVec 32)")),
        }
    }

    fn initial_ghost(&mut self, ty: &GhostType) -> G {
        match ty {
            GhostType::Map => G::Map {
                dom: EMPTY_DOM.into(),
                val: EMPTY_VAL.into(),
                size: bv(0, 64),
            },
            GhostType::Scalar(_) => G::Int(bv(0, 32)),
        }
    }

    // ---------------------------------------------------------------------------------
    // Obligations

    fn oblige(&mut self, st: &St, kind: ObKind, check: Option<&Check>, at_line: usize, goal: String) {
        let ob = Obligation {
            func: self.func,
            kind,
            check_kind: check.map(|c| c.kind),
            spec_line: check.map(|c| c.spec_line),
            at_line,
            smt: String::new(),
            hash: 0,
            approximate: st.approx,
            unsupported: None,
            cut: st.cut.clone(),
            reads: vec![],
            terms: vec![],
        };
        self.obligations.push((
            ob,
            self.decls.len(),
            st.path.clone(),
            goal,
            st.cut_state.clone(),
        ));
    }

    fn oblige_unsupported(&mut self, st: &St, kind: ObKind, check: Option<&Check>, at_line: usize, why: String) {
        self.oblige(st, kind, check, at_line, "true".into());
        self.obligations.last_mut().unwrap().0.unsupported = Some(why);
    }

    // Translate a check's predicate in the current state, then make it an obligation.
    #[allow(clippy::too_many_arguments)]
    fn oblige_check(
        &mut self,
        st: &St,
        kind: ObKind,
        check: &Check,
        at_line: usize,
        binds: &[(String, S)],
        fp: &FuncPlan,
        locals: &[V],
        results: Option<&[V]>,
        old: Option<&Snapshot>,
    ) {
        let mut cx = SpecCx {
            fp,
            locals,
            globals: &st.globals,
            mem: &st.mem,
            ghosts: &st.ghosts,
            ghost_locals: &st.ghost_locals,
            results,
            old,
            binders: binds.to_vec(),
        };
        match self.spec_bool(&mut cx, &check.expr) {
            Ok(goal) => self.oblige(st, kind, Some(check), at_line, goal),
            Err(why) => self.oblige_unsupported(st, kind, Some(check), at_line, why),
        }
    }

    fn assume_check(
        &mut self,
        st: &mut St,
        check: &Check,
        binds: &[(String, S)],
        fp: &FuncPlan,
        locals: &[V],
        results: Option<&[V]>,
        old: Option<&Snapshot>,
    ) {
        let r = {
            let mut cx = SpecCx {
                fp,
                locals,
                globals: &st.globals,
                mem: &st.mem,
                ghosts: &st.ghosts,
                ghost_locals: &st.ghost_locals,
                results,
                old,
                binders: binds.to_vec(),
            };
            self.spec_bool(&mut cx, &check.expr)
        };
        match r {
            Ok(fact) => st.path.push(fact),
            // a fact we cannot state is dropped: we know less (sound), so models are suspect
            Err(_) => st.approx = true,
        }
    }

    // ---------------------------------------------------------------------------------
    // Spec terms: 64-bit bitvectors, exact because every term's range is checked to fit.

    fn spec_bool(&mut self, cx: &mut SpecCx, e: &Expr) -> R<String> {
        match self.spec(cx, e)? {
            S::Bool(b) => Ok(b),
            _ => Err(format!("{e} is not a truth value")),
        }
    }

    fn spec_int(&mut self, cx: &mut SpecCx, e: &Expr) -> R<String> {
        match self.spec(cx, e)? {
            S::Int(i, r) => Ok(at(&i, r, 64)),
            _ => Err(format!("{e} is not a number")),
        }
    }

    // A spec-arithmetic function at width w (sadd_W …: plain bitvector operations, named so
    // that the integer translation knows they never wrap).
    fn sop(&mut self, op: &str, w: u32) -> String {
        self.spec_widths.insert(w);
        format!("{op}_{w}")
    }

    // The value of a constant expression (e.g. CAP, BASE + 12 * 3), if it is one.
    fn constant(&self, cx: &SpecCx, e: &Expr) -> Option<i128> {
        struct ConstEnv<'b>(&'b SpecPlan, &'b [(String, S)]);
        impl Env for ConstEnv<'_> {
            fn var(&self, name: &str) -> Option<Val> {
                self.1.iter().rev().find(|(n, _)| n == name).and_then(|(_, s)| match s {
                    S::Int(_, (lo, hi)) if lo == hi => Some(Val::Int(*lo)),
                    _ => None,
                })
            }
            fn define(&self, name: &str) -> Option<&Define> {
                self.0.defines.iter().find(|d| d.name == name)
            }
        }
        match spec::eval(e, &ConstEnv(self.plan, &cx.binders)) {
            Ok(Val::Int(i)) => Some(i),
            _ => None,
        }
    }

    fn var_term(&mut self, cx: &SpecCx, name: &str, old: bool) -> R<S> {
        if !old && let Some((_, s)) = cx.binders.iter().rev().find(|(n, _)| n == name) {
            return Ok(s.clone());
        }
        let (locals, globals, ghosts, ghost_locals): (&[V], &[V], _, _) = if old {
            let o = cx.old.ok_or("old(…) has no entry state here")?;
            (&o.locals, &o.globals, &o.ghosts, &o.ghost_locals)
        } else {
            (cx.locals, cx.globals, cx.ghosts, cx.ghost_locals)
        };
        if !old && let Some(results) = cx.results {
            for (i, (n, _)) in cx.fp.results.iter().enumerate() {
                if n.as_deref() == Some(name) {
                    return value_of(&results[i], name);
                }
            }
        }
        if let Some(g) = ghost_locals.get(name) {
            return Ok(ghost_term(g));
        }
        for (i, v) in cx.fp.vars.iter().enumerate() {
            if v.name.as_deref() == Some(name) {
                let l = locals.get(i).ok_or("no such local")?;
                return value_of(l, name);
            }
        }
        for (g, n) in self.plan.global_names.iter().enumerate() {
            if n.as_deref() == Some(name) {
                return value_of(&globals[g], name);
            }
        }
        if let Some(g) = ghosts.get(name) {
            return Ok(ghost_term(g));
        }
        Err(format!("${name} has no value here"))
    }

    fn load_term(&mut self, cx: &mut SpecCx, addr: &Expr, bytes: u32, old: bool) -> R<S> {
        let mem = if old {
            cx.old.ok_or("old(…) has no entry state here")?.mem.clone()
        } else {
            cx.mem.clone()
        };
        let a = match self.constant(cx, addr) {
            Some(c) => {
                if !(0..=u32::MAX as i128).contains(&c) {
                    return Err(format!("load({c}) is outside memory"));
                }
                self.addresses.insert(c as u32);
                bv(c, 32)
            }
            None => match self.spec_in(cx, addr, old)? {
                // (an address outside memory reads at the address mod 2^32: specs guard
                // their loads, e.g. 0 <= $s < CAP && st($s) == FULL)
                S::Int(t, r) => at(&t, r, 32),
                _ => return Err("a load address that is not a number".into()),
            },
        };
        Ok(if bytes == 4 {
            S::Int(format!("(ld32 {mem} {a})"), I32)
        } else {
            S::Int(format!("((_ zero_extend 1) (ld8 {mem} {a}))"), (0, 255))
        })
    }

    fn spec(&mut self, cx: &mut SpecCx, e: &Expr) -> R<S> {
        self.spec_in(cx, e, false)
    }

    fn spec_in(&mut self, cx: &mut SpecCx, e: &Expr, old: bool) -> R<S> {
        let int_of = |s: S, e: &Expr| match s {
            S::Int(t, r) => Ok((t, r)),
            _ => Err(format!("{e} is not a number")),
        };
        let bool_of = |s: S, e: &Expr| match s {
            S::Bool(t) => Ok(t),
            _ => Err(format!("{e} is not a truth value")),
        };
        Ok(match e {
            Expr::Int(i) => num(*i)?,
            Expr::Bool(b) => S::Bool(b.to_string()),
            Expr::MapEmpty => S::Map {
                dom: EMPTY_DOM.into(),
                val: EMPTY_VAL.into(),
                size: bv(0, 64),
            },
            Expr::Var(v) => self.var_term(cx, v, old)?,
            Expr::Name(n) => {
                if let Some((_, s)) = cx.binders.iter().rev().find(|(b, _)| b == n) {
                    s.clone()
                } else {
                    self.call_define(cx, n, &[], old)?
                }
            }
            Expr::Neg(a) => {
                let (x, rx) = int_of(self.spec_in(cx, a, old)?, a)?;
                let r = (-rx.1, -rx.0);
                check_range(r)?;
                let w = wid(rx).max(wid(r));
                let f = self.sop("sneg", w);
                mk(format!("({f} {})", at(&x, rx, w)), w, r)?
            }
            Expr::Not(a) => S::Bool(format!("(not {})", bool_of(self.spec_in(cx, a, old)?, a)?)),
            Expr::Bin(op, a, b) => {
                let x = self.spec_in(cx, a, old)?;
                let y = self.spec_in(cx, b, old)?;
                match op {
                    BinOp::And => S::Bool(format!("(and {} {})", bool_of(x, a)?, bool_of(y, b)?)),
                    BinOp::Or => S::Bool(format!("(or {} {})", bool_of(x, a)?, bool_of(y, b)?)),
                    BinOp::Implies => {
                        S::Bool(format!("(=> {} {})", bool_of(x, a)?, bool_of(y, b)?))
                    }
                    _ => {
                        let ((x, rx), (y, ry)) = (int_of(x, a)?, int_of(y, b)?);
                        let corners = |f: &dyn Fn(i128, i128) -> Option<i128>| -> Option<(i128, i128)> {
                            let mut v = vec![];
                            for p in [rx.0, rx.1] {
                                for q in [ry.0, ry.1] {
                                    v.push(f(p, q)?);
                                }
                            }
                            Some((*v.iter().min()?, *v.iter().max()?))
                        };
                        let mag = |r: (i128, i128)| r.0.abs().max(r.1.abs());
                        // computed at a width that holds the operands and the result, then
                        // narrowed to the result's
                        let arith = |this: &mut Self, op: &str, r: (i128, i128), extra: u32| -> R<S> {
                            check_range(r)?;
                            let w = wid(rx).max(wid(ry)).max(wid(r)) + extra;
                            let f = this.sop(op, w);
                            mk(format!("({f} {} {})", at(&x, rx, w), at(&y, ry, w)), w, r)
                        };
                        match op {
                            BinOp::Add => arith(self, "sadd", (rx.0 + ry.0, rx.1 + ry.1), 0)?,
                            BinOp::Sub => arith(self, "ssub", (rx.0 - ry.1, rx.1 - ry.0), 0)?,
                            BinOp::Mul => {
                                let r = corners(&|p, q| p.checked_mul(q)).ok_or("arithmetic beyond 64 bits")?;
                                arith(self, "smul", r, 0)?
                            }
                            BinOp::Div => {
                                let m = mag(rx);
                                arith(self, "ediv", (-m, m), 2)?
                            }
                            BinOp::Rem => {
                                let m = mag(ry);
                                arith(self, "emod", (0, (m - 1).max(0)), 2)?
                            }
                            BinOp::BitAnd | BinOp::BitXor => {
                                let r = if *op == BinOp::BitXor {
                                    let m = mag(rx).max(mag(ry));
                                    let p = ((m + 1) as u128).next_power_of_two() as i128;
                                    (-p, p - 1)
                                } else if rx.0 >= 0 && ry.0 >= 0 {
                                    (0, rx.1.min(ry.1))
                                } else if rx.0 >= 0 {
                                    (0, rx.1)
                                } else if ry.0 >= 0 {
                                    (0, ry.1)
                                } else {
                                    let m = mag(rx).max(mag(ry));
                                    (-m - 1, m)
                                };
                                check_range(r)?;
                                let w = wid(rx).max(wid(ry)).max(wid(r));
                                let f = if *op == BinOp::BitXor { "bvxor" } else { "bvand" };
                                mk(format!("({f} {} {})", at(&x, rx, w), at(&y, ry, w)), w, r)?
                            }
                            BinOp::Shl => match self.constant(cx, b) {
                                Some(_) if rx == (0, 0) => num(0)?,
                                Some(c) if (0..63).contains(&c) => {
                                    let k = 1i128 << c;
                                    let r = (rx.0 * k, rx.1 * k);
                                    check_range(r)?;
                                    let w = wid(rx).max(wid(r));
                                    mk(format!("(bvshl {} {})", at(&x, rx, w), bv(c, w)), w, r)?
                                }
                                _ => return Err("a shift by a variable amount".into()),
                            },
                            BinOp::Shr => match self.constant(cx, b) {
                                Some(c) if (0..63).contains(&c) => {
                                    let w = wid(rx);
                                    let c2 = c.min(w as i128 - 1);
                                    mk(format!("(bvashr {x} {})", bv(c2, w)), w, (rx.0 >> c, rx.1 >> c))?
                                }
                                _ => return Err("a shift by a variable amount".into()),
                            },
                            BinOp::And | BinOp::Or | BinOp::Implies => unreachable!(),
                        }
                    }
                }
            }
            Expr::Chain(es, ops) => {
                let mut terms = vec![];
                for x in es {
                    terms.push(self.spec_in(cx, x, old)?);
                }
                let mut parts = vec![];
                for (i, op) in ops.iter().enumerate() {
                    parts.push(compare(*op, &terms[i], &terms[i + 1])?);
                }
                if parts.len() == 1 {
                    S::Bool(parts.pop().unwrap())
                } else {
                    S::Bool(format!("(and {})", parts.join(" ")))
                }
            }
            Expr::Ite(c, a, b) => {
                let c = bool_of(self.spec_in(cx, c, old)?, c)?;
                match (self.spec_in(cx, a, old)?, self.spec_in(cx, b, old)?) {
                    (S::Int(x, rx), S::Int(y, ry)) => {
                        let r = (rx.0.min(ry.0), rx.1.max(ry.1));
                        let w = wid(r);
                        S::Int(format!("(ite {c} {} {})", at(&x, rx, w), at(&y, ry, w)), r)
                    }
                    (S::Bool(x), S::Bool(y)) => S::Bool(format!("(ite {c} {x} {y})")),
                    (
                        S::Map { dom: d1, val: v1, size: s1 },
                        S::Map { dom: d2, val: v2, size: s2 },
                    ) => S::Map {
                        dom: format!("(ite {c} {d1} {d2})"),
                        val: format!("(ite {c} {v1} {v2})"),
                        size: format!("(ite {c} {s1} {s2})"),
                    },
                    _ => return Err(format!("the branches of {e} differ in kind")),
                }
            }
            Expr::Call(n, args) => match n.as_str() {
                "old" => self.spec_in(cx, &args[0], true)?,
                "u" => {
                    let (x, r) = int_of(self.spec_in(cx, &args[0], old)?, &args[0])?;
                    if within(r, I32) {
                        S::Int(format!("((_ zero_extend 1) {})", at(&x, r, 32)), (0, u32::MAX as i128))
                    } else {
                        return Err("u(…) of a value wider than 32 bits".into());
                    }
                }
                "load" | "load8" => self.load_term(cx, &args[0], if n == "load" { 4 } else { 1 }, old)?,
                "abs" => {
                    let (x, r) = int_of(self.spec_in(cx, &args[0], old)?, &args[0])?;
                    let m = r.0.abs().max(r.1.abs());
                    let ra = if r.0 >= 0 { r } else { (0, m) };
                    check_range(ra)?;
                    let w = wid(r).max(wid(ra)).max(wid((-m, m)));
                    let f = self.sop("sneg", w);
                    let xw = at(&x, r, w);
                    mk(format!("(ite (bvslt {xw} {}) ({f} {xw}) {xw})", bv(0, w)), w, ra)?
                }
                "min" | "max" => {
                    let (x, rx) = int_of(self.spec_in(cx, &args[0], old)?, &args[0])?;
                    let (y, ry) = int_of(self.spec_in(cx, &args[1], old)?, &args[1])?;
                    let op = if n == "min" { "bvsle" } else { "bvsge" };
                    let r = (rx.0.min(ry.0), rx.1.max(ry.1));
                    let w = wid(r);
                    let (xw, yw) = (at(&x, rx, w), at(&y, ry, w));
                    S::Int(format!("(ite ({op} {xw} {yw}) {xw} {yw})"), r)
                }
                "size" => match self.spec_in(cx, &args[0], old)? {
                    S::Map { size, .. } => S::Int(format!("((_ extract 33 0) {size})"), (0, 1i128 << 32)),
                    _ => return Err("size(…) of a non-map".into()),
                },
                "remove" => match self.spec_in(cx, &args[0], old)? {
                    S::Map { dom, val, size } => {
                        let (k, rk) = int_of(self.spec_in(cx, &args[1], old)?, &args[1])?;
                        if !within(rk, I32) {
                            return Err("a map of i32 keyed by a wider value".into());
                        }
                        let k = at(&k, rk, 32);
                        let f = self.sop("ssub", 64);
                        S::Map {
                            dom: format!("(store {dom} {k} false)"),
                            val,
                            size: format!("(ite (select {dom} {k}) ({f} {size} {}) {size})", bv(1, 64)),
                        }
                    }
                    _ => return Err("remove(…) of a non-map".into()),
                },
                _ if n.starts_with("i32.") => {
                    let (x, rx) = int_of(self.spec_in(cx, &args[0], old)?, &args[0])?;
                    let (y, ry) = int_of(self.spec_in(cx, &args[1], old)?, &args[1])?;
                    let (bx, by) = (at(&x, rx, 32), at(&y, ry, 32));
                    let op = match &n[4..] {
                        "add" => "bvadd",
                        "sub" => "bvsub",
                        "mul" => "bvmul",
                        "and" => "bvand",
                        "or" => "bvor",
                        "xor" => "bvxor",
                        "shl" => "bvshl",
                        "shr_s" => "bvashr",
                        "shr_u" => "bvlshr",
                        "div_s" => "bvsdiv",
                        "div_u" => "bvudiv",
                        "rem_s" => "bvsrem",
                        "rem_u" => "bvurem",
                        other => return Err(format!("i32.{other} in a spec")),
                    };
                    let by = if matches!(op, "bvshl" | "bvashr" | "bvlshr") {
                        format!("(bvand {by} (_ bv31 32))")
                    } else {
                        by
                    };
                    S::Int(format!("({op} {bx} {by})"), I32)
                }
                _ => self.call_define(cx, n, args, old)?,
            },
            Expr::Quant(kind, x, dom, body) => match dom {
                Domain::Range(lo, hi) => {
                    let (clo, chi) = (self.constant(cx, lo), self.constant(cx, hi));
                    if let (Some(l), Some(h)) = (clo, chi)
                        && h - l <= 64
                    {
                        // expand
                        let mut parts = vec![];
                        for i in l..h.max(l) {
                            cx.binders.push((x.clone(), num(i)?));
                            let r = self.spec_in(cx, body, old);
                            cx.binders.pop();
                            parts.push(r?);
                        }
                        match kind {
                            QuantKind::Forall | QuantKind::Exists => {
                                let mut bs = vec![];
                                for p in parts {
                                    bs.push(bool_of(p, body)?);
                                }
                                let (op, unit) = if *kind == QuantKind::Forall {
                                    ("and", "true")
                                } else {
                                    ("or", "false")
                                };
                                S::Bool(if bs.is_empty() {
                                    unit.to_string()
                                } else {
                                    format!("({op} {})", bs.join(" "))
                                })
                            }
                            QuantKind::Count => {
                                let n = parts.len() as i128;
                                let w = wid((0, n));
                                let mut is = vec![];
                                for p in parts {
                                    is.push(format!("(ite {} (_ bv1 {w}) (_ bv0 {w}))", bool_of(p, body)?));
                                }
                                S::Int(
                                    if is.is_empty() {
                                        bv(0, w)
                                    } else {
                                        is.into_iter().reduce(|a, b| format!("(bvadd {a} {b})")).unwrap()
                                    },
                                    (0, n),
                                )
                            }
                        }
                    } else {
                        if *kind == QuantKind::Count {
                            return Err("a count over a range that is not constant".into());
                        }
                        let (lo, rlo) = int_of(self.spec_in(cx, lo, old)?, lo)?;
                        let (hi, rhi) = int_of(self.spec_in(cx, hi, old)?, hi)?;
                        let q = bound_name(cx);
                        let rq = (rlo.0, (rhi.1 - 1).max(rlo.0));
                        let wq = wid(rq);
                        cx.binders.push(("#q".into(), S::Bool("true".into())));
                        cx.binders.push((x.clone(), S::Int(q.clone(), rq)));
                        let b = self.spec_in(cx, body, old);
                        cx.binders.pop();
                        cx.binders.pop();
                        let b = bool_of(b?, body)?;
                        let w = wq.max(wid(rlo)).max(wid(rhi));
                        let qw = resize(&q, wq, w);
                        let range = format!("(and (bvsle {} {qw}) (bvslt {qw} {}))", at(&lo, rlo, w), at(&hi, rhi, w));
                        S::Bool(if *kind == QuantKind::Forall {
                            format!("(forall (({q} (_ BitVec {wq}))) (=> {range} {b}))")
                        } else {
                            format!("(exists (({q} (_ BitVec {wq}))) (and {range} {b}))")
                        })
                    }
                }
                Domain::MapKeys(m) => {
                    let S::Map { dom, .. } = self.spec_in(cx, m, old)? else {
                        return Err("a quantifier over a non-map".into());
                    };
                    if *kind == QuantKind::Count {
                        return Err("a count over a map".into());
                    }
                    let q = bound_name(cx);
                    cx.binders.push(("#q".into(), S::Bool("true".into())));
                    cx.binders.push((x.clone(), S::Int(q.clone(), I32)));
                    let b = self.spec_in(cx, body, old);
                    cx.binders.pop();
                    cx.binders.pop();
                    let b = bool_of(b?, body)?;
                    S::Bool(if *kind == QuantKind::Forall {
                        format!("(forall (({q} (_ BitVec 32))) (! (=> (select {dom} {q}) {b}) :pattern ((select {dom} {q}))))")
                    } else {
                        format!("(exists (({q} (_ BitVec 32))) (and (select {dom} {q}) {b}))")
                    })
                }
            },
            Expr::Index(m, k) => match self.spec_in(cx, m, old)? {
                S::Map { val, .. } => {
                    let (k, rk) = int_of(self.spec_in(cx, k, old)?, k)?;
                    if !within(rk, I32) {
                        return Err("a map of i32 indexed by a wider value".into());
                    }
                    S::Int(format!("(select {val} {})", at(&k, rk, 32)), I32)
                }
                _ => return Err(format!("{m} is not a map")),
            },
            Expr::Update(m, k, v) => match self.spec_in(cx, m, old)? {
                S::Map { dom, val, size } => {
                    let (k, rk) = int_of(self.spec_in(cx, k, old)?, k)?;
                    let (v, rv) = int_of(self.spec_in(cx, v, old)?, v)?;
                    if !within(rk, I32) || !within(rv, I32) {
                        return Err("a map of i32 updated with a wider value".into());
                    }
                    let (k, v) = (at(&k, rk, 32), at(&v, rv, 32));
                    let f = self.sop("sadd", 64);
                    S::Map {
                        dom: format!("(store {dom} {k} true)"),
                        val: format!("(store {val} {k} {v})"),
                        size: format!("(ite (select {dom} {k}) {size} ({f} {size} {}))", bv(1, 64)),
                    }
                }
                _ => return Err(format!("{m} is not a map")),
            },
            Expr::InSet(a, es) => {
                let x = self.spec_in(cx, a, old)?;
                let mut parts = vec![];
                for e in es {
                    let y = self.spec_in(cx, e, old)?;
                    parts.push(compare(CmpOp::Eq, &x, &y)?);
                }
                S::Bool(if parts.is_empty() {
                    "false".into()
                } else {
                    format!("(or {})", parts.join(" "))
                })
            }
            Expr::InMap(k, m) => {
                let (k, rk) = int_of(self.spec_in(cx, k, old)?, k)?;
                match self.spec_in(cx, m, old)? {
                    S::Map { dom, .. } if within(rk, I32) => S::Bool(format!("(select {dom} {})", at(&k, rk, 32))),
                    S::Map { dom, .. } => {
                        // a key outside i32 is in no map of i32
                        let w = wid(rk);
                        S::Bool(format!(
                            "(and (bvsle {} {k}) (bvsle {k} {}) (select {dom} ((_ extract 31 0) {k})))",
                            bv(I32.0, w),
                            bv(I32.1, w)
                        ))
                    }
                    _ => return Err(format!("{m} is not a map")),
                }
            }
        })
    }

    fn call_define(&mut self, cx: &mut SpecCx, n: &str, args: &[Expr], old: bool) -> R<S> {
        let d = self
            .plan
            .defines
            .iter()
            .find(|d| d.name == n)
            .ok_or_else(|| format!("unknown {n}"))?
            .clone();
        if d.params.len() != args.len() {
            return Err(format!("{n} takes {} argument(s)", d.params.len()));
        }
        let mut vals = vec![];
        for a in args {
            vals.push(self.spec_in(cx, a, old)?);
        }
        if self.recursive_defines.contains(n) {
            // an SMT function (define-fun-rec in the query's preamble)
            let mut ts = vec![];
            for v in vals {
                match v {
                    S::Int(t, r) => ts.push(at(&t, r, 64)),
                    _ => return Err(format!("{n} takes numbers")),
                }
            }
            let call = if ts.is_empty() {
                format!("|{n}|")
            } else {
                format!("(|{n}| {})", ts.join(" "))
            };
            return Ok(if expr_is_bool(&d.body, &self.plan.defines) {
                S::Bool(call)
            } else {
                S::Int(call, I64)
            });
        }
        // A define that reads memory, applied to an argument with a few possible values
        // (e.g. st(at($k, $d)), whose slot is 0..7), is split into its cases: each case
        // reads at a constant address, and the solver sees one word per slot rather than
        // loads at computed addresses.
        if std::env::var("VC_NOSPLIT").is_err() && reads_memory(&d.body, &self.plan.defines, &mut vec![])
            && let Some(i) = vals
                .iter()
                .position(|v| matches!(v, S::Int(_, (lo, hi)) if lo < hi && hi - lo < SPLIT_LIMIT))
        {
            let S::Int(t, (lo, hi)) = vals[i].clone() else { unreachable!() };
            // (named by the term, so equal facts are equal text)
            let z = format!("cs{:x}", fnv(&t));
            let mut arms = vec![];
            for c in lo..=hi {
                let mut vs = vals.clone();
                vs[i] = num(c)?;
                arms.push((c, self.unfold(cx, &d, vs, old)?));
            }
            let (_, last) = arms.pop().expect("a case");
            let body = match last {
                S::Int(last, rlast) => {
                    let mut r = rlast;
                    for (_, arm) in &arms {
                        let S::Int(_, ra) = arm else { return Err(format!("{n} is not a number")) };
                        r = (r.0.min(ra.0), r.1.max(ra.1));
                    }
                    let w = wid(r);
                    let mut acc = at(&last, rlast, w);
                    for (c, arm) in arms.into_iter().rev() {
                        let S::Int(a, ra) = arm else { unreachable!() };
                        acc = format!("(ite (= {z} {}) {} {acc})", bv(c, wid((lo, hi))), at(&a, ra, w));
                    }
                    S::Int(format!("(let (({z} {t})) {acc})"), r)
                }
                S::Bool(mut acc) => {
                    for (c, arm) in arms.into_iter().rev() {
                        let S::Bool(a) = arm else { return Err(format!("{n} is not a truth value")) };
                        acc = format!("(ite (= {z} {}) {a} {acc})", bv(c, wid((lo, hi))));
                    }
                    S::Bool(format!("(let (({z} {t})) {acc})"))
                }
                _ => return Err(format!("{n} cannot be split into cases")),
            };
            return Ok(body);
        }
        self.unfold(cx, &d, vals, old)
    }

    fn unfold(&mut self, cx: &mut SpecCx, d: &Define, vals: Vec<S>, old: bool) -> R<S> {
        let n = &d.name;
        // unfold, with the parameters bound
        let depth = cx.binders.iter().filter(|(b, _)| b == "#depth").count();
        if depth > 24 {
            return Err(format!("{n} unfolds too deeply"));
        }
        let saved = std::mem::take(&mut cx.binders);
        for b in saved.iter().filter(|(b, _)| b == "#depth" || b == "#q") {
            cx.binders.push(b.clone());
        }
        cx.binders.push(("#depth".into(), S::Bool("true".into())));
        for (p, v) in d.params.iter().zip(vals) {
            cx.binders.push((p.clone(), v));
        }
        let r = self.spec_in(cx, &d.body, old);
        cx.binders = saved;
        r
    }
}

const I32: (i128, i128) = (-(1i128 << 31), (1i128 << 31) - 1);
const I64: (i128, i128) = (-(1i128 << 63), (1i128 << 63) - 1);
const DOM_SORT: &str = "(Array (_ BitVec 32) Bool)";
const VAL_SORT: &str = "(Array (_ BitVec 32) (_ BitVec 32))";
const EMPTY_DOM: &str = "((as const (Array (_ BitVec 32) Bool)) false)";
const EMPTY_VAL: &str = "((as const (Array (_ BitVec 32) (_ BitVec 32))) (_ bv0 32))";

// The width of the narrowest signed bitvector that holds every value in r. (Widths 8 and
// 16 are left to memory bytes, which the integer translation reads as unsigned.)
fn wid(r: (i128, i128)) -> u32 {
    let mut w = 1;
    while w < 127 && !(r.0 >= -(1i128 << (w - 1)) && r.1 < (1i128 << (w - 1))) {
        w += 1;
    }
    if w == 8 || w == 16 { w + 1 } else { w }
}

// A term of width `from` at width `to`: sign-extended, or its low bits.
fn resize(t: &str, from: u32, to: u32) -> String {
    match to.cmp(&from) {
        std::cmp::Ordering::Equal => t.to_string(),
        std::cmp::Ordering::Greater => format!("((_ sign_extend {}) {t})", to - from),
        std::cmp::Ordering::Less => format!("((_ extract {} 0) {t})", to - 1),
    }
}

// A spec number's term (of width wid(r)) at width w.
fn at(t: &str, r: (i128, i128), w: u32) -> String {
    resize(t, wid(r), w)
}

fn check_range(r: (i128, i128)) -> R<()> {
    if within(r, I64) { Ok(()) } else { Err("arithmetic beyond 64 bits".into()) }
}

// A spec number from a term of width w whose value lies in r (exact: it fits).
fn mk(t: String, w: u32, r: (i128, i128)) -> R<S> {
    check_range(r)?;
    Ok(S::Int(resize(&t, w, wid(r)), r))
}

// The spec-arithmetic functions at width w.
fn spec_fns(w: u32) -> String {
    let b = format!("(_ BitVec {w})");
    let z = bv(0, w);
    format!(
        "(define-fun sadd_{w} ((a {b}) (b {b})) {b} (bvadd a b))
(define-fun ssub_{w} ((a {b}) (b {b})) {b} (bvsub a b))
(define-fun smul_{w} ((a {b}) (b {b})) {b} (bvmul a b))
(define-fun sneg_{w} ((a {b})) {b} (bvneg a))
(define-fun emod_{w} ((a {b}) (b {b})) {b} (let ((r (bvsrem a b))) (ite (bvslt r {z}) (ite (bvslt b {z}) (bvsub r b) (bvadd r b)) r)))
(define-fun ediv_{w} ((a {b}) (b {b})) {b} (bvsdiv (bvsub a (emod_{w} a b)) b))
"
    )
}

fn within(r: (i128, i128), bound: (i128, i128)) -> bool {
    r.0 >= bound.0 && r.1 <= bound.1
}

fn num(i: i128) -> R<S> {
    check_range((i, i))?;
    Ok(S::Int(bv(i, wid((i, i))), (i, i)))
}

fn value_of(v: &V, name: &str) -> R<S> {
    match v.w {
        W::B32 => Ok(S::Int(v.t.clone(), I32)),
        W::B64 => Ok(S::Int(v.t.clone(), I64)),
        W::Opaque => Err(format!("${name} is a float")),
    }
}

fn ghost_term(g: &G) -> S {
    match g {
        G::Int(t) => S::Int(t.clone(), I32),
        G::Map { dom, val, size } => S::Map {
            dom: dom.clone(),
            val: val.clone(),
            size: size.clone(),
        },
    }
}

fn expr_is_bool(e: &Expr, defines: &[Define]) -> bool {
    match e {
        Expr::Bool(_) | Expr::Not(_) | Expr::Chain(..) | Expr::InSet(..) | Expr::InMap(..) => {
            true
        }
        Expr::Bin(op, ..) => matches!(op, BinOp::And | BinOp::Or | BinOp::Implies),
        Expr::Quant(k, ..) => *k != QuantKind::Count,
        Expr::Ite(_, a, _) => expr_is_bool(a, defines),
        Expr::Name(n) | Expr::Call(n, _) => defines
            .iter()
            .find(|d| &d.name == n)
            .is_some_and(|d| expr_is_bool(&d.body, defines)),
        _ => false,
    }
}

fn compare(op: CmpOp, a: &S, b: &S) -> R<String> {
    Ok(match (a, b) {
        (S::Int(x, rx), S::Int(y, ry)) => {
            let w = wid(*rx).max(wid(*ry));
            let (x, y) = (at(x, *rx, w), at(y, *ry, w));
            match op {
            CmpOp::Eq => format!("(= {x} {y})"),
            CmpOp::Ne => format!("(not (= {x} {y}))"),
            CmpOp::Lt => format!("(bvslt {x} {y})"),
            CmpOp::Le => format!("(bvsle {x} {y})"),
            CmpOp::Gt => format!("(bvsgt {x} {y})"),
            CmpOp::Ge => format!("(bvsge {x} {y})"),
            }
        }
        (S::Bool(x), S::Bool(y)) => match op {
            CmpOp::Eq => format!("(= {x} {y})"),
            CmpOp::Ne => format!("(not (= {x} {y}))"),
            _ => return Err("ordering truth values".into()),
        },
        (
            S::Map { dom: d1, val: v1, size: s1 },
            S::Map { dom: d2, val: v2, size: s2 },
        ) => {
            let eq = format!("(and (= {d1} {d2}) (= {v1} {v2}) (= {s1} {s2}))");
            match op {
                CmpOp::Eq => eq,
                CmpOp::Ne => format!("(not {eq})"),
                _ => return Err("ordering maps".into()),
            }
        }
        _ => return Err("comparing different kinds of values".into()),
    })
}

struct SpecCx<'b> {
    fp: &'b FuncPlan,
    locals: &'b [V],
    globals: &'b [V],
    mem: &'b String,
    ghosts: &'b BTreeMap<String, G>,
    ghost_locals: &'b BTreeMap<String, G>,
    results: Option<&'b [V]>,
    old: Option<&'b Snapshot>,
    binders: Vec<(String, S)>,
}

// ---------------------------------------------------------------------------------------
// Symbolic execution

fn matching_ends(ops: &[&Operator]) -> HashMap<usize, (Option<usize>, usize)> {
    let mut out = HashMap::new();
    let mut stack: Vec<(usize, Option<usize>)> = vec![];
    for (i, op) in ops.iter().enumerate() {
        match op {
            Operator::Block { .. } | Operator::Loop { .. } | Operator::If { .. } => {
                stack.push((i, None))
            }
            Operator::Else => {
                if let Some(top) = stack.last_mut() {
                    top.1 = Some(i);
                }
            }
            Operator::End => {
                if let Some((start, els)) = stack.pop() {
                    out.insert(start, (els, i));
                }
            }
            _ => {}
        }
    }
    out
}

impl<'a> Gen<'a> {
    fn loop_plan(&self, line: usize) -> Option<&'a crate::checker::LoopPlan> {
        self.fp.loops.iter().find(|l| l.loop_line == line)
    }

    fn checks_cx_locals(&self, st: &St) -> Vec<V> {
        st.locals.clone()
    }

    // assert/assume/set lines that run on arrival at the op at `pc`
    fn line_actions(&mut self, st: &mut St) {
        let pc = st.pc;
        let line = self.lines[pc];
        if pc > 0 && self.lines[pc - 1] == line {
            return; // only before the first op of the line
        }
        let fp = self.fp;
        let mut acts: Vec<(usize, Option<&Check>, Option<&GhostSet>)> = vec![];
        for c in fp.asserts.get(&line).into_iter().flatten() {
            acts.push((c.spec_line, Some(c), None));
        }
        for s in fp.sets.get(&line).into_iter().flatten() {
            acts.push((s.line, None, Some(s)));
        }
        acts.sort_by_key(|a| a.0);
        for (_, c, s) in acts {
            let locals = self.checks_cx_locals(st);
            let old = st.entry.clone();
            if let Some(c) = c {
                if c.kind == CheckKind::Assert {
                    self.oblige_check(st, ObKind::Assert, c, line, &[], fp, &locals, None, Some(&old));
                }
                self.assume_check(st, c, &[], fp, &locals, None, Some(&old));
            }
            if let Some(s) = s {
                let r = {
                    let mut cx = SpecCx {
                        fp,
                        locals: &locals,
                        globals: &st.globals,
                        mem: &st.mem,
                        ghosts: &st.ghosts,
                        ghost_locals: &st.ghost_locals,
                        results: None,
                        old: Some(&old),
                        binders: vec![],
                    };
                    self.spec(&mut cx, &s.value)
                };
                let g = match r {
                    Ok(S::Int(t, range)) => {
                        let w = wid(range);
                        let full = self.define("g", &format!("(_ BitVec {w})"), t);
                        if !within(range, I32) {
                            // a ghost declared i32 must stay an i32
                            let ok = format!(
                                "(and (bvsge {full} {}) (bvsle {full} {}))",
                                bv(I32.0, w),
                                bv(I32.1, w)
                            );
                            let check = Check {
                                kind: CheckKind::Assert,
                                spec_line: s.line,
                                expr: s.value.clone(),
                                subject: Some(s.name.clone()),
                            };
                            self.oblige(st, ObKind::Assert, Some(&check), line, ok.clone());
                            st.path.push(ok);
                        }
                        Some(G::Int(resize(&full, w, 32)))
                    }
                    Ok(S::Map { dom, val, size }) => Some(G::Map {
                        dom: self.define("gd", DOM_SORT, dom),
                        val: self.define("gv", VAL_SORT, val),
                        size: self.define("gs", "(_ BitVec 64)", size),
                    }),
                    _ => None,
                };
                let target = if st.ghost_locals.contains_key(&s.name) {
                    &mut st.ghost_locals
                } else {
                    &mut st.ghosts
                };
                match g {
                    Some(g) => {
                        target.insert(s.name.clone(), g);
                    }
                    None => {
                        // an update we cannot state: the ghost becomes unknown
                        st.approx = true;
                        if let Some(old_g) = target.get(&s.name).cloned() {
                            let fresh = match old_g {
                                G::Int(_) => self.fresh_ghost(&GhostType::Scalar("int".into()), "gh", &mut st.path),
                                G::Map { .. } => self.fresh_ghost(&GhostType::Map, "gh", &mut st.path),
                            };
                            target.insert(s.name.clone(), fresh);
                        }
                    }
                }
            }
        }
    }

    fn check_local_refinements(&mut self, st: &mut St, var: usize, at_line: usize) {
        let fp = self.fp;
        if let Some(cs) = fp.local_checks.get(&var) {
            let locals = st.locals.clone();
            let old = st.entry.clone();
            for c in cs {
                self.oblige_check(st, ObKind::LocalRefinement, c, at_line, &[], fp, &locals, None, Some(&old));
                self.assume_check(st, c, &[], fp, &locals, None, Some(&old));
            }
        }
    }

    fn exit(&mut self, st: &mut St, results: Vec<V>, at_line: usize) {
        let fp = self.fp;
        let locals = st.locals.clone();
        let old = st.entry.clone();
        for c in &fp.exit_checks {
            self.oblige_check(st, ObKind::Ensures, c, at_line, &[], fp, &locals, Some(&results), Some(&old));
        }
        st.returned = Some(results);
    }

    fn trap(&mut self, st: &mut St, kind: TrapKind, at_line: usize, ok: String) {
        self.oblige(st, ObKind::NoTrap(kind), None, at_line, ok.clone());
        st.path.push(ok);
    }

    fn mem_access(&mut self, st: &mut St, addr: &V, offset: u64, bytes: u64, at_line: usize) -> String {
        let end = offset + bytes;
        let ok = format!(
            "(bvule (bvadd ((_ zero_extend 32) {}) (_ bv{end} 64)) (_ bv{} 64))",
            addr.t, self.mem_bytes
        );
        self.trap(st, TrapKind::OutOfBounds, at_line, ok);
        if offset == 0 {
            addr.t.clone()
        } else {
            format!("(bvadd {} (_ bv{offset} 32))", addr.t)
        }
    }

    // the state a loop's body may change: (locals, globals, memory, ghost names)
    fn loop_writes(&self, pc: usize, end: usize) -> (BTreeSet<u32>, BTreeSet<u32>, bool, BTreeSet<String>) {
        let mut locals = BTreeSet::new();
        let mut globals = BTreeSet::new();
        let mut mem = false;
        let mut ghosts = BTreeSet::new();
        let nimports = self.func_imports();
        for i in pc..=end {
            match self.ops[i] {
                Operator::LocalSet { local_index } | Operator::LocalTee { local_index } => {
                    locals.insert(*local_index);
                }
                Operator::GlobalSet { global_index } => {
                    globals.insert(*global_index);
                }
                Operator::Call { function_index } => {
                    if let Some(f) = (*function_index as usize).checked_sub(nimports)
                        && let Some(info) = self.infos.get(f)
                    {
                        mem |= info.writes_mem;
                        globals.extend(info.writes_globals.iter().copied());
                        ghosts.extend(info.sets_ghosts.iter().cloned());
                    }
                }
                Operator::CallIndirect { .. } => {
                    mem = true;
                    globals.extend(0..self.module.globals.len() as u32);
                    ghosts.extend(self.plan.ghost_globals.iter().map(|(n, _)| n.clone()));
                }
                op if is_store(op) => mem = true,
                Operator::MemoryFill { .. }
                | Operator::MemoryCopy { .. }
                | Operator::MemoryGrow { .. } => mem = true,
                _ => {}
            }
        }
        let (l0, l1) = (self.lines[pc], self.lines[end]);
        for (line, sets) in &self.fp.sets {
            if *line >= l0 && *line <= l1 {
                for s in sets {
                    ghosts.insert(s.name.clone());
                }
            }
        }
        (locals, globals, mem, ghosts)
    }

    fn func_imports(&self) -> usize {
        self.module
            .imports
            .iter()
            .filter(|i| matches!(i.ty, wasmparser::TypeRef::Func(_)))
            .count()
    }

    fn enter_loop(&mut self, st: &mut St, pc: usize, end: usize) {
        let line = self.lines[pc];
        let lp = self.loop_plan(line);
        let fp = self.fp;
        let old = st.entry.clone();
        if let Some(lp) = lp {
            let locals = st.locals.clone();
            for c in &lp.invariants {
                self.oblige_check(st, ObKind::InvariantEntry, c, line, &[], fp, &locals, None, Some(&old));
            }
            if let Some(c) = &lp.decreases {
                let r = {
                    let mut cx = SpecCx {
                        fp,
                        locals: &locals,
                        globals: &st.globals,
                        mem: &st.mem,
                        ghosts: &st.ghosts,
                        ghost_locals: &st.ghost_locals,
                        results: None,
                        old: Some(&old),
                        binders: vec![],
                    };
                    self.spec_int(&mut cx, &c.expr)
                };
                match r {
                    Ok(m) => self.oblige(st, ObKind::MeasureEntry, Some(c), line, format!("(bvsge {m} (_ bv0 64))")),
                    Err(why) => self.oblige_unsupported(st, ObKind::MeasureEntry, Some(c), line, why),
                }
            }
        }
        // the head: what the body writes is arbitrary, then the invariant holds
        let (wl, wg, wm, wgh) = self.loop_writes(pc, end);
        for l in &wl {
            let w = st.locals[*l as usize].w;
            st.locals[*l as usize] = self.fresh_value(w, "l");
        }
        for g in &wg {
            let w = st.globals[*g as usize].w;
            st.globals[*g as usize] = self.fresh_value(w, "glob");
        }
        if wm {
            st.mem = self.declare("mem", MEM_SORT);
        }
        for name in &wgh {
            let ty = |g: &G| match g {
                G::Int(_) => GhostType::Scalar("int".into()),
                G::Map { .. } => GhostType::Map,
            };
            if let Some(g) = st.ghost_locals.get(name).cloned() {
                let f = self.fresh_ghost(&ty(&g), name, &mut st.path);
                st.ghost_locals.insert(name.clone(), f);
            } else if let Some(g) = st.ghosts.get(name).cloned() {
                let f = self.fresh_ghost(&ty(&g), name, &mut st.path);
                st.ghosts.insert(name.clone(), f);
            }
        }
        // refined locals keep their promise
        let locals = st.locals.clone();
        for l in &wl {
            if let Some(cs) = fp.local_checks.get(&(*l as usize)) {
                for c in cs {
                    self.assume_check(st, c, &[], fp, &locals, None, Some(&old));
                }
            }
        }
        let mut measure = None;
        if let Some(lp) = lp {
            for c in &lp.invariants {
                self.assume_check(st, c, &[], fp, &locals, None, Some(&old));
            }
            if let Some(c) = &lp.decreases {
                let r = {
                    let mut cx = SpecCx {
                        fp,
                        locals: &locals,
                        globals: &st.globals,
                        mem: &st.mem,
                        ghosts: &st.ghosts,
                        ghost_locals: &st.ghost_locals,
                        results: None,
                        old: Some(&old),
                        binders: vec![],
                    };
                    self.spec_int(&mut cx, &c.expr)
                };
                if let Ok(m) = r {
                    let m0 = self.define("m", "(_ BitVec 64)", m);
                    st.path.push(format!("(bvsge {m0} (_ bv0 64))"));
                    measure = Some(m0);
                }
            }
        }
        st.cut = Cut::LoopHead(line);
        st.cut_state = Rc::new(st.snapshot());
        st.ctl.push(Ctl::Loop {
            pc,
            end,
            height: st.stack.len(),
            measure,
        });
    }

    fn back_edge(&mut self, st: &mut St, loop_pc: usize, measure: Option<String>, at_line: usize) {
        let line = self.lines[loop_pc];
        let fp = self.fp;
        let old = st.entry.clone();
        if let Some(lp) = self.loop_plan(line) {
            let locals = st.locals.clone();
            for c in &lp.invariants {
                self.oblige_check(st, ObKind::InvariantKept, c, at_line, &[], fp, &locals, None, Some(&old));
            }
            if let Some(c) = &lp.decreases {
                let r = {
                    let mut cx = SpecCx {
                        fp,
                        locals: &locals,
                        globals: &st.globals,
                        mem: &st.mem,
                        ghosts: &st.ghosts,
                        ghost_locals: &st.ghost_locals,
                        results: None,
                        old: Some(&old),
                        binders: vec![],
                    };
                    self.spec_int(&mut cx, &c.expr)
                };
                match (r, measure) {
                    (Ok(m1), Some(m0)) => self.oblige(
                        st,
                        ObKind::Measure,
                        Some(c),
                        at_line,
                        format!("(and (bvsle (_ bv0 64) {m1}) (bvslt {m1} {m0}))"),
                    ),
                    (Err(why), _) => self.oblige_unsupported(st, ObKind::Measure, Some(c), at_line, why),
                    (Ok(_), None) => self.oblige_unsupported(
                        st,
                        ObKind::Measure,
                        Some(c),
                        at_line,
                        "the measure at the loop head could not be stated".into(),
                    ),
                }
            }
        }
    }

    // A branch to the frame `depth` levels out: returns whether the path continues.
    fn branch(&mut self, st: &mut St, depth: u32, at_line: usize) -> bool {
        let idx = st.ctl.len() - 1 - depth as usize;
        match st.ctl[idx].clone() {
            Ctl::Loop { pc, measure, height, .. } => {
                let _ = height;
                self.back_edge(st, pc, measure, at_line);
                false
            }
            Ctl::Block { end, arity, height } | Ctl::If { end, arity, height } => {
                let results: Vec<V> = st.stack[st.stack.len() - arity..].to_vec();
                st.stack.truncate(height);
                st.stack.extend(results);
                st.ctl.truncate(idx);
                st.pc = end + 1;
                true
            }
            Ctl::Func => {
                let n = self.fp.results.len();
                let results = st.stack[st.stack.len() - n..].to_vec();
                self.exit(st, results, at_line);
                false
            }
        }
    }

    fn binop(&mut self, st: &mut St, w: W, f: &str) {
        let b = st.stack.pop().unwrap();
        let a = st.stack.pop().unwrap();
        let v = self.value(w, format!("({f} {} {})", a.t, b.t));
        st.stack.push(v);
    }

    fn cmp(&mut self, st: &mut St, f: &str) {
        let b = st.stack.pop().unwrap();
        let a = st.stack.pop().unwrap();
        let v = self.value(W::B32, format!("(ite ({f} {} {}) (_ bv1 32) (_ bv0 32))", a.t, b.t));
        st.stack.push(v);
    }

    fn shift(&mut self, st: &mut St, w: W, f: &str) {
        let bits = if w == W::B32 { 32 } else { 64 };
        let b = st.stack.pop().unwrap();
        let a = st.stack.pop().unwrap();
        let v = self.value(
            w,
            format!("({f} {} (bvand {} (_ bv{} {bits})))", a.t, b.t, bits - 1),
        );
        st.stack.push(v);
    }

    fn divide(&mut self, st: &mut St, w: W, f: &str, signed: bool, at_line: usize) {
        let bits = if w == W::B32 { 32 } else { 64 };
        let b = st.stack.pop().unwrap();
        let a = st.stack.pop().unwrap();
        self.trap(st, TrapKind::DivideByZero, at_line, format!("(not (= {} (_ bv0 {bits})))", b.t));
        if signed && (f == "bvsdiv") {
            let min = if bits == 32 { "#x80000000" } else { "#x8000000000000000" };
            let ones = if bits == 32 { "#xffffffff" } else { "#xffffffffffffffff" };
            self.trap(
                st,
                TrapKind::Overflow,
                at_line,
                format!("(not (and (= {} {min}) (= {} {ones})))", a.t, b.t),
            );
        }
        let v = self.value(w, format!("({f} {} {})", a.t, b.t));
        st.stack.push(v);
    }

    fn load(&mut self, st: &mut St, offset: u64, bytes: u64, w: W, signed: bool, at_line: usize) {
        let a = st.stack.pop().unwrap();
        let addr = self.mem_access(st, &a, offset, bytes, at_line);
        let raw = match bytes {
            1 => format!("(ld8 {} {addr})", st.mem),
            2 => format!("(ld16 {} {addr})", st.mem),
            4 => format!("(ld32 {} {addr})", st.mem),
            _ => format!("(ld64 {} {addr})", st.mem),
        };
        let bits = if w == W::B32 { 32 } else { 64 };
        let term = if bytes * 8 == bits {
            raw
        } else if signed {
            format!("((_ sign_extend {}) {raw})", bits - bytes * 8)
        } else {
            format!("((_ zero_extend {}) {raw})", bits - bytes * 8)
        };
        let v = self.value(w, term);
        st.stack.push(v);
    }

    fn store(&mut self, st: &mut St, offset: u64, bytes: u64, at_line: usize) {
        let v = st.stack.pop().unwrap();
        let a = st.stack.pop().unwrap();
        let addr = self.mem_access(st, &a, offset, bytes, at_line);
        let val = |bits: u64| {
            let vb = if v.w == W::B32 { 32 } else { 64 };
            if bits == vb {
                v.t.clone()
            } else {
                format!("((_ extract {} 0) {})", bits - 1, v.t)
            }
        };
        let term = match bytes {
            1 => format!("(st8 {} {addr} {})", st.mem, val(8)),
            2 => format!("(st16 {} {addr} {})", st.mem, val(16)),
            4 => format!("(st32 {} {addr} {})", st.mem, val(32)),
            _ => format!("(st64 {} {addr} {})", st.mem, val(64)),
        };
        st.mem = self.define("mem", MEM_SORT, term);
    }

    fn call(&mut self, st: &mut St, function_index: u32, at_line: usize) {
        let nimports = self.func_imports();
        let Some(f) = (function_index as usize).checked_sub(nimports) else {
            // an imported (host) function: its results are arbitrary
            if let Some(ty) = self.import_type(function_index) {
                for _ in 0..ty.0 {
                    st.stack.pop();
                }
                for w in ty.1 {
                    let v = self.fresh_value(w, "r");
                    st.stack.push(v);
                }
                if !ty.2 {
                    st.approx = true;
                }
            }
            return;
        };
        let callee = &self.plan.funcs[f];
        let module_func = &self.module.functions[f];
        let ft = &self.module.types[module_func.type_idx as usize];
        let nargs = ft.params().len();
        let args: Vec<V> = st.stack.split_off(st.stack.len() - nargs);
        // the callee's view: its params are the arguments, its other locals arbitrary
        let mut callee_locals = args.clone();
        for v in &callee.vars[nargs..] {
            let w = if v.width == 64 { W::B64 } else if v.width == 32 { W::B32 } else { W::Opaque };
            let fv = self.fresh_value(w, "cl");
            callee_locals.push(fv);
        }
        let callee_ghost_locals: BTreeMap<String, G> = callee
            .ghost_locals
            .iter()
            .map(|(n, t)| (n.clone(), self.initial_ghost(t)))
            .collect();
        // its precondition, at the call
        let pre = Snapshot {
            locals: callee_locals.clone(),
            globals: st.globals.clone(),
            mem: st.mem.clone(),
            ghosts: st.ghosts.clone(),
            ghost_locals: callee_ghost_locals.clone(),
        };
        for c in &callee.entry_checks {
            let mut cx = SpecCx {
                fp: callee,
                locals: &callee_locals,
                globals: &st.globals,
                mem: &st.mem,
                ghosts: &st.ghosts,
                ghost_locals: &callee_ghost_locals,
                results: None,
                old: None,
                binders: vec![],
            };
            let r = self.spec_bool(&mut cx, &c.expr);
            let ob = Obligation {
                func: self.func,
                kind: ObKind::Requires,
                check_kind: Some(c.kind),
                spec_line: Some(c.spec_line),
                at_line,
                smt: String::new(),
                hash: 0,
                    approximate: st.approx,
                unsupported: None,
                cut: st.cut.clone(),
                reads: vec![],
                terms: vec![],
            };
            match r {
                Ok(goal) => {
                    self.obligations.push((ob, self.decls.len(), st.path.clone(), goal.clone(), st.cut_state.clone()));
                    st.path.push(goal);
                }
                Err(why) => {
                    let mut ob = ob;
                    ob.unsupported = Some(why);
                    self.obligations.push((ob, self.decls.len(), st.path.clone(), "true".into(), st.cut_state.clone()));
                    st.approx = true;
                }
            }
        }
        // what it may change is arbitrary afterwards
        let info = &self.infos[f];
        if info.writes_mem {
            st.mem = self.declare("mem", MEM_SORT);
        }
        for g in info.writes_globals.clone() {
            let w = st.globals[g as usize].w;
            st.globals[g as usize] = self.fresh_value(w, "glob");
        }
        for name in info.sets_ghosts.clone() {
            if let Some(g) = st.ghosts.get(&name).cloned() {
                let ty = match g {
                    G::Int(_) => GhostType::Scalar("int".into()),
                    G::Map { .. } => GhostType::Map,
                };
                let fresh = self.fresh_ghost(&ty, &name, &mut st.path);
                st.ghosts.insert(name, fresh);
            }
        }
        let results: Vec<V> = ft
            .results()
            .iter()
            .map(|t| width(t))
            .collect::<Vec<_>>()
            .into_iter()
            .map(|w| self.fresh_value(w, "ret"))
            .collect();
        // its postcondition is a fact
        for c in &callee.exit_checks {
            let r = {
                let mut cx = SpecCx {
                    fp: callee,
                    locals: &callee_locals,
                    globals: &st.globals,
                    mem: &st.mem,
                    ghosts: &st.ghosts,
                    ghost_locals: &callee_ghost_locals,
                    results: Some(&results),
                    old: Some(&pre),
                    binders: vec![],
                };
                self.spec_bool(&mut cx, &c.expr)
            };
            match r {
                Ok(fact) => st.path.push(fact),
                Err(_) => st.approx = true,
            }
        }
        st.stack.extend(results);
    }

    fn import_type(&self, function_index: u32) -> Option<(usize, Vec<W>, bool)> {
        let mut i = 0;
        for imp in &self.module.imports {
            if let wasmparser::TypeRef::Func(t) = imp.ty {
                if i == function_index {
                    let ft = self.module.types.get(t as usize)?;
                    let ws: Vec<W> = ft.results().iter().map(width).collect();
                    return Some((ft.params().len(), ws.clone(), ws.is_empty()));
                }
                i += 1;
            }
        }
        None
    }

    // Run one path until it ends; forks go onto `work`.
    fn run_path(&mut self, mut st: St, work: &mut Vec<St>) {
        let mut steps = 0;
        loop {
            steps += 1;
            if steps > 20_000 || self.obligations.len() > 2_000 {
                self.unsupported = Some("the function is too large to analyse".into());
                return;
            }
            if st.pc >= self.ops.len() {
                return;
            }
            self.line_actions(&mut st);
            let pc = st.pc;
            let line = self.lines[pc];
            let op = self.ops[pc];
            st.pc += 1;
            use Operator as O;
            match op {
                O::Nop => {}
                O::Unreachable => {
                    self.oblige(&st, ObKind::Unreachable, None, line, "false".into());
                    return;
                }
                O::Block { blockty } => {
                    let Ok((_, arity)) = block_arity(self.module, blockty) else { return };
                    let end = self.matching[&pc].1;
                    st.ctl.push(Ctl::Block { end, arity, height: st.stack.len() });
                }
                O::Loop { .. } => {
                    let end = self.matching[&pc].1;
                    self.enter_loop(&mut st, pc, end);
                }
                O::If { blockty } => {
                    let Ok((_, arity)) = block_arity(self.module, blockty) else { return };
                    let (els, end) = self.matching[&pc];
                    let c = st.stack.pop().unwrap();
                    let mut other = st.clone();
                    st.path.push(format!("(not (= {} (_ bv0 32)))", c.t));
                    st.ctl.push(Ctl::If { end, arity, height: st.stack.len() });
                    other.path.push(format!("(= {} (_ bv0 32))", c.t));
                    other.ctl.push(Ctl::If { end, arity, height: other.stack.len() });
                    other.pc = match els {
                        Some(e) => e + 1,
                        None => end,
                    };
                    work.push(other);
                }
                O::Else => {
                    // the then-arm is done: go to the end
                    if let Some(Ctl::If { end, .. }) = st.ctl.pop() {
                        st.pc = end + 1;
                    }
                }
                O::End => match st.ctl.pop() {
                    Some(Ctl::Func) | None => {
                        let n = self.fp.results.len();
                        let results = st.stack[st.stack.len().saturating_sub(n)..].to_vec();
                        self.exit(&mut st, results, line);
                        return;
                    }
                    Some(_) => {}
                },
                O::Br { relative_depth } => {
                    if !self.branch(&mut st, *relative_depth, line) {
                        return;
                    }
                }
                O::BrIf { relative_depth } => {
                    let c = st.stack.pop().unwrap();
                    let mut taken = st.clone();
                    taken.path.push(format!("(not (= {} (_ bv0 32)))", c.t));
                    st.path.push(format!("(= {} (_ bv0 32))", c.t));
                    if self.branch(&mut taken, *relative_depth, line) {
                        work.push(taken);
                    }
                }
                O::Return => {
                    let n = self.fp.results.len();
                    let results = st.stack[st.stack.len() - n..].to_vec();
                    self.exit(&mut st, results, line);
                    return;
                }
                O::Call { function_index } => self.call(&mut st, *function_index, line),
                O::Drop => {
                    st.stack.pop();
                }
                O::Select | O::TypedSelect { .. } => {
                    let c = st.stack.pop().unwrap();
                    let b = st.stack.pop().unwrap();
                    let a = st.stack.pop().unwrap();
                    let v = self.value(a.w, format!("(ite (not (= {} (_ bv0 32))) {} {})", c.t, a.t, b.t));
                    st.stack.push(v);
                }
                O::LocalGet { local_index } => {
                    let v = st.locals[*local_index as usize].clone();
                    st.stack.push(v);
                }
                O::LocalSet { local_index } | O::LocalTee { local_index } => {
                    let v = st.stack.pop().unwrap();
                    st.locals[*local_index as usize] = v.clone();
                    if matches!(op, O::LocalTee { .. }) {
                        st.stack.push(v);
                    }
                    self.check_local_refinements(&mut st, *local_index as usize, line);
                }
                O::GlobalGet { global_index } => {
                    let v = st.globals[*global_index as usize].clone();
                    st.stack.push(v);
                }
                O::GlobalSet { global_index } => {
                    let v = st.stack.pop().unwrap();
                    st.globals[*global_index as usize] = v;
                }
                O::I32Const { value } => st.stack.push(V { t: bv(*value as i128, 32), w: W::B32 }),
                O::I64Const { value } => st.stack.push(V { t: bv(*value as i128, 64), w: W::B64 }),
                O::I32Add => self.binop(&mut st, W::B32, "bvadd"),
                O::I32Sub => self.binop(&mut st, W::B32, "bvsub"),
                O::I32Mul => self.binop(&mut st, W::B32, "bvmul"),
                O::I32And => self.binop(&mut st, W::B32, "bvand"),
                O::I32Or => self.binop(&mut st, W::B32, "bvor"),
                O::I32Xor => self.binop(&mut st, W::B32, "bvxor"),
                O::I32Shl => self.shift(&mut st, W::B32, "bvshl"),
                O::I32ShrS => self.shift(&mut st, W::B32, "bvashr"),
                O::I32ShrU => self.shift(&mut st, W::B32, "bvlshr"),
                O::I32Rotl => self.shift(&mut st, W::B32, "ext_rotate_left"),
                O::I32Rotr => self.shift(&mut st, W::B32, "ext_rotate_right"),
                O::I32DivS => self.divide(&mut st, W::B32, "bvsdiv", true, line),
                O::I32DivU => self.divide(&mut st, W::B32, "bvudiv", false, line),
                O::I32RemS => self.divide(&mut st, W::B32, "bvsrem", true, line),
                O::I32RemU => self.divide(&mut st, W::B32, "bvurem", false, line),
                O::I64Add => self.binop(&mut st, W::B64, "bvadd"),
                O::I64Sub => self.binop(&mut st, W::B64, "bvsub"),
                O::I64Mul => self.binop(&mut st, W::B64, "bvmul"),
                O::I64And => self.binop(&mut st, W::B64, "bvand"),
                O::I64Or => self.binop(&mut st, W::B64, "bvor"),
                O::I64Xor => self.binop(&mut st, W::B64, "bvxor"),
                O::I64Shl => self.shift(&mut st, W::B64, "bvshl"),
                O::I64ShrS => self.shift(&mut st, W::B64, "bvashr"),
                O::I64ShrU => self.shift(&mut st, W::B64, "bvlshr"),
                O::I64DivS => self.divide(&mut st, W::B64, "bvsdiv", true, line),
                O::I64DivU => self.divide(&mut st, W::B64, "bvudiv", false, line),
                O::I64RemS => self.divide(&mut st, W::B64, "bvsrem", true, line),
                O::I64RemU => self.divide(&mut st, W::B64, "bvurem", false, line),
                O::I32Eqz | O::I64Eqz => {
                    let a = st.stack.pop().unwrap();
                    let zero = if a.w == W::B32 { "(_ bv0 32)" } else { "(_ bv0 64)" };
                    let v = self.value(W::B32, format!("(ite (= {} {zero}) (_ bv1 32) (_ bv0 32))", a.t));
                    st.stack.push(v);
                }
                O::I32Eq | O::I64Eq => self.cmp(&mut st, "="),
                O::I32Ne | O::I64Ne => {
                    let b = st.stack.pop().unwrap();
                    let a = st.stack.pop().unwrap();
                    let v = self.value(W::B32, format!("(ite (= {} {}) (_ bv0 32) (_ bv1 32))", a.t, b.t));
                    st.stack.push(v);
                }
                O::I32LtS | O::I64LtS => self.cmp(&mut st, "bvslt"),
                O::I32LtU | O::I64LtU => self.cmp(&mut st, "bvult"),
                O::I32GtS | O::I64GtS => self.cmp(&mut st, "bvsgt"),
                O::I32GtU | O::I64GtU => self.cmp(&mut st, "bvugt"),
                O::I32LeS | O::I64LeS => self.cmp(&mut st, "bvsle"),
                O::I32LeU | O::I64LeU => self.cmp(&mut st, "bvule"),
                O::I32GeS | O::I64GeS => self.cmp(&mut st, "bvsge"),
                O::I32GeU | O::I64GeU => self.cmp(&mut st, "bvuge"),
                O::I32WrapI64 => {
                    let a = st.stack.pop().unwrap();
                    let v = self.value(W::B32, format!("((_ extract 31 0) {})", a.t));
                    st.stack.push(v);
                }
                O::I64ExtendI32S | O::I64ExtendI32U => {
                    let a = st.stack.pop().unwrap();
                    let f = if matches!(op, O::I64ExtendI32S) { "sign_extend" } else { "zero_extend" };
                    let v = self.value(W::B64, format!("((_ {f} 32) {})", a.t));
                    st.stack.push(v);
                }
                O::I32Extend8S | O::I32Extend16S => {
                    let a = st.stack.pop().unwrap();
                    let n = if matches!(op, O::I32Extend8S) { 8 } else { 16 };
                    let v = self.value(
                        W::B32,
                        format!("((_ sign_extend {}) ((_ extract {} 0) {}))", 32 - n, n - 1, a.t),
                    );
                    st.stack.push(v);
                }
                O::I32Load { memarg } => self.load(&mut st, memarg.offset, 4, W::B32, false, line),
                O::I32Load8S { memarg } => self.load(&mut st, memarg.offset, 1, W::B32, true, line),
                O::I32Load8U { memarg } => self.load(&mut st, memarg.offset, 1, W::B32, false, line),
                O::I32Load16S { memarg } => self.load(&mut st, memarg.offset, 2, W::B32, true, line),
                O::I32Load16U { memarg } => self.load(&mut st, memarg.offset, 2, W::B32, false, line),
                O::I64Load { memarg } => self.load(&mut st, memarg.offset, 8, W::B64, false, line),
                O::I32Store { memarg } => self.store(&mut st, memarg.offset, 4, line),
                O::I32Store8 { memarg } => self.store(&mut st, memarg.offset, 1, line),
                O::I32Store16 { memarg } => self.store(&mut st, memarg.offset, 2, line),
                O::I64Store { memarg } => self.store(&mut st, memarg.offset, 8, line),
                O::BrTable { .. } | O::ReturnCall { .. } | O::ReturnCallIndirect { .. } => {
                    self.unsupported = Some(format!("{op:?} is not supported by the prover"));
                    return;
                }
                _ => {
                    // anything else (floats, bulk memory, …): its results are arbitrary
                    let ty = &self.op_types[pc];
                    for _ in 0..ty.0 {
                        st.stack.pop();
                    }
                    for w in ty.1.clone() {
                        let v = self.fresh_value(w, "x");
                        st.stack.push(v);
                    }
                    if is_store(op)
                        || matches!(op, O::MemoryFill { .. } | O::MemoryCopy { .. } | O::MemoryGrow { .. })
                    {
                        st.mem = self.declare("mem", MEM_SORT);
                    }
                    if matches!(op, O::CallIndirect { .. }) {
                        st.mem = self.declare("mem", MEM_SORT);
                        for g in 0..st.globals.len() {
                            let w = st.globals[g].w;
                            st.globals[g] = self.fresh_value(w, "glob");
                        }
                    }
                    st.approx = true;
                }
            }
        }
    }
}

fn is_store(op: &Operator) -> bool {
    use Operator as O;
    matches!(
        op,
        O::I32Store { .. }
            | O::I64Store { .. }
            | O::F32Store { .. }
            | O::F64Store { .. }
            | O::I32Store8 { .. }
            | O::I32Store16 { .. }
            | O::I64Store8 { .. }
            | O::I64Store16 { .. }
            | O::I64Store32 { .. }
    )
}

// ---------------------------------------------------------------------------------------
// The whole module

fn is_pure_define(d: &Define, defines: &[Define], seen: &mut Vec<String>) -> bool {
    if seen.contains(&d.name) {
        return true; // recursion: pure if the rest is
    }
    seen.push(d.name.clone());
    let mut bound: Vec<String> = d.params.clone();
    let r = pure_expr(&d.body, defines, &mut bound, seen);
    seen.pop();
    r
}

fn pure_expr(e: &Expr, defines: &[Define], bound: &mut Vec<String>, seen: &mut Vec<String>) -> bool {
    match e {
        Expr::Int(_) | Expr::Bool(_) => true,
        Expr::Var(v) => bound.contains(v),
        Expr::Name(n) => {
            bound.contains(n)
                || defines
                    .iter()
                    .find(|d| &d.name == n)
                    .is_some_and(|d| d.params.is_empty() && is_pure_define(d, defines, seen))
        }
        Expr::Call(n, args) => {
            let ok_args = args.iter().all(|a| pure_expr(a, defines, bound, seen));
            match n.as_str() {
                "load" | "load8" | "old" | "size" | "remove" => false,
                "u" | "abs" | "min" | "max" => ok_args,
                _ if n.starts_with("i32.") => ok_args,
                _ => {
                    ok_args
                        && defines
                            .iter()
                            .find(|d| &d.name == n)
                            .is_some_and(|d| is_pure_define(d, defines, seen))
                }
            }
        }
        Expr::Quant(_, x, dom, body) => {
            let dom_ok = match dom {
                Domain::Range(lo, hi) => {
                    pure_expr(lo, defines, bound, seen) && pure_expr(hi, defines, bound, seen)
                }
                Domain::MapKeys(_) => false,
            };
            bound.push(x.clone());
            let r = dom_ok && pure_expr(body, defines, bound, seen);
            bound.pop();
            r
        }
        Expr::MapEmpty | Expr::Index(..) | Expr::Update(..) | Expr::InMap(..) => false,
        Expr::Neg(a) | Expr::Not(a) => pure_expr(a, defines, bound, seen),
        Expr::Bin(_, a, b) => pure_expr(a, defines, bound, seen) && pure_expr(b, defines, bound, seen),
        Expr::Chain(es, _) => es.iter().all(|x| pure_expr(x, defines, bound, seen)),
        Expr::Ite(a, b, c) => [a, b, c].iter().all(|x| pure_expr(x, defines, bound, seen)),
        Expr::InSet(a, es) => {
            pure_expr(a, defines, bound, seen) && es.iter().all(|x| pure_expr(x, defines, bound, seen))
        }
    }
}

const SPLIT_LIMIT: i128 = 16;

// Bound variables are named by their nesting depth, so equal facts are equal text.
fn bound_name(cx: &SpecCx) -> String {
    format!("qb{}", cx.binders.iter().filter(|(b, _)| b == "#q").count())
}

// The conjuncts of an SMT term, flattening nested (and …), in one pass.
fn conjuncts(t: &str) -> Vec<&str> {
    let t = t.trim();
    if !t.starts_with("(and ") {
        return vec![t];
    }
    let b = t.as_bytes();
    let mut out = vec![];
    // for each open list: is it an (and …), and where it starts if it is a conjunct
    let mut stack: Vec<(bool, Option<usize>)> = vec![];
    let in_and = |stack: &Vec<(bool, Option<usize>)>| stack.last().is_some_and(|(a, _)| *a);
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'(' => {
                let is_and = t[i + 1..].starts_with("and ") && (stack.is_empty() || in_and(&stack));
                let start = (!is_and && in_and(&stack)).then_some(i);
                stack.push((is_and, start));
                if is_and {
                    i += 4;
                }
            }
            b')' => {
                if let Some((_, Some(s))) = stack.pop() {
                    out.push(&t[s..=i]);
                }
            }
            c if c.is_ascii_whitespace() => {}
            _ => {
                // an atom (or |quoted symbol|)
                let s = i;
                if b[i] == b'|' {
                    i += 1;
                    while i < b.len() && b[i] != b'|' {
                        i += 1;
                    }
                } else {
                    while i + 1 < b.len() && !b[i + 1].is_ascii_whitespace() && b[i + 1] != b'(' && b[i + 1] != b')' {
                        i += 1;
                    }
                }
                if in_and(&stack) {
                    out.push(&t[s..=i.min(b.len() - 1)]);
                }
            }
        }
        i += 1;
    }
    out
}

// Whether an expression reads memory, directly or through the defines it uses.
fn reads_memory(e: &Expr, defines: &[Define], seen: &mut Vec<String>) -> bool {
    let mut found = false;
    let mut called = vec![];
    e.walk(&mut |x| match x {
        Expr::Call(n, _) if n == "load" || n == "load8" => found = true,
        Expr::Call(n, _) | Expr::Name(n) => called.push(n.clone()),
        _ => {}
    });
    found
        || called.iter().any(|n| {
            if seen.contains(n) {
                return false;
            }
            seen.push(n.clone());
            defines
                .iter()
                .find(|d| &d.name == n)
                .is_some_and(|d| reads_memory(&d.body, defines, seen))
        })
}

fn mentions_name(e: &Expr, name: &str) -> bool {
    let mut found = false;
    e.walk(&mut |x| {
        if matches!(x, Expr::Call(n, _) | Expr::Name(n) if n == name) {
            found = true
        }
    });
    found
}

fn fnv(s: &str) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in s.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

fn func_infos(plan: &SpecPlan, module: &ValidModule) -> Vec<FuncInfo> {
    let nimports = module
        .imports
        .iter()
        .filter(|i| matches!(i.ty, wasmparser::TypeRef::Func(_)))
        .count();
    let ghost_globals: HashSet<&String> = plan.ghost_globals.iter().map(|(n, _)| n).collect();
    let mut infos: Vec<FuncInfo> = vec![];
    let mut calls: Vec<Vec<usize>> = vec![];
    for (f, func) in module.functions.iter().enumerate() {
        let mut info = FuncInfo {
            writes_mem: false,
            writes_globals: BTreeSet::new(),
            sets_ghosts: BTreeSet::new(),
        };
        let mut cs = vec![];
        for op in &func.operators {
            let op = op.inner.operator();
            match op {
                Operator::GlobalSet { global_index } => {
                    info.writes_globals.insert(*global_index);
                }
                Operator::Call { function_index } => {
                    if let Some(c) = (*function_index as usize).checked_sub(nimports) {
                        cs.push(c);
                    }
                }
                Operator::CallIndirect { .. } => {
                    info.writes_mem = true;
                    info.writes_globals.extend(0..module.globals.len() as u32);
                    info.sets_ghosts.extend(ghost_globals.iter().map(|n| (*n).clone()));
                }
                Operator::MemoryFill { .. } | Operator::MemoryCopy { .. } | Operator::MemoryGrow { .. } => {
                    info.writes_mem = true
                }
                op if is_store(op) => info.writes_mem = true,
                _ => {}
            }
        }
        if let Some(fp) = plan.funcs.get(f) {
            for sets in fp.sets.values() {
                for s in sets {
                    if ghost_globals.contains(&s.name) {
                        info.sets_ghosts.insert(s.name.clone());
                    }
                }
            }
        }
        infos.push(info);
        calls.push(cs);
    }
    // what callees change, the caller changes
    loop {
        let mut changed = false;
        for f in 0..infos.len() {
            for &c in &calls[f] {
                if c == f || c >= infos.len() {
                    continue;
                }
                let (m, g, h) = (
                    infos[c].writes_mem,
                    infos[c].writes_globals.clone(),
                    infos[c].sets_ghosts.clone(),
                );
                let i = &mut infos[f];
                if m && !i.writes_mem {
                    i.writes_mem = true;
                    changed = true;
                }
                for x in g {
                    changed |= i.writes_globals.insert(x);
                }
                for x in h {
                    changed |= i.sets_ghosts.insert(x);
                }
            }
        }
        if !changed {
            break;
        }
    }
    infos
}

/// Generate every obligation of the module.
pub fn generate(plan: &SpecPlan, module: &ValidModule, types: &TypedModule) -> Vec<Obligation> {
    if !plan.has_checks() {
        return vec![];
    }
    let infos = func_infos(plan, module);
    // recursive definitions that read no state become SMT functions; the rest unfold
    let pure: HashSet<String> = plan
        .defines
        .iter()
        .filter(|d| mentions_name(&d.body, &d.name) && is_pure_define(d, &plan.defines, &mut vec![]))
        .map(|d| d.name.clone())
        .collect();
    let mem_bytes = module
        .memory
        .first()
        .map(|m| m.initial << m.page_size_log2.unwrap_or(16))
        .unwrap_or(0);

    // pure definitions become SMT functions
    let dummy = FuncPlan::default();
    let empty_ghosts = BTreeMap::new();
    let mut header = String::new();
    let header_widths: BTreeSet<u32>;
    {
        let mut g = Gen {
            plan,
            module,
            func: 0,
            fp: &dummy,
            ops: vec![],
            lines: vec![],
            op_types: vec![],
            matching: HashMap::new(),
            decls: vec![],
            counter: 0,
            obligations: vec![],
            addresses: BTreeSet::new(),
            infos: &infos,
            recursive_defines: &pure,
            unsupported: None,
            mem_bytes,
            spec_widths: BTreeSet::new(),
        };
        let mem = String::new();
        for d in &plan.defines {
            if !pure.contains(&d.name) {
                continue;
            }
            let mut cx = SpecCx {
                fp: &dummy,
                locals: &[],
                globals: &[],
                mem: &mem,
                ghosts: &empty_ghosts,
                ghost_locals: &empty_ghosts,
                results: None,
                old: None,
                binders: d
                    .params
                    .iter()
                    .map(|p| (p.clone(), S::Int(format!("|p_{p}|"), I64)))
                    .collect(),
            };
            let sort = if expr_is_bool(&d.body, &plan.defines) { "Bool" } else { "(_ BitVec 64)" };
            let params: Vec<String> =
                d.params.iter().map(|p| format!("(|p_{p}| (_ BitVec 64))")).collect();
            let body = match g.spec(&mut cx, &d.body) {
                Ok(S::Int(t, r)) => at(&t, r, 64),
                Ok(S::Bool(t)) => t,
                _ => continue,
            };
            let kw = "define-fun-rec";
            let _ = writeln!(header, "({kw} |{}| ({}) {sort} {body})", d.name, params.join(" "));
        }
        header_widths = std::mem::take(&mut g.spec_widths);
    }

    let mut out = vec![];
    for (f, func) in module.functions.iter().enumerate() {
        let Some(fp) = plan.funcs.get(f) else { continue };
        let ops: Vec<&Operator> = func.operators.iter().map(|o| o.inner.operator()).collect();
        let lines: Vec<usize> = func.operators.iter().map(|o| o.line_idx).collect();
        let op_types: Vec<(usize, Vec<W>)> = types.funcs[f]
            .ops
            .iter()
            .map(|t| {
                (
                    t.inputs.len(),
                    t.outputs
                        .iter()
                        .map(|s| types.slots[s.usize()].ty().map(|t| width(&t)).unwrap_or(W::Opaque))
                        .collect(),
                )
            })
            .collect();
        let mut g = Gen {
            plan,
            module,
            func: f,
            fp,
            matching: matching_ends(&ops),
            ops,
            lines,
            op_types,
            decls: vec![],
            counter: 0,
            obligations: vec![],
            addresses: BTreeSet::new(),
            infos: &infos,
            recursive_defines: &pure,
            unsupported: None,
            mem_bytes,
            spec_widths: BTreeSet::new(),
        };
        if func.operators.iter().any(|o| o.inner.is_synthetic()) {
            g.unsupported = Some("the function has invalid code".into());
        }

        // the entry state
        let ft = &module.types[func.type_idx as usize];
        let mut locals = vec![];
        for (i, var) in fp.vars.iter().enumerate() {
            let w = if var.width == 64 { W::B64 } else if var.width == 32 { W::B32 } else { W::Opaque };
            if i < ft.params().len() {
                let name = format!("|{}|", var.name.clone().unwrap_or(format!("p{i}")));
                g.decls.push(format!("(declare-const {name} {})", sort_of(w)));
                locals.push(V { t: name, w });
            } else {
                locals.push(V { t: if w == W::B32 { bv(0, 32) } else { bv(0, 64) }, w });
            }
        }
        let initial = f == 0; // the program starts here, from the initial state
        let mut globals = vec![];
        for (gi, glob) in module.globals.iter().enumerate() {
            let w = width(&glob.inner.ty.content_type);
            let init = if initial {
                let mut reader = glob.inner.init_expr.get_operators_reader();
                match reader.read() {
                    Ok(Operator::I32Const { value }) => Some(bv(value as i128, 32)),
                    Ok(Operator::I64Const { value }) => Some(bv(value as i128, 64)),
                    _ => None,
                }
            } else {
                None
            };
            let t = match init {
                Some(t) => t,
                None => {
                    let name = format!(
                        "|{}|",
                        plan.global_names
                            .get(gi)
                            .cloned()
                            .flatten()
                            .unwrap_or(format!("global{gi}"))
                    );
                    g.decls.push(format!("(declare-const {name} {})", sort_of(w)));
                    name
                }
            };
            globals.push(V { t, w });
        }
        let mem = if initial {
            format!("((as const {MEM_SORT}) (_ bv0 32))")
        } else {
            g.declare("mem", MEM_SORT)
        };
        let mut ghosts = BTreeMap::new();
        let mut entry_facts = vec![];
        for (n, ty) in &plan.ghost_globals {
            let gh = if initial { g.initial_ghost(ty) } else { g.fresh_ghost(ty, n, &mut entry_facts) };
            ghosts.insert(n.clone(), gh);
        }
        let mut ghost_locals = BTreeMap::new();
        for (n, ty) in &fp.ghost_locals {
            let gh = g.initial_ghost(ty);
            ghost_locals.insert(n.clone(), gh);
        }
        let snap = Rc::new(Snapshot {
            locals: locals.clone(),
            globals: globals.clone(),
            mem: mem.clone(),
            ghosts: ghosts.clone(),
            ghost_locals: ghost_locals.clone(),
        });
        let mut st = St {
            pc: 0,
            stack: vec![],
            locals,
            globals,
            mem,
            ghosts,
            ghost_locals,
            path: entry_facts,
            ctl: vec![Ctl::Func],
            entry: snap.clone(),
            cut: Cut::Entry,
            cut_state: snap,
            approx: false,
            returned: None,
        };
        let entry_locals = st.locals.clone();
        for c in &fp.entry_checks {
            g.assume_check(&mut st, c, &[], fp, &entry_locals, None, None);
        }
        // refined locals start at zero
        let mut vars: Vec<&usize> = fp.local_checks.keys().collect();
        vars.sort();
        for var in vars {
            for c in &fp.local_checks[var] {
                let old = st.entry.clone();
                g.oblige_check(&st, ObKind::LocalRefinement, c, fp.lines.0, &[], fp, &entry_locals, None, Some(&old));
                g.assume_check(&mut st, c, &[], fp, &entry_locals, None, Some(&old));
            }
        }

        if g.unsupported.is_none() {
            let mut work = vec![st];
            while let Some(path) = work.pop() {
                g.run_path(path, &mut work);
                if g.unsupported.is_some() {
                    break;
                }
            }
        }

        // assemble the queries
        let addresses: Vec<u32> = g.addresses.iter().copied().collect();
        for (mut ob, ndecls, path, goal, cut) in std::mem::take(&mut g.obligations) {
            if let Some(why) = &g.unsupported {
                ob.unsupported = Some(why.clone());
            }
            if ob.unsupported.is_some() {
                out.push(ob);
                continue;
            }
            let mut reads: Vec<Read> = vec![];
            let mut terms: Vec<String> = vec![];
            let mut keys: Vec<(usize, String)> = vec![]; // (read index, Int term)
            for (i, var) in fp.vars.iter().enumerate() {
                let Some(name) = &var.name else { continue };
                if ob.cut == Cut::Entry && i >= fp.nparams {
                    continue;
                }
                let v = &cut.locals[i];
                if v.w == W::Opaque {
                    continue;
                }
                if v.w == W::B32 {
                    keys.push((reads.len(), v.t.clone()));
                }
                reads.push(Read::Var { name: name.clone(), bits: if v.w == W::B32 { 32 } else { 64 } });
                terms.push(v.t.clone());
            }
            for (gi, v) in cut.globals.iter().enumerate() {
                if v.w == W::Opaque {
                    continue;
                }
                let name = plan.global_names.get(gi).cloned().flatten().unwrap_or(format!("global {gi}"));
                reads.push(Read::Global { index: gi, name, bits: if v.w == W::B32 { 32 } else { 64 } });
                terms.push(v.t.clone());
            }
            if mem_bytes > 0 {
                for a in &addresses {
                    keys.push((reads.len(), format!("(ld32 {} (_ bv{a} 32))", cut.mem)));
                    reads.push(Read::Word(*a));
                    terms.push(format!("(ld32 {} (_ bv{a} 32))", cut.mem));
                }
            }
            for (n, gh) in cut.ghosts.iter().chain(cut.ghost_locals.iter()) {
                match gh {
                    G::Int(t) => {
                        reads.push(Read::Ghost(n.clone()));
                        terms.push(t.clone());
                    }
                    G::Map { dom, val, .. } => {
                        for (ki, kt) in &keys {
                            reads.push(Read::MapHas { map: n.clone(), key: *ki });
                            terms.push(format!("(select {dom} {kt})"));
                            reads.push(Read::MapVal { map: n.clone(), key: *ki });
                            terms.push(format!("(select {val} {kt})"));
                        }
                    }
                }
            }
            let mut q = String::new();
            let _ = writeln!(q, "(set-option :produce-models true)");
            let _ = writeln!(q, "(set-option :rlimit {RLIMIT})");
            q.push_str(PREAMBLE);
            for w in header_widths.union(&g.spec_widths) {
                q.push_str(&spec_fns(*w));
            }
            q.push_str(&header);
            for d in &g.decls[..ndecls] {
                q.push_str(d);
                q.push('\n');
            }
            for p in &path {
                let _ = writeln!(q, "(assert {p})");
            }
            // goal conjuncts that are facts verbatim (e.g. R after a call that ensures R)
            // need no search
            let facts: HashSet<&str> = path.iter().flat_map(|p| conjuncts(p)).collect();
            let rest: Vec<&str> = conjuncts(&goal).into_iter().filter(|c| !facts.contains(c)).collect();
            let goal = match rest.as_slice() {
                [] => "true".to_string(),
                [one] => one.to_string(),
                _ => format!("(and {})", rest.join(" ")),
            };
            let _ = writeln!(q, "(assert (not {goal}))");
            q.push_str("(check-sat)\n");
            if !terms.is_empty() {
                let _ = writeln!(q, "(get-value ({}))", terms.join(" "));
            }
            ob.hash = fnv(&q);
            ob.smt = q;
            ob.reads = reads;
            ob.terms = terms;
            out.push(ob);
        }
    }
    out
}

// ---------------------------------------------------------------------------------------
// Results

#[derive(Debug, Clone, PartialEq)]
pub enum Verdict {
    Proven,
    Refuted(Model),
    Unknown(String),
}

/// A state the contract allows, decoded from a model.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Model {
    pub vars: Vec<(String, i128)>,
    pub globals: Vec<(usize, String, i128)>,
    pub words: BTreeMap<u32, i128>,
    pub ghosts: Vec<(String, i128)>,
    pub maps: BTreeMap<String, BTreeMap<i128, i128>>,
}

// A minimal s-expression reader for Z3's output.
#[derive(Debug, Clone, PartialEq)]
enum Sx {
    Atom(String),
    List(Vec<Sx>),
}

fn parse_sx(s: &str) -> Vec<Sx> {
    let mut out = vec![];
    let mut stack: Vec<Vec<Sx>> = vec![];
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c == '(' {
            stack.push(vec![]);
            i += 1;
        } else if c == ')' {
            let l = stack.pop().unwrap_or_default();
            match stack.last_mut() {
                Some(top) => top.push(Sx::List(l)),
                None => out.push(Sx::List(l)),
            }
            i += 1;
        } else if c.is_whitespace() {
            i += 1;
        } else {
            let start = i;
            if c == '"' {
                i += 1;
                while i < chars.len() && chars[i] != '"' {
                    i += 1;
                }
                i += 1;
            } else if c == '|' {
                i += 1;
                while i < chars.len() && chars[i] != '|' {
                    i += 1;
                }
                i += 1;
            } else {
                while i < chars.len() && !chars[i].is_whitespace() && chars[i] != '(' && chars[i] != ')' {
                    i += 1;
                }
            }
            let a = Sx::Atom(chars[start..i.min(chars.len())].iter().collect());
            match stack.last_mut() {
                Some(top) => top.push(a),
                None => out.push(a),
            }
        }
    }
    out
}

fn sx_value(v: &Sx) -> Option<i128> {
    match v {
        Sx::Atom(a) => {
            if let Some(h) = a.strip_prefix("#x") {
                u128::from_str_radix(h, 16).ok().map(|x| x as i128)
            } else if let Some(b) = a.strip_prefix("#b") {
                u128::from_str_radix(b, 2).ok().map(|x| x as i128)
            } else if a == "true" {
                Some(1)
            } else if a == "false" {
                Some(0)
            } else {
                a.parse::<i128>().ok()
            }
        }
        Sx::List(l) => match l.as_slice() {
            [Sx::Atom(minus), x] if minus == "-" => sx_value(x).map(|x| -x),
            [Sx::Atom(us), Sx::Atom(bvn), Sx::Atom(_w)] if us == "_" => {
                bvn.strip_prefix("bv").and_then(|n| n.parse::<i128>().ok())
            }
            _ => None,
        },
    }
}

fn sx_width(v: &Sx) -> Option<u32> {
    match v {
        Sx::Atom(a) => a
            .strip_prefix("#x")
            .map(|h| 4 * h.len() as u32)
            .or_else(|| a.strip_prefix("#b").map(|b| b.len() as u32)),
        Sx::List(l) => match l.as_slice() {
            [Sx::Atom(us), _, Sx::Atom(w)] if us == "_" => w.parse().ok(),
            _ => None,
        },
    }
}

fn signed(v: i128, w: u32) -> i128 {
    if w == 32 {
        v as u32 as i32 as i128
    } else if w == 64 {
        v as u64 as i64 as i128
    } else {
        v
    }
}

// The answer to check-sat: the first line of the output. (The browser build reports a
// later error, e.g. get-value after unsat, by prefixing the whole output with "error:".)
fn answer(output: &str) -> &str {
    let first = output.lines().map(str::trim).find(|l| !l.is_empty()).unwrap_or("");
    first.strip_prefix("error:").unwrap_or(first).trim()
}

/// Read Z3's answer to an obligation's query.
pub fn verdict(ob: &Obligation, output: &str) -> Verdict {
    if let Some(why) = &ob.unsupported {
        return Verdict::Unknown(why.clone());
    }
    let first = answer(output);
    match first {
        "unsat" => Verdict::Proven,
        "sat" => {
            if ob.approximate {
                return Verdict::Unknown(
                    "a counterexample was found, but the program was only approximated".into(),
                );
            }
            let rest: String = output
                .lines()
                .skip_while(|l| l.trim().trim_start_matches("error:") != "sat")
                .skip(1)
                .collect::<Vec<_>>()
                .join("\n");
            Verdict::Refuted(decode(ob, &rest))
        }
        "unknown" => Verdict::Unknown(
            if output.contains("canceled") || output.contains("resource") {
                "the solver ran out of budget".into()
            } else {
                "the solver could not decide".into()
            },
        ),
        _ => Verdict::Unknown(format!("solver error: {}", first.chars().take(120).collect::<String>())),
    }
}

fn decode(ob: &Obligation, text: &str) -> Model {
    let mut m = Model::default();
    let sx = parse_sx(text);
    let Some(Sx::List(pairs)) = sx.first() else {
        return m;
    };
    let values: Vec<Option<(i128, Option<u32>)>> = pairs
        .iter()
        .map(|p| match p {
            Sx::List(l) if l.len() == 2 => sx_value(&l[1]).map(|v| (v, sx_width(&l[1]))),
            _ => None,
        })
        .collect();
    let num = |i: usize| -> Option<i128> {
        values.get(i).copied().flatten().map(|(v, w)| match w {
            Some(w) => signed(v, w),
            None => v,
        })
    };
    let mut has: HashMap<(String, usize), bool> = HashMap::new();
    let mut vals: HashMap<(String, usize), i128> = HashMap::new();
    for (i, r) in ob.reads.iter().enumerate() {
        match r {
            Read::Var { name, .. } => {
                if let Some(v) = num(i) {
                    m.vars.push((name.clone(), v));
                }
            }
            Read::Global { index, name, .. } => {
                if let Some(v) = num(i) {
                    m.globals.push((*index, name.clone(), v));
                }
            }
            Read::Ghost(n) => {
                if let Some(v) = num(i) {
                    m.ghosts.push((n.clone(), v));
                }
            }
            Read::Word(a) => {
                if let Some(v) = num(i) {
                    m.words.insert(*a, v);
                }
            }
            Read::MapHas { map, key } => {
                has.insert((map.clone(), *key), num(i) == Some(1));
            }
            Read::MapVal { map, key } => {
                if let Some(v) = num(i) {
                    vals.insert((map.clone(), *key), v);
                }
            }
        }
    }
    for ((map, key), present) in has {
        if present
            && let Some(k) = num(key)
        {
            let v = vals.get(&(map.clone(), key)).copied().unwrap_or(0);
            m.maps.entry(map).or_default().insert(k, v);
        }
    }
    m
}

// ---------------------------------------------------------------------------------------
// Proving an obligation: a few queries, in stages
//
// 1. the obligation's query; 2. its integer translation (for nonlinear facts); 3. the goal
// split into its conjuncts, one query each, with the facts quantified over a ghost map's
// keys replaced by their instances at the keys the query mentions (so the queries are
// quantifier-free), conjuncts left undecided tried again with a larger budget. The
// solver is a function from SMT-LIB text to its output: the driver (a test, or the
// editor's Web Worker) runs each query that `next` asks for and `feed`s back the answer.

/// The budget of a split part's second attempt.
pub const RLIMIT_RETRY: u64 = 20_000_000;

#[derive(Debug, Clone, PartialEq)]
enum Stage {
    Whole,
    Int,
    Parts { queries: Vec<String>, full: Vec<String>, exact: bool, results: Vec<Option<char>>, retry: bool },
    // a part was sat without the map-quantified facts: is it with them?
    Confirm(String),
    // a counterexample: look for one with small numbers
    Minimize { query: String, bounds: Vec<i128>, found: Model },
    Done,
}

/// The progress of one obligation's proof.
#[derive(Debug, Clone)]
pub struct Proof {
    stage: Stage,
    asked: Option<usize>, // the part whose query is out
    verdict: Option<Verdict>,
    /// Queries run, for timings and reports.
    pub queries: usize,
}

impl Proof {
    pub fn new(ob: &Obligation) -> Proof {
        let mut p = Proof { stage: Stage::Whole, asked: None, verdict: None, queries: 0 };
        if let Some(why) = &ob.unsupported {
            p.finish(Verdict::Unknown(why.clone()));
        }
        p
    }

    pub fn verdict(&self) -> Option<&Verdict> {
        self.verdict.as_ref()
    }

    // A counterexample was found by `query`: try again with every value it shows small.
    fn minimize(&mut self, query: String, found: Model) {
        let small = |v: &i128| v.abs() <= 8;
        let all_small = found.vars.iter().all(|(_, v)| small(v))
            && found.globals.iter().all(|(_, _, v)| small(v))
            && found.words.values().all(small)
            && found.ghosts.iter().all(|(_, v)| small(v))
            && found.maps.values().all(|m| m.iter().all(|(k, v)| small(k) && small(v)));
        if all_small {
            self.finish(Verdict::Refuted(found));
        } else {
            self.stage = Stage::Minimize { query, bounds: vec![8, 100, 10_000], found };
        }
    }

    fn finish(&mut self, v: Verdict) {
        self.verdict = Some(v);
        self.stage = Stage::Done;
    }

    /// The next query to run, if the proof is not finished.
    pub fn next(&mut self, ob: &Obligation) -> Option<String> {
        loop {
            match &mut self.stage {
                Stage::Done => return None,
                Stage::Whole => {
                    self.queries += 1;
                    return Some(ob.smt.clone());
                }
                Stage::Confirm(q) => {
                    self.queries += 1;
                    return Some(with_rlimit(q, RLIMIT_RETRY));
                }
                Stage::Minimize { query, bounds, .. } => {
                    let b = bounds[0];
                    self.queries += 1;
                    let bound = small_values(ob, b);
                    return Some(query.replacen("(check-sat)", &format!("(assert {bound})\n(check-sat)"), 1));
                }
                // the same query in integer arithmetic (for nonlinear facts)
                Stage::Int => match crate::vc_int::translate(&ob.smt) {
                    Some(q) => {
                        self.queries += 1;
                        return Some(q);
                    }
                    None => self.stage = split_stage(ob),
                },
                Stage::Parts { queries, results, retry, .. } => {
                    if let Some(i) = results.iter().position(|r| r.is_none()) {
                        self.asked = Some(i);
                        self.queries += 1;
                        let q = &queries[i];
                        return Some(if *retry { with_rlimit(q, RLIMIT_RETRY) } else { q.clone() });
                    }
                    // every part has an answer, none of them sat (that ends the proof)
                    if results.iter().all(|r| *r == Some('u')) {
                        self.finish(Verdict::Proven);
                    } else if !*retry {
                        *retry = true;
                        for r in results.iter_mut() {
                            if *r == Some('?') {
                                *r = None;
                            }
                        }
                    } else {
                        self.finish(Verdict::Unknown("the solver could not decide".into()));
                    }
                }
            }
        }
    }

    /// The solver's answer to the query `next` returned.
    pub fn feed(&mut self, ob: &Obligation, output: &str) {
        match &mut self.stage {
            Stage::Done => {}
            Stage::Whole => match verdict(ob, output) {
                Verdict::Unknown(_) => self.stage = Stage::Int,
                Verdict::Refuted(m) => self.minimize(ob.smt.clone(), m),
                v => self.finish(v),
            },
            Stage::Int => match verdict(ob, output) {
                Verdict::Unknown(_) => self.stage = split_stage(ob),
                v => self.finish(v),
            },
            Stage::Confirm(q) => {
                let q = with_rlimit(q, RLIMIT_RETRY);
                match verdict(ob, output) {
                    Verdict::Refuted(m) => self.minimize(q, m),
                    _ => self.finish(Verdict::Unknown(
                        "a counterexample to a weakened query, which may not be one".into(),
                    )),
                }
            }
            Stage::Minimize { bounds, found, .. } => {
                bounds.remove(0);
                if let Verdict::Refuted(m) = verdict(ob, output) {
                    self.finish(Verdict::Refuted(m));
                } else if bounds.is_empty() {
                    let m = std::mem::take(found);
                    self.finish(Verdict::Refuted(m));
                }
            }
            Stage::Parts { exact, results, full, queries, .. } => {
                let Some(i) = self.asked.take() else { return };
                let first = answer(output);
                results[i] = Some(match first {
                    "unsat" => 'u',
                    "sat" => 's',
                    _ => '?',
                });
                if first == "sat" {
                    if *exact {
                        let q = queries[i].clone();
                        match verdict(ob, output) {
                            Verdict::Refuted(m) => self.minimize(q, m),
                            v => self.finish(v),
                        }
                    } else {
                        self.stage = Stage::Confirm(full[i].clone());
                    }
                }
            }
        }
    }
}

// Every value a model shows within ±b.
fn small_values(ob: &Obligation, b: i128) -> String {
    let mut parts = vec![];
    for (r, t) in ob.reads.iter().zip(&ob.terms) {
        let bits = match r {
            Read::Var { bits, .. } | Read::Global { bits, .. } => *bits,
            Read::Ghost(_) | Read::Word(_) | Read::MapVal { .. } => 32,
            Read::MapHas { .. } => continue,
        };
        parts.push(format!("(bvsle {} {t}) (bvsle {t} {})", bv(-b, bits), bv(b, bits)));
    }
    if parts.is_empty() { "true".into() } else { format!("(and {})", parts.join(" ")) }
}

fn with_rlimit(q: &str, n: u64) -> String {
    match q.find("(set-option :rlimit ") {
        Some(i) => {
            let j = q[i..].find(')').map(|j| i + j + 1).unwrap_or(q.len());
            format!("{}(set-option :rlimit {n}){}", &q[..i], &q[j..])
        }
        None => q.to_string(),
    }
}

fn split_stage(ob: &Obligation) -> Stage {
    match split_queries(&ob.smt) {
        Some((queries, full, exact)) if !queries.is_empty() => {
            let n = queries.len();
            Stage::Parts { queries, full, exact, results: vec![None; n], retry: false }
        }
        _ => Stage::Parts { queries: vec![], full: vec![], exact: true, results: vec![Some('?')], retry: true },
    }
}

fn show_sx(s: &Sx) -> String {
    let mut out = String::new();
    fn go(s: &Sx, out: &mut String) {
        match s {
            Sx::Atom(a) => out.push_str(a),
            Sx::List(l) => {
                out.push('(');
                for (i, x) in l.iter().enumerate() {
                    if i > 0 {
                        out.push(' ');
                    }
                    go(x, out);
                }
                out.push(')');
            }
        }
    }
    go(s, &mut out);
    out
}

fn sx_conjuncts(s: &Sx, out: &mut Vec<Sx>) {
    match s {
        Sx::List(l) if matches!(l.first(), Some(Sx::Atom(a)) if a == "and") => {
            for x in &l[1..] {
                sx_conjuncts(x, out);
            }
        }
        _ => out.push(s.clone()),
    }
}

// (forall ((q S)) (! (=> (select D q) B) :pattern …)) → (q, S, D, B)
fn map_forall(s: &Sx) -> Option<(String, Sx, Sx, Sx)> {
    let Sx::List(l) = s else { return None };
    let [Sx::Atom(f), Sx::List(binds), body] = l.as_slice() else { return None };
    if f != "forall" || binds.len() != 1 {
        return None;
    }
    let Sx::List(b) = &binds[0] else { return None };
    let [Sx::Atom(q), sort] = b.as_slice() else { return None };
    let body = match body {
        Sx::List(x) if matches!(x.first(), Some(Sx::Atom(a)) if a == "!") => x.get(1)?,
        other => other,
    };
    let Sx::List(imp) = body else { return None };
    let [Sx::Atom(arrow), Sx::List(sel), inner] = imp.as_slice() else { return None };
    let [Sx::Atom(select), dom, Sx::Atom(k)] = sel.as_slice() else { return None };
    if arrow != "=>" || select != "select" || k != q {
        return None;
    }
    Some((q.clone(), sort.clone(), dom.clone(), inner.clone()))
}

fn subst_sx(s: &Sx, v: &str, by: &Sx) -> Sx {
    match s {
        Sx::Atom(a) if a == v => by.clone(),
        Sx::Atom(_) => s.clone(),
        Sx::List(l) => Sx::List(l.iter().map(|x| subst_sx(x, v, by)).collect()),
    }
}

fn mentions_any(s: &Sx, names: &[String]) -> bool {
    match s {
        Sx::Atom(a) => names.iter().any(|n| n == a),
        Sx::List(l) => l.iter().any(|x| mentions_any(x, names)),
    }
}

// The indices at which ghost-map arrays are read or written (closed terms only).
fn map_keys(s: &Sx, maps: &HashSet<String>, bound: &mut Vec<String>, out: &mut BTreeSet<String>) {
    let Sx::List(l) = s else { return };
    match l.first() {
        Some(Sx::Atom(q)) if (q == "forall" || q == "exists" || q == "let") && l.len() == 3 => {
            let n = bound.len();
            if let Sx::List(bs) = &l[1] {
                for b in bs {
                    if let Sx::List(b) = b {
                        if q == "let" {
                            map_keys(&b[1], maps, bound, out);
                        }
                        if let Some(Sx::Atom(name)) = b.first() {
                            bound.push(name.clone());
                        }
                    }
                }
            }
            map_keys(&l[2], maps, bound, out);
            bound.truncate(n);
            return;
        }
        Some(Sx::Atom(f)) if (f == "select" || f == "store") && l.len() >= 3 && is_map_array(&l[1], maps) => {
            if !mentions_any(&l[2], bound) {
                out.insert(show_sx(&l[2]));
            }
        }
        _ => {}
    }
    for x in l {
        map_keys(x, maps, bound, out);
    }
}

fn is_map_array(s: &Sx, maps: &HashSet<String>) -> bool {
    match s {
        Sx::Atom(a) => maps.contains(a),
        Sx::List(l) => match l.first() {
            Some(Sx::Atom(f)) if f == "store" => l.get(1).is_some_and(|a| is_map_array(a, maps)),
            Some(Sx::Atom(f)) if f == "ite" => l.get(2).is_some_and(|a| is_map_array(a, maps)),
            Some(Sx::List(h)) => {
                // ((as const (Array (_ BitVec 32) …)) v)
                let t = show_sx(&Sx::List(h.clone()));
                t == format!("(as const {DOM_SORT})") || t == format!("(as const {VAL_SORT})")
            }
            _ => false,
        },
    }
}

/// The parts of a query: one per conjunct of its goal, with the map-quantified facts
/// instantiated; and the same with those facts kept as well (to confirm a model). `exact`
/// is whether nothing was dropped (so a model of a part is one of the original query).
fn split_queries(q: &str) -> Option<(Vec<String>, Vec<String>, bool)> {
    let cmds = parse_sx(q);
    let head = |c: &Sx| match c {
        Sx::List(l) => match l.first() {
            Some(Sx::Atom(a)) => a.clone(),
            _ => String::new(),
        },
        _ => String::new(),
    };
    let asserts: Vec<&Sx> = cmds.iter().filter(|c| head(c) == "assert").collect();
    let goal = match asserts.last()? {
        Sx::List(l) => match l.get(1)? {
            Sx::List(n) if matches!(n.first(), Some(Sx::Atom(a)) if a == "not") => n.get(1)?.clone(),
            _ => return None,
        },
        _ => return None,
    };
    // map arrays: declared or defined with a map sort
    let mut maps = HashSet::new();
    for c in &cmds {
        if let Sx::List(l) = c {
            let (name, sort) = match head(c).as_str() {
                "declare-const" => (l.get(1), l.get(2)),
                "define-fun" if matches!(l.get(2), Some(Sx::List(p)) if p.is_empty()) => (l.get(1), l.get(3)),
                _ => (None, None),
            };
            if let (Some(Sx::Atom(n)), Some(s)) = (name, sort) {
                let s = show_sx(s);
                if s == DOM_SORT || s == VAL_SORT {
                    maps.insert(n.clone());
                }
            }
        }
    }
    let mut decls = vec![];
    let mut goals = vec![];
    let mut sk = 0;
    let mut gs = vec![];
    sx_conjuncts(&goal, &mut gs);
    for g in gs {
        match map_forall(&g) {
            Some((qv, sort, dom, body)) => {
                let n = format!("sk{sk}");
                sk += 1;
                decls.push(format!("(declare-const {n} {})", show_sx(&sort)));
                let k = Sx::Atom(n);
                goals.push(Sx::List(vec![
                    Sx::Atom("=>".into()),
                    Sx::List(vec![Sx::Atom("select".into()), dom, k.clone()]),
                    subst_sx(&body, &qv, &k),
                ]));
            }
            None => goals.push(g),
        }
    }
    let mut facts: Vec<Sx> = vec![];
    let mut seen = HashSet::new();
    let mut quants = vec![];
    let mut quantified = vec![];
    for a in &asserts[..asserts.len() - 1] {
        let Sx::List(l) = a else { continue };
        let mut cs = vec![];
        sx_conjuncts(l.get(1)?, &mut cs);
        for c in cs {
            if !seen.insert(show_sx(&c)) {
                continue;
            }
            match map_forall(&c) {
                Some(m) => {
                    quantified.push(c.clone());
                    quants.push(m)
                }
                None => facts.push(c),
            }
        }
    }
    if goals.len() <= 1 && quants.is_empty() {
        return None; // nothing to gain
    }
    let mut keys = BTreeSet::new();
    for x in facts.iter().chain(goals.iter()) {
        map_keys(x, &maps, &mut vec![], &mut keys);
    }
    for c in &cmds {
        if head(c) == "define-fun"
            && let Sx::List(l) = c
            && matches!(l.get(2), Some(Sx::List(p)) if p.is_empty())
            && let Some(body) = l.get(4)
        {
            map_keys(body, &maps, &mut vec![], &mut keys);
        }
    }
    for i in 0..sk {
        keys.insert(format!("sk{i}"));
    }
    let keys: Vec<Sx> = keys.iter().filter_map(|k| parse_sx(k).into_iter().next()).collect();
    let mut instances = vec![];
    for (qv, _, dom, body) in &quants {
        for k in &keys {
            let inst = Sx::List(vec![
                Sx::Atom("=>".into()),
                Sx::List(vec![Sx::Atom("select".into()), dom.clone(), k.clone()]),
                subst_sx(body, qv, k),
            ]);
            if seen.insert(show_sx(&inst)) {
                instances.push(inst);
            }
        }
    }
    let exact = quants.is_empty();
    let mut prefix = String::new();
    for c in &cmds {
        if !matches!(head(c).as_str(), "assert" | "check-sat" | "get-value") {
            prefix.push_str(&show_sx(c));
            prefix.push('\n');
        }
    }
    for d in &decls {
        prefix.push_str(d);
        prefix.push('\n');
    }
    for f in facts.iter().chain(instances.iter()) {
        let _ = writeln!(prefix, "(assert {})", show_sx(f));
    }
    let get_value = cmds.iter().find(|c| head(c) == "get-value").map(show_sx);
    let part = |prefix: &str, g: &Sx, models: bool| {
        let mut q = prefix.to_string();
        let _ = writeln!(q, "(assert (not {}))", show_sx(g));
        q.push_str("(check-sat)\n");
        if models && let Some(gv) = &get_value {
            q.push_str(gv);
            q.push('\n');
        }
        q
    };
    let mut prefix_full = prefix.clone();
    for f in &quantified {
        let _ = writeln!(prefix_full, "(assert {})", show_sx(f));
    }
    let queries = goals.iter().map(|g| part(&prefix, g, exact)).collect();
    let full = if exact { vec![] } else { goals.iter().map(|g| part(&prefix_full, g, true)).collect() };
    Some((queries, full, exact))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conjuncts_flatten() {
        assert_eq!(conjuncts("(and (and a (f |x y|)) (and b) c)"), vec!["a", "(f |x y|)", "b", "c"]);
        assert_eq!(conjuncts("(or a b)"), vec!["(or a b)"]);
        assert_eq!(conjuncts("(and (= (and p q) r) s)"), vec!["(= (and p q) r)", "s"]);
    }
}
