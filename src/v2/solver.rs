//! The decision procedure behind `prove k` (design 16 §3): linear integer arithmetic over unsigned
//! readings with explicit wrap variables, monomials as atoms, an interval pre-pass, case splits and
//! Omega-lite (Fourier–Motzkin with exactness tracking). Deterministic, with fixed caps.

use super::ast::{IOp, ValTy};
use super::term::{Atom, Key, Rel, TermId, Terms};
use std::collections::HashMap;

mod explain;
pub use explain::{Explanation, explain};

pub const CAP_TERMS: usize = 64;
pub const CAP_VARS: usize = 24;
pub const CAP_CASES: u32 = 256;
pub const CAP_CONS: usize = 256;
pub const UNFOLD_DEPTH: u32 = 4;

/// What the procedure may ask of the module: unfolding and evaluation of predicate calls.
pub trait Env {
    /// The body term of a non-recursive pure predicate call (R29), if it unfolds.
    fn unfold(&mut self, terms: &mut Terms, call: TermId) -> Option<TermId>;
    /// Evaluate a non-memory pure call whose arguments are all constants (R28).
    fn eval_call(&mut self, terms: &Terms, call: TermId) -> Option<u64>;
    /// Was this value computed by a real slot (so a `rem_u` divisor is nonzero, R24)?
    fn is_real(&self, t: TermId) -> bool;
}

#[derive(Clone, Debug, PartialEq)]
pub enum Outcome {
    Valid { wraps: Vec<String> },
    NotImplied(Vec<(String, i128)>),
    Cap(String),
    Inexact(String),
}

pub type VarId = u32;

/// Σ cᵢ·xᵢ + c (terms sorted by variable, no zero coefficients).
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Lin {
    pub ts: Vec<(VarId, i128)>,
    pub c: i128,
}

#[derive(Debug)]
pub enum Stop {
    Infeasible,
    Cap(String),
}

type R<T> = Result<T, Stop>;

fn ovf() -> Stop {
    Stop::Cap("coefficients exceed i128 (cap)".into())
}

fn mul(a: i128, b: i128) -> R<i128> {
    a.checked_mul(b).ok_or_else(ovf)
}
fn add(a: i128, b: i128) -> R<i128> {
    a.checked_add(b).ok_or_else(ovf)
}

impl Lin {
    pub fn konst(c: i128) -> Lin {
        Lin { ts: vec![], c }
    }
    pub fn var(v: VarId) -> Lin {
        Lin {
            ts: vec![(v, 1)],
            c: 0,
        }
    }
    pub fn as_const(&self) -> Option<i128> {
        if self.ts.is_empty() {
            Some(self.c)
        } else {
            None
        }
    }
    pub fn scale(&self, k: i128) -> R<Lin> {
        if k == 0 {
            return Ok(Lin::default());
        }
        let mut ts = Vec::with_capacity(self.ts.len());
        for (v, c) in &self.ts {
            ts.push((*v, mul(*c, k)?));
        }
        Ok(Lin {
            ts,
            c: mul(self.c, k)?,
        })
    }
    pub fn plus(&self, o: &Lin) -> R<Lin> {
        let mut ts = Vec::with_capacity(self.ts.len() + o.ts.len());
        let (mut i, mut j) = (0, 0);
        while i < self.ts.len() || j < o.ts.len() {
            if j >= o.ts.len() || (i < self.ts.len() && self.ts[i].0 < o.ts[j].0) {
                if self.ts[i].1 != 0 {
                    ts.push(self.ts[i]);
                }
                i += 1;
            } else if i >= self.ts.len() || o.ts[j].0 < self.ts[i].0 {
                if o.ts[j].1 != 0 {
                    ts.push(o.ts[j]);
                }
                j += 1;
            } else {
                let c = add(self.ts[i].1, o.ts[j].1)?;
                if c != 0 {
                    ts.push((self.ts[i].0, c));
                }
                i += 1;
                j += 1;
            }
        }
        Ok(Lin {
            ts,
            c: add(self.c, o.c)?,
        })
    }
    pub fn minus(&self, o: &Lin) -> R<Lin> {
        self.plus(&o.scale(-1)?)
    }
    pub fn add_c(&self, k: i128) -> R<Lin> {
        Ok(Lin {
            ts: self.ts.clone(),
            c: add(self.c, k)?,
        })
    }
    pub fn coef(&self, v: VarId) -> i128 {
        self.ts
            .iter()
            .find(|(x, _)| *x == v)
            .map(|(_, c)| *c)
            .unwrap_or(0)
    }
    /// Replace variable v by the linear form e.
    pub fn subst(&self, v: VarId, e: &Lin) -> R<Lin> {
        let k = self.coef(v);
        if k == 0 {
            return Ok(self.clone());
        }
        let rest = Lin {
            ts: self.ts.iter().filter(|(x, _)| *x != v).copied().collect(),
            c: self.c,
        };
        rest.plus(&e.scale(k)?)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum VarDesc {
    /// an opaque term (leaf, call, load, …)
    Term(TermId),
    /// a monomial over base variables (sorted, with repetition)
    Mono(Vec<VarId>),
    /// a monomial over canonical ids, when a factor still had a wrap
    TermMono(Vec<TermId>),
    /// wrap quotient of a term
    Wrap(TermId),
    /// quotient of a division/remainder/mask/shift
    Div(TermId),
    /// signed quotient of shr_s
    SDiv(TermId),
    /// value of a non-constant div_u / rem_u
    Res(TermId),
}

#[derive(Clone, Debug)]
pub struct Var {
    pub lo: i128,
    pub hi: i128,
    pub desc: VarDesc,
}

/// Translation of a term: a linear form and the term's known range (unsigned reading).
#[derive(Clone, Debug)]
pub struct Tr {
    pub lin: Lin,
    pub lo: i128,
    pub hi: i128,
}

#[derive(Clone, Debug)]
pub enum Con {
    Le(Lin),
    Eq(Lin),
}

fn pow2(k: u32) -> i128 {
    1i128 << k
}

fn width(ty: ValTy) -> u32 {
    ty.bits()
}

fn fdiv(a: i128, b: i128) -> i128 {
    a.div_euclid(b)
}

pub struct Solver<'a> {
    pub terms: &'a mut Terms,
    pub env: &'a mut dyn Env,
    /// cases enumerated by the last `prove` (a deterministic measure of its work)
    pub cases: u32,
    /// bounds learned by the interval pre-pass, by term (§3.3)
    bounds: HashMap<TermId, (i128, i128)>,
    // ---- per run (one case) ----
    pub vars: Vec<Var>,
    var_of: HashMap<VarDesc, VarId>,
    memo: HashMap<TermId, Tr>,
    memo_s: HashMap<TermId, Tr>,
    cons: Vec<Con>,
    choices: Vec<bool>,
    pos: usize,
    depth: u32,
    pre: bool,
    pub wraps: Vec<String>,
    /// explanation trace (only for `explain`; never changes an outcome)
    trace: Option<Box<explain::Trace>>,
}

/// Abort of a pre-pass atom at its first split.
const SPLIT_IN_PRE: &str = "split";

impl<'a> Solver<'a> {
    pub fn new(terms: &'a mut Terms, env: &'a mut dyn Env) -> Self {
        Solver {
            cases: 0,
            terms,
            env,
            bounds: HashMap::new(),
            vars: vec![],
            var_of: HashMap::new(),
            memo: HashMap::new(),
            memo_s: HashMap::new(),
            cons: vec![],
            choices: vec![],
            pos: 0,
            depth: 0,
            pre: false,
            wraps: vec![],
            trace: None,
        }
    }

    fn reset_run(&mut self) {
        self.vars.clear();
        self.var_of.clear();
        self.memo.clear();
        self.memo_s.clear();
        self.cons.clear();
        self.pos = 0;
        self.depth = 0;
        self.wraps.clear();
        self.t_reset();
    }

    /// A case split: returns the branch taken in this run.
    fn choose(&mut self) -> R<bool> {
        if self.pre {
            return Err(Stop::Cap(SPLIT_IN_PRE.into()));
        }
        if self.pos == self.choices.len() {
            self.choices.push(false);
        }
        let b = self.choices[self.pos];
        self.pos += 1;
        Ok(b)
    }

    fn new_var(&mut self, desc: VarDesc, lo: i128, hi: i128) -> R<VarId> {
        if let Some(&v) = self.var_of.get(&desc) {
            return Ok(v);
        }
        if lo > hi {
            return Err(self.t_fail(|s| s.t_empty(&desc)));
        }
        let id = self.vars.len() as VarId;
        self.vars.push(Var {
            lo,
            hi,
            desc: desc.clone(),
        });
        self.var_of.insert(desc, id);
        Ok(id)
    }

    /// A variable as a translated term; a point interval becomes a constant (§3.3).
    fn var_tr(&mut self, desc: VarDesc, lo: i128, hi: i128) -> R<Tr> {
        if lo == hi {
            return Ok(Tr {
                lin: Lin::konst(lo),
                lo,
                hi,
            });
        }
        let v = self.new_var(desc, lo, hi)?;
        let (lo, hi) = (self.vars[v as usize].lo, self.vars[v as usize].hi);
        if lo == hi {
            return Ok(Tr {
                lin: Lin::konst(lo),
                lo,
                hi,
            });
        }
        Ok(Tr {
            lin: Lin::var(v),
            lo,
            hi,
        })
    }

    /// Range of a linear form from its variables' intervals.
    fn range(&self, l: &Lin) -> R<(i128, i128)> {
        let (mut lo, mut hi) = (l.c, l.c);
        for (v, c) in &l.ts {
            let var = &self.vars[*v as usize];
            let (a, b) = (mul(var.lo, *c)?, mul(var.hi, *c)?);
            lo = add(lo, a.min(b))?;
            hi = add(hi, a.max(b))?;
        }
        Ok((lo, hi))
    }

    /// Assert l ≤ 0.
    fn le0(&mut self, l: Lin) -> R<()> {
        if let Some(c) = l.as_const() {
            return if c <= 0 {
                Ok(())
            } else {
                Err(self.t_fail(|s| s.t_const_false()))
            };
        }
        // single-variable constraints tighten the interval at once
        if l.ts.len() == 1 {
            let (v, k) = l.ts[0];
            let var = &mut self.vars[v as usize];
            let old = (var.lo, var.hi);
            if k > 0 {
                var.hi = var.hi.min(fdiv(-l.c, k));
            } else {
                var.lo = var.lo.max(-fdiv(-l.c, -k)); // x ≥ ⌈c/|k|⌉
            }
            if var.lo > var.hi {
                return Err(self.t_fail(|s| s.t_interval(v, old, &l, false)));
            }
        }
        let (lo, _) = self.range(&l)?;
        if lo > 0 {
            return Err(self.t_fail(|s| s.t_range(&l, lo, false)));
        }
        self.cons.push(Con::Le(l));
        Ok(())
    }

    fn eq0(&mut self, l: Lin) -> R<()> {
        if let Some(c) = l.as_const() {
            return if c == 0 {
                Ok(())
            } else {
                Err(self.t_fail(|s| s.t_const_false()))
            };
        }
        if l.ts.len() == 1 {
            let (v, k) = l.ts[0];
            if l.c % k != 0 {
                return Err(self.t_fail_mod(k.abs(), |s| s.t_gcd(&l, k.abs())));
            }
            let x = -l.c / k;
            let var = &mut self.vars[v as usize];
            let old = (var.lo, var.hi);
            if x < var.lo || x > var.hi {
                return Err(self.t_fail(|s| s.t_interval(v, old, &l, true)));
            }
            var.lo = x;
            var.hi = x;
        }
        let (lo, hi) = self.range(&l)?;
        if lo > 0 || hi < 0 {
            return Err(self.t_fail(|s| s.t_range(&l, if lo > 0 { lo } else { hi }, true)));
        }
        self.cons.push(Con::Eq(l));
        Ok(())
    }

    /// a ≤ b
    fn le(&mut self, a: &Lin, b: &Lin) -> R<()> {
        self.le0(a.minus(b)?)
    }

    fn default_range(&self, t: TermId) -> (i128, i128) {
        let term = self.terms.get(t);
        let w = width(term.ty);
        let full = (0, pow2(w) - 1);
        if let Some((lo, hi)) = term.range {
            return (lo as i128, hi as i128);
        }
        match &term.key {
            Key::Load(_, bytes, false, ..) if *bytes * 8 < w => (0, pow2(bytes * 8) - 1),
            Key::Op(IOp::Clz | IOp::Ctz | IOp::Popcnt, ..) => (0, w as i128),
            _ if self.terms.is_cmp(t) => (0, 1),
            _ => full,
        }
    }

    fn opaque(&mut self, t: TermId) -> R<Tr> {
        let (mut lo, mut hi) = self.default_range(t);
        if let Some(&(a, b)) = self.bounds.get(&t) {
            lo = lo.max(a);
            hi = hi.min(b);
        }
        self.var_tr(VarDesc::Term(t), lo, hi)
    }

    pub fn tr(&mut self, t: TermId) -> R<Tr> {
        if let Some(x) = self.memo.get(&t) {
            return Ok(x.clone());
        }
        let r = match self.tr_inner(t) {
            Err(Stop::Cap(c)) if c.starts_with("coefficients") => self.opaque(t),
            r => r,
        }?;
        if r.lin.ts.len() > CAP_TERMS {
            return Err(Stop::Cap(format!(
                "this fact expands to {} terms (cap {CAP_TERMS}); state an intermediate fact with a lemma",
                r.lin.ts.len()
            )));
        }
        self.memo.insert(t, r.clone());
        Ok(r)
    }

    /// Resolve or split the wrap quotient of an exact result in [lo, hi] (§3.2, §3.3):
    /// returns the form `exact − W·q` with its range.
    fn wrap(&mut self, t: TermId, exact: Lin, lo: i128, hi: i128, w: u32, split01: bool) -> R<Tr> {
        let wv = pow2(w);
        let (q0, q1) = (fdiv(lo, wv), fdiv(hi, wv));
        if q0 == q1 {
            if q0 != 0 && lo != hi {
                self.wraps
                    .push(format!("{} wraps by {q0}·2^{w}", self.terms.render(t)));
            } else if lo != hi
                && (lo < 0 || hi > 0)
                && !matches!(self.terms.key(t), Key::Op(IOp::ExtendI32U, ..))
            {
                self.wraps
                    .push(format!("{} does not wrap", self.terms.render(t)));
            }
            let lin = exact.add_c(mul(-q0, wv)?)?;
            return Ok(Tr {
                lin,
                lo: lo - q0 * wv,
                hi: hi - q0 * wv,
            });
        }
        if split01 && q1 - q0 == 1 {
            let q = if self.choose()? { q1 } else { q0 };
            self.t_split(|s| {
                let w = if q != 0 { "wraps" } else { "does not wrap" };
                format!("{} {w}", s.terms.render(t))
            });
            let lin = exact.add_c(mul(-q, wv)?)?;
            self.le0(lin.scale(-1)?)?;
            self.le0(lin.add_c(-(wv - 1))?)?;
            let (a, b) = self.range(&lin)?;
            return Ok(Tr {
                lin,
                lo: a.max(0),
                hi: b.min(wv - 1),
            });
        }
        let q = self.new_var(VarDesc::Wrap(t), q0, q1)?;
        let lin = exact.minus(&Lin::var(q).scale(wv)?)?;
        self.le0(lin.scale(-1)?)?;
        self.le0(lin.add_c(-(wv - 1))?)?;
        Ok(Tr {
            lin,
            lo: 0,
            hi: wv - 1,
        })
    }

    fn has_wrap(&self, l: &Lin) -> bool {
        l.ts.iter().any(|(v, _)| {
            matches!(
                self.vars[*v as usize].desc,
                VarDesc::Wrap(_) | VarDesc::TermMono(_)
            )
        })
    }

    /// Base factors of a variable (a monomial's factors, or itself).
    fn factors(&self, v: VarId) -> Vec<VarId> {
        match &self.vars[v as usize].desc {
            VarDesc::Mono(f) => f.clone(),
            _ => vec![v],
        }
    }

    fn mono(&mut self, mut f: Vec<VarId>) -> R<VarId> {
        f.sort();
        let (mut lo, mut hi) = (1i128, 1i128);
        for v in &f {
            let var = &self.vars[*v as usize];
            let c = [
                mul(lo, var.lo)?,
                mul(lo, var.hi)?,
                mul(hi, var.lo)?,
                mul(hi, var.hi)?,
            ];
            lo = *c.iter().min().unwrap();
            hi = *c.iter().max().unwrap();
        }
        self.new_var(VarDesc::Mono(f), lo, hi)
    }

    /// Expand A·B as a polynomial; degree ≥ 2 products become monomial variables.
    fn poly_mul(&mut self, a: &Lin, b: &Lin) -> R<Lin> {
        let mut out = Lin::konst(mul(a.c, b.c)?);
        out = out.plus(&b.scale(a.c)?.add_c(-mul(a.c, b.c)?)?)?;
        out = out.plus(&a.scale(b.c)?.add_c(-mul(a.c, b.c)?)?)?;
        for (va, ca) in &a.ts {
            for (vb, cb) in &b.ts {
                let mut f = self.factors(*va);
                f.extend(self.factors(*vb));
                let m = self.mono(f)?;
                out = out.plus(&Lin {
                    ts: vec![(m, mul(*ca, *cb)?)],
                    c: 0,
                })?;
            }
        }
        Ok(out)
    }
}

impl<'a> Solver<'a> {
    fn tr_inner(&mut self, t: TermId) -> R<Tr> {
        let key = self.terms.key(t).clone();
        let ty = self.terms.ty(t);
        match key {
            Key::Const(cty, b) => {
                let v = if cty.is_int() {
                    b as i128
                } else {
                    return self.opaque(t);
                };
                Ok(Tr {
                    lin: Lin::konst(v),
                    lo: v,
                    hi: v,
                })
            }
            Key::Op(op, w, args) => self.tr_op(t, op, w, &args),
            Key::Ite(c, a, b) => {
                let br = self.choose()?;
                self.t_split(|s| {
                    format!(
                        "{} is {}",
                        s.terms.render(c),
                        if br { "true" } else { "false" }
                    )
                });
                self.truthy(c, br)?;
                self.tr(if br { a } else { b })
            }
            Key::Call(..) => {
                if let Some(v) = self.env.eval_call(self.terms, t) {
                    let v = v as i128;
                    return Ok(Tr {
                        lin: Lin::konst(v),
                        lo: v,
                        hi: v,
                    });
                }
                if self.depth < UNFOLD_DEPTH
                    && let Some(body) = self.env.unfold(self.terms, t)
                {
                    self.depth += 1;
                    let r = self.tr(body);
                    self.depth -= 1;
                    return r;
                }
                let _ = ty;
                self.opaque(t)
            }
            _ => self.opaque(t),
        }
    }

    fn tr_op(&mut self, t: TermId, op: IOp, wty: ValTy, args: &[TermId]) -> R<Tr> {
        use IOp::*;
        let w = width(wty);
        let wv = pow2(w);
        let konst = |s: &Self, x: TermId| s.terms.as_const(x).map(|c| c as i128);
        match op {
            Add | Sub => {
                let (a, b) = (self.tr(args[0])?, self.tr(args[1])?);
                let (exact, lo, hi) = if op == Add {
                    (a.lin.plus(&b.lin)?, a.lo + b.lo, a.hi + b.hi)
                } else {
                    (a.lin.minus(&b.lin)?, a.lo - b.hi, a.hi - b.lo)
                };
                self.wrap(t, exact, lo, hi, w, true)
            }
            Mul | Shl => {
                let (ca, cb) = (konst(self, args[0]), konst(self, args[1]));
                let k = match (op, ca, cb) {
                    (Shl, _, Some(c)) => Some((pow2((c as u32) % w), args[0])),
                    (Mul, _, Some(c)) => Some((c, args[0])),
                    (Mul, Some(c), _) => Some((c, args[1])),
                    _ => None,
                };
                if let Some((k, x)) = k {
                    let a = self.tr(x)?;
                    return self.wrap(t, a.lin.scale(k)?, mul(a.lo, k)?, mul(a.hi, k)?, w, false);
                }
                if op == Shl {
                    return self.opaque(t);
                }
                let (a, b) = (self.tr(args[0])?, self.tr(args[1])?);
                let (lo, hi) = (mul(a.lo, b.lo)?, mul(a.hi, b.hi)?);
                let exact = if !self.has_wrap(&a.lin) && !self.has_wrap(&b.lin) {
                    self.poly_mul(&a.lin, &b.lin)?
                } else {
                    let mut f = vec![args[0], args[1]];
                    f.sort();
                    Lin::var(self.new_var(VarDesc::TermMono(f), lo, hi)?)
                };
                self.wrap(t, exact, lo, hi, w, false)
            }
            DivU | ShrU | RemU | And => {
                let c = match (op, konst(self, args[0]), konst(self, args[1])) {
                    (ShrU, _, Some(k)) => Some((pow2((k as u32) % w), args[0])),
                    (DivU | RemU, _, Some(c)) => Some((c, args[0])),
                    (And, _, Some(m)) if m >= 0 && (m + 1) & m == 0 => Some((m + 1, args[0])),
                    (And, Some(m), _) if m >= 0 && (m + 1) & m == 0 => Some((m + 1, args[1])),
                    _ => None,
                };
                let is_div = matches!(op, DivU | ShrU);
                match c {
                    Some((0, _)) => self.opaque(t),
                    Some((c, x)) => {
                        let a = self.tr(x)?;
                        if c == 1 {
                            return Ok(if is_div {
                                a
                            } else {
                                Tr {
                                    lin: Lin::konst(0),
                                    lo: 0,
                                    hi: 0,
                                }
                            });
                        }
                        if !is_div && a.lo >= 0 && a.hi < c {
                            return Ok(a);
                        }
                        let dt = self.var_tr(VarDesc::Div(t), fdiv(a.lo, c), fdiv(a.hi, c))?;
                        // c·d ≤ A ≤ c·d + c − 1
                        let cd = dt.lin.scale(c)?;
                        self.le(&cd, &a.lin)?;
                        self.le(&a.lin, &cd.add_c(c - 1)?)?;
                        if is_div {
                            Ok(dt)
                        } else {
                            let lin = a.lin.minus(&cd)?;
                            let (lo, hi) = self.range(&lin)?;
                            Ok(Tr {
                                lin,
                                lo: lo.max(0),
                                hi: hi.min(c - 1),
                            })
                        }
                    }
                    None if matches!(op, DivU | RemU) => {
                        let (a, b) = (self.tr(args[0])?, self.tr(args[1])?);
                        // is the divisor nonzero? A real slot's is (its R24 cup guards it); a
                        // virtual term's is split: B = 0 (the operation traps: its value is an
                        // unconstrained leaf) or B ≥ 1 (B5: bounds only in this branch)
                        let defined = self.env.is_real(t) || b.lo > 0 || !self.choose()?;
                        if !defined {
                            self.eq0(b.lin.clone())?;
                            let w = pow2(width(self.terms.ty(t)));
                            return self.var_tr(VarDesc::Res(t), 0, w - 1);
                        }
                        self.le(&Lin::konst(1), &b.lin)?;
                        let hi = if op == RemU {
                            a.hi.min(b.hi - 1).max(0)
                        } else {
                            a.hi
                        };
                        let r = self.var_tr(VarDesc::Res(t), 0, hi)?;
                        self.le(&r.lin, &a.lin)?;
                        if op == RemU {
                            self.le(&r.lin.add_c(1)?, &b.lin)?;
                        }
                        Ok(r)
                    }
                    None => self.opaque(t),
                }
            }
            WrapI64 => {
                let a = self.tr(args[0])?;
                self.wrap(t, a.lin.clone(), a.lo, a.hi, 32, false)
            }
            ExtendI32U => self.tr(args[0]),
            ExtendI32S => {
                let s = self.signed(args[0])?;
                // s(a) mod 2^64
                if s.lo >= 0 {
                    return Ok(s);
                }
                if s.hi < 0 {
                    return Ok(Tr {
                        lin: s.lin.add_c(pow2(64))?,
                        lo: s.lo + pow2(64),
                        hi: s.hi + pow2(64),
                    });
                }
                if self.choose()? {
                    self.le0(s.lin.add_c(1)?)?;
                    let lin = s.lin.add_c(pow2(64))?;
                    let (lo, hi) = self.range(&lin)?;
                    Ok(Tr { lin, lo, hi })
                } else {
                    self.le0(s.lin.scale(-1)?)?;
                    let (lo, hi) = self.range(&s.lin)?;
                    Ok(Tr { lin: s.lin, lo, hi })
                }
            }
            ShrS => {
                let Some(k) = konst(self, args[1]) else {
                    return self.opaque(t);
                };
                let k = (k as u32) % w;
                if k == 0 {
                    return self.tr(args[0]);
                }
                let s = self.signed(args[0])?;
                let p = pow2(k);
                let half = pow2(w - 1 - k);
                let d = self.var_tr(
                    VarDesc::SDiv(t),
                    fdiv(s.lo, p).max(-half),
                    fdiv(s.hi, p).min(half - 1),
                )?;
                let pd = d.lin.scale(p)?;
                self.le(&pd, &s.lin)?;
                self.le(&s.lin, &pd.add_c(p - 1)?)?;
                if d.lo >= 0 {
                    return Ok(d);
                }
                if d.hi < 0 {
                    return Ok(Tr {
                        lin: d.lin.add_c(wv)?,
                        lo: d.lo + wv,
                        hi: d.hi + wv,
                    });
                }
                if self.choose()? {
                    self.le0(d.lin.add_c(1)?)?;
                    let lin = d.lin.add_c(wv)?;
                    let (lo, hi) = self.range(&lin)?;
                    Ok(Tr { lin, lo, hi })
                } else {
                    self.le0(d.lin.scale(-1)?)?;
                    let (lo, hi) = self.range(&d.lin)?;
                    Ok(Tr { lin: d.lin, lo, hi })
                }
            }
            o if o.is_cmp() => {
                let b = self.choose()?;
                self.t_split(|s| format!("{} = {}", s.terms.render(t), b as u8));
                self.truthy(t, b)?;
                let v = b as i128;
                Ok(Tr {
                    lin: Lin::konst(v),
                    lo: v,
                    hi: v,
                })
            }
            _ => self.opaque(t),
        }
    }

    /// The signed reading S(t) = A − 2ʷ·σ (§3.2).
    fn signed(&mut self, t: TermId) -> R<Tr> {
        if let Some(x) = self.memo_s.get(&t) {
            return Ok(x.clone());
        }
        let w = width(self.terms.ty(t));
        let a = self.tr(t)?;
        let half = pow2(w - 1);
        let r = if a.hi < half {
            a
        } else if a.lo >= half {
            Tr {
                lin: a.lin.add_c(-pow2(w))?,
                lo: a.lo - pow2(w),
                hi: a.hi - pow2(w),
            }
        } else if self.choose()? {
            self.t_split(|s| format!("{} is negative", s.terms.render(t)));
            self.le(&Lin::konst(half), &a.lin)?;
            let lin = a.lin.add_c(-pow2(w))?;
            let (lo, hi) = self.range(&lin)?;
            Tr { lin, lo, hi }
        } else {
            self.t_split(|s| format!("{} is non-negative", s.terms.render(t)));
            self.le(&a.lin, &Lin::konst(half - 1))?;
            let (lo, hi) = self.range(&a.lin)?;
            Tr { lin: a.lin, lo, hi }
        };
        self.memo_s.insert(t, r.clone());
        Ok(r)
    }

    /// Assert that the i32 value t is nonzero (pol) or zero (¬pol).
    fn truthy(&mut self, t: TermId, pol: bool) -> R<()> {
        match self.terms.key(t).clone() {
            Key::Const(_, c) => {
                if (c != 0) == pol {
                    Ok(())
                } else {
                    Err(self.t_fail(|s| s.t_const_false()))
                }
            }
            Key::Op(o, ..) if o.is_cmp() => {
                let a = self.terms.atom_of(t, pol);
                self.assert(&a, true)
            }
            Key::Op(IOp::And, _, args)
                if self.terms.is_cmp(args[0]) && self.terms.is_cmp(args[1]) =>
            {
                if pol {
                    self.truthy(args[0], true)?;
                    self.truthy(args[1], true)
                } else if self.choose()? {
                    self.truthy(args[0], true)?;
                    self.truthy(args[1], false)
                } else {
                    self.truthy(args[0], false)
                }
            }
            Key::Ite(c, a, b) => {
                let br = self.choose()?;
                self.t_split(|s| {
                    format!(
                        "{} is {}",
                        s.terms.render(c),
                        if br { "true" } else { "false" }
                    )
                });
                self.truthy(c, br)?;
                self.truthy(if br { a } else { b }, pol)
            }
            Key::Call(..) => {
                if let Some(v) = self.env.eval_call(self.terms, t) {
                    return if (v != 0) == pol {
                        Ok(())
                    } else {
                        Err(self.t_fail(|s| format!("{} evaluates to {v}", s.terms.render(t))))
                    };
                }
                if self.depth < UNFOLD_DEPTH
                    && let Some(body) = self.env.unfold(self.terms, t)
                {
                    self.depth += 1;
                    let r = self.truthy(body, pol);
                    self.depth -= 1;
                    return r;
                }
                self.truthy_lin(t, pol)
            }
            _ => self.truthy_lin(t, pol),
        }
    }

    fn truthy_lin(&mut self, t: TermId, pol: bool) -> R<()> {
        let x = self.tr(t)?;
        if pol {
            self.le(&Lin::konst(1), &x.lin)
        } else {
            self.eq0(x.lin)
        }
    }

    /// Assert an atom (pol) or its negation.
    pub fn assert(&mut self, a: &Atom, pol: bool) -> R<()> {
        match a {
            Atom::True => {
                if pol {
                    Ok(())
                } else {
                    Err(self.t_fail(|s| s.t_const_false()))
                }
            }
            Atom::False => {
                if pol {
                    Err(self.t_fail(|s| s.t_const_false()))
                } else {
                    Ok(())
                }
            }
            Atom::Bool { t, neg } => self.truthy(*t, pol != *neg),
            Atom::Or(x, y) => {
                if pol {
                    let b = self.choose()?;
                    let d = if b { y } else { x };
                    self.t_split(|s| s.terms.render_atom(d));
                    self.assert(d, true)
                } else {
                    self.assert(x, false)?;
                    self.assert(y, false)
                }
            }
            Atom::Cmp { rel, signed, a, b } => {
                let (x, y) = if *signed {
                    (self.signed(*a)?, self.signed(*b)?)
                } else {
                    (self.tr(*a)?, self.tr(*b)?)
                };
                let (rel, x, y) = match (rel, pol) {
                    (Rel::Lt, true) => (Rel::Lt, x, y),
                    (Rel::Lt, false) => (Rel::Le, y, x),
                    (Rel::Le, true) => (Rel::Le, x, y),
                    (Rel::Le, false) => (Rel::Lt, y, x),
                    (Rel::Eq, true) | (Rel::Ne, false) => (Rel::Eq, x, y),
                    (Rel::Ne, true) | (Rel::Eq, false) => (Rel::Ne, x, y),
                };
                match rel {
                    Rel::Lt => self.le(&x.lin.add_c(1)?, &y.lin),
                    Rel::Le => self.le(&x.lin, &y.lin),
                    Rel::Eq => self.eq0(x.lin.minus(&y.lin)?),
                    Rel::Ne => {
                        if x.hi < y.lo || y.hi < x.lo {
                            return Ok(());
                        }
                        let gt = self.choose()?;
                        self.t_ne_split(*a, *b, *signed, gt, (x.lo, x.hi), (y.lo, y.hi));
                        if gt {
                            self.le(&y.lin.add_c(1)?, &x.lin)
                        } else {
                            self.le(&x.lin.add_c(1)?, &y.lin)
                        }
                    }
                }
            }
        }
    }
}

enum Fm {
    Unsat,
    Sat(Vec<(VarId, i128)>),
    Inexact(VarId),
}

impl<'a> Solver<'a> {
    fn run(&mut self, hyps: &[Atom], goal: &Atom) -> R<()> {
        self.reset_run();
        for (i, h) in hyps.iter().enumerate() {
            self.t_atom(Some(i));
            self.defined(h, true)?;
            self.assert(h, true)?;
        }
        self.t_atom(None);
        // a goal that traps is false: the negated goal holds in the trapping branch
        if !self.defined(goal, false)? {
            return Ok(());
        }
        self.assert(goal, false)
    }

    /// A fact holds iff it evaluates *without trapping* to a nonzero value. For a hypothesis
    /// (`hyp`), assert that every divisor in its eager terms is nonzero (and no signed
    /// INT_MIN / −1); for the goal, split on each such trap: returns false in a branch where the
    /// goal traps (and so is false). Unfolded bodies (`ite`) and call bodies are not eager: their
    /// own guards decide. Real slots are already known not to trap.
    fn defined(&mut self, a: &Atom, hyp: bool) -> R<bool> {
        let mut roots = vec![];
        atom_roots(a, &mut roots);
        let mut divs = vec![];
        let mut seen = std::collections::HashSet::new();
        while let Some(t) = roots.pop() {
            if !seen.insert(t) || self.env.is_real(t) {
                continue;
            }
            match self.terms.key(t).clone() {
                Key::Op(op, w, args) => {
                    if matches!(op, IOp::DivU | IOp::DivS | IOp::RemU | IOp::RemS) {
                        divs.push((t, op, w, args[0], args[1]));
                    }
                    roots.extend(args.iter().copied());
                }
                Key::Call(_, args, _) => roots.extend(args.iter().copied()),
                Key::Float(_, args) => roots.extend(args.iter().copied()),
                Key::Load(.., addr, _) => roots.push(addr),
                _ => {}
            }
        }
        divs.sort_by_key(|d| d.0);
        for (_, op, w, x, y) in divs {
            let b = self.tr(y)?;
            let wv = pow2(width(w));
            if hyp {
                self.le(&Lin::konst(1), &b.lin)?;
                continue;
            }
            if b.lo == 0 {
                if self.choose()? {
                    self.eq0(b.lin.clone())?;
                    return Ok(false);
                }
                self.le(&Lin::konst(1), &b.lin)?;
            }
            if op == IOp::DivS && b.hi == wv - 1 {
                let a = self.tr(x)?;
                if a.lo <= wv / 2 && wv / 2 <= a.hi {
                    if self.choose()? {
                        self.eq0(a.lin.add_c(-(wv / 2))?)?;
                        self.eq0(b.lin.add_c(-(wv - 1))?)?;
                        return Ok(false);
                    }
                    // not both: A ≠ MIN ∨ B ≠ −1
                    if self.choose()? {
                        let m1 = self.terms.konst(w, (wv - 1) as u64);
                        let ne = self.terms.mk_eq(y, m1, false);
                        self.assert(&ne, true)?;
                    } else {
                        let min = self.terms.konst(w, (wv / 2) as u64);
                        let ne = self.terms.mk_eq(x, min, false);
                        self.assert(&ne, true)?;
                    }
                }
            }
        }
        Ok(true)
    }

    /// Interval pre-pass (§3.3): two rounds over the top-level single-variable constraints.
    fn prepass(&mut self, hyps: &[Atom], goal: &Atom) {
        for _round in 0..2 {
            self.reset_run();
            self.pre = true;
            let mut all: Vec<(Atom, bool)> = hyps.iter().map(|h| (h.clone(), true)).collect();
            all.push((goal.clone(), false));
            for (a, pol) in &all {
                if let Err(Stop::Infeasible) = self.assert(a, *pol) {
                    break;
                }
            }
            self.pre = false;
            for v in &self.vars {
                if let VarDesc::Term(t) = v.desc {
                    let e = self.bounds.entry(t).or_insert((v.lo, v.hi));
                    e.0 = e.0.max(v.lo);
                    e.1 = e.1.min(v.hi);
                }
            }
        }
    }

    /// Decide H₁ ∧ … ∧ Hₖ ⇒ G.
    pub fn prove(&mut self, hyps: &[Atom], goal: &Atom) -> Outcome {
        self.prepass(hyps, goal);
        self.choices.clear();
        let mut cases = 0u32;
        let mut inexact: Option<String> = None;
        let mut wraps: Vec<String> = Vec::new();
        loop {
            cases += 1;
            self.cases = cases;
            if cases > CAP_CASES {
                return Outcome::Cap(format!("too many cases (cap {CAP_CASES})"));
            }
            match self.run(hyps, goal) {
                Err(Stop::Cap(c)) => return Outcome::Cap(c),
                Err(Stop::Infeasible) => self.t_end_case(),
                Ok(()) => match self.omega() {
                    Err(Stop::Cap(c)) => return Outcome::Cap(c),
                    Err(Stop::Infeasible) | Ok(Fm::Unsat) => self.t_end_case(),
                    Ok(Fm::Sat(model)) => return Outcome::NotImplied(self.render_model(&model)),
                    Ok(Fm::Inexact(v)) => {
                        if inexact.is_none() {
                            inexact = Some(self.render_var(v));
                        }
                    }
                },
            }
            for w in self.wraps.drain(..) {
                if !wraps.contains(&w) {
                    wraps.push(w);
                }
            }
            // next case: flip the last un-flipped choice used by this run
            self.choices.truncate(self.pos);
            while let Some(&last) = self.choices.last() {
                if last {
                    self.choices.pop();
                } else {
                    *self.choices.last_mut().unwrap() = true;
                    break;
                }
            }
            if self.choices.is_empty() {
                break;
            }
        }
        match inexact {
            Some(v) => Outcome::Inexact(format!(
                "could not decide (inexact step on {v}); add a lemma"
            )),
            None => Outcome::Valid { wraps },
        }
    }

    pub fn render_var(&self, v: VarId) -> String {
        match &self.vars[v as usize].desc {
            VarDesc::Term(t) => format!("u({})", self.terms.render(*t)),
            VarDesc::Mono(f) => f
                .iter()
                .map(|x| self.render_var(*x))
                .collect::<Vec<_>>()
                .join("·"),
            VarDesc::TermMono(f) => f
                .iter()
                .map(|x| self.terms.render(*x))
                .collect::<Vec<_>>()
                .join("·"),
            VarDesc::Wrap(t) => format!("wrap({})", self.terms.render(*t)),
            VarDesc::Div(t) | VarDesc::SDiv(t) => format!("quot({})", self.terms.render(*t)),
            VarDesc::Res(t) => format!("u({})", self.terms.render(*t)),
        }
    }

    fn render_model(&self, m: &[(VarId, i128)]) -> Vec<(String, i128)> {
        let mut out: Vec<(String, i128)> = m
            .iter()
            .filter(|(v, _)| {
                matches!(
                    self.vars[*v as usize].desc,
                    VarDesc::Term(_) | VarDesc::Res(_)
                )
            })
            .map(|(v, x)| (self.render_var(*v), *x))
            .collect();
        out.sort();
        out.dedup();
        out
    }

    /// Omega-lite on the current case (§3.5).
    fn omega(&mut self) -> R<Fm> {
        let mut eqs: Vec<Lin> = vec![];
        let mut ineqs: Vec<Lin> = vec![];
        for c in &self.cons {
            match c {
                Con::Le(l) => ineqs.push(l.clone()),
                Con::Eq(l) => eqs.push(l.clone()),
            }
        }
        // variable bounds
        let mut used: Vec<VarId> = vec![];
        for l in eqs.iter().chain(ineqs.iter()) {
            for (v, _) in &l.ts {
                if !used.contains(v) {
                    used.push(*v);
                }
            }
        }
        used.sort();
        for &v in &used {
            let var = &self.vars[v as usize];
            ineqs.push(Lin {
                ts: vec![(v, -1)],
                c: var.lo,
            });
            ineqs.push(Lin {
                ts: vec![(v, 1)],
                c: -var.hi,
            });
        }
        if used.len() > CAP_VARS {
            return Err(Stop::Cap(format!(
                "too many variables: {} (cap {CAP_VARS})",
                used.len()
            )));
        }
        // 1. equalities
        let mut solved: Vec<(VarId, Lin)> = vec![];
        let mut i = 0;
        while i < eqs.len() {
            let e = eqs[i].clone();
            i += 1;
            if let Some(c) = e.as_const() {
                if c != 0 {
                    self.t_fail(|s| s.t_const_false());
                    return Ok(Fm::Unsat);
                }
                continue;
            }
            if let Some(&(v, k)) = e.ts.iter().find(|(_, k)| k.abs() == 1) {
                // v = −(e − k·v)/k
                let rest = Lin {
                    ts: e.ts.iter().filter(|(x, _)| *x != v).copied().collect(),
                    c: e.c,
                };
                let sol = rest.scale(-k)?;
                for l in eqs.iter_mut().skip(i) {
                    *l = l.subst(v, &sol)?;
                }
                for l in ineqs.iter_mut() {
                    *l = l.subst(v, &sol)?;
                }
                for (_, s) in solved.iter_mut() {
                    *s = s.subst(v, &sol)?;
                }
                solved.push((v, sol));
            } else {
                let g = e.ts.iter().fold(0i128, |g, (_, k)| gcd(g, *k));
                if e.c % g != 0 {
                    self.t_fail_mod(g, |s| s.t_gcd(&e, g));
                    return Ok(Fm::Unsat);
                }
                ineqs.push(e.clone());
                ineqs.push(e.scale(-1)?);
            }
        }
        self.t_omega(&ineqs);
        // 2–4. tighten and eliminate
        let mut exact = true;
        let mut inexact_var = 0;
        let mut elim: Vec<(VarId, Vec<Lin>)> = vec![];
        let mut eliminated: Vec<VarId> = vec![];
        for _round in 0..=used.len() + 1 {
            let mut tight: HashMap<Vec<(VarId, i128)>, i128> = HashMap::new();
            let mut order: Vec<Vec<(VarId, i128)>> = vec![];
            for l in &ineqs {
                if l.ts.is_empty() {
                    if l.c > 0 {
                        return Ok(Fm::Unsat);
                    }
                    continue;
                }
                let g = l.ts.iter().fold(0i128, |g, (_, k)| gcd(g, *k));
                let ts: Vec<(VarId, i128)> = l.ts.iter().map(|(v, k)| (*v, k / g)).collect();
                // Σ k x + c ≤ 0  ⇔  Σ (k/g) x ≤ ⌊−c/g⌋
                let d = fdiv(-l.c, g);
                match tight.get_mut(&ts) {
                    Some(old) => *old = (*old).min(d),
                    None => {
                        order.push(ts.clone());
                        tight.insert(ts, d);
                    }
                }
            }
            if order.len() > CAP_CONS {
                return Err(Stop::Cap(format!("too many constraints (cap {CAP_CONS})")));
            }
            ineqs = order
                .into_iter()
                .map(|ts| {
                    let d = tight[&ts];
                    Lin { ts, c: -d }
                })
                .collect();
            // pick the variable with the fewest lower × upper pairs
            let mut best: Option<(usize, VarId)> = None;
            let mut vars: Vec<VarId> = ineqs
                .iter()
                .flat_map(|l| l.ts.iter().map(|(v, _)| *v))
                .collect();
            vars.sort();
            vars.dedup();
            vars.retain(|v| !eliminated.contains(v));
            if vars.is_empty() {
                break;
            }
            for &v in &vars {
                let lo = ineqs.iter().filter(|l| l.coef(v) < 0).count();
                let hi = ineqs.iter().filter(|l| l.coef(v) > 0).count();
                let p = lo * hi;
                if best.is_none_or(|(bp, _)| p < bp) {
                    best = Some((p, v));
                }
            }
            let v = best.unwrap().1;
            eliminated.push(v);
            let (lows, rest): (Vec<Lin>, Vec<Lin>) =
                ineqs.iter().cloned().partition(|l| l.coef(v) < 0);
            let (ups, keep): (Vec<Lin>, Vec<Lin>) = rest.into_iter().partition(|l| l.coef(v) > 0);
            let mut next = keep;
            for lo in &lows {
                for up in &ups {
                    let (a, b) = (-lo.coef(v), up.coef(v));
                    if a != 1 && b != 1 && exact {
                        exact = false;
                        inexact_var = v;
                    }
                    let g = gcd(a, b);
                    let mut n = lo.scale(b / g)?.plus(&up.scale(a / g)?)?;
                    n.ts.retain(|(x, _)| *x != v);
                    next.push(n);
                }
            }
            let mut bounds = lows;
            bounds.extend(ups);
            elim.push((v, bounds));
            ineqs = next;
        }
        if ineqs.iter().any(|l| l.ts.is_empty() && l.c > 0) {
            return Ok(Fm::Unsat);
        }
        if !exact {
            return Ok(Fm::Inexact(inexact_var));
        }
        // back-substitution: least allowed integer, in reverse elimination order
        let mut val: HashMap<VarId, i128> = HashMap::new();
        for (v, bounds) in elim.iter().rev() {
            let (mut lo, mut hi): (Option<i128>, Option<i128>) = (None, None);
            for b in bounds {
                let k = b.coef(*v);
                let mut rest = b.c;
                for (x, c) in &b.ts {
                    if x != v {
                        rest += c * val.get(x).copied().unwrap_or(0);
                    }
                }
                // k·v + rest ≤ 0
                if k < 0 {
                    let ceil = -fdiv(-rest, -k); // v ≥ ⌈rest / −k⌉
                    lo = Some(lo.map_or(ceil, |l: i128| l.max(ceil)));
                } else {
                    let floor = fdiv(-rest, k);
                    hi = Some(hi.map_or(floor, |h: i128| h.min(floor)));
                }
            }
            val.insert(*v, lo.or(hi).unwrap_or(0));
        }
        for (v, sol) in solved.iter().rev() {
            let mut x = sol.c;
            for (y, c) in &sol.ts {
                x += c * val.get(y).copied().unwrap_or(0);
            }
            val.insert(*v, x);
        }
        // variables fixed by their interval never reached elimination: report them too
        for (v, var) in self.vars.iter().enumerate() {
            val.entry(v as VarId).or_insert(var.lo);
        }
        let mut model: Vec<(VarId, i128)> = val.into_iter().collect();
        model.sort();
        Ok(Fm::Sat(model))
    }
}

fn atom_roots(a: &Atom, v: &mut Vec<TermId>) {
    match a {
        Atom::Cmp { a, b, .. } => v.extend([*a, *b]),
        Atom::Bool { t, .. } => v.push(*t),
        Atom::Or(x, y) => {
            atom_roots(x, v);
            atom_roots(y, v);
        }
        _ => {}
    }
}

pub fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a.max(1)
}
