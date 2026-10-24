//! Canonical value ids (R1), terms, atoms and R4 atom normalization.

use super::ast::{IOp, ValTy};
use smallvec::SmallVec;
use std::collections::HashMap;

pub type TermId = u32;
pub const NO_EPOCH: u32 = u32::MAX;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Key {
    Const(ValTy, u64),
    /// a fresh value: parameter, φ, impure call result, global, …
    Leaf(u32),
    Op(IOp, ValTy, SmallVec<[TermId; 2]>),
    /// float / conversion op: opaque
    Float(String, SmallVec<[TermId; 2]>),
    /// call of a pure function; epoch is NO_EPOCH unless it reads memory
    Call(u32, SmallVec<[TermId; 4]>, u32),
    /// (ty, bytes, signed, offset, addr, epoch)
    Load(ValTy, u32, bool, u64, TermId, u32),
    /// ite(cond ≠ 0, a, b), from `select` or an unfolded `if`
    Ite(TermId, TermId, TermId),
}

#[derive(Clone, Debug)]
pub struct Term {
    pub key: Key,
    pub ty: ValTy,
    /// rendering name of a leaf
    pub name: Option<String>,
    /// unsigned range of a leaf, if narrower than its type
    pub range: Option<(u128, u128)>,
}

#[derive(Default, Clone, Debug)]
pub struct Terms {
    pub terms: Vec<Term>,
    vn: HashMap<Key, TermId>,
    leaves: u32,
    /// function names, for rendering calls
    pub fnames: Vec<String>,
}

pub fn mask(ty: ValTy) -> u64 {
    if ty.bits() == 32 { 0xffff_ffff } else { u64::MAX }
}

impl Terms {
    pub fn new(fnames: Vec<String>) -> Terms {
        Terms { fnames, ..Default::default() }
    }
    pub fn get(&self, t: TermId) -> &Term {
        &self.terms[t as usize]
    }
    pub fn key(&self, t: TermId) -> &Key {
        &self.terms[t as usize].key
    }
    pub fn ty(&self, t: TermId) -> ValTy {
        self.terms[t as usize].ty
    }
    pub fn intern(&mut self, key: Key, ty: ValTy) -> TermId {
        if let Some(&t) = self.vn.get(&key) {
            return t;
        }
        let id = self.terms.len() as TermId;
        self.terms.push(Term { key: key.clone(), ty, name: None, range: None });
        self.vn.insert(key, id);
        id
    }
    pub fn konst(&mut self, ty: ValTy, bits: u64) -> TermId {
        self.intern(Key::Const(ty, bits & mask(ty)), ty)
    }
    pub fn leaf(&mut self, ty: ValTy, name: impl Into<String>, range: Option<(u128, u128)>) -> TermId {
        let id = self.terms.len() as TermId;
        self.leaves += 1;
        self.terms.push(Term { key: Key::Leaf(self.leaves), ty, name: Some(name.into()), range });
        id
    }
    pub fn op(&mut self, op: IOp, w: ValTy, args: &[TermId]) -> TermId {
        self.intern(Key::Op(op, w, args.iter().copied().collect()), op.result(w))
    }
    pub fn as_const(&self, t: TermId) -> Option<u64> {
        match self.key(t) {
            Key::Const(_, b) => Some(*b),
            _ => None,
        }
    }
    pub fn is_const(&self, t: TermId) -> bool {
        self.as_const(t).is_some()
    }
    /// A 0/1-valued comparison (integer or float).
    pub fn is_cmp(&self, t: TermId) -> bool {
        match self.key(t) {
            Key::Op(o, _, _) => o.is_cmp(),
            Key::Float(n, _) => {
                let op = n.split('.').nth(1).unwrap_or("");
                matches!(op, "eq" | "ne" | "lt" | "gt" | "le" | "ge")
            }
            _ => false,
        }
    }
    pub fn is_call(&self, t: TermId) -> bool {
        matches!(self.key(t), Key::Call(..)) && self.ty(t) == ValTy::I32
    }

    /// ⟦t⟧ (pol = true) or ¬⟦t⟧ (pol = false), normalized by R4.
    pub fn atom_of(&mut self, t: TermId, pol: bool) -> Atom {
        match self.key(t).clone() {
            Key::Const(_, c) => {
                if (c != 0) == pol {
                    Atom::True
                } else {
                    Atom::False
                }
            }
            Key::Op(IOp::Eqz, w, a) => {
                let z = self.konst(w, 0);
                self.mk_eq(a[0], z, pol)
            }
            Key::Op(o, w, a) if o.is_cmp() => {
                let _ = w;
                use IOp::*;
                let at = match o {
                    Eq => return self.mk_eq(a[0], a[1], pol),
                    Ne => return self.mk_eq(a[0], a[1], !pol),
                    LtU => Atom::cmp(Rel::Lt, false, a[0], a[1]),
                    GtU => Atom::cmp(Rel::Lt, false, a[1], a[0]),
                    LeU => Atom::cmp(Rel::Le, false, a[0], a[1]),
                    GeU => Atom::cmp(Rel::Le, false, a[1], a[0]),
                    LtS => Atom::cmp(Rel::Lt, true, a[0], a[1]),
                    GtS => Atom::cmp(Rel::Lt, true, a[1], a[0]),
                    LeS => Atom::cmp(Rel::Le, true, a[0], a[1]),
                    GeS => Atom::cmp(Rel::Le, true, a[1], a[0]),
                    _ => unreachable!(),
                };
                if pol { at } else { self.negate(&at) }
            }
            Key::Call(..) if self.ty(t) == ValTy::I32 => Atom::Bool { t, neg: !pol },
            Key::Float(..) if self.is_cmp(t) => Atom::Bool { t, neg: !pol },
            _ => {
                let z = self.konst(self.ty(t), 0);
                self.mk_eq(t, z, !pol)
            }
        }
    }

    /// eq(a, b) (pol) or ne(a, b) (¬pol), with R4 rule 2 and rule 5 (sorted operands).
    pub fn mk_eq(&mut self, a: TermId, b: TermId, pol: bool) -> Atom {
        let zero = |s: &Self, x: TermId| s.as_const(x) == Some(0);
        let boolish = |s: &Self, x: TermId| s.is_cmp(x) || s.is_call(x);
        if zero(self, b) && boolish(self, a) {
            return self.atom_of(a, !pol);
        }
        if zero(self, a) && boolish(self, b) {
            return self.atom_of(b, !pol);
        }
        let (x, y) = self.sorted(a, b);
        Atom::Cmp { rel: if pol { Rel::Eq } else { Rel::Ne }, signed: false, a: x, b: y }
    }

    fn sorted(&self, a: TermId, b: TermId) -> (TermId, TermId) {
        let k = |x: TermId| (self.is_const(x), x);
        if k(a) <= k(b) { (a, b) } else { (b, a) }
    }

    pub fn negate(&mut self, a: &Atom) -> Atom {
        match a {
            Atom::True => Atom::False,
            Atom::False => Atom::True,
            Atom::Cmp { rel, signed, a, b } => match rel {
                Rel::Eq => Atom::Cmp { rel: Rel::Ne, signed: false, a: *a, b: *b },
                Rel::Ne => Atom::Cmp { rel: Rel::Eq, signed: false, a: *a, b: *b },
                Rel::Lt => Atom::cmp(Rel::Le, *signed, *b, *a),
                Rel::Le => Atom::cmp(Rel::Lt, *signed, *b, *a),
            },
            Atom::Bool { t, neg } => Atom::Bool { t: *t, neg: !neg },
            Atom::Or(..) => panic!("negating a disjunctive cup"),
        }
    }

    /// The constant ids an atom mentions directly (for R28: all must be constants).
    pub fn atom_args(&self, a: &Atom) -> Vec<TermId> {
        match a {
            Atom::Cmp { a, b, .. } => vec![*a, *b],
            Atom::Bool { t, .. } => match self.key(*t) {
                Key::Call(_, args, _) => args.to_vec(),
                _ => vec![*t],
            },
            Atom::Or(x, y) => {
                let mut v = self.atom_args(x);
                v.extend(self.atom_args(y));
                v
            }
            _ => vec![],
        }
    }

    pub fn render(&self, t: TermId) -> String {
        let term = self.get(t);
        match &term.key {
            Key::Const(ty, b) => match ty {
                ValTy::I32 => (*b as u32 as i32).to_string(),
                ValTy::I64 => (*b as i64).to_string(),
                ValTy::F32 => f32::from_bits(*b as u32).to_string(),
                ValTy::F64 => f64::from_bits(*b).to_string(),
            },
            Key::Leaf(_) => term.name.clone().unwrap_or_else(|| format!("#{t}")),
            Key::Op(o, w, a) => {
                let args: Vec<String> = a.iter().map(|x| self.render(*x)).collect();
                let n = o.name(*w);
                let short = n.split('.').nth(1).unwrap_or(&n);
                let short = match short {
                    "extend_i32_u" => "ext_u",
                    "extend_i32_s" => "ext_s",
                    "wrap_i64" => "wrap",
                    s => s,
                };
                format!("{short}({})", args.join(", "))
            }
            Key::Float(n, a) => {
                let args: Vec<String> = a.iter().map(|x| self.render(*x)).collect();
                format!("{n}({})", args.join(", "))
            }
            Key::Call(f, a, e) => {
                let args: Vec<String> = a.iter().map(|x| self.render(*x)).collect();
                let name = self.fnames.get(*f as usize).cloned().unwrap_or_else(|| format!("${f}"));
                let ep = if *e == NO_EPOCH { String::new() } else { format!("@ε{e}") };
                format!("{name}({}){ep}", args.join(", "))
            }
            Key::Load(ty, bytes, _, off, a, e) => {
                format!("{}.load{}[{}+{off}]@ε{e}", ty.name(), bytes * 8, self.render(*a))
            }
            Key::Ite(c, a, b) => format!("ite({}, {}, {})", self.render(*c), self.render(*a), self.render(*b)),
        }
    }

    pub fn render_atom(&self, a: &Atom) -> String {
        match a {
            Atom::True => "True".into(),
            Atom::False => "False".into(),
            Atom::Cmp { rel, signed, a, b } => {
                let (x, y) = (self.render(*a), self.render(*b));
                let r = |v: String| if *signed { format!("s({v})") } else { format!("u({v})") };
                match rel {
                    Rel::Eq => format!("{x} = {y}"),
                    Rel::Ne => format!("{x} ≠ {y}"),
                    Rel::Lt => format!("{} < {}", r(x), r(y)),
                    Rel::Le => format!("{} ≤ {}", r(x), r(y)),
                }
            }
            Atom::Bool { t, neg } => format!("{}{}", if *neg { "¬" } else { "" }, self.render(*t)),
            Atom::Or(x, y) => format!("{} ∨ {}", self.render_atom(x), self.render_atom(y)),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Rel {
    Eq,
    Ne,
    Lt,
    Le,
}

/// A normalized atom (R4). Two atoms match iff they are equal.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Atom {
    True,
    False,
    Cmp { rel: Rel, signed: bool, a: TermId, b: TermId },
    /// a predicate call (or float comparison) taken as a truth value
    Bool { t: TermId, neg: bool },
    /// the disjunctive cup of R25
    Or(Box<Atom>, Box<Atom>),
}

impl Atom {
    pub fn cmp(rel: Rel, signed: bool, a: TermId, b: TermId) -> Atom {
        Atom::Cmp { rel, signed, a, b }
    }
    /// Does a fact with this atom feed a cup with goal `goal`? (Exact match; a disjunctive goal
    /// accepts either disjunct.)
    pub fn feeds(&self, goal: &Atom) -> bool {
        match goal {
            Atom::Or(x, y) => self == goal || self.feeds(x) || self.feeds(y),
            _ => self == goal,
        }
    }
    pub fn mentions(&self, t: TermId) -> bool {
        match self {
            Atom::Cmp { a, b, .. } => *a == t || *b == t,
            Atom::Bool { t: x, .. } => *x == t,
            Atom::Or(x, y) => x.mentions(t) || y.mentions(t),
            _ => false,
        }
    }
}
