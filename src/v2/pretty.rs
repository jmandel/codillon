//! The infix printer for everything a student reads (design 16 §8, research/24 §4): cups,
//! chips, accounts and error messages. `(x·2)&1 ≠ 0`, `u(r) ≤ 65534`, `x ≠ 0`. Values bound to
//! locals print by the local's name, the current value plainly and older ones versioned
//! (`i@12`, or `x₀` for a parameter's entry value), from the naming view the kernel keeps in
//! [`Terms::view`] (review B2). The kernel form (`Terms::render`) stays for internal use.

use super::ast::{IOp, ValTy};
use super::term::{Atom, Key, NO_EPOCH, Rel, TermId, Terms};

// precedence: higher binds tighter
const P_ATOM: u8 = 10;
const P_MUL: u8 = 7;
const P_ADD: u8 = 6;
const P_SHIFT: u8 = 5;
const P_AND: u8 = 4;
const P_XOR: u8 = 3;
const P_OR: u8 = 2;
const P_CMP: u8 = 1;

fn sup(n: u32) -> String {
    const D: [char; 10] = ['⁰', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹'];
    n.to_string()
        .chars()
        .map(|c| D[c.to_digit(10).unwrap_or(0) as usize])
        .collect()
}

/// A constant as a student reads it: decimal up to 2¹⁶, then `2ⁿ` and `2ⁿ−k` for small k.
pub fn num(u: u128) -> String {
    if u > 65536 {
        if u.is_power_of_two() {
            return format!("2{}", sup(u.trailing_zeros()));
        }
        let next = u.next_power_of_two();
        if next - u <= 256 {
            return format!("2{}−{}", sup(next.trailing_zeros()), next - u);
        }
    }
    u.to_string()
}

impl Terms {
    /// A term in infix, by the current naming view.
    pub fn show(&self, t: TermId) -> String {
        self.pt(t, true).0
    }

    /// A term in infix without naming the term itself (its parts are named): what a local's
    /// current value is made of, e.g. `r@30 + 1`.
    pub fn show_def(&self, t: TermId) -> String {
        self.pt(t, false).0
    }

    fn paren(&self, t: TermId, min: u8) -> String {
        let (s, p) = self.pt(t, true);
        if p < min { format!("({s})") } else { s }
    }

    fn bin(&self, a: TermId, op: &str, b: TermId, p: u8) -> (String, u8) {
        // left-associative: the right operand needs strictly tighter binding. Bitwise and shift
        // operators take only atoms (a chain of the same bitwise operator excepted), so a reader
        // never needs C's precedence table: `((x − 1)&7)<<2`, `(x·2)&1`.
        let tight = matches!(p, P_AND | P_XOR | P_OR | P_SHIFT);
        let left = if tight {
            let (s, q) = self.pt(a, true);
            if q == P_ATOM || (q == p && p != P_SHIFT) {
                s
            } else {
                format!("({s})")
            }
        } else {
            self.paren(a, p)
        };
        let right = self.paren(b, if tight { P_ATOM } else { p + 1 });
        (format!("{left}{op}{right}"), p)
    }

    fn signed_const(&self, t: TermId) -> Option<i128> {
        let Key::Const(ty, b) = self.key(t) else {
            return None;
        };
        Some(match ty {
            ValTy::I32 => *b as u32 as i32 as i128,
            ValTy::I64 => *b as i64 as i128,
            _ => return None,
        })
    }

    fn pt(&self, t: TermId, named: bool) -> (String, u8) {
        if named && let Some(n) = self.view.get(&t) {
            return (n.clone(), P_ATOM);
        }
        let term = self.get(t);
        match &term.key {
            Key::Const(ty, b) => (
                match ty {
                    // a small negative number reads as one (−1, a tombstone); an unsigned
                    // comparison prints its constants unsigned (see `reading`)
                    ValTy::I32 | ValTy::I64 => match self.signed_const(t) {
                        Some(c) if (-65536..0).contains(&c) => format!("−{}", c.unsigned_abs()),
                        _ => num(*b as u128),
                    },
                    ValTy::F32 => f32::from_bits(*b as u32).to_string(),
                    ValTy::F64 => f64::from_bits(*b).to_string(),
                },
                P_ATOM,
            ),
            Key::Leaf(_) => (
                term.name
                    .clone()
                    .map(|n| n.trim_start_matches('$').to_string())
                    .unwrap_or_else(|| format!("#{t}")),
                P_ATOM,
            ),
            Key::Op(o, _, a) => self.show_op(*o, a),
            Key::Float(n, a) => {
                let args: Vec<String> = a.iter().map(|x| self.show(*x)).collect();
                (format!("{n}({})", args.join(", ")), P_ATOM)
            }
            Key::Call(f, a, e) => {
                let args: Vec<String> = a.iter().map(|x| self.show(*x)).collect();
                let name = self
                    .fnames
                    .get(*f as usize)
                    .map(|n| n.trim_start_matches('$').to_string())
                    .unwrap_or_else(|| format!("f{f}"));
                let ep = if *e == NO_EPOCH || *e == 0 {
                    String::new()
                } else {
                    format!("@ε{e}")
                };
                (format!("{name}({}){ep}", args.join(", ")), P_ATOM)
            }
            Key::Load(_, bytes, _, off, a, e) => {
                let addr = if *off == 0 {
                    self.show(*a)
                } else {
                    format!("{}+{off}", self.paren(*a, P_ADD))
                };
                let ep = if *e == 0 {
                    String::new()
                } else {
                    format!("@ε{e}")
                };
                (format!("mem{}[{addr}]{ep}", bytes * 8), P_ATOM)
            }
            Key::Ite(c, a, b) => (
                format!(
                    "({} ? {} : {})",
                    self.show_cond(*c),
                    self.show(*a),
                    self.show(*b)
                ),
                P_ATOM,
            ),
        }
    }
}

impl Terms {
    /// `u(a)` / `s(a)` for an ordered comparison of a non-constant (constants print as numbers).
    fn reading(&self, t: TermId, signed: bool) -> String {
        if signed {
            match self.signed_const(t) {
                Some(c) if c < 0 => format!("−{}", num(c.unsigned_abs())),
                Some(_) => self.show(t),
                None => format!("s({})", self.show(t)),
            }
        } else if let Some(c) = self.as_const(t) {
            num(c as u128)
        } else {
            format!("u({})", self.show(t))
        }
    }

    fn cmp_text(&self, rel: Rel, signed: bool, a: TermId, b: TermId) -> String {
        match rel {
            Rel::Eq => format!("{} = {}", self.paren(a, P_OR), self.paren(b, P_OR)),
            Rel::Ne => format!("{} ≠ {}", self.paren(a, P_OR), self.paren(b, P_OR)),
            Rel::Lt => format!("{} < {}", self.reading(a, signed), self.reading(b, signed)),
            Rel::Le => format!("{} ≤ {}", self.reading(a, signed), self.reading(b, signed)),
        }
    }

    /// A comparison op as a proposition, if `o` is one.
    fn cmp_op(&self, o: IOp, a: &[TermId]) -> Option<String> {
        use IOp::*;
        Some(match (o, a) {
            (Eqz, [x]) => format!("{} = 0", self.paren(*x, P_OR)),
            (Eq, [x, y]) => self.cmp_text(Rel::Eq, false, *x, *y),
            (Ne, [x, y]) => self.cmp_text(Rel::Ne, false, *x, *y),
            (LtU, [x, y]) => self.cmp_text(Rel::Lt, false, *x, *y),
            (LtS, [x, y]) => self.cmp_text(Rel::Lt, true, *x, *y),
            (LeU, [x, y]) => self.cmp_text(Rel::Le, false, *x, *y),
            (LeS, [x, y]) => self.cmp_text(Rel::Le, true, *x, *y),
            (GtU, [x, y]) => self.cmp_text(Rel::Lt, false, *y, *x),
            (GtS, [x, y]) => self.cmp_text(Rel::Lt, true, *y, *x),
            (GeU, [x, y]) => self.cmp_text(Rel::Le, false, *y, *x),
            (GeS, [x, y]) => self.cmp_text(Rel::Le, true, *y, *x),
            _ => return None,
        })
    }

    fn show_op(&self, o: IOp, a: &[TermId]) -> (String, u8) {
        use IOp::*;
        if let Some(c) = self.cmp_op(o, a) {
            return (c, P_CMP);
        }
        match (o, a) {
            (Add, [x, y]) => match self.signed_const(*y) {
                Some(c) if c < 0 => (
                    format!("{} − {}", self.paren(*x, P_ADD), num(c.unsigned_abs())),
                    P_ADD,
                ),
                _ => self.bin(*x, " + ", *y, P_ADD),
            },
            (Sub, [x, y]) => self.bin(*x, " − ", *y, P_ADD),
            (Mul, [x, y]) => self.bin(*x, "·", *y, P_MUL),
            (DivU, [x, y]) => self.bin(*x, "/", *y, P_MUL),
            (DivS, [x, y]) => self.bin(*x, " /ₛ ", *y, P_MUL),
            (RemU, [x, y]) => self.bin(*x, " % ", *y, P_MUL),
            (RemS, [x, y]) => self.bin(*x, " %ₛ ", *y, P_MUL),
            (And, [x, y]) => self.bin(*x, "&", *y, P_AND),
            (Or, [x, y]) => self.bin(*x, "|", *y, P_OR),
            (Xor, [x, y]) => self.bin(*x, "^", *y, P_XOR),
            (Shl, [x, y]) => self.bin(*x, "<<", *y, P_SHIFT),
            (ShrU, [x, y]) => self.bin(*x, ">>", *y, P_SHIFT),
            (ShrS, [x, y]) => self.bin(*x, " >>ₛ ", *y, P_SHIFT),
            // the unsigned reading is unchanged by zero extension
            (ExtendI32U, [x]) => self.pt(*x, true),
            (ExtendI32S, [x]) => (format!("s({})", self.show(*x)), P_ATOM),
            (WrapI64, [x]) => (format!("{} mod 2³²", self.paren(*x, P_MUL + 1)), P_MUL),
            (_, args) => {
                let n = o.name(ValTy::I32);
                let short = n.split('.').nth(1).unwrap_or(&n).to_string();
                let v: Vec<String> = args.iter().map(|x| self.show(*x)).collect();
                (format!("{short}({})", v.join(", ")), P_ATOM)
            }
        }
    }

    /// The condition of an `ite` as a proposition.
    pub fn show_cond(&self, c: TermId) -> String {
        if let Key::Op(o, _, a) = self.key(c)
            && let Some(s) = self.cmp_op(*o, a)
            && !self.view.contains_key(&c)
        {
            return s;
        }
        format!("{} ≠ 0", self.paren(c, P_OR))
    }

    /// An atom in infix.
    pub fn show_atom(&self, a: &Atom) -> String {
        match a {
            Atom::True => "True".into(),
            Atom::False => "False".into(),
            Atom::Cmp { rel, signed, a, b } => self.cmp_text(*rel, *signed, *a, *b),
            Atom::Bool { t, neg } => format!("{}{}", if *neg { "¬" } else { "" }, self.show(*t)),
            Atom::Or(x, y) => format!("{} ∨ {}", self.show_atom(x), self.show_atom(y)),
        }
    }
}
