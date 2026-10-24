// A second encoding of an obligation, in integer arithmetic.
//
// Bit-blasting decides most obligations quickly, but not nonlinear ones (r * r <= n), which
// Z3's integer arithmetic handles well. This translates our own bitvector queries (vc.rs)
// into integers, exactly: a bitvector becomes an integer in its signed range, except
// widths 8 and 16 (memory bytes), which are unsigned; machine arithmetic wraps; spec
// arithmetic (sadd_W, smul_W, …) does not, because vc.rs proved that it fits.
// Operations without an exact linear translation (bitwise and with a non-mask, or, xor,
// rotations, shifts by variables) make the translation fail, and the obligation keeps its
// bitvector verdict.

use std::fmt::Write;

#[derive(Debug, Clone, PartialEq)]
enum Sx {
    Atom(String),
    List(Vec<Sx>),
}

fn parse(s: &str) -> Option<Vec<Sx>> {
    let mut out = vec![];
    let mut stack: Vec<Vec<Sx>> = vec![];
    let b = s.as_bytes();
    let mut i = 0;
    while i < b.len() {
        let c = b[i];
        if c == b'(' {
            stack.push(vec![]);
            i += 1;
        } else if c == b')' {
            let l = stack.pop()?;
            match stack.last_mut() {
                Some(top) => top.push(Sx::List(l)),
                None => out.push(Sx::List(l)),
            }
            i += 1;
        } else if c.is_ascii_whitespace() {
            i += 1;
        } else if c == b';' {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
        } else {
            let start = i;
            if c == b'|' {
                i += 1;
                while i < b.len() && b[i] != b'|' {
                    i += 1;
                }
                i += 1;
            } else {
                while i < b.len() && !b[i].is_ascii_whitespace() && b[i] != b'(' && b[i] != b')' {
                    i += 1;
                }
            }
            let a = Sx::Atom(s[start..i.min(b.len())].to_string());
            match stack.last_mut() {
                Some(top) => top.push(a),
                None => out.push(a),
            }
        }
    }
    if stack.is_empty() { Some(out) } else { None }
}

fn show(s: &Sx) -> String {
    match s {
        Sx::Atom(a) => a.clone(),
        Sx::List(l) => format!("({})", l.iter().map(show).collect::<Vec<_>>().join(" ")),
    }
}

#[derive(Debug, Clone, PartialEq)]
enum Sort {
    Bool,
    Bv(u32),
    Arr(Box<Sort>, Box<Sort>),
}

fn sort_of(s: &Sx) -> Option<Sort> {
    match s {
        Sx::Atom(a) if a == "Bool" => Some(Sort::Bool),
        Sx::List(l) => match l.as_slice() {
            [Sx::Atom(u), Sx::Atom(bv), Sx::Atom(w)] if u == "_" && bv == "BitVec" => {
                w.parse().ok().map(Sort::Bv)
            }
            [Sx::Atom(arr), a, b] if arr == "Array" => {
                Some(Sort::Arr(Box::new(sort_of(a)?), Box::new(sort_of(b)?)))
            }
            _ => None,
        },
        _ => None,
    }
}

fn int_sort(s: &Sort) -> String {
    match s {
        Sort::Bool => "Bool".into(),
        Sort::Bv(_) => "Int".into(),
        Sort::Arr(a, b) => format!("(Array {} {})", int_sort(a), int_sort(b)),
    }
}

fn pow2(w: u32) -> i128 {
    1i128 << w
}

fn lit(v: i128) -> String {
    if v < 0 {
        format!("(- {})", -v)
    } else {
        v.to_string()
    }
}

// Widths 8 and 16 are memory bytes and halves, read as unsigned; all others are signed.
fn signed_rep(w: u32) -> bool {
    w != 8 && w != 16
}

// The integer that a bitvector value of width w stands for.
fn value(raw: u128, w: u32) -> i128 {
    let raw = raw as i128;
    if signed_rep(w) && raw >= pow2(w - 1) {
        raw - pow2(w)
    } else {
        raw
    }
}

fn range(t: &str, w: u32) -> String {
    if signed_rep(w) {
        format!(
            "(and (<= {} {t}) (< {t} {}))",
            lit(-pow2(w - 1)),
            lit(pow2(w - 1))
        )
    } else {
        format!("(and (<= 0 {t}) (< {t} {}))", pow2(w))
    }
}

// wrap an integer into the representation of width w
fn wrap(t: &str, w: u32) -> String {
    if signed_rep(w) {
        // as cases, so that the solver can use what it knows of t's range
        let (h, f) = (pow2(w - 1), pow2(w));
        format!(
            "(let ((z {t})) (ite (and (<= {} z) (< z {h})) z (ite (and (<= {h} z) (< z {f})) (- z {f}) (ite (and (<= {} z) (< z {})) (+ z {f}) (- (mod (+ z {h}) {f}) {h})))))",
            lit(-h),
            lit(-f),
            lit(-h)
        )
    } else {
        format!("(mod {t} {})", pow2(w))
    }
}

// the unsigned reading of a value of width w
fn unsigned(t: &str, w: u32) -> String {
    if signed_rep(w) {
        format!("(ite (< {t} 0) (+ {t} {}) {t})", pow2(w))
    } else {
        t.to_string()
    }
}

// an unsigned integer in [0, 2^w) into the representation of width w
fn from_unsigned(t: &str, w: u32) -> String {
    if signed_rep(w) {
        format!("(ite (>= {t} {}) (- {t} {}) {t})", pow2(w - 1), pow2(w))
    } else {
        t.to_string()
    }
}

const INT_PREAMBLE: &str = "\
(define-fun ld8 ((m (Array Int Int)) (a Int)) Int (mod (select m a) 256))
(define-fun ld16 ((m (Array Int Int)) (a Int)) Int (+ (ld8 m a) (* 256 (ld8 m (- (mod (+ a 2147483649) 4294967296) 2147483648)))))
(define-fun ld32u ((m (Array Int Int)) (a Int)) Int (+ (ld16 m a) (* 65536 (ld16 m (- (mod (+ a 2147483650) 4294967296) 2147483648)))))
(define-fun ld32 ((m (Array Int Int)) (a Int)) Int (let ((z (ld32u m a))) (ite (>= z 2147483648) (- z 4294967296) z)))
(define-fun st8 ((m (Array Int Int)) (a Int) (v Int)) (Array Int Int) (store m a (mod v 256)))
(define-fun st16 ((m (Array Int Int)) (a Int) (v Int)) (Array Int Int) (st8 (st8 m a (mod v 256)) (- (mod (+ a 2147483649) 4294967296) 2147483648) (mod (div v 256) 256)))
(define-fun st32 ((m (Array Int Int)) (a Int) (v Int)) (Array Int Int) (let ((u (ite (< v 0) (+ v 4294967296) v))) (st16 (st16 m a (mod u 65536)) (- (mod (+ a 2147483650) 4294967296) 2147483648) (div u 65536))))
";

// functions of vc.rs's preamble that INT_PREAMBLE replaces
const REPLACED: &[&str] = &["ld8", "ld16", "ld32", "ld64", "st8", "st16", "st32", "st64"];

// vc.rs's spec arithmetic at width W: sadd_W … (translated inline, without wrapping)
fn spec_op(f: &str) -> Option<&str> {
    let (op, w) = f.rsplit_once('_')?;
    (matches!(op, "sadd" | "ssub" | "smul" | "sneg" | "emod" | "ediv") && w.parse::<u32>().is_ok())
        .then_some(op)
}

struct Tr {
    // sorts of named things: constants, defined functions (result sort), bound variables
    consts: Vec<(String, Sort)>,
    funs: Vec<(String, Sort)>,
}

type R<T> = Option<T>;

impl Tr {
    fn sort_of_name(&self, n: &str) -> Option<Sort> {
        self.consts
            .iter()
            .rev()
            .find(|(m, _)| m == n)
            .map(|(_, s)| s.clone())
    }

    fn fun_sort(&self, n: &str) -> Option<Sort> {
        self.funs
            .iter()
            .rev()
            .find(|(m, _)| m == n)
            .map(|(_, s)| s.clone())
    }

    // literal value of a term, if it is a bitvector literal
    fn literal(&self, s: &Sx) -> Option<(i128, u32)> {
        match s {
            Sx::Atom(a) => {
                if let Some(h) = a.strip_prefix("#x") {
                    let w = 4 * h.len() as u32;
                    Some((value(u128::from_str_radix(h, 16).ok()?, w), w))
                } else if let Some(b) = a.strip_prefix("#b") {
                    let w = b.len() as u32;
                    Some((value(u128::from_str_radix(b, 2).ok()?, w), w))
                } else {
                    None
                }
            }
            Sx::List(l) => match l.as_slice() {
                [Sx::Atom(u), Sx::Atom(n), Sx::Atom(w)] if u == "_" && n.starts_with("bv") => {
                    let w: u32 = w.parse().ok()?;
                    Some((value(n[2..].parse().ok()?, w), w))
                }
                [Sx::Atom(f), a, b] if f == "bvand" => {
                    // a masked shift amount, e.g. (bvand (_ bv1 32) (_ bv31 32))
                    let (x, w) = self.literal(a)?;
                    let (y, _) = self.literal(b)?;
                    Some((value((x as u128 & y as u128) & (pow2(w) as u128 - 1), w), w))
                }
                _ => None,
            },
        }
    }

    fn term(&mut self, s: &Sx) -> R<(String, Sort)> {
        if let Some((v, w)) = self.literal(s) {
            return Some((lit(v), Sort::Bv(w)));
        }
        match s {
            Sx::Atom(a) => {
                if a == "true" || a == "false" {
                    return Some((a.clone(), Sort::Bool));
                }
                if let Some(srt) = self.sort_of_name(a) {
                    return Some((a.clone(), srt));
                }
                if let Some(srt) = self.fun_sort(a) {
                    return Some((a.clone(), srt));
                }
                if a.parse::<i128>().is_ok() {
                    return None; // Int literals do not occur in our queries
                }
                None
            }
            Sx::List(l) => self.app(l),
        }
    }

    fn args(&mut self, l: &[Sx]) -> R<Vec<(String, Sort)>> {
        l.iter().map(|x| self.term(x)).collect()
    }

    fn app(&mut self, l: &[Sx]) -> R<(String, Sort)> {
        let head = l.first()?;
        // indexed operators: ((_ extract hi lo) x), ((_ sign_extend k) x), ((as const S) v)
        if let Sx::List(h) = head {
            match h.as_slice() {
                [Sx::Atom(u), Sx::Atom(op), Sx::Atom(i), Sx::Atom(j)]
                    if u == "_" && op == "extract" =>
                {
                    let (hi, lo): (u32, u32) = (i.parse().ok()?, j.parse().ok()?);
                    let (x, srt) = self.term(&l[1])?;
                    let Sort::Bv(w) = srt else { return None };
                    let n = hi - lo + 1;
                    let u = unsigned(&x, w);
                    let slice = if lo == 0 {
                        if n == w {
                            u
                        } else {
                            format!("(mod {u} {})", pow2(n))
                        }
                    } else {
                        format!("(mod (div {u} {}) {})", pow2(lo), pow2(n))
                    };
                    return Some((from_unsigned(&slice, n), Sort::Bv(n)));
                }
                [Sx::Atom(u), Sx::Atom(op), Sx::Atom(k)]
                    if u == "_" && (op == "sign_extend" || op == "zero_extend") =>
                {
                    let k: u32 = k.parse().ok()?;
                    let (x, srt) = self.term(&l[1])?;
                    let Sort::Bv(w) = srt else { return None };
                    let n = w + k;
                    let t = if op == "sign_extend" {
                        // the signed value of x, in width n
                        if signed_rep(w) {
                            x
                        } else {
                            format!("(ite (>= {x} {}) (- {x} {}) {x})", pow2(w - 1), pow2(w))
                        }
                    } else {
                        from_unsigned(&unsigned(&x, w), n)
                    };
                    return Some((t, Sort::Bv(n)));
                }
                [Sx::Atom(a), srt] if a == "as" => {
                    // ((as const (Array I E)) v)
                    let arr = match srt {
                        Sx::List(x) if x.len() == 2 => sort_of(&x[1])?,
                        _ => return None,
                    };
                    let (v, _) = self.term(&l[1])?;
                    return Some((format!("((as const {}) {v})", int_sort(&arr)), arr));
                }
                _ => return None,
            }
        }
        let Sx::Atom(f) = head else { return None };
        let f = f.as_str();
        match f {
            "forall" | "exists" => {
                let Sx::List(binds) = &l[1] else { return None };
                let mut names = vec![];
                let mut guards = vec![];
                for b in binds {
                    let Sx::List(b) = b else { return None };
                    let (Sx::Atom(n), s) = (&b[0], &b[1]) else {
                        return None;
                    };
                    let srt = sort_of(s)?;
                    if let Sort::Bv(w) = srt {
                        guards.push(range(n, w));
                    }
                    names.push(format!("({n} {})", int_sort(&srt)));
                    self.consts.push((n.clone(), srt));
                }
                // (! body :pattern …) must stay directly under the quantifier
                let (inner_sx, attrs) = match &l[2] {
                    Sx::List(b) if matches!(b.first(), Some(Sx::Atom(a)) if a == "!") => {
                        (&b[1], Some(&b[2..]))
                    }
                    other => (other, None),
                };
                let body = self.term(inner_sx);
                let mut rest = String::new();
                if let (Some(attrs), Some(_)) = (attrs, &body) {
                    let mut i = 0;
                    while i + 1 < attrs.len() {
                        let (Sx::Atom(key), Sx::List(ps)) = (&attrs[i], &attrs[i + 1]) else {
                            for _ in binds {
                                self.consts.pop();
                            }
                            return None;
                        };
                        let mut pats = vec![];
                        for p in ps {
                            match self.term(p) {
                                Some((t, _)) => pats.push(t),
                                None => {
                                    for _ in binds {
                                        self.consts.pop();
                                    }
                                    return None;
                                }
                            }
                        }
                        let _ = write!(rest, " {key} ({})", pats.join(" "));
                        i += 2;
                    }
                }
                for _ in binds {
                    self.consts.pop();
                }
                let (body, _) = body?;
                let g = if guards.is_empty() {
                    "true".to_string()
                } else {
                    format!("(and {})", guards.join(" "))
                };
                let inner = if f == "forall" {
                    format!("(=> {g} {body})")
                } else {
                    format!("(and {g} {body})")
                };
                let inner = if rest.is_empty() {
                    inner
                } else {
                    format!("(! {inner}{rest})")
                };
                return Some((format!("({f} ({}) {inner})", names.join(" ")), Sort::Bool));
            }
            "!" => {
                // (! t :pattern (p…))
                let (t, srt) = self.term(&l[1])?;
                let mut rest = String::new();
                let mut i = 2;
                while i + 1 < l.len() {
                    let Sx::Atom(key) = &l[i] else { return None };
                    let Sx::List(ps) = &l[i + 1] else { return None };
                    let mut pats = vec![];
                    for p in ps {
                        pats.push(self.term(p)?.0);
                    }
                    let _ = write!(rest, " {key} ({})", pats.join(" "));
                    i += 2;
                }
                return Some((format!("(! {t}{rest})",), srt));
            }
            "let" => {
                let Sx::List(binds) = &l[1] else { return None };
                let mut parts = vec![];
                let mut n = 0;
                for b in binds {
                    let Sx::List(b) = b else { return None };
                    let Sx::Atom(name) = &b[0] else { return None };
                    let (t, srt) = self.term(&b[1])?;
                    parts.push(format!("({name} {t})"));
                    self.consts.push((name.clone(), srt));
                    n += 1;
                }
                let body = self.term(&l[2]);
                for _ in 0..n {
                    self.consts.pop();
                }
                let (body, srt) = body?;
                return Some((format!("(let ({}) {body})", parts.join(" ")), srt));
            }
            _ => {}
        }
        let a = self.args(&l[1..])?;
        let w = |i: usize| match a.get(i).map(|x| &x.1) {
            Some(Sort::Bv(w)) => Some(*w),
            _ => None,
        };
        let t = |i: usize| a[i].0.clone();
        Some(match f {
            "and" | "or" | "not" | "=>" => (
                format!(
                    "({f} {})",
                    a.iter().map(|x| x.0.clone()).collect::<Vec<_>>().join(" ")
                ),
                Sort::Bool,
            ),
            "=" | "distinct" => (format!("({f} {} {})", t(0), t(1)), Sort::Bool),
            "ite" => (format!("(ite {} {} {})", t(0), t(1), t(2)), a[1].1.clone()),
            "select" => {
                let Sort::Arr(_, e) = a[0].1.clone() else {
                    return None;
                };
                (format!("(select {} {})", t(0), t(1)), *e)
            }
            "store" => (
                format!("(store {} {} {})", t(0), t(1), t(2)),
                a[0].1.clone(),
            ),
            // spec arithmetic: never wraps
            _ if spec_op(f).is_some() => {
                let w = w(0)?;
                let t = match spec_op(f)? {
                    "sadd" => format!("(+ {} {})", t(0), t(1)),
                    "ssub" => format!("(- {} {})", t(0), t(1)),
                    "smul" => format!("(* {} {})", t(0), t(1)),
                    "sneg" => format!("(- {})", t(0)),
                    "emod" => format!("(mod {} {})", t(0), t(1)),
                    _ => format!("(div {} {})", t(0), t(1)),
                };
                (t, Sort::Bv(w))
            }
            "ld8" => (format!("(ld8 {} {})", t(0), t(1)), Sort::Bv(8)),
            "ld16" => (format!("(ld16 {} {})", t(0), t(1)), Sort::Bv(16)),
            "ld32" => (format!("(ld32 {} {})", t(0), t(1)), Sort::Bv(32)),
            "st8" | "st16" | "st32" => {
                (format!("({f} {} {} {})", t(0), t(1), t(2)), a[0].1.clone())
            }
            "ld64" | "st64" => return None,
            // machine arithmetic: wraps
            "bvadd" | "bvsub" | "bvmul" => {
                let w = w(0)?;
                let op = match f {
                    "bvadd" => "+",
                    "bvsub" => "-",
                    _ => "*",
                };
                let mut acc = t(0);
                for x in &a[1..] {
                    acc = format!("({op} {acc} {})", x.0);
                }
                (wrap(&acc, w), Sort::Bv(w))
            }
            "bvneg" => {
                let w = w(0)?;
                (wrap(&format!("(- {})", t(0)), w), Sort::Bv(w))
            }
            "bvslt" | "bvsle" | "bvsgt" | "bvsge" => {
                let op = match f {
                    "bvslt" => "<",
                    "bvsle" => "<=",
                    "bvsgt" => ">",
                    _ => ">=",
                };
                let w = w(0)?;
                let (x, y) = if signed_rep(w) {
                    (t(0), t(1))
                } else {
                    (
                        format!(
                            "(ite (>= {} {}) (- {} {}) {})",
                            t(0),
                            pow2(w - 1),
                            t(0),
                            pow2(w),
                            t(0)
                        ),
                        format!(
                            "(ite (>= {} {}) (- {} {}) {})",
                            t(1),
                            pow2(w - 1),
                            t(1),
                            pow2(w),
                            t(1)
                        ),
                    )
                };
                (format!("({op} {x} {y})"), Sort::Bool)
            }
            "bvult" | "bvule" | "bvugt" | "bvuge" => {
                let op = match f {
                    "bvult" => "<",
                    "bvule" => "<=",
                    "bvugt" => ">",
                    _ => ">=",
                };
                let w = w(0)?;
                (
                    format!("({op} {} {})", unsigned(&t(0), w), unsigned(&t(1), w)),
                    Sort::Bool,
                )
            }
            "bvand" => {
                let w = w(0)?;
                let mask = |i: usize| {
                    self.literal(&l[i + 1])
                        .filter(|(v, _)| *v >= 0 && (v + 1).count_ones() == 1)
                };
                let (x, m) = match (mask(1), mask(0)) {
                    (Some((m, _)), _) => (t(0), m),
                    (_, Some((m, _))) => (t(1), m),
                    _ => return None,
                };
                (
                    from_unsigned(&format!("(mod {} {})", unsigned(&x, w), m + 1), w),
                    Sort::Bv(w),
                )
            }
            "bvshl" | "bvashr" | "bvlshr" => {
                let w = w(0)?;
                let (c, _) = self.literal(&l[2])?;
                let c = (c as u32) % w;
                let k = pow2(c);
                let r = match f {
                    "bvshl" => wrap(&format!("(* {} {k})", t(0)), w),
                    "bvashr" => format!("(div {} {k})", t(0)),
                    _ => from_unsigned(&format!("(div {} {k})", unsigned(&t(0), w)), w),
                };
                (r, Sort::Bv(w))
            }
            "bvudiv" | "bvurem" => {
                let w = w(0)?;
                let (x, y) = (unsigned(&t(0), w), unsigned(&t(1), w));
                let op = if f == "bvudiv" { "div" } else { "mod" };
                (from_unsigned(&format!("({op} {x} {y})"), w), Sort::Bv(w))
            }
            "bvsdiv" | "bvsrem" => {
                let w = w(0)?;
                let (x, y) = (t(0), t(1));
                // truncating division
                let q = format!(
                    "(ite (>= {x} 0) (ite (>= {y} 0) (div {x} {y}) (- (div {x} (- {y})))) (ite (>= {y} 0) (- (div (- {x}) {y})) (div (- {x}) (- {y}))))"
                );
                let r = if f == "bvsdiv" {
                    wrap(&q, w)
                } else {
                    format!("(- {x} (* {y} {q}))")
                };
                (r, Sort::Bv(w))
            }
            "concat" => {
                let (w0, w1) = (w(0)?, w(1)?);
                let n = w0 + w1;
                let z = format!(
                    "(+ (* {} {}) {})",
                    unsigned(&t(0), w0),
                    pow2(w1),
                    unsigned(&t(1), w1)
                );
                (from_unsigned(&z, n), Sort::Bv(n))
            }
            _ => {
                // a user function (define-fun-rec) or a defined constant
                let srt = self.fun_sort(f)?;
                (
                    format!(
                        "({f} {})",
                        a.iter().map(|x| x.0.clone()).collect::<Vec<_>>().join(" ")
                    ),
                    srt,
                )
            }
        })
    }
}

/// The integer version of a query from vc.rs, if it has one.
pub fn translate(smt: &str) -> Option<String> {
    let cmds = parse(smt)?;
    let mut tr = Tr {
        consts: vec![],
        funs: vec![],
    };
    let mut out = String::new();
    for c in &cmds {
        let Sx::List(l) = c else { return None };
        let Some(Sx::Atom(head)) = l.first() else {
            return None;
        };
        match head.as_str() {
            "set-option" | "check-sat" => {
                out.push_str(&show(c));
                out.push('\n');
                if head == "set-option"
                    && matches!(l.get(1), Some(Sx::Atom(o)) if o == ":produce-models")
                {
                    out.push_str(INT_PREAMBLE);
                }
            }
            "declare-const" => {
                let Sx::Atom(n) = &l[1] else { return None };
                let srt = sort_of(&l[2])?;
                let _ = writeln!(out, "(declare-const {n} {})", int_sort(&srt));
                if let Sort::Bv(w) = srt {
                    let _ = writeln!(out, "(assert {})", range(n, w));
                }
                tr.consts.push((n.clone(), srt));
            }
            "define-fun" | "define-fun-rec" => {
                let Sx::Atom(n) = &l[1] else { return None };
                if REPLACED.contains(&n.as_str()) || spec_op(n).is_some() {
                    continue;
                }
                let Sx::List(params) = &l[2] else { return None };
                let res = sort_of(&l[3])?;
                let mut ps = vec![];
                for p in params {
                    let Sx::List(p) = p else { return None };
                    let Sx::Atom(pn) = &p[0] else { return None };
                    let ps_sort = sort_of(&p[1])?;
                    ps.push(format!("({pn} {})", int_sort(&ps_sort)));
                    tr.consts.push((pn.clone(), ps_sort));
                }
                if head == "define-fun-rec" {
                    tr.funs.push((n.clone(), res.clone()));
                }
                let body = tr.term(&l[4]);
                for _ in params {
                    tr.consts.pop();
                }
                let (body, _) = body?;
                if params.is_empty() {
                    tr.consts.push((n.clone(), res.clone()));
                } else if head != "define-fun-rec" {
                    tr.funs.push((n.clone(), res.clone()));
                }
                let _ = writeln!(
                    out,
                    "({head} {n} ({}) {} {body})",
                    ps.join(" "),
                    int_sort(&res)
                );
            }
            "assert" => {
                let (t, _) = tr.term(&l[1])?;
                let _ = writeln!(out, "(assert {t})");
            }
            "get-value" => {
                let Sx::List(ts) = &l[1] else { return None };
                let mut xs = vec![];
                for t in ts {
                    xs.push(tr.term(t)?.0);
                }
                let _ = writeln!(out, "(get-value ({}))", xs.join(" "));
            }
            _ => return None,
        }
    }
    Some(out)
}
