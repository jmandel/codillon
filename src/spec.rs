// Refinement specifications for Codillon: the predicate language, spec lines,
// erasure of header sugar, and a host-side evaluator.
//
// Spec lines are whole editor lines written as WebAssembly custom annotations:
//   (@requires P)  (@ensures P)  (@invariant P)  (@decreases e)  (@assert P)  (@assume P)
//   (@define name($a, $b) = e, NAME = e, ...)
//   (@ghost global $M (map i32 i32))   (@ghost local $j i32)   (@set $j := e)   (@run 10 20)
// Header sugar refines a declared value type:
//   (param $n (i32 | P))   (result $r (i32 | P))   (local $x (i32 | P))
// Erasure replaces `(T | P)` by `T` and drops result names, so the Wasm that Codillon
// compiles is exactly the module without specs, with the same lines.
//
// Predicates range over mathematical integers (no wraparound). An i32 name denotes its
// signed value; u(e) reads it unsigned. `/` and `%` are Euclidean. Names of program
// values are written with `$` (params, locals, named results, globals, ghosts, binders);
// bare names refer to `@define`d functions and constants, and to builtins.

use std::{collections::BTreeMap, fmt, rc::Rc};

// ---------------------------------------------------------------------------------------
// Syntax tree

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl CmpOp {
    fn src(&self) -> &'static str {
        match self {
            CmpOp::Eq => "==",
            CmpOp::Ne => "!=",
            CmpOp::Lt => "<",
            CmpOp::Le => "<=",
            CmpOp::Gt => ">",
            CmpOp::Ge => ">=",
        }
    }

    // typeset form, used in commentary
    fn pretty(&self) -> &'static str {
        match self {
            CmpOp::Eq => "==",
            CmpOp::Ne => "\u{2260}",
            CmpOp::Lt => "<",
            CmpOp::Le => "\u{2264}",
            CmpOp::Gt => ">",
            CmpOp::Ge => "\u{2265}",
        }
    }

    fn holds(&self, a: &Val, b: &Val) -> Result<bool, EvalError> {
        match (a, b) {
            (Val::Int(x), Val::Int(y)) => Ok(match self {
                CmpOp::Eq => x == y,
                CmpOp::Ne => x != y,
                CmpOp::Lt => x < y,
                CmpOp::Le => x <= y,
                CmpOp::Gt => x > y,
                CmpOp::Ge => x >= y,
            }),
            (Val::Bool(x), Val::Bool(y)) => match self {
                CmpOp::Eq => Ok(x == y),
                CmpOp::Ne => Ok(x != y),
                _ => Err(EvalError::new("cannot order truth values")),
            },
            (Val::Map(x), Val::Map(y)) => match self {
                CmpOp::Eq => Ok(x == y),
                CmpOp::Ne => Ok(x != y),
                _ => Err(EvalError::new("cannot order maps")),
            },
            _ => Err(EvalError::new("comparison of a number with a truth value")),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
    BitXor,
    Shl,
    Shr,
    And,
    Or,
    Implies,
}

impl BinOp {
    fn src(&self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Rem => "%",
            BinOp::BitAnd => "&",
            BinOp::BitXor => "^",
            BinOp::Shl => "<<",
            BinOp::Shr => ">>",
            BinOp::And => "&&",
            BinOp::Or => "||",
            BinOp::Implies => "==>",
        }
    }

    // binding strength (higher binds tighter)
    fn prec(&self) -> u8 {
        match self {
            BinOp::Implies => 1,
            BinOp::Or => 2,
            BinOp::And => 3,
            BinOp::BitXor => 5,
            BinOp::BitAnd => 6,
            BinOp::Shl | BinOp::Shr => 7,
            BinOp::Add | BinOp::Sub => 8,
            BinOp::Mul | BinOp::Div | BinOp::Rem => 9,
        }
    }
}
const PREC_TERNARY: u8 = 0;
const PREC_CMP: u8 = 4;
const PREC_UNARY: u8 = 10;
const PREC_ATOM: u8 = 11;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuantKind {
    Forall,
    Exists,
    Count,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Domain {
    Range(Box<Expr>, Box<Expr>), // half-open lo..hi
    MapKeys(Box<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Int(i128),
    Bool(bool),
    Var(String),  // `$name`, stored without the `$`
    Name(String), // bare identifier: a define, a define parameter, or a binder
    Neg(Box<Expr>),
    Not(Box<Expr>),
    Bin(BinOp, Box<Expr>, Box<Expr>),
    Chain(Vec<Expr>, Vec<CmpOp>), // a <= b < c
    Ite(Box<Expr>, Box<Expr>, Box<Expr>),
    Call(String, Vec<Expr>),
    Quant(QuantKind, String, Domain, Box<Expr>),
    Index(Box<Expr>, Box<Expr>),             // M[k]
    Update(Box<Expr>, Box<Expr>, Box<Expr>), // M[k -> v]
    InSet(Box<Expr>, Vec<Expr>),             // e in {a, b}
    InMap(Box<Expr>, Box<Expr>),             // k in M
    MapEmpty,
}

impl Expr {
    fn prec(&self) -> u8 {
        match self {
            Expr::Bin(op, ..) => op.prec(),
            Expr::Chain(..) | Expr::InSet(..) | Expr::InMap(..) => PREC_CMP,
            Expr::Ite(..) | Expr::Quant(..) => PREC_TERNARY,
            Expr::Neg(_) | Expr::Not(_) => PREC_UNARY,
            Expr::Int(i) if *i < 0 => PREC_UNARY,
            _ => PREC_ATOM,
        }
    }

    /// Every `$name` mentioned (outside of binders that shadow it), in order.
    pub fn vars(&self, out: &mut Vec<String>) {
        self.walk(&mut |e| {
            if let Expr::Var(v) = e
                && !out.contains(v)
            {
                out.push(v.clone());
            }
        });
    }

    /// Every bare name called or mentioned.
    pub fn names(&self, out: &mut Vec<String>) {
        self.walk(&mut |e| match e {
            Expr::Name(n) | Expr::Call(n, _) if !out.contains(n) => out.push(n.clone()),
            _ => {}
        });
    }

    pub fn walk(&self, f: &mut impl FnMut(&Expr)) {
        f(self);
        match self {
            Expr::Int(_) | Expr::Bool(_) | Expr::Var(_) | Expr::Name(_) | Expr::MapEmpty => {}
            Expr::Neg(a) | Expr::Not(a) => a.walk(f),
            Expr::Bin(_, a, b) | Expr::Index(a, b) | Expr::InMap(a, b) => {
                a.walk(f);
                b.walk(f)
            }
            Expr::Chain(es, _) | Expr::Call(_, es) => es.iter().for_each(|e| e.walk(f)),
            Expr::Ite(a, b, c) | Expr::Update(a, b, c) => {
                a.walk(f);
                b.walk(f);
                c.walk(f)
            }
            Expr::Quant(_, _, dom, body) => {
                match dom {
                    Domain::Range(lo, hi) => {
                        lo.walk(f);
                        hi.walk(f)
                    }
                    Domain::MapKeys(m) => m.walk(f),
                }
                body.walk(f)
            }
            Expr::InSet(a, es) => {
                a.walk(f);
                es.iter().for_each(|e| e.walk(f))
            }
        }
    }

    pub fn mentions_old(&self) -> bool {
        let mut found = false;
        self.walk(&mut |e| {
            if matches!(e, Expr::Call(n, _) if n == "old") {
                found = true
            }
        });
        found
    }

    pub fn is_literally_true(&self) -> bool {
        matches!(self, Expr::Bool(true))
    }
}

fn fmt_child(f: &mut fmt::Formatter, e: &Expr, min_prec: u8) -> fmt::Result {
    if e.prec() < min_prec {
        write!(f, "({e})")
    } else {
        write!(f, "{e}")
    }
}

fn fmt_name(n: &str) -> String {
    n.to_string()
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Int(i) => write!(f, "{i}"),
            Expr::Bool(b) => write!(f, "{b}"),
            Expr::Var(v) => write!(f, "${v}"),
            Expr::Name(n) => write!(f, "{}", fmt_name(n)),
            Expr::MapEmpty => write!(f, "map.empty"),
            Expr::Neg(a) => {
                write!(f, "-")?;
                fmt_child(f, a, PREC_UNARY)
            }
            Expr::Not(a) => {
                write!(f, "!")?;
                fmt_child(f, a, PREC_UNARY)
            }
            Expr::Bin(op, a, b) => {
                let p = op.prec();
                // left-associative except ==> (right-associative)
                let (lp, rp) = if *op == BinOp::Implies {
                    (p + 1, p)
                } else {
                    (p, p + 1)
                };
                fmt_child(f, a, lp)?;
                write!(f, " {} ", op.src())?;
                fmt_child(f, b, rp)
            }
            Expr::Chain(es, ops) => {
                fmt_child(f, &es[0], PREC_CMP + 1)?;
                for (op, e) in ops.iter().zip(&es[1..]) {
                    write!(f, " {} ", op.src())?;
                    fmt_child(f, e, PREC_CMP + 1)?;
                }
                Ok(())
            }
            Expr::Ite(c, a, b) => {
                fmt_child(f, c, PREC_TERNARY + 1)?;
                write!(f, " ? ")?;
                fmt_child(f, a, PREC_TERNARY + 1)?;
                write!(f, " : ")?;
                fmt_child(f, b, PREC_TERNARY)
            }
            Expr::Call(n, args) => {
                write!(f, "{}(", fmt_name(n))?;
                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{a}")?;
                }
                write!(f, ")")
            }
            Expr::Quant(k, x, dom, body) => {
                let kw = match k {
                    QuantKind::Forall => "forall",
                    QuantKind::Exists => "exists",
                    QuantKind::Count => "count",
                };
                write!(f, "{kw} ${x} in ")?;
                match dom {
                    Domain::Range(lo, hi) => {
                        fmt_child(f, lo, PREC_UNARY)?;
                        write!(f, "..")?;
                        fmt_child(f, hi, PREC_UNARY)?;
                    }
                    Domain::MapKeys(m) => fmt_child(f, m, PREC_ATOM)?,
                }
                write!(f, ": {body}")
            }
            Expr::Index(m, k) => {
                fmt_child(f, m, PREC_ATOM)?;
                write!(f, "[{k}]")
            }
            Expr::Update(m, k, v) => {
                fmt_child(f, m, PREC_ATOM)?;
                write!(f, "[{k} -> {v}]")
            }
            Expr::InSet(a, es) => {
                fmt_child(f, a, PREC_CMP + 1)?;
                write!(f, " in {{")?;
                for (i, e) in es.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, "}}")
            }
            Expr::InMap(k, m) => {
                fmt_child(f, k, PREC_CMP + 1)?;
                write!(f, " in ")?;
                fmt_child(f, m, PREC_CMP + 1)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Define {
    pub name: String,
    pub params: Vec<String>,
    pub body: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GhostScope {
    Global,
    Local,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GhostType {
    Scalar(String), // i32 / i64 / int
    Map,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Annotation {
    Requires(Expr),
    Ensures(Expr),
    Invariant(Expr),
    Decreases(Expr),
    Assert(Expr),
    Assume(Expr),
    Define(Vec<Define>),
    Ghost {
        scope: GhostScope,
        name: String,
        ty: GhostType,
    },
    Set {
        name: String,
        value: Expr,
    },
    Run(Vec<i128>),
}

impl Annotation {
    pub fn keyword(&self) -> &'static str {
        match self {
            Annotation::Requires(_) => "requires",
            Annotation::Ensures(_) => "ensures",
            Annotation::Invariant(_) => "invariant",
            Annotation::Decreases(_) => "decreases",
            Annotation::Assert(_) => "assert",
            Annotation::Assume(_) => "assume",
            Annotation::Define(_) => "define",
            Annotation::Ghost { .. } => "ghost",
            Annotation::Set { .. } => "set",
            Annotation::Run(_) => "run",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclKind {
    Param,
    Result,
    Local,
}

/// One declared value in a `(param …)`, `(result …)` or `(local …)` group.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decl {
    pub kind: DeclKind,
    pub name: Option<String>, // without `$`
    pub ty: String,           // i32, i64, f32, f64
    pub refinement: Option<Expr>,
}

/// The spec content of one editor line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LineSpec {
    /// The whole line is an annotation; it erases to nothing.
    Annotation(Annotation),
    /// A header or local line: its declarations, and (if it has refinements or named
    /// results) the plain WebAssembly text that is compiled instead.
    Header {
        erased: Option<String>,
        decls: Vec<Decl>,
    },
}

impl LineSpec {
    pub fn erased(&self) -> Option<&str> {
        match self {
            LineSpec::Header { erased, .. } => erased.as_deref(),
            LineSpec::Annotation(_) => None,
        }
    }

    pub fn decls(&self) -> &[Decl] {
        match self {
            LineSpec::Header { decls, .. } => decls,
            LineSpec::Annotation(_) => &[],
        }
    }

    pub fn has_refinement(&self) -> bool {
        self.decls().iter().any(|d| d.refinement.is_some())
    }
}

// ---------------------------------------------------------------------------------------
// Lexer

#[derive(Debug, Clone, PartialEq)]
enum Tok {
    Int(i128),
    Var(String),
    Ident(String),
    At(String), // `@keyword`
    P(&'static str),
}

impl fmt::Display for Tok {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Tok::Int(i) => write!(f, "{i}"),
            Tok::Var(v) => write!(f, "${v}"),
            Tok::Ident(n) => write!(f, "{n}"),
            Tok::At(n) => write!(f, "@{n}"),
            Tok::P(p) => write!(f, "{p}"),
        }
    }
}

const PUNCT: &[&str] = &[
    "==>", "..", "==", "!=", "<=", ">=", "&&", "||", "<<", ">>", "->", ":=", "(", ")", "[", "]",
    "{", "}", ",", ":", "?", "+", "-", "*", "/", "%", "&", "^", "<", ">", "!", "=", "|", ".",
];

fn is_name_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

fn lex(s: &str) -> Result<Vec<Tok>, String> {
    let mut toks = Vec::new();
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        if c.is_ascii_digit() {
            let start = i;
            if c == '0' && i + 1 < chars.len() && (chars[i + 1] == 'x' || chars[i + 1] == 'X') {
                i += 2;
                while i < chars.len() && (chars[i].is_ascii_hexdigit() || chars[i] == '_') {
                    i += 1;
                }
                let digits: String = chars[start + 2..i].iter().filter(|c| **c != '_').collect();
                let v = i128::from_str_radix(&digits, 16).map_err(|_| "bad hex number")?;
                toks.push(Tok::Int(v));
            } else {
                while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '_') {
                    i += 1;
                }
                let digits: String = chars[start..i].iter().filter(|c| **c != '_').collect();
                let v = digits.parse::<i128>().map_err(|_| "number too large")?;
                toks.push(Tok::Int(v));
            }
            if i < chars.len() && is_name_char(chars[i]) {
                return Err(format!("unexpected ‘{}’ after number", chars[i]));
            }
            continue;
        }
        if c == '$' || c == '@' {
            let start = i + 1;
            i += 1;
            while i < chars.len() && is_name_char(chars[i]) {
                i += 1;
            }
            if i == start {
                return Err(format!("expected a name after ‘{c}’"));
            }
            let name: String = chars[start..i].iter().collect();
            toks.push(if c == '$' {
                Tok::Var(name)
            } else {
                Tok::At(name)
            });
            continue;
        }
        if c.is_ascii_alphabetic() || c == '_' {
            let start = i;
            while i < chars.len()
                && (is_name_char(chars[i])
                    || (chars[i] == '.'
                        && i + 1 < chars.len()
                        && chars[i + 1].is_ascii_alphabetic()))
            {
                i += 1;
            }
            toks.push(Tok::Ident(chars[start..i].iter().collect()));
            continue;
        }
        let rest: String = chars[i..chars.len().min(i + 3)].iter().collect();
        match PUNCT.iter().find(|p| rest.starts_with(**p)) {
            Some(p) => {
                toks.push(Tok::P(p));
                i += p.chars().count();
            }
            None => return Err(format!("unexpected character ‘{c}’")),
        }
    }
    Ok(toks)
}

// ---------------------------------------------------------------------------------------
// Parser

struct Parser {
    toks: Vec<Tok>,
    pos: usize,
}

type PResult<T> = Result<T, String>;

impl Parser {
    fn new(toks: Vec<Tok>) -> Self {
        Self { toks, pos: 0 }
    }

    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }

    fn peek_at(&self, n: usize) -> Option<&Tok> {
        self.toks.get(self.pos + n)
    }

    fn is_p(&self, p: &str) -> bool {
        matches!(self.peek(), Some(Tok::P(q)) if *q == p)
    }

    fn is_ident(&self, kw: &str) -> bool {
        matches!(self.peek(), Some(Tok::Ident(n)) if n == kw)
    }

    fn eat_p(&mut self, p: &str) -> bool {
        if self.is_p(p) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn eat_ident(&mut self, kw: &str) -> bool {
        if self.is_ident(kw) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn describe_next(&self) -> String {
        match self.peek() {
            Some(t) => format!("‘{t}’"),
            None => "end of line".to_string(),
        }
    }

    fn expect_p(&mut self, p: &str) -> PResult<()> {
        if self.eat_p(p) {
            Ok(())
        } else {
            Err(format!("expected ‘{p}’, found {}", self.describe_next()))
        }
    }

    fn at_end(&self) -> bool {
        self.pos >= self.toks.len()
    }

    fn binder(&mut self) -> PResult<String> {
        match self.peek().cloned() {
            Some(Tok::Var(v)) | Some(Tok::Ident(v)) => {
                self.pos += 1;
                Ok(v)
            }
            _ => Err(format!("expected a name, found {}", self.describe_next())),
        }
    }

    // expr := ternary
    fn expr(&mut self) -> PResult<Expr> {
        let c = self.implies()?;
        if self.eat_p("?") {
            let a = self.expr()?;
            self.expect_p(":")?;
            let b = self.expr()?;
            return Ok(Expr::Ite(Box::new(c), Box::new(a), Box::new(b)));
        }
        Ok(c)
    }

    fn implies(&mut self) -> PResult<Expr> {
        let a = self.or()?;
        if self.eat_p("==>") {
            let b = self.implies()?;
            return Ok(Expr::Bin(BinOp::Implies, Box::new(a), Box::new(b)));
        }
        Ok(a)
    }

    fn or(&mut self) -> PResult<Expr> {
        let mut a = self.and()?;
        while self.eat_p("||") {
            let b = self.and()?;
            a = Expr::Bin(BinOp::Or, Box::new(a), Box::new(b));
        }
        Ok(a)
    }

    fn and(&mut self) -> PResult<Expr> {
        let mut a = self.cmp()?;
        while self.eat_p("&&") {
            let b = self.cmp()?;
            a = Expr::Bin(BinOp::And, Box::new(a), Box::new(b));
        }
        Ok(a)
    }

    fn cmp_op(&self) -> Option<CmpOp> {
        match self.peek() {
            Some(Tok::P("==")) => Some(CmpOp::Eq),
            Some(Tok::P("!=")) => Some(CmpOp::Ne),
            Some(Tok::P("<")) => Some(CmpOp::Lt),
            Some(Tok::P("<=")) => Some(CmpOp::Le),
            Some(Tok::P(">")) => Some(CmpOp::Gt),
            Some(Tok::P(">=")) => Some(CmpOp::Ge),
            _ => None,
        }
    }

    fn cmp(&mut self) -> PResult<Expr> {
        let first = self.bitxor()?;
        if self.eat_ident("in") {
            if self.eat_p("{") {
                let mut items = vec![];
                if !self.is_p("}") {
                    loop {
                        items.push(self.expr()?);
                        if !self.eat_p(",") {
                            break;
                        }
                    }
                }
                self.expect_p("}")?;
                return Ok(Expr::InSet(Box::new(first), items));
            }
            let m = self.bitxor()?;
            return Ok(Expr::InMap(Box::new(first), Box::new(m)));
        }
        let mut es = vec![first];
        let mut ops = vec![];
        while let Some(op) = self.cmp_op() {
            self.pos += 1;
            ops.push(op);
            es.push(self.bitxor()?);
        }
        if ops.is_empty() {
            Ok(es.pop().unwrap())
        } else {
            Ok(Expr::Chain(es, ops))
        }
    }

    fn bitxor(&mut self) -> PResult<Expr> {
        let mut a = self.bitand()?;
        while self.eat_p("^") {
            let b = self.bitand()?;
            a = Expr::Bin(BinOp::BitXor, Box::new(a), Box::new(b));
        }
        Ok(a)
    }

    fn bitand(&mut self) -> PResult<Expr> {
        let mut a = self.shift()?;
        while self.eat_p("&") {
            let b = self.shift()?;
            a = Expr::Bin(BinOp::BitAnd, Box::new(a), Box::new(b));
        }
        Ok(a)
    }

    fn shift(&mut self) -> PResult<Expr> {
        let mut a = self.add()?;
        loop {
            let op = if self.eat_p("<<") {
                BinOp::Shl
            } else if self.eat_p(">>") {
                BinOp::Shr
            } else {
                break;
            };
            let b = self.add()?;
            a = Expr::Bin(op, Box::new(a), Box::new(b));
        }
        Ok(a)
    }

    fn add(&mut self) -> PResult<Expr> {
        let mut a = self.mul()?;
        loop {
            let op = if self.eat_p("+") {
                BinOp::Add
            } else if self.eat_p("-") {
                BinOp::Sub
            } else {
                break;
            };
            let b = self.mul()?;
            a = Expr::Bin(op, Box::new(a), Box::new(b));
        }
        Ok(a)
    }

    fn mul(&mut self) -> PResult<Expr> {
        let mut a = self.unary()?;
        loop {
            let op = if self.eat_p("*") {
                BinOp::Mul
            } else if self.eat_p("/") {
                BinOp::Div
            } else if self.eat_p("%") {
                BinOp::Rem
            } else {
                break;
            };
            let b = self.unary()?;
            a = Expr::Bin(op, Box::new(a), Box::new(b));
        }
        Ok(a)
    }

    fn unary(&mut self) -> PResult<Expr> {
        if self.eat_p("-") {
            let a = self.unary()?;
            return Ok(match a {
                Expr::Int(i) => Expr::Int(-i),
                a => Expr::Neg(Box::new(a)),
            });
        }
        if self.eat_p("!") {
            let a = self.unary()?;
            return Ok(Expr::Not(Box::new(a)));
        }
        self.postfix()
    }

    fn postfix(&mut self) -> PResult<Expr> {
        let mut a = self.primary()?;
        while self.eat_p("[") {
            let k = self.expr()?;
            if self.eat_p("->") {
                let v = self.expr()?;
                self.expect_p("]")?;
                a = Expr::Update(Box::new(a), Box::new(k), Box::new(v));
            } else {
                self.expect_p("]")?;
                a = Expr::Index(Box::new(a), Box::new(k));
            }
        }
        Ok(a)
    }

    fn quantifier(&mut self, kind: QuantKind) -> PResult<Expr> {
        let x = self.binder()?;
        if !self.eat_ident("in") {
            return Err(format!(
                "expected ‘in’ after the bound name, found {}",
                self.describe_next()
            ));
        }
        let lo = self.add()?;
        let dom = if self.eat_p("..") {
            let hi = self.add()?;
            Domain::Range(Box::new(lo), Box::new(hi))
        } else {
            Domain::MapKeys(Box::new(lo))
        };
        if !(self.eat_p(":") || self.eat_p(".")) {
            return Err(format!(
                "expected ‘:’ before the quantifier body, found {}",
                self.describe_next()
            ));
        }
        let body = self.expr()?;
        Ok(Expr::Quant(kind, x, dom, Box::new(body)))
    }

    fn args(&mut self) -> PResult<Vec<Expr>> {
        let mut args = vec![];
        if !self.is_p(")") {
            loop {
                args.push(self.expr()?);
                if !self.eat_p(",") {
                    break;
                }
            }
        }
        self.expect_p(")")?;
        Ok(args)
    }

    fn primary(&mut self) -> PResult<Expr> {
        let Some(tok) = self.peek().cloned() else {
            return Err("the predicate ends too early".to_string());
        };
        self.pos += 1;
        match tok {
            Tok::Int(i) => Ok(Expr::Int(i)),
            Tok::Var(v) => Ok(Expr::Var(v)),
            Tok::P("(") => {
                let e = self.expr()?;
                self.expect_p(")")?;
                Ok(e)
            }
            Tok::Ident(n) => match n.as_str() {
                "true" => Ok(Expr::Bool(true)),
                "false" => Ok(Expr::Bool(false)),
                "forall" => self.quantifier(QuantKind::Forall),
                "exists" => self.quantifier(QuantKind::Exists),
                "count" => self.quantifier(QuantKind::Count),
                "if" => {
                    let c = self.expr()?;
                    if !self.eat_ident("then") {
                        return Err(format!("expected ‘then’, found {}", self.describe_next()));
                    }
                    let a = self.expr()?;
                    if !self.eat_ident("else") {
                        return Err(format!("expected ‘else’, found {}", self.describe_next()));
                    }
                    let b = self.expr()?;
                    Ok(Expr::Ite(Box::new(c), Box::new(a), Box::new(b)))
                }
                "map.empty" => Ok(Expr::MapEmpty),
                "in" | "then" | "else" => Err(format!("unexpected ‘{n}’")),
                _ => {
                    if self.eat_p("(") {
                        Ok(Expr::Call(n, self.args()?))
                    } else {
                        Ok(Expr::Name(n))
                    }
                }
            },
            t => Err(format!("expected a value, found ‘{t}’")),
        }
    }
}

/// Parse a complete predicate or expression.
pub fn parse_expr(s: &str) -> Result<Expr, String> {
    let toks = lex(s)?;
    if toks.is_empty() {
        return Err("empty predicate".to_string());
    }
    let mut p = Parser::new(toks);
    let e = p.expr()?;
    if !p.at_end() {
        return Err(format!("unexpected {} in predicate", p.describe_next()));
    }
    Ok(e)
}

fn parse_annotation_body(kw: &str, p: &mut Parser) -> PResult<Annotation> {
    Ok(match kw {
        "requires" => Annotation::Requires(p.expr()?),
        "ensures" => Annotation::Ensures(p.expr()?),
        "invariant" => Annotation::Invariant(p.expr()?),
        "decreases" => Annotation::Decreases(p.expr()?),
        "assert" => Annotation::Assert(p.expr()?),
        "assume" => Annotation::Assume(p.expr()?),
        "define" => {
            let mut defs = vec![];
            loop {
                let name = match p.peek().cloned() {
                    Some(Tok::Ident(n)) => {
                        p.pos += 1;
                        n
                    }
                    Some(Tok::Var(_)) => {
                        return Err("a defined name is written without ‘$’".to_string());
                    }
                    _ => return Err(format!("expected a name, found {}", p.describe_next())),
                };
                let mut params = vec![];
                if p.eat_p("(") {
                    if !p.is_p(")") {
                        loop {
                            params.push(p.binder()?);
                            if !p.eat_p(",") {
                                break;
                            }
                        }
                    }
                    p.expect_p(")")?;
                }
                p.expect_p("=")?;
                let body = p.expr()?;
                defs.push(Define { name, params, body });
                if !p.eat_p(",") {
                    break;
                }
            }
            Annotation::Define(defs)
        }
        "ghost" => {
            let scope = if p.eat_ident("global") {
                GhostScope::Global
            } else if p.eat_ident("local") {
                GhostScope::Local
            } else {
                return Err("expected ‘global’ or ‘local’ after @ghost".to_string());
            };
            let name = match p.peek().cloned() {
                Some(Tok::Var(v)) => {
                    p.pos += 1;
                    v
                }
                _ => return Err("expected a $name for the ghost".to_string()),
            };
            let ty = if p.eat_p("(") {
                if !(p.eat_ident("map") || p.eat_ident("Map")) {
                    return Err("expected a map type, like (map i32 i32)".to_string());
                }
                while !p.is_p(")") && !p.at_end() {
                    p.pos += 1;
                }
                p.expect_p(")")?;
                GhostType::Map
            } else {
                match p.peek().cloned() {
                    Some(Tok::Ident(t)) if ["i32", "i64", "int"].contains(&t.as_str()) => {
                        p.pos += 1;
                        GhostType::Scalar(t)
                    }
                    _ => return Err("expected a ghost type (i32, i64, int or a map)".to_string()),
                }
            };
            Annotation::Ghost { scope, name, ty }
        }
        "set" => {
            let name = match p.peek().cloned() {
                Some(Tok::Var(v)) => {
                    p.pos += 1;
                    v
                }
                _ => return Err("expected a $name to set".to_string()),
            };
            p.expect_p(":=")?;
            Annotation::Set {
                name,
                value: p.expr()?,
            }
        }
        "run" => {
            let mut args = vec![];
            while let Some(tok) = p.peek().cloned() {
                match tok {
                    Tok::Int(i) => {
                        p.pos += 1;
                        args.push(i)
                    }
                    Tok::P("-") => match p.peek_at(1).cloned() {
                        Some(Tok::Int(i)) => {
                            p.pos += 2;
                            args.push(-i)
                        }
                        _ => return Err("expected a number".to_string()),
                    },
                    _ => break,
                }
            }
            Annotation::Run(args)
        }
        other => return Err(format!("unknown annotation ‘@{other}’")),
    })
}

/// Parse a whole-line annotation such as `(@invariant 0 <= $r)`.
pub fn parse_annotation(line: &str) -> Result<Annotation, String> {
    let toks = lex(line)?;
    let mut p = Parser::new(toks);
    p.expect_p("(")?;
    let kw = match p.peek().cloned() {
        Some(Tok::At(kw)) => {
            p.pos += 1;
            kw
        }
        _ => return Err("expected an annotation like (@assert …)".to_string()),
    };
    let ann = parse_annotation_body(&kw, &mut p)?;
    if !p.eat_p(")") {
        return Err(format!(
            "expected ‘)’ to close (@{kw} …), found {}",
            p.describe_next()
        ));
    }
    if !p.at_end() {
        return Err("one annotation per line".to_string());
    }
    Ok(ann)
}

// ---------------------------------------------------------------------------------------
// Line scanning and erasure

pub enum ScanResult {
    Plain,          // no spec content: the line is ordinary WebAssembly
    Spec(LineSpec), // spec content (annotation line or refined header)
    Malformed(String),
}

/// Does this line start with `(@`? (Such lines are spec lines, never Wasm.)
pub fn is_annotation_line(s: &str) -> bool {
    let t = s.trim_start();
    t.strip_prefix('(')
        .map(|r| r.trim_start().starts_with('@'))
        .unwrap_or(false)
}

/// Classify one line (without its `;;` comment) and erase any header sugar.
pub fn scan_line(s: &str) -> ScanResult {
    if is_annotation_line(s) {
        return match parse_annotation(s) {
            Ok(a) => ScanResult::Spec(LineSpec::Annotation(a)),
            Err(e) => ScanResult::Malformed(e),
        };
    }
    if !(s.contains("param") || s.contains("result") || s.contains("local")) || !s.contains('(') {
        return ScanResult::Plain;
    }
    match scan_header(s) {
        Ok((erased, decls, changed)) => {
            if changed || !decls.is_empty() {
                ScanResult::Spec(LineSpec::Header {
                    erased: changed.then_some(erased),
                    decls,
                })
            } else {
                ScanResult::Plain
            }
        }
        // a bare `|` that is not a refinement is left for the WebAssembly parser to reject
        Err(_) if !s.contains('|') => ScanResult::Plain,
        Err(e) => ScanResult::Malformed(e),
    }
}

const VALTYPES: &[&str] = &["i32", "i64", "f32", "f64"];

/// Find `(param …)`, `(result …)` and `(local …)` groups in a header line, returning the
/// erased text, the declarations, and whether erasure changed anything.
pub fn scan_header(s: &str) -> Result<(String, Vec<Decl>, bool), String> {
    let b = s.as_bytes();
    let mut out = String::with_capacity(s.len());
    let mut decls = vec![];
    let mut changed = false;
    let mut i = 0;
    let mut copied = 0; // bytes of s copied to out so far

    // skip a string literal starting at b[i] == '"'
    fn skip_string(b: &[u8], mut i: usize) -> usize {
        i += 1;
        while i < b.len() {
            match b[i] {
                b'\\' => i += 2,
                b'"' => return i + 1,
                _ => i += 1,
            }
        }
        i
    }
    fn skip_ws(b: &[u8], mut i: usize) -> usize {
        while i < b.len() && (b[i] as char).is_whitespace() {
            i += 1;
        }
        i
    }
    fn word(b: &[u8], i: usize) -> (usize, &str) {
        let mut j = i;
        while j < b.len() && !(b[j] as char).is_whitespace() && b[j] != b'(' && b[j] != b')' {
            j += 1;
        }
        (j, std::str::from_utf8(&b[i..j]).unwrap_or(""))
    }
    // find the ')' matching the '(' at b[open]
    fn matching(b: &[u8], open: usize) -> Option<usize> {
        let mut depth = 0;
        let mut i = open;
        while i < b.len() {
            match b[i] {
                b'"' => {
                    i = skip_string(b, i);
                    continue;
                }
                b'(' => depth += 1,
                b')' => {
                    depth -= 1;
                    if depth == 0 {
                        return Some(i);
                    }
                }
                _ => {}
            }
            i += 1;
        }
        None
    }

    while i < b.len() {
        match b[i] {
            b'"' => {
                i = skip_string(b, i);
            }
            b'(' => {
                let j = skip_ws(b, i + 1);
                let (k, kw) = word(b, j);
                let kind = match kw {
                    "param" => Some(DeclKind::Param),
                    "result" => Some(DeclKind::Result),
                    "local" => Some(DeclKind::Local),
                    _ => None,
                };
                let Some(kind) = kind else {
                    i += 1;
                    continue;
                };
                let Some(close) = matching(b, i) else {
                    return Err(format!("unclosed ({kw} …)"));
                };
                // items between k and close
                let mut pos = k;
                let mut name: Option<String> = None;
                let mut group_decls = vec![];
                loop {
                    pos = skip_ws(b, pos);
                    if pos >= close {
                        break;
                    }
                    if b[pos] == b'$' {
                        let (e, w) = word(b, pos);
                        if name.is_some() || !group_decls.is_empty() {
                            return Err(format!("unexpected name {w} in ({kw} …)"));
                        }
                        name = Some(w[1..].to_string());
                        if kind == DeclKind::Result {
                            // named results are spec-only: erase the name
                            out.push_str(&s[copied..pos]);
                            copied = skip_ws(b, e);
                            changed = true;
                        }
                        pos = e;
                    } else if b[pos] == b'(' {
                        let Some(rclose) = matching(b, pos) else {
                            return Err("unclosed refinement".to_string());
                        };
                        let inner = &s[pos + 1..rclose];
                        let Some((ty, pred)) = inner.split_once('|') else {
                            return Err(format!(
                                "expected a refinement like (i32 | P) in ({kw} …)"
                            ));
                        };
                        let ty = ty.trim();
                        if !VALTYPES.contains(&ty) {
                            return Err(format!("cannot refine ‘{ty}’"));
                        }
                        let pred = parse_expr(pred.trim())?;
                        if name.is_none() {
                            return Err(format!(
                                "a refined {kw} needs a name: ({kw} $x ({ty} | …))"
                            ));
                        }
                        out.push_str(&s[copied..pos]);
                        out.push_str(ty);
                        copied = rclose + 1;
                        changed = true;
                        group_decls.push(Decl {
                            kind,
                            name: name.clone(),
                            ty: ty.to_string(),
                            refinement: Some(pred),
                        });
                        pos = rclose + 1;
                    } else {
                        let (e, w) = word(b, pos);
                        if e == pos {
                            pos += 1;
                            continue;
                        }
                        if VALTYPES.contains(&w) {
                            group_decls.push(Decl {
                                kind,
                                name: if group_decls.is_empty() {
                                    name.clone()
                                } else {
                                    None
                                },
                                ty: w.to_string(),
                                refinement: None,
                            });
                        }
                        pos = e;
                    }
                }
                if name.is_some() && group_decls.len() > 1 {
                    return Err(format!("a named {kw} declares one value"));
                }
                decls.extend(group_decls);
                i = close + 1;
            }
            _ => i += 1,
        }
    }
    out.push_str(&s[copied.min(s.len())..]);
    Ok((out, decls, changed))
}

// ---------------------------------------------------------------------------------------
// Values and evaluation

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Val {
    Int(i128),
    Bool(bool),
    Map(Rc<BTreeMap<i128, i128>>),
}

impl fmt::Display for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Val::Int(i) => write!(f, "{i}"),
            Val::Bool(b) => write!(f, "{b}"),
            Val::Map(m) => {
                write!(f, "{{")?;
                for (i, (k, v)) in m.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    if i >= 6 {
                        write!(f, "…")?;
                        break;
                    }
                    write!(f, "{k}\u{21a6}{v}")?;
                }
                write!(f, "}}")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvalError(pub String);

impl EvalError {
    fn new(s: impl Into<String>) -> Self {
        EvalError(s.into())
    }
}

type EResult<T> = Result<T, EvalError>;

/// What the evaluator needs from the program state at a checkpoint.
pub trait Env {
    /// Current value of a `$name` (param, local, named result, global, ghost).
    fn var(&self, name: &str) -> Option<Val>;
    /// Value of a `$name` at function entry (for `old(…)`).
    fn old_var(&self, name: &str) -> Option<Val> {
        self.var(name)
    }
    /// Bit width of a program value (for `u(…)`).
    fn width(&self, _name: &str) -> u32 {
        32
    }
    /// Read `bytes` bytes of linear memory at `addr` (little-endian, unsigned).
    fn load(&self, _addr: i128, _bytes: u32) -> EResult<u64> {
        Err(EvalError::new("memory is not available here"))
    }
    fn define(&self, name: &str) -> Option<&Define>;
}

// (each level of spec recursion costs several KB of native stack; keep well inside the 1 MB wasm stack)
const MAX_DEPTH: usize = if cfg!(debug_assertions) { 60 } else { 150 };
const MAX_RANGE: i128 = 1 << 16;

pub struct Evaluator<'a> {
    env: &'a dyn Env,
    scopes: Vec<(String, Val)>,
    in_old: bool,
    depth: usize,
}

fn wrap32(x: i128) -> i128 {
    x as u32 as i32 as i128
}

impl<'a> Evaluator<'a> {
    pub fn new(env: &'a dyn Env) -> Self {
        Self {
            env,
            scopes: vec![],
            in_old: false,
            depth: 0,
        }
    }

    fn bound(&self, name: &str) -> Option<Val> {
        self.scopes
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, v)| v.clone())
    }

    fn int(&mut self, e: &Expr) -> EResult<i128> {
        match self.eval(e)? {
            Val::Int(i) => Ok(i),
            Val::Bool(_) => Err(EvalError::new(format!(
                "{e} is a truth value, not a number"
            ))),
            Val::Map(_) => Err(EvalError::new(format!("{e} is a map, not a number"))),
        }
    }

    fn boolean(&mut self, e: &Expr) -> EResult<bool> {
        match self.eval(e)? {
            Val::Bool(b) => Ok(b),
            _ => Err(EvalError::new(format!("{e} is not a truth value"))),
        }
    }

    fn map(&mut self, e: &Expr) -> EResult<Rc<BTreeMap<i128, i128>>> {
        match self.eval(e)? {
            Val::Map(m) => Ok(m),
            _ => Err(EvalError::new(format!("{e} is not a map"))),
        }
    }

    fn lookup_var(&self, v: &str) -> EResult<Val> {
        if let Some(x) = self.bound(v) {
            return Ok(x);
        }
        let r = if self.in_old {
            self.env.old_var(v)
        } else {
            self.env.var(v)
        };
        r.ok_or_else(|| EvalError::new(format!("${v} has no value here")))
    }

    fn checked(x: Option<i128>) -> EResult<i128> {
        x.ok_or_else(|| EvalError::new("number too large to evaluate"))
    }

    pub fn eval(&mut self, e: &Expr) -> EResult<Val> {
        Ok(match e {
            Expr::Int(i) => Val::Int(*i),
            Expr::Bool(b) => Val::Bool(*b),
            Expr::MapEmpty => Val::Map(Rc::new(BTreeMap::new())),
            Expr::Var(v) => self.lookup_var(v)?,
            Expr::Name(n) => {
                if let Some(x) = self.bound(n) {
                    x
                } else if let Some(d) = self.env.define(n) {
                    if !d.params.is_empty() {
                        return Err(EvalError::new(format!("{n} needs arguments")));
                    }
                    self.call_define(&d.clone(), &[])?
                } else {
                    return Err(EvalError::new(format!("unknown name {n}")));
                }
            }
            Expr::Neg(a) => Val::Int(Self::checked(self.int(a)?.checked_neg())?),
            Expr::Not(a) => Val::Bool(!self.boolean(a)?),
            Expr::Bin(op, a, b) => match op {
                BinOp::And => Val::Bool(self.boolean(a)? && self.boolean(b)?),
                BinOp::Or => Val::Bool(self.boolean(a)? || self.boolean(b)?),
                BinOp::Implies => Val::Bool(!self.boolean(a)? || self.boolean(b)?),
                _ => {
                    let x = self.int(a)?;
                    let y = self.int(b)?;
                    Val::Int(match op {
                        BinOp::Add => Self::checked(x.checked_add(y))?,
                        BinOp::Sub => Self::checked(x.checked_sub(y))?,
                        BinOp::Mul => Self::checked(x.checked_mul(y))?,
                        BinOp::Div | BinOp::Rem if y == 0 => {
                            return Err(EvalError::new(format!("{e}: division by zero")));
                        }
                        BinOp::Div => x.div_euclid(y),
                        BinOp::Rem => x.rem_euclid(y),
                        BinOp::BitAnd => x & y,
                        BinOp::BitXor => x ^ y,
                        BinOp::Shl if (0..64).contains(&y) => {
                            Self::checked(x.checked_mul(1i128 << y))?
                        }
                        BinOp::Shr if (0..127).contains(&y) => x >> y,
                        BinOp::Shl | BinOp::Shr => {
                            return Err(EvalError::new("shift amount out of range"));
                        }
                        BinOp::And | BinOp::Or | BinOp::Implies => unreachable!(),
                    })
                }
            },
            Expr::Chain(es, ops) => {
                let mut prev = self.eval(&es[0])?;
                for (op, e) in ops.iter().zip(&es[1..]) {
                    let next = self.eval(e)?;
                    if !op.holds(&prev, &next)? {
                        return Ok(Val::Bool(false));
                    }
                    prev = next;
                }
                Val::Bool(true)
            }
            Expr::Ite(c, a, b) => {
                if self.boolean(c)? {
                    self.eval(a)?
                } else {
                    self.eval(b)?
                }
            }
            Expr::Call(n, args) => self.call(n, args)?,
            Expr::Quant(kind, x, dom, body) => {
                let items: Vec<i128> = match dom {
                    Domain::Range(lo, hi) => {
                        let lo = self.int(lo)?;
                        let hi = self.int(hi)?;
                        if hi - lo > MAX_RANGE {
                            return Err(EvalError::new(format!(
                                "range {lo}..{hi} is too large to check"
                            )));
                        }
                        (lo..hi.max(lo)).collect()
                    }
                    Domain::MapKeys(m) => self.map(m)?.keys().copied().collect(),
                };
                let mut count = 0;
                for item in items {
                    self.scopes.push((x.clone(), Val::Int(item)));
                    let r = self.boolean(body);
                    self.scopes.pop();
                    let r = r?;
                    match kind {
                        QuantKind::Forall if !r => return Ok(Val::Bool(false)),
                        QuantKind::Exists if r => return Ok(Val::Bool(true)),
                        QuantKind::Count if r => count += 1,
                        _ => {}
                    }
                }
                match kind {
                    QuantKind::Forall => Val::Bool(true),
                    QuantKind::Exists => Val::Bool(false),
                    QuantKind::Count => Val::Int(count),
                }
            }
            Expr::Index(m, k) => {
                let m = self.map(m)?;
                let k = self.int(k)?;
                match m.get(&k) {
                    Some(v) => Val::Int(*v),
                    None => return Err(EvalError::new(format!("key {k} is not in the map"))),
                }
            }
            Expr::Update(m, k, v) => {
                let mut m = (*self.map(m)?).clone();
                let k = self.int(k)?;
                let v = self.int(v)?;
                m.insert(k, v);
                Val::Map(Rc::new(m))
            }
            Expr::InSet(a, es) => {
                let x = self.eval(a)?;
                for e in es {
                    if self.eval(e)? == x {
                        return Ok(Val::Bool(true));
                    }
                }
                Val::Bool(false)
            }
            Expr::InMap(k, m) => {
                let k = self.int(k)?;
                Val::Bool(self.map(m)?.contains_key(&k))
            }
        })
    }

    fn call_define(&mut self, d: &Define, args: &[Val]) -> EResult<Val> {
        if self.depth >= MAX_DEPTH {
            return Err(EvalError::new(format!("{}: recursion too deep", d.name)));
        }
        // a define's body sees only its own parameters (and globals / other defines)
        let saved = std::mem::take(&mut self.scopes);
        for (p, a) in d.params.iter().zip(args) {
            self.scopes.push((p.clone(), a.clone()));
        }
        self.depth += 1;
        let r = self.eval(&d.body);
        self.depth -= 1;
        self.scopes = saved;
        r
    }

    fn call(&mut self, n: &str, args: &[Expr]) -> EResult<Val> {
        let arity = |k: usize| -> EResult<()> {
            if args.len() == k {
                Ok(())
            } else {
                Err(EvalError::new(format!("{n} takes {k} argument(s)")))
            }
        };
        match n {
            "old" => {
                arity(1)?;
                let was = self.in_old;
                self.in_old = true;
                let r = self.eval(&args[0]);
                self.in_old = was;
                r
            }
            "u" => {
                arity(1)?;
                let width = match &args[0] {
                    Expr::Var(v) => self.env.width(v),
                    _ => 32,
                };
                let x = self.int(&args[0])?;
                Ok(Val::Int(if x < 0 { x + (1i128 << width) } else { x }))
            }
            "load" | "load8" => {
                arity(1)?;
                let addr = self.int(&args[0])?;
                let bytes = if n == "load" { 4 } else { 1 };
                let raw = self.env.load(addr, bytes)?;
                Ok(Val::Int(if n == "load" {
                    raw as u32 as i32 as i128
                } else {
                    raw as i128
                }))
            }
            "abs" => {
                arity(1)?;
                Ok(Val::Int(self.int(&args[0])?.abs()))
            }
            "min" | "max" => {
                arity(2)?;
                let a = self.int(&args[0])?;
                let b = self.int(&args[1])?;
                Ok(Val::Int(if n == "min" { a.min(b) } else { a.max(b) }))
            }
            "size" => {
                arity(1)?;
                Ok(Val::Int(self.map(&args[0])?.len() as i128))
            }
            "remove" => {
                arity(2)?;
                let mut m = (*self.map(&args[0])?).clone();
                m.remove(&self.int(&args[1])?);
                Ok(Val::Map(Rc::new(m)))
            }
            _ if n.starts_with("i32.") => {
                arity(2)?;
                let a = wrap32(self.int(&args[0])?);
                let b = wrap32(self.int(&args[1])?);
                let (ua, ub) = (a as u32, b as u32);
                let div0 = || EvalError::new(format!("{n}: division by zero"));
                Ok(Val::Int(match &n[4..] {
                    "add" => wrap32(a + b),
                    "sub" => wrap32(a - b),
                    "mul" => wrap32(a * b),
                    "and" => a & b,
                    "or" => a | b,
                    "xor" => a ^ b,
                    "shl" => (ua.wrapping_shl(ub)) as i32 as i128,
                    "shr_s" => ((a as i32).wrapping_shr(ub)) as i128,
                    "shr_u" => (ua.wrapping_shr(ub)) as i32 as i128,
                    "div_s" if b == 0 => return Err(div0()),
                    "div_s" => wrap32(((a as i32).wrapping_div(b as i32)) as i128),
                    "div_u" if b == 0 => return Err(div0()),
                    "div_u" => (ua / ub) as i32 as i128,
                    "rem_s" if b == 0 => return Err(div0()),
                    "rem_s" => ((a as i32).wrapping_rem(b as i32)) as i128,
                    "rem_u" if b == 0 => return Err(div0()),
                    "rem_u" => (ua % ub) as i32 as i128,
                    _ => return Err(EvalError::new(format!("unknown operation {n}"))),
                }))
            }
            _ => {
                let Some(d) = self.env.define(n) else {
                    return Err(EvalError::new(format!("unknown function {n}")));
                };
                let d = d.clone();
                if d.params.len() != args.len() {
                    return Err(EvalError::new(format!(
                        "{n} takes {} argument(s)",
                        d.params.len()
                    )));
                }
                let vals = args
                    .iter()
                    .map(|a| self.eval(a))
                    .collect::<EResult<Vec<_>>>()?;
                self.call_define(&d, &vals)
            }
        }
    }
}

pub fn eval(e: &Expr, env: &dyn Env) -> EResult<Val> {
    Evaluator::new(env).eval(e)
}

pub fn eval_bool(e: &Expr, env: &dyn Env) -> EResult<bool> {
    Evaluator::new(env).boolean(e)
}

pub fn eval_int(e: &Expr, env: &dyn Env) -> EResult<i128> {
    Evaluator::new(env).int(e)
}

/// Names that a predicate may use without a definition.
pub const BUILTINS: &[&str] = &[
    "old", "u", "load", "load8", "abs", "min", "max", "size", "remove",
];

pub fn is_builtin(n: &str) -> bool {
    BUILTINS.contains(&n) || n.starts_with("i32.")
}

// ---------------------------------------------------------------------------------------
// Explaining a failure: the predicate with values substituted and the false conjunct marked.

fn is_simple(e: &Expr) -> bool {
    matches!(
        e,
        Expr::Int(_) | Expr::Bool(_) | Expr::Var(_) | Expr::Name(_)
    )
}

// Render an expression with program values substituted for `$names`.
fn substituted(e: &Expr, ev: &mut Evaluator) -> String {
    fn child(c: &Expr, min: u8, ev: &mut Evaluator) -> String {
        let s = substituted(c, ev);
        let neg_val = matches!(c, Expr::Var(_)) && s.starts_with('-');
        if c.prec() < min || (neg_val && min > PREC_CMP + 1) {
            format!("({s})")
        } else {
            s
        }
    }
    let value_or_src = |e: &Expr, ev: &mut Evaluator| match ev.eval(e) {
        Ok(v) => v.to_string(),
        Err(_) => e.to_string(),
    };
    match e {
        Expr::Var(_) => value_or_src(e, ev),
        Expr::Call(n, _) if n == "old" => value_or_src(e, ev),
        Expr::Bin(op, a, b) => {
            let p = op.prec();
            let (lp, rp) = if *op == BinOp::Implies {
                (p + 1, p)
            } else {
                (p, p + 1)
            };
            let l = child(a, lp, ev);
            let r = child(b, rp, ev);
            match op {
                BinOp::Mul => format!("{l}\u{b7}{r}"),
                _ => format!("{l} {} {r}", op.src()),
            }
        }
        Expr::Neg(a) => format!("-{}", child(a, PREC_UNARY, ev)),
        Expr::Not(a) => format!("!{}", child(a, PREC_UNARY, ev)),
        Expr::Chain(es, ops) => {
            let mut out = child(&es[0], PREC_CMP + 1, ev);
            for (op, x) in ops.iter().zip(&es[1..]) {
                out.push_str(&format!(" {} {}", op.pretty(), child(x, PREC_CMP + 1, ev)));
            }
            out
        }
        Expr::Call(n, args) => {
            let args: Vec<String> = args.iter().map(|a| child(a, 0, ev)).collect();
            format!("{n}({})", args.join(", "))
        }
        Expr::Ite(c, a, b) => format!(
            "{} ? {} : {}",
            child(c, PREC_TERNARY + 1, ev),
            child(a, PREC_TERNARY + 1, ev),
            child(b, PREC_TERNARY, ev)
        ),
        _ => e.to_string(),
    }
}

// "subst = value" for a compound side, or just the value for a simple one
fn side(e: &Expr, ev: &mut Evaluator) -> String {
    let v = match ev.eval(e) {
        Ok(v) => v.to_string(),
        Err(_) => "?".to_string(),
    };
    if is_simple(e) {
        v
    } else {
        let s = substituted(e, ev);
        if s == v { v } else { format!("{s} = {v}") }
    }
}

// The innermost false part of a false predicate, as (source text, explanation).
fn false_part(e: &Expr, ev: &mut Evaluator) -> (String, String) {
    match e {
        Expr::Bin(BinOp::And, a, b) => {
            if let Ok(false) = ev.boolean(a) {
                false_part(a, ev)
            } else {
                false_part(b, ev)
            }
        }
        Expr::Bin(BinOp::Implies, _, b) => false_part(b, ev),
        Expr::Chain(es, ops) => {
            for (i, op) in ops.iter().enumerate() {
                let (l, r) = (&es[i], &es[i + 1]);
                let lv = ev.eval(l);
                let rv = ev.eval(r);
                if let (Ok(lv), Ok(rv)) = (&lv, &rv)
                    && let Ok(false) = op.holds(lv, rv)
                {
                    let link = Expr::Chain(vec![l.clone(), r.clone()], vec![*op]);
                    return (
                        link.to_string(),
                        format!("{} {} {}", side(l, ev), op.pretty(), side(r, ev)),
                    );
                }
            }
            (e.to_string(), substituted(e, ev))
        }
        Expr::Quant(QuantKind::Forall, x, dom, body) => {
            let items: Vec<i128> = match dom {
                Domain::Range(lo, hi) => match (ev.int(lo), ev.int(hi)) {
                    (Ok(lo), Ok(hi)) if hi - lo <= MAX_RANGE => (lo..hi.max(lo)).collect(),
                    _ => vec![],
                },
                Domain::MapKeys(m) => ev
                    .map(m)
                    .map(|m| m.keys().copied().collect())
                    .unwrap_or_default(),
            };
            for item in items {
                ev.scopes.push((x.clone(), Val::Int(item)));
                let r = ev.boolean(body);
                let ret = if let Ok(false) = r {
                    let (src, why) = false_part(body, ev);
                    Some((e.to_string(), format!("at ${x} = {item}, {src} : {why}")))
                } else {
                    None
                };
                ev.scopes.pop();
                if let Some(ret) = ret {
                    return ret;
                }
            }
            (e.to_string(), "false".to_string())
        }
        Expr::Not(a) => (e.to_string(), format!("{} holds", substituted(a, ev))),
        _ => (e.to_string(), substituted(e, ev)),
    }
}

/// Explain why `e` is false: `conjunct : substituted values ✗`.
pub fn explain_false(e: &Expr, env: &dyn Env) -> String {
    let mut ev = Evaluator::new(env);
    let (src, why) = false_part(e, &mut ev);
    if why.is_empty() || why == src {
        format!("{src} \u{2717}")
    } else {
        format!("{src} : {why} \u{2717}")
    }
}

/// Render an integer-valued expression with its value, e.g. `$n - $r * $r = 10 - 3·3 = 1`.
pub fn show_value(e: &Expr, env: &dyn Env) -> String {
    let mut ev = Evaluator::new(env);
    side(e, &mut ev)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[derive(Default)]
    struct TestEnv {
        vars: HashMap<String, Val>,
        old: HashMap<String, Val>,
        defs: Vec<Define>,
        mem: HashMap<i128, u8>,
    }

    impl TestEnv {
        fn with(vars: &[(&str, i128)]) -> Self {
            Self {
                vars: vars
                    .iter()
                    .map(|(n, v)| (n.to_string(), Val::Int(*v)))
                    .collect(),
                ..Default::default()
            }
        }
        fn define(mut self, line: &str) -> Self {
            match parse_annotation(line).unwrap() {
                Annotation::Define(ds) => self.defs.extend(ds),
                _ => panic!(),
            }
            self
        }
    }

    impl Env for TestEnv {
        fn var(&self, name: &str) -> Option<Val> {
            self.vars.get(name).cloned()
        }
        fn old_var(&self, name: &str) -> Option<Val> {
            self.old.get(name).or(self.vars.get(name)).cloned()
        }
        fn load(&self, addr: i128, bytes: u32) -> EResult<u64> {
            let mut v = 0u64;
            for i in 0..bytes as i128 {
                v |= (*self.mem.get(&(addr + i)).unwrap_or(&0) as u64) << (8 * i);
            }
            Ok(v)
        }
        fn define(&self, name: &str) -> Option<&Define> {
            self.defs.iter().find(|d| d.name == name)
        }
    }

    fn p(s: &str) -> Expr {
        parse_expr(s).unwrap_or_else(|e| panic!("{s}: {e}"))
    }

    fn holds(s: &str, env: &TestEnv) -> bool {
        eval_bool(&p(s), env).unwrap_or_else(|e| panic!("{s}: {e:?}"))
    }

    #[test]
    fn precedence_and_printing() {
        assert_eq!(p("1 + 2 * 3").to_string(), "1 + 2 * 3");
        assert_eq!(p("(1 + 2) * 3").to_string(), "(1 + 2) * 3");
        assert_eq!(
            p("0 <= $r && $r * $r <= $n").to_string(),
            "0 <= $r && $r * $r <= $n"
        );
        assert_eq!(p("$a ==> $b ==> $c").to_string(), "$a ==> $b ==> $c");
        assert_eq!(p("($a ==> $b) ==> $c").to_string(), "($a ==> $b) ==> $c");
        assert_eq!(p("!($x < 3)").to_string(), "!($x < 3)");
        assert_eq!(p("$k & 7").to_string(), "$k & 7");
        assert_eq!(p("$k + 1 & 7").to_string(), "$k + 1 & 7");
        assert_eq!(
            p("$e == ($x % 2 == 0 ? 1 : 0)").to_string(),
            "$e == ($x % 2 == 0 ? 1 : 0)"
        );
        assert_eq!(
            p("if $y == 0 then $x else gcd($y, $x % $y)").to_string(),
            "$y == 0 ? $x : gcd($y, $x % $y)"
        );
        assert_eq!(
            p("forall $s in 0..8: st($s) in {0, 1, 2}").to_string(),
            "forall $s in 0..8: st($s) in {0, 1, 2}"
        );
        assert_eq!(p("$M[$k -> $v][3]").to_string(), "$M[$k -> $v][3]");
        // round trip of printing through parsing
        for s in [
            "0 <= $r && $r * $r <= $n && $n < ($r + 1) * ($r + 1)",
            "-$x + -3 < u($x)",
            "($x % 2 == 0 && $y + $y == $x) || ($x % 2 == 1 && $y == -1)",
            "count $s in 0..8: load(65440 + 12 * $s) == 1",
            "$k in $M && $M[$k] == old($v)",
        ] {
            let e = p(s);
            assert_eq!(p(&e.to_string()), e, "{s}");
        }
    }

    #[test]
    fn parse_errors() {
        for s in [
            "",
            "$x <",
            "(1 + 2",
            "1 + * 2",
            "$",
            "forall $s 0..3: true",
            "if $x then 1",
            "3x",
            "$x ; 1",
        ] {
            assert!(parse_expr(s).is_err(), "{s} should not parse");
        }
    }

    #[test]
    fn arithmetic_is_mathematical() {
        let env = TestEnv::with(&[("r", 46340), ("n", 2147483647), ("m", -3)]);
        // no wraparound in predicates
        assert!(holds("($r + 1) * ($r + 1) > $n", &env));
        assert!(holds("$r * $r <= $n", &env));
        // Euclidean division and remainder
        assert!(holds("$m % 2 == 1", &env));
        assert!(holds("$m / 2 == -2", &env));
        assert!(holds("-7 % -2 == 1", &env));
        // unsigned reading
        let env = TestEnv::with(&[("x", -1)]);
        assert!(holds("u($x) == 4294967295", &env));
        assert!(holds("$x < 0 && u($x) > 0", &env));
        // machine operations wrap
        let env = TestEnv::with(&[("a", 2147483647)]);
        assert!(holds("i32.add($a, 1) == -2147483648", &env));
        assert!(holds("i32.mul(46341, 46341) == -2147479015", &env));
        assert!(holds("i32.shr_u(-4, 1) == 2147483646", &env));
        assert!(holds("i32.shr_s(-4, 1) == -2", &env));
        assert!(holds("0x9E3779B1 == 2654435761", &env));
        assert!(holds("-5 & 7 == 3", &env));
    }

    #[test]
    fn chains_quantifiers_and_definitions() {
        let env = TestEnv::with(&[("i", 4), ("n", 16)])
            .define("(@define gcd($x, $y) = ($y == 0 ? $x : gcd($y, $x % $y)))")
            .define("(@define CAP = 8, even(x) = x % 2 == 0)");
        assert!(holds("0 <= $i < CAP", &env));
        assert!(!holds("0 <= $i < 4", &env));
        assert!(holds(
            "gcd(12, 8) == 4 && gcd(0, 5) == 5 && gcd(7, 0) == 7",
            &env
        ));
        assert!(holds("even($i) && !even($i + 1)", &env));
        assert!(holds("forall $d in 0..$i: $d * $d < $n", &env));
        assert!(!holds("forall $d in 0..$n: $d * $d < $n", &env));
        assert!(holds("exists $d in 0..$n: $d * $d == $n", &env));
        assert_eq!(
            eval_int(&p("count $d in 0..10: even($d)"), &env).unwrap(),
            5
        );
        assert!(holds("if $i > 3 then true else false", &env));
        assert!(holds("$i in {1, 4, 9}", &env));
        // binders shadow program names
        assert!(holds("forall $i in 0..3: $i < 3", &env));
        // errors are reported, not guessed
        assert!(eval_bool(&p("$q > 0"), &env).is_err());
        assert!(eval_bool(&p("$i / 0 == 1"), &env).is_err());
        assert!(eval_bool(&p("nosuch($i)"), &env).is_err());
        assert!(eval_bool(&p("$i + 1"), &env).is_err());
        assert!(eval_bool(&p("forall $d in 0..100000000: true"), &env).is_err());
        let deep = TestEnv::default().define("(@define f(x) = f(x + 1))");
        assert!(eval_bool(&p("f(0) == 0"), &deep).is_err());
    }

    #[test]
    fn old_maps_and_memory() {
        let mut env = TestEnv::with(&[("x", 5)]);
        env.old.insert("x".into(), Val::Int(2));
        assert!(holds("$x == old($x) + 3", &env));
        assert!(holds("old($x + 1) == 3", &env));
        let m: BTreeMap<i128, i128> = [(3, 30), (11, 110)].into_iter().collect();
        env.vars.insert("M".into(), Val::Map(Rc::new(m)));
        assert!(holds("3 in $M && $M[3] == 30 && !(4 in $M)", &env));
        assert!(holds(
            "$M[4 -> 40][4] == 40 && size($M[4 -> 40]) == 3",
            &env
        ));
        assert!(holds("size(remove($M, 3)) == 1", &env));
        assert!(holds("forall $k in $M: $M[$k] == 10 * $k", &env));
        assert!(eval_bool(&p("$M[5] == 0"), &env).is_err());
        env.mem.insert(100, 0xff);
        env.mem.insert(101, 0xff);
        env.mem.insert(102, 0xff);
        env.mem.insert(103, 0xff);
        env.mem.insert(200, 7);
        assert!(holds(
            "load(100) == -1 && load8(100) == 255 && load(200) == 7",
            &env
        ));
    }

    #[test]
    fn annotations() {
        assert_eq!(
            parse_annotation("(@invariant 0 <= $r && $r * $r <= $n)").unwrap(),
            Annotation::Invariant(p("0 <= $r && $r * $r <= $n"))
        );
        assert_eq!(
            parse_annotation("  ( @decreases $n - $r * $r )").unwrap(),
            Annotation::Decreases(p("$n - $r * $r"))
        );
        match parse_annotation("(@define EMPTY = 0, FULL = 1, st($s) = load(65440 + 12*$s))")
            .unwrap()
        {
            Annotation::Define(ds) => {
                assert_eq!(ds.len(), 3);
                assert_eq!(ds[2].params, vec!["s".to_string()]);
            }
            _ => panic!(),
        }
        assert_eq!(
            parse_annotation("(@ghost global $M (map i32 i32))").unwrap(),
            Annotation::Ghost {
                scope: GhostScope::Global,
                name: "M".into(),
                ty: GhostType::Map
            }
        );
        assert_eq!(
            parse_annotation("(@set $M := $M[$k -> $x])").unwrap(),
            Annotation::Set {
                name: "M".into(),
                value: p("$M[$k -> $x]")
            }
        );
        assert_eq!(
            parse_annotation("(@run 10 -3)").unwrap(),
            Annotation::Run(vec![10, -3])
        );
        for bad in [
            "(@invariant)",
            "(@invariant 0 <=)",
            "(@frobnicate 1)",
            "(@assert 1 < 2",
            "(@assert 1 < 2) (@assert 2 < 3)",
            "(@define $x = 1)",
            "(@ghost $M i32)",
        ] {
            assert!(parse_annotation(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn erasure() {
        let (e, decls, changed) = scan_header(
            "(func $isqrt (param $n (i32 | 0 <= $n)) (result $root (i32 | 0 <= $root)))",
        )
        .unwrap();
        assert!(changed);
        assert_eq!(e, "(func $isqrt (param $n i32) (result i32))");
        assert_eq!(decls.len(), 2);
        assert_eq!(decls[0].kind, DeclKind::Param);
        assert_eq!(decls[0].name.as_deref(), Some("n"));
        assert_eq!(decls[1].name.as_deref(), Some("root"));
        assert_eq!(decls[1].refinement, Some(p("0 <= $root")));

        // a refinement that contains parentheses and a string literal elsewhere
        let (e, _, _) = scan_header(
            "(func $f (export \"a(b|c)\") (param $x (i32 | ($x % 2 == 0))) (result i32)",
        )
        .unwrap();
        assert_eq!(
            e,
            "(func $f (export \"a(b|c)\") (param $x i32) (result i32)"
        );

        let (e, decls, changed) = scan_header("(local $r (i32 | 0 <= $r <= 46340))").unwrap();
        assert!(changed);
        assert_eq!(e, "(local $r i32)");
        assert_eq!(decls[0].kind, DeclKind::Local);

        // named result without refinement
        let (e, _, changed) = scan_header("(func $g (result $v i32)").unwrap();
        assert!(changed);
        assert_eq!(e, "(func $g (result i32)");

        // plain headers are untouched and still report their declarations
        let (e, decls, changed) =
            scan_header("(func $gcd (param $a i32) (param i32 i64) (result i32)").unwrap();
        assert!(!changed);
        assert_eq!(e, "(func $gcd (param $a i32) (param i32 i64) (result i32)");
        assert_eq!(decls.len(), 4);
        assert_eq!(decls[0].name.as_deref(), Some("a"));
        assert_eq!(decls[1].name, None);
        assert_eq!(decls[3].kind, DeclKind::Result);

        // erasure never changes the number of lines
        assert!(!e.contains('\n'));

        for bad in [
            "(func (param (i32 | 0 <= $n)))",
            "(func (param $n (i33 | 0 <= $n)))",
            "(func (param $n (i32 | 0 <=)))",
            "(func (param $n (i32 0 <= $n)))",
            "(func (param $n (i32 | 0 <= $n)",
        ] {
            assert!(scan_header(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn scan_lines() {
        assert!(matches!(scan_line("i32.const 5"), ScanResult::Plain));
        assert!(matches!(
            scan_line("(local $x i32)"),
            ScanResult::Spec(LineSpec::Header { erased: None, .. })
        ));
        assert!(matches!(scan_line("local.get $x"), ScanResult::Plain));
        assert!(matches!(
            scan_line("(@assert $x % 2 == 0)"),
            ScanResult::Spec(LineSpec::Annotation(Annotation::Assert(_)))
        ));
        assert!(matches!(
            scan_line("(@assert $x %% 2)"),
            ScanResult::Malformed(_)
        ));
        assert!(matches!(
            scan_line("(param $x (i32 | $x >"),
            ScanResult::Malformed(_)
        ));
        match scan_line(
            "(func $half (param $x (i32 | $x % 2 == 0)) (result $h (i32 | $h + $h == $x))",
        ) {
            ScanResult::Spec(LineSpec::Header { erased, decls }) => {
                assert_eq!(erased.unwrap(), "(func $half (param $x i32) (result i32)");
                assert_eq!(decls.len(), 2);
            }
            _ => panic!(),
        }
    }

    #[test]
    fn explanations() {
        let env = TestEnv::with(&[("r", 46341), ("n", 2147483647)]);
        let e = p("0 <= $r && $r * $r <= $n");
        assert!(!eval_bool(&e, &env).unwrap());
        assert_eq!(
            explain_false(&e, &env),
            "$r * $r <= $n : 46341\u{b7}46341 = 2147488281 \u{2264} 2147483647 \u{2717}"
        );
        let env = TestEnv::with(&[("root", 2), ("n", 4)]);
        let e = p("$root * $root < $n && $n <= ($root + 1) * ($root + 1)");
        assert_eq!(
            explain_false(&e, &env),
            "$root * $root < $n : 2\u{b7}2 = 4 < 4 \u{2717}"
        );
        let env = TestEnv::with(&[("x", 1), ("a", 0), ("b", 1)]);
        let e = p("0 <= $b && $b <= $a");
        assert_eq!(explain_false(&e, &env), "$b <= $a : 1 \u{2264} 0 \u{2717}");
        let env = TestEnv::with(&[("x", -3)]);
        let e = p("$x % 2 == 0");
        assert_eq!(
            explain_false(&e, &env),
            "$x % 2 == 0 : (-3) % 2 = 1 == 0 \u{2717}"
        );
        let env = TestEnv::with(&[("i", 2)]);
        let e = p("forall $d in 0..5: $d < 4");
        assert_eq!(
            explain_false(&e, &env),
            "forall $d in 0..5: $d < 4 : at $d = 4, $d < 4 : 4 < 4 \u{2717}"
        );
        let env = TestEnv::with(&[("n", 10), ("r", 3)]);
        assert_eq!(show_value(&p("$n - $r * $r"), &env), "10 - 3\u{b7}3 = 1");
    }
}
