//! The v2 line syntax (design 16 §1.3), parsed into a module model.
//! Instruction lines are decoded into [`Ins`]; propositions stay as [`Expr`] templates.

use super::sexpr::{LineItems, S, parse_int, read_line, split_comment};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ValTy {
    I32,
    I64,
    F32,
    F64,
}

impl ValTy {
    pub fn parse(s: &str) -> Option<ValTy> {
        Some(match s {
            "i32" => ValTy::I32,
            "i64" => ValTy::I64,
            "f32" => ValTy::F32,
            "f64" => ValTy::F64,
            _ => return None,
        })
    }
    pub fn bits(self) -> u32 {
        match self {
            ValTy::I32 | ValTy::F32 => 32,
            _ => 64,
        }
    }
    pub fn is_int(self) -> bool {
        matches!(self, ValTy::I32 | ValTy::I64)
    }
    pub fn name(self) -> &'static str {
        match self {
            ValTy::I32 => "i32",
            ValTy::I64 => "i64",
            ValTy::F32 => "f32",
            ValTy::F64 => "f64",
        }
    }
}

/// Pure integer opcodes (R3, R4). The width is carried separately.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IOp {
    Add, Sub, Mul, DivS, DivU, RemS, RemU, And, Or, Xor, Shl, ShrS, ShrU, Rotl, Rotr,
    Clz, Ctz, Popcnt, Eqz, Eq, Ne, LtS, LtU, GtS, GtU, LeS, LeU, GeS, GeU,
    Extend8S, Extend16S, Extend32S, WrapI64, ExtendI32S, ExtendI32U,
}

impl IOp {
    pub fn parse(full: &str) -> Option<(IOp, ValTy)> {
        let (ty, op) = full.split_once('.')?;
        let ty = ValTy::parse(ty)?;
        if !ty.is_int() {
            return None;
        }
        use IOp::*;
        let o = match op {
            "add" => Add, "sub" => Sub, "mul" => Mul, "div_s" => DivS, "div_u" => DivU,
            "rem_s" => RemS, "rem_u" => RemU, "and" => And, "or" => Or, "xor" => Xor,
            "shl" => Shl, "shr_s" => ShrS, "shr_u" => ShrU, "rotl" => Rotl, "rotr" => Rotr,
            "clz" => Clz, "ctz" => Ctz, "popcnt" => Popcnt, "eqz" => Eqz, "eq" => Eq, "ne" => Ne,
            "lt_s" => LtS, "lt_u" => LtU, "gt_s" => GtS, "gt_u" => GtU, "le_s" => LeS,
            "le_u" => LeU, "ge_s" => GeS, "ge_u" => GeU, "extend8_s" => Extend8S,
            "extend16_s" => Extend16S,
            "extend32_s" if ty == ValTy::I64 => Extend32S,
            "wrap_i64" if ty == ValTy::I32 => WrapI64,
            "extend_i32_s" if ty == ValTy::I64 => ExtendI32S,
            "extend_i32_u" if ty == ValTy::I64 => ExtendI32U,
            _ => return None,
        };
        // the width is the operand width
        let w = match o {
            WrapI64 => ValTy::I64,
            ExtendI32S | ExtendI32U => ValTy::I32,
            _ => ty,
        };
        Some((o, w))
    }
    pub fn unary(self) -> bool {
        use IOp::*;
        matches!(self, Clz | Ctz | Popcnt | Eqz | Extend8S | Extend16S | Extend32S | WrapI64 | ExtendI32S | ExtendI32U)
    }
    pub fn is_cmp(self) -> bool {
        use IOp::*;
        matches!(self, Eqz | Eq | Ne | LtS | LtU | GtS | GtU | LeS | LeU | GeS | GeU)
    }
    /// Result type given the operand width.
    pub fn result(self, w: ValTy) -> ValTy {
        use IOp::*;
        if self.is_cmp() || self == WrapI64 {
            ValTy::I32
        } else if matches!(self, ExtendI32S | ExtendI32U) {
            ValTy::I64
        } else {
            w
        }
    }
    pub fn name(self, w: ValTy) -> String {
        use IOp::*;
        let s = match self {
            Add => "add", Sub => "sub", Mul => "mul", DivS => "div_s", DivU => "div_u", RemS => "rem_s",
            RemU => "rem_u", And => "and", Or => "or", Xor => "xor", Shl => "shl", ShrS => "shr_s",
            ShrU => "shr_u", Rotl => "rotl", Rotr => "rotr", Clz => "clz", Ctz => "ctz", Popcnt => "popcnt",
            Eqz => "eqz", Eq => "eq", Ne => "ne", LtS => "lt_s", LtU => "lt_u", GtS => "gt_s", GtU => "gt_u",
            LeS => "le_s", LeU => "le_u", GeS => "ge_s", GeU => "ge_u", Extend8S => "extend8_s",
            Extend16S => "extend16_s", Extend32S => "extend32_s", WrapI64 => "wrap_i64",
            ExtendI32S => "extend_i32_s", ExtendI32U => "extend_i32_u",
        };
        format!("{}.{}", self.result_prefix(w).name(), s)
    }
    fn result_prefix(self, w: ValTy) -> ValTy {
        match self {
            IOp::WrapI64 => ValTy::I32,
            IOp::ExtendI32S | IOp::ExtendI32U => ValTy::I64,
            _ => w,
        }
    }
}

/// A proposition or refinement expression (a template; `$x` and `v` are bound at instantiation).
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
    Var(String),
    V,
    Int(i128),
    Op(String, Vec<Expr>),
    Call(String, Vec<Expr>),
}

impl Expr {
    pub fn parse(s: &S) -> Result<Expr, String> {
        match s {
            S::Atom(a) if a == "v" => Ok(Expr::V),
            S::Atom(a) if a.starts_with('$') => Ok(Expr::Var(a.clone())),
            S::Atom(a) => parse_int(a).map(Expr::Int).ok_or_else(|| format!("bad expression `{a}`")),
            S::Str(_) => Err("unexpected string in expression".into()),
            S::List(l) => {
                let head = l.first().and_then(|h| h.atom()).ok_or("empty expression")?;
                if head == "call" {
                    let f = l.get(1).and_then(|x| x.atom()).ok_or("call needs a function")?;
                    let args = l[2..].iter().map(Expr::parse).collect::<Result<_, _>>()?;
                    Ok(Expr::Call(f.to_string(), args))
                } else {
                    let args = l[1..].iter().map(Expr::parse).collect::<Result<_, _>>()?;
                    Ok(Expr::Op(head.to_string(), args))
                }
            }
        }
    }
}

/// `T` or `(T | refinement)`; the refinement is expanded to a full expression mentioning `v`.
#[derive(Clone, Debug, PartialEq)]
pub struct Refined {
    pub ty: ValTy,
    pub refine: Option<Expr>,
}

impl Refined {
    pub fn parse(s: &S) -> Result<Refined, String> {
        match s {
            S::Atom(a) => Ok(Refined { ty: ValTy::parse(a).ok_or_else(|| format!("bad type `{a}`"))?, refine: None }),
            S::List(l) => {
                let ty = l.first().and_then(|x| x.atom()).and_then(ValTy::parse).ok_or("bad refined type")?;
                if l.get(1).and_then(|x| x.atom()) != Some("|") {
                    return Err("expected `|` in refined type".into());
                }
                let rest = &l[2..];
                let e = match rest {
                    [S::List(_)] => Expr::parse(&rest[0])?,
                    [S::Atom(p), args @ ..] if p.starts_with('$') => {
                        let mut a = vec![Expr::V];
                        for x in args {
                            a.push(Expr::parse(x)?);
                        }
                        Expr::Call(p.clone(), a)
                    }
                    _ => return Err("bad refinement".into()),
                };
                Ok(Refined { ty, refine: Some(e) })
            }
            _ => Err("bad type".into()),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Decl {
    Val(Refined),
    Fact(Expr),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Param {
    pub name: Option<String>,
    pub decl: Decl,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Header {
    pub name: Option<String>,
    pub exports: Vec<String>,
    pub import: Option<(String, String)>,
    pub params: Vec<Param>,
    pub results: Vec<Decl>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BlockKind {
    Block,
    Loop,
    If,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct BlockType {
    pub label: Option<String>,
    pub facts: Vec<Expr>,
    pub params: Vec<Refined>,
    pub results: Vec<Refined>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemArg {
    pub ty: ValTy,
    pub bytes: u32,
    pub signed: bool,
    pub offset: u64,
}

/// One decoded instruction line (plain Wasm or a v2 proof instruction).
#[derive(Clone, Debug, PartialEq)]
pub enum Ins {
    Nop,
    Unreachable,
    Drop,
    Select,
    Return,
    Block(BlockKind, BlockType),
    Else,
    End,
    Br(String),
    BrIf(String),
    /// targets; the last one is the default
    BrTable(Vec<String>),
    Call(String),
    CallIndirect,
    LocalGet(String),
    LocalSet(String),
    LocalTee(String),
    GlobalGet(String),
    GlobalSet(String),
    Load(MemArg),
    Store(MemArg),
    MemorySize,
    MemoryGrow,
    MemoryFill,
    MemoryCopy,
    Const(ValTy, u64),
    Int(IOp, ValTy),
    /// float or conversion op, opaque to the kernel; `trap` marks trapping `trunc`
    Float { name: String, ins: Vec<ValTy>, out: ValTy, trap: bool },
    Prove(u32),
    Lemma(String, Vec<Expr>),
    Unfold(String, Vec<Expr>),
    Assume(Expr),
}

impl Ins {
    pub fn is_proof(&self) -> bool {
        matches!(self, Ins::Prove(_) | Ins::Lemma(..) | Ins::Unfold(..) | Ins::Assume(_))
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum LocalKind {
    Val(Refined),
    Fact,
}

#[derive(Clone, Debug, PartialEq)]
pub struct LocalDecl {
    pub name: Option<String>,
    pub kind: LocalKind,
    pub line: u32,
}

#[derive(Clone, Debug, PartialEq)]
pub enum LineKind {
    Blank,
    FuncHeader(Header),
    FuncEnd,
    Locals(Vec<LocalDecl>),
    Instr(Ins),
    Memory(u64),
    Global { name: Option<String>, ty: Refined, mutable: bool, init: Option<u64> },
    Import { module: String, name: String, header: Option<Header> },
    Other,
    Error(String),
}

pub fn to_bits(ty: ValTy, v: i128) -> u64 {
    match ty {
        ValTy::I32 => (v as i64 as u64) & 0xffff_ffff,
        _ => v as i64 as u64,
    }
}

fn parse_float_bits(ty: ValTy, s: &str) -> Option<u64> {
    let t = s.replace('_', "");
    let f: f64 = match t.as_str() {
        "inf" | "+inf" => f64::INFINITY,
        "-inf" => f64::NEG_INFINITY,
        "nan" | "+nan" | "-nan" => f64::NAN,
        _ => t.parse().ok().or_else(|| parse_int(&t).map(|i| i as f64))?,
    };
    Some(if ty == ValTy::F32 { (f as f32).to_bits() as u64 } else { f.to_bits() })
}

fn parse_float_op(name: &str) -> Option<Ins> {
    let (pre, op) = name.split_once('.')?;
    let ty = ValTy::parse(pre)?;
    let fl = |a: &str| ValTy::parse(a);
    let mk = |ins: Vec<ValTy>, out: ValTy, trap: bool| Some(Ins::Float { name: name.into(), ins, out, trap });
    if !ty.is_int() {
        match op {
            "add" | "sub" | "mul" | "div" | "min" | "max" | "copysign" => return mk(vec![ty, ty], ty, false),
            "abs" | "neg" | "sqrt" | "ceil" | "floor" | "trunc" | "nearest" => return mk(vec![ty], ty, false),
            "eq" | "ne" | "lt" | "gt" | "le" | "ge" => return mk(vec![ty, ty], ValTy::I32, false),
            "demote_f64" => return mk(vec![ValTy::F64], ty, false),
            "promote_f32" => return mk(vec![ValTy::F32], ty, false),
            _ => {}
        }
        if let Some(src) = op.strip_prefix("convert_") {
            return mk(vec![fl(src.get(..3)?)?], ty, false);
        }
        if let Some(src) = op.strip_prefix("reinterpret_") {
            return mk(vec![fl(src)?], ty, false);
        }
        return None;
    }
    if let Some(src) = op.strip_prefix("trunc_sat_") {
        return mk(vec![fl(src.get(..3)?)?], ty, false);
    }
    if let Some(src) = op.strip_prefix("trunc_") {
        return mk(vec![fl(src.get(..3)?)?], ty, true);
    }
    if let Some(src) = op.strip_prefix("reinterpret_") {
        return mk(vec![fl(src)?], ty, false);
    }
    None
}

fn parse_memarg(name: &str, imms: &[String]) -> Option<(bool, MemArg)> {
    let (pre, op) = name.split_once('.')?;
    let ty = ValTy::parse(pre)?;
    let (store, rest) = if let Some(r) = op.strip_prefix("load") {
        (false, r)
    } else if let Some(r) = op.strip_prefix("store") {
        (true, r)
    } else {
        return None;
    };
    let (bytes, signed) = match rest {
        "" => (ty.bits() / 8, false),
        "8" if store => (1, false),
        "16" if store => (2, false),
        "32" if store => (4, false),
        "8_s" => (1, true),
        "8_u" => (1, false),
        "16_s" => (2, true),
        "16_u" => (2, false),
        "32_s" => (4, true),
        "32_u" => (4, false),
        _ => return None,
    };
    let mut offset = 0;
    for i in imms {
        if let Some(o) = i.strip_prefix("offset=") {
            offset = parse_int(o)? as u64;
        } else if !i.starts_with("align=") {
            return None;
        }
    }
    Some((store, MemArg { ty, bytes, signed, offset }))
}

pub fn parse_block_type(items: &[S]) -> Result<BlockType, String> {
    let mut bt = BlockType::default();
    for it in items {
        match it {
            S::Atom(a) if a.starts_with('$') && bt.label.is_none() => bt.label = Some(a.clone()),
            S::List(l) => match it.head() {
                Some("fact") => bt.facts.push(Expr::parse(l.get(1).ok_or("empty fact")?)?),
                Some("param") => {
                    for x in &l[1..] {
                        bt.params.push(Refined::parse(x)?);
                    }
                }
                Some("result") => {
                    for x in &l[1..] {
                        bt.results.push(Refined::parse(x)?);
                    }
                }
                Some("type") => {}
                _ => return Err(format!("unexpected `{}` in block type", it.render())),
            },
            _ => return Err(format!("unexpected `{}` in block type", it.render())),
        }
    }
    Ok(bt)
}

fn parse_instr(items: &[S]) -> Result<Ins, String> {
    let name = items[0].atom().ok_or("expected an instruction")?;
    let rest = &items[1..];
    let atoms = || -> Result<Vec<String>, String> {
        rest.iter().map(|x| x.atom().map(|a| a.to_string()).ok_or_else(|| format!("unexpected `{}`", x.render()))).collect()
    };
    let one = || -> Result<String, String> {
        let a = atoms()?;
        if a.len() != 1 {
            return Err(format!("`{name}` takes one immediate"));
        }
        Ok(a[0].clone())
    };
    let exprs = |xs: &[S]| xs.iter().map(Expr::parse).collect::<Result<Vec<_>, _>>();
    Ok(match name {
        "nop" => Ins::Nop,
        "unreachable" => Ins::Unreachable,
        "drop" => Ins::Drop,
        "select" => Ins::Select,
        "return" => Ins::Return,
        "else" => Ins::Else,
        "end" => Ins::End,
        "block" => Ins::Block(BlockKind::Block, parse_block_type(rest)?),
        "loop" => Ins::Block(BlockKind::Loop, parse_block_type(rest)?),
        "if" => Ins::Block(BlockKind::If, parse_block_type(rest)?),
        "br" => Ins::Br(one()?),
        "br_if" => Ins::BrIf(one()?),
        "br_table" => Ins::BrTable(atoms()?),
        "call" => Ins::Call(one()?),
        "call_indirect" => Ins::CallIndirect,
        "local.get" => Ins::LocalGet(one()?),
        "local.set" => Ins::LocalSet(one()?),
        "local.tee" => Ins::LocalTee(one()?),
        "global.get" => Ins::GlobalGet(one()?),
        "global.set" => Ins::GlobalSet(one()?),
        "memory.size" => Ins::MemorySize,
        "memory.grow" => Ins::MemoryGrow,
        "memory.fill" => Ins::MemoryFill,
        "memory.copy" => Ins::MemoryCopy,
        "prove" => {
            let k = parse_int(&one()?).ok_or("prove needs a number")?;
            if !(0..=8).contains(&k) {
                return Err("prove k needs 0 ≤ k ≤ 8".into());
            }
            Ins::Prove(k as u32)
        }
        "lemma" | "unfold" => {
            let f = rest.first().and_then(|x| x.atom()).ok_or("needs a function name")?.to_string();
            let args = exprs(&rest[1..])?;
            if name == "lemma" { Ins::Lemma(f, args) } else { Ins::Unfold(f, args) }
        }
        "assume" => {
            let f = rest.first().filter(|x| x.head() == Some("fact")).ok_or("assume needs (fact …)")?;
            Ins::Assume(Expr::parse(f.list().unwrap().get(1).ok_or("empty fact")?)?)
        }
        _ => {
            if let Some(t) = name.strip_suffix(".const") {
                let ty = ValTy::parse(t).ok_or("bad const")?;
                let lit = one()?;
                let bits = if ty.is_int() {
                    to_bits(ty, parse_int(&lit).ok_or("bad integer")?)
                } else {
                    parse_float_bits(ty, &lit).ok_or("bad float")?
                };
                return Ok(Ins::Const(ty, bits));
            }
            if let Some((o, w)) = IOp::parse(name) {
                if !rest.is_empty() {
                    return Err(format!("`{name}` takes no immediates"));
                }
                return Ok(Ins::Int(o, w));
            }
            if let Some((store, m)) = parse_memarg(name, &atoms()?) {
                return Ok(if store { Ins::Store(m) } else { Ins::Load(m) });
            }
            if let Some(f) = parse_float_op(name) {
                return Ok(f);
            }
            return Err(format!("unknown instruction `{name}`"));
        }
    })
}

fn parse_func_items(items: &[S]) -> Result<Header, String> {
    let mut h = Header::default();
    for it in items {
        match it {
            S::Atom(a) if a.starts_with('$') && h.name.is_none() => h.name = Some(a.clone()),
            S::List(l) => match it.head() {
                Some("export") => match l.get(1) {
                    Some(S::Str(s)) => h.exports.push(s.clone()),
                    _ => return Err("export needs a name".into()),
                },
                Some("import") => match (l.get(1), l.get(2)) {
                    (Some(S::Str(m)), Some(S::Str(n))) => h.import = Some((m.clone(), n.clone())),
                    _ => return Err("bad import".into()),
                },
                Some("param") => {
                    let rest = &l[1..];
                    if let Some(S::Atom(n)) = rest.first()
                        && n.starts_with('$')
                    {
                        let d = rest.get(1).ok_or("param needs a type")?;
                        let decl = if d.head() == Some("fact") {
                            Decl::Fact(Expr::parse(d.list().unwrap().get(1).ok_or("empty fact")?)?)
                        } else {
                            Decl::Val(Refined::parse(d)?)
                        };
                        h.params.push(Param { name: Some(n.clone()), decl });
                    } else {
                        for x in rest {
                            h.params.push(Param { name: None, decl: Decl::Val(Refined::parse(x)?) });
                        }
                    }
                }
                Some("result") => {
                    for x in &l[1..] {
                        if x.head() == Some("fact") {
                            h.results.push(Decl::Fact(Expr::parse(x.list().unwrap().get(1).ok_or("empty fact")?)?));
                        } else {
                            h.results.push(Decl::Val(Refined::parse(x)?));
                        }
                    }
                }
                Some("type") => {}
                _ => return Err(format!("unexpected `{}` in function header", it.render())),
            },
            _ => return Err(format!("unexpected `{}` in function header", it.render())),
        }
    }
    Ok(h)
}

fn parse_locals(l: &[S], line: u32) -> Result<Vec<LocalDecl>, String> {
    let rest = &l[1..];
    if let Some(S::Atom(n)) = rest.first()
        && n.starts_with('$')
    {
        let d = rest.get(1).ok_or("local needs a type")?;
        let kind = if d.atom() == Some("fact") { LocalKind::Fact } else { LocalKind::Val(Refined::parse(d)?) };
        return Ok(vec![LocalDecl { name: Some(n.clone()), kind, line }]);
    }
    rest.iter().map(|x| Ok(LocalDecl { name: None, kind: LocalKind::Val(Refined::parse(x)?), line })).collect()
}

/// Classify one line of v2 text.
pub fn parse_line(text: &str, line: u32) -> LineKind {
    let (code, _) = split_comment(text);
    if code.trim().is_empty() {
        return LineKind::Blank;
    }
    let LineItems { items, open, extra_close } = match read_line(code) {
        Ok(r) => r,
        Err(e) => return LineKind::Error(e),
    };
    let res = (|| -> Result<LineKind, String> {
        if items.is_empty() && open.is_empty() && extra_close == 1 {
            return Ok(LineKind::FuncEnd);
        }
        if extra_close > 0 {
            return Err("unmatched `)`".into());
        }
        if open.len() == 1 && items.is_empty() {
            let o = &open[0];
            if o.first().and_then(|x| x.atom()) == Some("func") {
                return Ok(LineKind::FuncHeader(parse_func_items(&o[1..])?));
            }
            if o.first().and_then(|x| x.atom()) == Some("module") {
                return Ok(LineKind::Other);
            }
            return Err("unclosed `(`".into());
        }
        if !open.is_empty() {
            return Err("unclosed `(`".into());
        }
        if let [S::List(l)] = items.as_slice() {
            match items[0].head() {
                Some("func") => return Ok(LineKind::FuncHeader(parse_func_items(&l[1..])?)),
                Some("local") => return Ok(LineKind::Locals(parse_locals(l, line)?)),
                Some("memory") => {
                    let n = l.iter().skip(1).filter_map(|x| x.atom()).filter_map(parse_int).next().unwrap_or(0);
                    return Ok(LineKind::Memory(n as u64));
                }
                Some("global") => {
                    let mut i = 1;
                    let name = l.get(1).and_then(|x| x.atom()).filter(|a| a.starts_with('$')).map(|s| s.to_string());
                    if name.is_some() {
                        i += 1;
                    }
                    let tyd = l.get(i).ok_or("global needs a type")?;
                    let (ty, mutable) = if tyd.head() == Some("mut") {
                        (Refined::parse(tyd.list().unwrap().get(1).ok_or("bad mut")?)?, true)
                    } else {
                        (Refined::parse(tyd)?, false)
                    };
                    let init = match l.get(i + 1) {
                        Some(S::List(c)) if c.len() == 2 => match parse_instr(c) {
                            Ok(Ins::Const(_, b)) => Some(b),
                            _ => None,
                        },
                        _ => None,
                    };
                    return Ok(LineKind::Global { name, ty, mutable, init });
                }
                Some("import") => {
                    let (Some(S::Str(m)), Some(S::Str(n))) = (l.get(1), l.get(2)) else {
                        return Err("bad import".into());
                    };
                    let header = match l.get(3) {
                        Some(f) if f.head() == Some("func") => Some(parse_func_items(&f.list().unwrap()[1..])?),
                        _ => None,
                    };
                    return Ok(LineKind::Import { module: m.clone(), name: n.clone(), header });
                }
                Some(_) => return Ok(LineKind::Other),
                None => {}
            }
        }
        if items.first().and_then(|x| x.atom()).is_some() {
            return Ok(LineKind::Instr(parse_instr(&items)?));
        }
        Err("not a line Codillon understands".into())
    })();
    res.unwrap_or_else(LineKind::Error)
}

#[derive(Clone, Debug, PartialEq)]
pub struct Func {
    pub header: Header,
    /// 1-based line of the header (for imports, the import line)
    pub header_line: u32,
    /// 1-based line of the closing `)` (0 for imports)
    pub end_line: u32,
    pub locals: Vec<LocalDecl>,
    pub body: Vec<(u32, Ins)>,
    pub imported: bool,
}

impl Func {
    pub fn name(&self) -> String {
        self.header.name.clone().unwrap_or_else(|| "<anon>".into())
    }
    pub fn export_role(&self, prefix: &str) -> Option<&str> {
        self.header.exports.iter().find_map(|e| e.strip_prefix(prefix))
    }
    pub fn is_lemma(&self) -> bool {
        self.export_role("lemma:").is_some()
    }
    pub fn is_axiom(&self) -> bool {
        self.export_role("axiom:").is_some()
    }
    pub fn is_harness(&self) -> bool {
        self.export_role("harness:").is_some()
    }
    pub fn value_params(&self) -> impl Iterator<Item = (usize, &Param, &Refined)> {
        self.header.params.iter().enumerate().filter_map(|(i, p)| match &p.decl {
            Decl::Val(r) => Some((i, p, r)),
            _ => None,
        })
    }
    pub fn value_results(&self) -> Vec<&Refined> {
        self.header.results.iter().filter_map(|d| if let Decl::Val(r) = d { Some(r) } else { None }).collect()
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Global {
    pub name: Option<String>,
    pub ty: Refined,
    pub mutable: bool,
    pub init: Option<u64>,
    pub line: u32,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct Module {
    pub funcs: Vec<Func>,
    pub memory_min: Option<u64>,
    pub globals: Vec<Global>,
    /// (1-based line, message): syntax errors
    pub errors: Vec<(u32, String)>,
}

impl Module {
    pub fn parse(text: &str) -> Module {
        let lines: Vec<&str> = text.split('\n').collect();
        Self::parse_lines(&lines)
    }

    pub fn parse_lines<S: AsRef<str>>(lines: &[S]) -> Module {
        let mut m = Module::default();
        let mut imports = Vec::new();
        let mut defined: Vec<Func> = Vec::new();
        let mut cur: Option<Func> = None;
        for (i, t) in lines.iter().enumerate() {
            let ln = i as u32 + 1;
            let kind = parse_line(t.as_ref(), ln);
            match kind {
                LineKind::Blank | LineKind::Other => {}
                LineKind::Error(e) => m.errors.push((ln, e)),
                LineKind::FuncHeader(h) => {
                    if let Some(f) = cur.take() {
                        m.errors.push((f.header_line, "function is not closed".into()));
                        defined.push(f);
                    }
                    let imported = h.import.is_some();
                    let f = Func { header: h, header_line: ln, end_line: 0, locals: vec![], body: vec![], imported };
                    if imported {
                        imports.push(f);
                    } else {
                        cur = Some(f);
                    }
                }
                LineKind::FuncEnd => match cur.take() {
                    Some(mut f) => {
                        f.end_line = ln;
                        defined.push(f);
                    }
                    None => m.errors.push((ln, "unmatched `)`".into())),
                },
                LineKind::Locals(ls) => match cur.as_mut() {
                    Some(f) if f.body.is_empty() => f.locals.extend(ls),
                    _ => m.errors.push((ln, "locals must come right after the function header".into())),
                },
                LineKind::Instr(ins) => match cur.as_mut() {
                    Some(f) => f.body.push((ln, ins)),
                    None => m.errors.push((ln, "instruction outside a function".into())),
                },
                LineKind::Memory(n) => m.memory_min = Some(n),
                LineKind::Global { name, ty, mutable, init } => m.globals.push(Global { name, ty, mutable, init, line: ln }),
                LineKind::Import { module, name, header } => {
                    if let Some(mut h) = header {
                        h.import = Some((module, name));
                        imports.push(Func { header: h, header_line: ln, end_line: 0, locals: vec![], body: vec![], imported: true });
                    }
                }
            }
        }
        if let Some(f) = cur.take() {
            m.errors.push((f.header_line, "function is not closed".into()));
            defined.push(f);
        }
        m.funcs = imports;
        m.funcs.extend(defined);
        m
    }

    pub fn func_index(&self, name: &str) -> Option<usize> {
        if name.starts_with('$') {
            self.funcs.iter().position(|f| f.header.name.as_deref() == Some(name))
        } else {
            name.parse::<usize>().ok().filter(|i| *i < self.funcs.len())
        }
    }
}
