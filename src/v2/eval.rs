//! Reference interpreter for evaluation on constants (R28) and for predicate checks.
//! Integer semantics are exactly Wasm's; floats are supported only as opaque bits.

use super::ast::{BlockKind, Decl, IOp, Ins, LocalKind, Module, ValTy};
use super::out::Capture;
use super::runtime::{CheckOutcome, RuntimePlan, ShadowAct};
use super::term::mask;

pub const EVAL_BUDGET: u32 = 100_000;

#[derive(Clone, Debug, PartialEq)]
pub enum EvalErr {
    Trap(String),
    Budget,
    Unsupported(String),
    /// a runtime check (R35) failed before the instruction of this line
    CheckFailed { line: u32, msg: String },
}

fn sext(v: u64, ty: ValTy) -> i64 {
    if ty == ValTy::I32 { v as u32 as i32 as i64 } else { v as i64 }
}

/// One integer operation on bit patterns (operands masked to the operand width).
pub fn eval_iop(op: IOp, w: ValTy, args: &[u64]) -> Result<u64, EvalErr> {
    use IOp::*;
    let m = mask(w);
    let bits = w.bits() as u64;
    let a = args[0] & m;
    let b = args.get(1).copied().unwrap_or(0) & m;
    let (sa, sb) = (sext(a, w), sext(b, w));
    let bool = |x: bool| x as u64;
    let r = match op {
        Add => a.wrapping_add(b),
        Sub => a.wrapping_sub(b),
        Mul => a.wrapping_mul(b),
        DivU | RemU | DivS | RemS if b == 0 => return Err(EvalErr::Trap("integer divide by zero".into())),
        DivU => a / b,
        RemU => a % b,
        DivS => {
            let min = if w == ValTy::I32 { i32::MIN as i64 } else { i64::MIN };
            if sa == min && sb == -1 {
                return Err(EvalErr::Trap("integer overflow".into()));
            }
            if w == ValTy::I32 { (sa / sb) as u64 } else { sa.wrapping_div(sb) as u64 }
        }
        RemS => {
            if sb == -1 { 0 } else if w == ValTy::I32 { (sa % sb) as u64 } else { sa.wrapping_rem(sb) as u64 }
        }
        And => a & b,
        Or => a | b,
        Xor => a ^ b,
        Shl => a << (b % bits),
        ShrU => a >> (b % bits),
        ShrS => (sa >> (b % bits)) as u64,
        Rotl => {
            if w == ValTy::I32 { (a as u32).rotate_left(b as u32 % 32) as u64 } else { a.rotate_left((b % 64) as u32) }
        }
        Rotr => {
            if w == ValTy::I32 { (a as u32).rotate_right(b as u32 % 32) as u64 } else { a.rotate_right((b % 64) as u32) }
        }
        Clz => {
            if w == ValTy::I32 { (a as u32).leading_zeros() as u64 } else { a.leading_zeros() as u64 }
        }
        Ctz => {
            if w == ValTy::I32 { (a as u32).trailing_zeros() as u64 } else { a.trailing_zeros() as u64 }
        }
        Popcnt => a.count_ones() as u64,
        Eqz => bool(a == 0),
        Eq => bool(a == b),
        Ne => bool(a != b),
        LtU => bool(a < b),
        GtU => bool(a > b),
        LeU => bool(a <= b),
        GeU => bool(a >= b),
        LtS => bool(sa < sb),
        GtS => bool(sa > sb),
        LeS => bool(sa <= sb),
        GeS => bool(sa >= sb),
        Extend8S => a as u8 as i8 as i64 as u64,
        Extend16S => a as u16 as i16 as i64 as u64,
        Extend32S => a as u32 as i32 as i64 as u64,
        WrapI64 => a & 0xffff_ffff,
        ExtendI32S => a as u32 as i32 as i64 as u64,
        ExtendI32U => a & 0xffff_ffff,
    };
    Ok(r & mask(op.result(w)))
}

/// Matching `else`/`end` positions for every block in a body.
pub fn block_table(body: &[(u32, Ins)]) -> Vec<(usize, usize)> {
    let mut tab = vec![(usize::MAX, usize::MAX); body.len()];
    let mut stack: Vec<usize> = Vec::new();
    for (i, (_, ins)) in body.iter().enumerate() {
        match ins {
            Ins::Block(..) => stack.push(i),
            Ins::Else => {
                if let Some(&b) = stack.last() {
                    tab[b].0 = i;
                }
            }
            Ins::End => {
                if let Some(b) = stack.pop() {
                    tab[b].1 = i;
                    if tab[b].0 == usize::MAX {
                        tab[b].0 = i;
                    }
                    tab[i] = (b, b);
                }
            }
            _ => {}
        }
    }
    tab
}

/// Value-local slots of a function: (name, type) for params then locals; fact params/locals excluded.
pub fn value_locals(m: &Module, f: usize) -> Vec<(Option<String>, ValTy)> {
    let func = &m.funcs[f];
    let mut v = Vec::new();
    for p in &func.header.params {
        if let Decl::Val(r) = &p.decl {
            v.push((p.name.clone(), r.ty));
        }
    }
    for l in &func.locals {
        if let LocalKind::Val(r) = &l.kind {
            v.push((l.name.clone(), r.ty));
        }
    }
    v
}

pub fn resolve_local(locals: &[(Option<String>, ValTy)], name: &str) -> Option<usize> {
    if name.starts_with('$') {
        locals.iter().position(|(n, _)| n.as_deref() == Some(name))
    } else {
        name.parse().ok().filter(|i: &usize| *i < locals.len())
    }
}

struct Ctl {
    kind: BlockKind,
    label: Option<String>,
    start: usize,
    end: usize,
    height: usize,
    arity: usize,
}

/// The reference interpreter. With a [`RuntimePlan`] it is also a model of the instrumented
/// program of gradual mode: shadow captures and checks run exactly where the instrumentation puts them.
pub struct Interp<'m> {
    pub m: &'m Module,
    pub steps: u32,
    pub budget: u32,
    /// linear memory (empty: none)
    pub mem: Vec<u8>,
    pub globals: Vec<u64>,
    pub plan: Option<&'m RuntimePlan>,
    /// checks evaluated (and held) during this run
    pub checks_run: u32,
    tables: Vec<Option<Vec<(usize, usize)>>>,
    depth: u32,
}

impl<'m> Interp<'m> {
    pub fn new(m: &'m Module) -> Self {
        let globals = m.globals.iter().map(|g| g.init.unwrap_or(0)).collect();
        Interp { m, steps: 0, budget: EVAL_BUDGET, mem: vec![], globals, plan: None, checks_run: 0, tables: vec![None; m.funcs.len()], depth: 0 }
    }

    /// An interpreter for a whole run: memory of the declared minimum size, checks from `plan`.
    pub fn for_run(m: &'m Module, plan: Option<&'m RuntimePlan>) -> Self {
        let mut it = Interp::new(m);
        it.mem = vec![0; (m.memory_min.unwrap_or(0) * 65536) as usize];
        it.plan = plan;
        it.budget = 10_000_000;
        it
    }

    pub fn call(&mut self, f: usize, args: &[u64]) -> Result<Vec<u64>, EvalErr> {
        let func = &self.m.funcs[f];
        if func.imported {
            return Err(EvalErr::Unsupported(format!("{} is imported", func.name())));
        }
        if self.depth > 2000 {
            return Err(EvalErr::Budget);
        }
        if self.tables[f].is_none() {
            self.tables[f] = Some(block_table(&func.body));
        }
        let tab = self.tables[f].clone().unwrap();
        let locs = value_locals(self.m, f);
        let mut locals: Vec<u64> = vec![0; locs.len()];
        for (i, a) in args.iter().enumerate().take(locs.len()) {
            locals[i] = *a & mask(locs[i].1);
        }
        let nres = func.value_results().len();
        self.depth += 1;
        let r = self.run(f, &tab, &locs, &mut locals, nres);
        self.depth -= 1;
        r
    }

    fn capture(&self, acts: &[ShadowAct], locals: &[u64], st: &[u64], shadows: &mut [u64]) {
        for a in acts {
            let v = match a.how {
                Capture::Param(i) | Capture::Local(i) => locals.get(i as usize).copied(),
                Capture::Top => st.last().copied(),
                Capture::Global(i) => self.globals.get(i as usize).copied(),
            };
            if let (Some(v), Some(s)) = (v, shadows.get_mut(a.shadow as usize)) {
                *s = v;
            }
        }
    }

    fn after(&self, f: usize, line: u32, locals: &[u64], st: &[u64], shadows: &mut [u64]) {
        if let Some(fp) = self.plan.and_then(|p| p.func_plan(f as u32))
            && let Some(acts) = fp.after.get(&line)
        {
            self.capture(acts, locals, st, shadows);
        }
    }

    fn checks(&mut self, f: usize, line: u32, shadows: &[u64]) -> Result<(), EvalErr> {
        let Some(plan) = self.plan else { return Ok(()) };
        let Some(ids) = plan.func_plan(f as u32).and_then(|fp| fp.before.get(&line)) else { return Ok(()) };
        for &id in ids {
            let c = &plan.checks[id as usize];
            let vals: Vec<u64> = c.sends.iter().map(|(_, s, _)| shadows[*s as usize]).collect();
            self.checks_run += 1;
            if let CheckOutcome::Fails(msg) = plan.eval_check(id, &vals, Some(&self.mem)) {
                return Err(EvalErr::CheckFailed { line, msg });
            }
        }
        Ok(())
    }

    fn run(
        &mut self,
        f: usize,
        tab: &[(usize, usize)],
        locs: &[(Option<String>, ValTy)],
        locals: &mut [u64],
        nres: usize,
    ) -> Result<Vec<u64>, EvalErr> {
        let m = self.m;
        let body = &m.funcs[f].body;
        let fplan = self.plan.and_then(|p| p.func_plan(f as u32));
        let mut shadows: Vec<u64> = vec![0; fplan.map(|p| p.shadow_tys.len()).unwrap_or(0)];
        if let Some(fp) = fplan {
            self.capture(&fp.entry, locals, &[], &mut shadows);
        }
        let mut st: Vec<u64> = Vec::new();
        let mut ctl: Vec<Ctl> = vec![Ctl { kind: BlockKind::Block, label: None, start: 0, end: body.len(), height: 0, arity: nres }];
        let mut pc = 0usize;
        let pop = |st: &mut Vec<u64>| st.pop().ok_or_else(|| EvalErr::Unsupported("stack underflow".into()));
        let line_of = |i: usize| body.get(i).map(|x| x.0).unwrap_or(0);
        loop {
            if pc >= body.len() {
                self.checks(f, m.funcs[f].end_line, &shadows)?;
                let n = st.len();
                return Ok(st[n.saturating_sub(nres)..].to_vec());
            }
            self.steps += 1;
            if self.steps > self.budget {
                return Err(EvalErr::Budget);
            }
            let (line, ins) = (body[pc].0, &body[pc].1);
            self.checks(f, line, &shadows)?;
            // a branch: Some(depth)
            let mut branch: Option<usize> = None;
            match ins {
                Ins::Nop | Ins::Prove(_) | Ins::Lemma(..) | Ins::Unfold(..) | Ins::Assume(_) => {}
                Ins::Unreachable => return Err(EvalErr::Trap("unreachable".into())),
                Ins::Drop => {
                    pop(&mut st)?;
                }
                Ins::Select => {
                    let c = pop(&mut st)?;
                    let b = pop(&mut st)?;
                    let a = pop(&mut st)?;
                    st.push(if c as u32 != 0 { a } else { b });
                }
                Ins::Return => {
                    let n = st.len();
                    return Ok(st[n.saturating_sub(nres)..].to_vec());
                }
                Ins::Block(kind, bt) => {
                    let (els, end) = tab[pc];
                    let mut taken = true;
                    if *kind == BlockKind::If {
                        taken = pop(&mut st)? as u32 != 0;
                    }
                    let arity = if *kind == BlockKind::Loop { bt.params.len() } else { bt.results.len() };
                    ctl.push(Ctl { kind: *kind, label: bt.label.clone(), start: pc, end, height: st.len() - bt.params.len(), arity });
                    if !taken {
                        if els == end {
                            ctl.pop();
                            pc = end + 1;
                            self.after(f, line_of(end), locals, &st, &mut shadows);
                            continue;
                        }
                        pc = els + 1;
                        continue;
                    }
                }
                Ins::Else => {
                    // end of the then-arm: jump past the end
                    let c = ctl.pop().unwrap();
                    pc = c.end + 1;
                    self.after(f, line_of(c.end), locals, &st, &mut shadows);
                    continue;
                }
                Ins::End => {
                    ctl.pop();
                }
                Ins::Br(l) => branch = Some(self.label(&ctl, l)?),
                Ins::BrIf(l) => {
                    if pop(&mut st)? as u32 != 0 {
                        branch = Some(self.label(&ctl, l)?);
                    }
                }
                Ins::BrTable(ls) => {
                    let i = pop(&mut st)? as u32 as usize;
                    let l = ls.get(i).unwrap_or(ls.last().unwrap());
                    branch = Some(self.label(&ctl, l)?);
                }
                Ins::Call(name) => {
                    let g = m.func_index(name).ok_or_else(|| EvalErr::Unsupported(format!("no function {name}")))?;
                    let np = m.funcs[g].value_params().count();
                    if st.len() < np {
                        return Err(EvalErr::Unsupported("stack underflow".into()));
                    }
                    let args = st.split_off(st.len() - np);
                    let r = self.call(g, &args)?;
                    st.extend(r);
                }
                Ins::LocalGet(n) | Ins::LocalSet(n) | Ins::LocalTee(n) => {
                    if let Some(i) = resolve_local(locs, n) {
                        match ins {
                            Ins::LocalGet(_) => st.push(locals[i]),
                            Ins::LocalSet(_) => locals[i] = pop(&mut st)?,
                            _ => locals[i] = *st.last().ok_or_else(|| EvalErr::Unsupported("stack underflow".into()))?,
                        }
                    }
                }
                Ins::GlobalGet(n) | Ins::GlobalSet(n) => {
                    let gi = m.globals.iter().position(|g| g.name.as_deref() == Some(n.as_str()))
                        .or_else(|| n.parse().ok())
                        .filter(|i| *i < m.globals.len())
                        .ok_or_else(|| EvalErr::Unsupported(format!("no global {n}")))?;
                    if matches!(ins, Ins::GlobalGet(_)) {
                        if m.globals[gi].mutable && self.plan.is_none() {
                            return Err(EvalErr::Unsupported("mutable global".into()));
                        }
                        st.push(self.globals[gi]);
                    } else {
                        self.globals[gi] = pop(&mut st)?;
                    }
                }
                Ins::Load(ma) => {
                    let a = pop(&mut st)? as u32 as u64 + ma.offset;
                    if a + ma.bytes as u64 > self.mem.len() as u64 {
                        return Err(EvalErr::Trap("out of bounds memory access".into()));
                    }
                    let mut v: u64 = 0;
                    for k in 0..ma.bytes as usize {
                        v |= (self.mem[a as usize + k] as u64) << (8 * k);
                    }
                    if ma.signed {
                        let sh = 64 - 8 * ma.bytes;
                        v = (((v << sh) as i64) >> sh) as u64;
                    }
                    st.push(v & mask(ma.ty));
                }
                Ins::Store(ma) => {
                    let v = pop(&mut st)?;
                    let a = pop(&mut st)? as u32 as u64 + ma.offset;
                    if a + ma.bytes as u64 > self.mem.len() as u64 {
                        return Err(EvalErr::Trap("out of bounds memory access".into()));
                    }
                    for k in 0..ma.bytes as usize {
                        self.mem[a as usize + k] = (v >> (8 * k)) as u8;
                    }
                }
                Ins::MemorySize => st.push(self.mem.len() as u64 / 65536),
                Ins::Const(_, b) => st.push(*b),
                Ins::Int(op, w) => {
                    let n = if op.unary() { 1 } else { 2 };
                    if st.len() < n {
                        return Err(EvalErr::Unsupported("stack underflow".into()));
                    }
                    let args = st.split_off(st.len() - n);
                    st.push(eval_iop(*op, *w, &args)?);
                }
                other => return Err(EvalErr::Unsupported(format!("{other:?}"))),
            }
            if let Some(d) = branch {
                if d + 1 >= ctl.len() {
                    let n = st.len();
                    return Ok(st[n.saturating_sub(nres)..].to_vec());
                }
                let idx = ctl.len() - 1 - d;
                let c = &ctl[idx];
                let keep: Vec<u64> = st[st.len() - c.arity..].to_vec();
                st.truncate(c.height);
                st.extend(keep);
                if c.kind == BlockKind::Loop {
                    pc = c.start + 1;
                    let l = line_of(c.start);
                    ctl.truncate(idx + 1);
                    self.after(f, l, locals, &st, &mut shadows);
                } else {
                    pc = c.end + 1;
                    let l = line_of(c.end);
                    ctl.truncate(idx);
                    self.after(f, l, locals, &st, &mut shadows);
                }
                continue;
            }
            self.after(f, line, locals, &st, &mut shadows);
            pc += 1;
        }
    }

    fn label(&self, ctl: &[Ctl], l: &str) -> Result<usize, EvalErr> {
        if l.starts_with('$') {
            ctl.iter().rev().position(|c| c.label.as_deref() == Some(l)).ok_or_else(|| EvalErr::Unsupported(format!("no label {l}")))
        } else {
            l.parse().map_err(|_| EvalErr::Unsupported(format!("bad label {l}")))
        }
    }
}
