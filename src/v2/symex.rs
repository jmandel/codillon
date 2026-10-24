//! Symbolic execution of a predicate body to a term (R29 automatic unfolding, R30 `unfold`).
//! Straight-line code becomes terms; `if … else … end` becomes `ite`. Calls stay as call terms
//! (the decision procedure unfolds non-recursive ones lazily, to depth 4).

use super::ast::{BlockKind, Ins, Module, ValTy};
use super::eval::{block_table, resolve_local, value_locals};
use super::info::FnInfo;
use super::term::{Key, NO_EPOCH, TermId, Terms};

struct St {
    stack: Vec<TermId>,
    locals: Vec<TermId>,
}

pub fn call_term(m: &Module, info: &[FnInfo], terms: &mut Terms, g: usize, args: &[TermId], epoch: u32) -> Option<TermId> {
    let ty = *m.funcs[g].value_results().first().map(|r| &r.ty)?;
    let ep = if info[g].reads_mem { epoch } else { NO_EPOCH };
    Some(terms.intern(Key::Call(g as u32, args.iter().copied().collect(), ep), ty))
}

/// The result term of `f(args)` evaluated symbolically in memory epoch `epoch`; None if the body
/// has a shape the unfolder does not handle (loops, branches other than `if`, …).
pub fn symex(m: &Module, info: &[FnInfo], terms: &mut Terms, f: usize, args: &[TermId], epoch: u32) -> Option<TermId> {
    let func = &m.funcs[f];
    if func.imported || info[f].impure.is_some() || info[f].has_loop.is_some() {
        return None;
    }
    let locs = value_locals(m, f);
    let mut locals: Vec<TermId> = Vec::with_capacity(locs.len());
    for (i, (_, ty)) in locs.iter().enumerate() {
        locals.push(match args.get(i) {
            Some(a) if i < func.value_params().count() => *a,
            _ => terms.konst(*ty, 0),
        });
    }
    let tab = block_table(&func.body);
    let mut st = St { stack: vec![], locals };
    exec(m, info, terms, f, &locs, &tab, 0, func.body.len(), &mut st, epoch)?;
    st.stack.last().copied()
}

#[allow(clippy::too_many_arguments)]
fn exec(
    m: &Module,
    info: &[FnInfo],
    terms: &mut Terms,
    f: usize,
    locs: &[(Option<String>, ValTy)],
    tab: &[(usize, usize)],
    from: usize,
    to: usize,
    st: &mut St,
    epoch: u32,
) -> Option<()> {
    let body = &m.funcs[f].body;
    let mut pc = from;
    while pc < to {
        match &body[pc].1 {
            Ins::Nop | Ins::Prove(_) | Ins::Lemma(..) | Ins::Unfold(..) | Ins::Assume(_) => {}
            Ins::Drop => {
                st.stack.pop()?;
            }
            Ins::Const(ty, b) => st.stack.push(terms.konst(*ty, *b)),
            Ins::LocalGet(n) => match resolve_local(locs, n) {
                Some(i) => st.stack.push(st.locals[i]),
                None => {}
            },
            Ins::LocalSet(n) | Ins::LocalTee(n) => {
                if let Some(i) = resolve_local(locs, n) {
                    let v = if matches!(body[pc].1, Ins::LocalSet(_)) { st.stack.pop()? } else { *st.stack.last()? };
                    st.locals[i] = v;
                }
            }
            Ins::Int(op, w) => {
                let n = if op.unary() { 1 } else { 2 };
                if st.stack.len() < n {
                    return None;
                }
                let a = st.stack.split_off(st.stack.len() - n);
                st.stack.push(terms.op(*op, *w, &a));
            }
            Ins::Float { name, ins, out, trap: false } => {
                let a = st.stack.split_off(st.stack.len().checked_sub(ins.len())?);
                st.stack.push(terms.intern(Key::Float(name.clone(), a.into_iter().collect()), *out));
            }
            Ins::Select => {
                let c = st.stack.pop()?;
                let b = st.stack.pop()?;
                let a = st.stack.pop()?;
                let ty = terms.ty(a);
                st.stack.push(terms.intern(Key::Ite(c, a, b), ty));
            }
            Ins::Load(ma) => {
                let a = st.stack.pop()?;
                st.stack.push(terms.intern(Key::Load(ma.ty, ma.bytes, ma.signed, ma.offset, a, epoch), ma.ty));
            }
            Ins::GlobalGet(g) => {
                let gl = m.globals.iter().find(|x| x.name.as_deref() == Some(g.as_str()))?;
                if gl.mutable {
                    return None;
                }
                st.stack.push(terms.konst(gl.ty.ty, gl.init?));
            }
            Ins::Call(c) => {
                let g = m.func_index(c)?;
                if info[g].impure.is_some() {
                    return None;
                }
                let np = m.funcs[g].value_params().count();
                let a = st.stack.split_off(st.stack.len().checked_sub(np)?);
                let t = call_term(m, info, terms, g, &a, epoch)?;
                st.stack.push(t);
            }
            Ins::Block(BlockKind::If, bt) if bt.params.is_empty() => {
                let c = st.stack.pop()?;
                let (els, end) = tab[pc];
                let mut a = St { stack: st.stack.clone(), locals: st.locals.clone() };
                exec(m, info, terms, f, locs, tab, pc + 1, els, &mut a, epoch)?;
                let mut b = St { stack: st.stack.clone(), locals: st.locals.clone() };
                if els != end {
                    exec(m, info, terms, f, locs, tab, els + 1, end, &mut b, epoch)?;
                }
                if a.stack.len() != b.stack.len() {
                    return None;
                }
                let merge = |terms: &mut Terms, x: TermId, y: TermId| {
                    if x == y { x } else { let ty = terms.ty(x); terms.intern(Key::Ite(c, x, y), ty) }
                };
                st.stack = a.stack.iter().zip(b.stack.iter()).map(|(x, y)| merge(terms, *x, *y)).collect();
                st.locals = a.locals.iter().zip(b.locals.iter()).map(|(x, y)| merge(terms, *x, *y)).collect();
                pc = end + 1;
                continue;
            }
            Ins::Block(BlockKind::Block, bt) if bt.params.is_empty() => {
                // a plain block without branches out of it
                let (_, end) = tab[pc];
                exec(m, info, terms, f, locs, tab, pc + 1, end, st, epoch)?;
                pc = end + 1;
                continue;
            }
            Ins::End => {}
            _ => return None,
        }
        pc += 1;
    }
    Some(())
}
