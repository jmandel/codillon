//! Per-module pre-scans (§5.2): purity, memory reads, loops, recursion, predicates and measures.

use super::ast::{Decl, Expr, Ins, LocalKind, Module};

#[derive(Clone, Debug, Default)]
pub struct FnInfo {
    /// stores, grows, sets or reads a mutable global, calls an import or an impure function (R13)
    pub impure: Option<(u32, String)>,
    /// contains a load, directly or through callees (R12)
    pub reads_mem: bool,
    pub has_loop: Option<u32>,
    /// directly self-recursive (a `call` to itself, or a `lemma` line naming itself)
    pub self_rec: bool,
    pub calls: Vec<usize>,
    /// `lemma $g` lines (ghost calls): edges for recursion through lemmas (R31, R33)
    pub lemma_calls: Vec<usize>,
    /// named in some proposition (R29)
    pub is_pred: bool,
    /// reaches itself through another function (mutual recursion): that function
    pub mutual_rec: Option<usize>,
    /// functions named in this function's propositions (its contract and proof lines)
    pub uses: Vec<usize>,
    /// the `measure:<f>` function of this one
    pub measure: Option<usize>,
    /// this function is `measure:` for some function
    pub is_measure: bool,
}

pub fn expr_calls(e: &Expr, out: &mut Vec<String>) {
    match e {
        Expr::Call(f, a) => {
            out.push(f.clone());
            a.iter().for_each(|x| expr_calls(x, out));
        }
        Expr::Op(_, a) => a.iter().for_each(|x| expr_calls(x, out)),
        _ => {}
    }
}

pub fn analyze(m: &Module) -> Vec<FnInfo> {
    let n = m.funcs.len();
    let mut info = vec![FnInfo::default(); n];
    let mut named: Vec<String> = vec![];
    for (i, f) in m.funcs.iter().enumerate() {
        let before = named.len();
        let fi = &mut info[i];
        if f.imported {
            fi.impure = Some((f.header_line, "is imported".into()));
        }
        for p in &f.header.params {
            match &p.decl {
                Decl::Val(r) => r.refine.iter().for_each(|e| expr_calls(e, &mut named)),
                Decl::Fact(e) => expr_calls(e, &mut named),
            }
        }
        for r in &f.header.results {
            match r {
                Decl::Val(r) => r.refine.iter().for_each(|e| expr_calls(e, &mut named)),
                Decl::Fact(e) => expr_calls(e, &mut named),
            }
        }
        for l in &f.locals {
            if let LocalKind::Val(r) = &l.kind {
                r.refine.iter().for_each(|e| expr_calls(e, &mut named));
            }
        }
        for (ln, ins) in &f.body {
            match ins {
                Ins::Block(k, bt) => {
                    if *k == super::ast::BlockKind::Loop && fi.has_loop.is_none() {
                        fi.has_loop = Some(*ln);
                    }
                    bt.facts.iter().for_each(|e| expr_calls(e, &mut named));
                    for r in bt.params.iter().chain(bt.results.iter()) {
                        r.refine.iter().for_each(|e| expr_calls(e, &mut named));
                    }
                }
                Ins::Store(_) | Ins::MemoryFill | Ins::MemoryCopy | Ins::MemoryGrow
                    if fi.impure.is_none() =>
                {
                    fi.impure = Some((*ln, "stores".into()));
                }
                Ins::GlobalSet(_) if fi.impure.is_none() => {
                    fi.impure = Some((*ln, "sets a global".into()))
                }
                Ins::GlobalGet(g) => {
                    let mutable = m
                        .globals
                        .iter()
                        .find(|x| x.name.as_deref() == Some(g.as_str()))
                        .or_else(|| g.parse::<usize>().ok().and_then(|i| m.globals.get(i)))
                        .is_none_or(|x| x.mutable);
                    if mutable && fi.impure.is_none() {
                        fi.impure = Some((*ln, "reads a mutable global".into()));
                    }
                }
                Ins::CallIndirect if fi.impure.is_none() => {
                    fi.impure = Some((*ln, "uses call_indirect".into()))
                }
                Ins::Load(_) | Ins::MemorySize => fi.reads_mem = true,
                Ins::Call(c) => {
                    if let Some(g) = m.func_index(c) {
                        fi.calls.push(g);
                        if g == i {
                            fi.self_rec = true;
                        }
                    }
                }
                Ins::Lemma(c, args) | Ins::Unfold(c, args) => {
                    if matches!(ins, Ins::Lemma(..))
                        && let Some(g) = m.func_index(c)
                    {
                        fi.lemma_calls.push(g);
                        if g == i {
                            fi.self_rec = true;
                        }
                    }
                    if matches!(ins, Ins::Unfold(..)) {
                        named.push(c.clone());
                    }
                    args.iter().for_each(|e| expr_calls(e, &mut named));
                }
                Ins::Assume(e) => expr_calls(e, &mut named),
                _ => {}
            }
        }
        let uses: Vec<usize> = named[before..]
            .iter()
            .filter_map(|n| m.func_index(n))
            .collect();
        info[i].uses = uses;
    }
    // propagate impurity and memory reads along calls
    loop {
        let mut changed = false;
        for i in 0..n {
            for &g in &info[i].calls.clone() {
                if info[i].impure.is_none()
                    && let Some(_) = info[g].impure
                {
                    let line = m.funcs[i]
                        .body
                        .iter()
                        .find(|(_, ins)| matches!(ins, Ins::Call(c) if m.func_index(c) == Some(g)))
                        .map(|x| x.0)
                        .unwrap_or(0);
                    info[i].impure = Some((
                        line,
                        format!("calls {}, which is impure", m.funcs[g].name()),
                    ));
                    changed = true;
                }
                if !info[i].reads_mem && info[g].reads_mem {
                    info[i].reads_mem = true;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    // mutual recursion: f reaches itself through a call or lemma path of length ≥ 2
    let edges = |x: &FnInfo| -> Vec<usize> {
        x.calls
            .iter()
            .chain(x.lemma_calls.iter())
            .copied()
            .collect()
    };
    for f in 0..n {
        for g in edges(&info[f]) {
            if g == f {
                continue;
            }
            let mut seen = vec![false; n];
            let mut work = vec![g];
            while let Some(x) = work.pop() {
                if x == f {
                    info[f].mutual_rec = Some(g);
                    break;
                }
                if std::mem::replace(&mut seen[x], true) {
                    continue;
                }
                work.extend(edges(&info[x]));
            }
            if info[f].mutual_rec.is_some() {
                break;
            }
        }
    }
    // a global's refinement names predicates too (R9, R29; research/22 S2)
    for g in &m.globals {
        g.ty.refine.iter().for_each(|e| expr_calls(e, &mut named));
    }
    for name in named {
        if let Some(g) = m.func_index(&name) {
            info[g].is_pred = true;
        }
    }
    for (i, f) in m.funcs.iter().enumerate() {
        if let Some(target) = f.export_role("measure:")
            && let Some(g) = m.func_index(&format!("${target}"))
        {
            info[g].measure = Some(i);
            info[i].is_measure = true;
        }
    }
    // R29: a predicate or measure may call only predicates, so totality is inductive. A function
    // reached by `call` from one is therefore itself a predicate (helpers like gcd's `$common` are
    // never named in a proposition) and gets every R29 check; an ordinary function that loops or
    // recurses unmeasured is then rejected on its own header instead of lending its vacuous
    // contract to the predicate (research/22 B1).
    let mut work: Vec<usize> = (0..n)
        .filter(|&i| info[i].is_pred || info[i].is_measure)
        .collect();
    while let Some(i) = work.pop() {
        for g in info[i].calls.clone() {
            if !info[g].is_pred && !m.funcs[g].is_lemma() && !m.funcs[g].is_axiom() {
                info[g].is_pred = true;
                work.push(g);
            }
        }
    }
    info
}
