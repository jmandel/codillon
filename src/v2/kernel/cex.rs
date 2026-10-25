//! Counterexamples (design 16 §3.7). The solver's countermodel is a model of its relaxation:
//! an opaque term (`xor`, a call it does not unfold, …) may take a value its arguments cannot
//! produce. So a countermodel is shown only after concrete evaluation confirms it: the free
//! values of the cup's facts and goal (parameters, local versions, call results) get the
//! model's values, the facts and goal are evaluated with the reference interpreter, and the
//! facts must hold while the goal fails. Otherwise the kernel searches boundary values for a
//! real counterexample, and says so honestly when it finds none.

use super::super::adequacy::{EDGES, module_consts};
use super::super::eval::{eval_fop, eval_iop};
use super::super::out::{Cex, signed_text};
use super::super::pretty::num;
use super::super::term::{Rel, mask};
use super::*;

/// Assignments the boundary search evaluates for one cup, at most.
const SEARCH_BUDGET: usize = 1024;
/// Interpreter steps the search may spend in calls, over all its assignments.
const SEARCH_STEPS: u32 = 400_000;
/// Free values beyond which the search does not run.
const MAX_FREE: usize = 6;

/// Why an evaluation did not produce a value.
enum Ev {
    /// a division by zero, an overflow or an `unreachable` in a call: the atom is false
    Trap,
    /// a value the kernel cannot compute (memory, an unsupported operation, the step budget)
    Stuck,
}

/// What the check and the search found for one unproved goal.
pub(super) enum Found {
    Cex(Cex),
    /// neither the solver's model nor any boundary value tried is a counterexample
    Nothing,
    /// nothing to evaluate: no free values, or values the kernel cannot compute (memory)
    Unevaluable,
}

impl Found {
    /// The diagnostic's account of it. `allow` is the phrase for values that are not all
    /// inputs (`the 3 facts about these values allow`).
    pub(super) fn text(&self, allow: &str) -> Option<String> {
        match self {
            Found::Cex(c) => {
                let vals = c.vals_text();
                let mut s = if c.inputs || allow.is_empty() {
                    format!("it fails for {vals}")
                } else {
                    format!("{allow} {vals}")
                };
                if !c.wraps.is_empty() {
                    s = format!("{s}: {}", c.wraps.join(", "));
                }
                Some(s)
            }
            Found::Nothing => {
                Some("no counterexample found among the boundary values tried".into())
            }
            Found::Unevaluable => None,
        }
    }
}

/// A w-bit value in its signed reading.
fn signed(bits: u64, w: u32) -> i128 {
    if w == 32 {
        bits as u32 as i32 as i128
    } else {
        bits as i64 as i128
    }
}

/// The boundary values of a w-bit type (signed readings): 0, ±1, ±2, 2ᵏ and 2ᵏ ± 1 near the
/// byte, half-word and word edges, the extremes, the harness edges (§6.3) and the module's
/// constants; smallest magnitude first, a positive value before its negation.
fn boundary_values(w: u32, extra: &[i64]) -> Vec<i128> {
    let wv = 1i128 << w;
    let norm = |v: i128| {
        let u = v.rem_euclid(wv);
        if u >= wv / 2 { u - wv } else { u }
    };
    let mut ks = vec![7u32, 8, 15, 16, 30, 31];
    if w == 64 {
        ks.extend([32, 62, 63]);
    }
    let mut v: Vec<i128> = vec![0, 1, 2];
    for k in ks {
        let p = 1i128 << k;
        v.extend([p - 1, p, p + 1]);
    }
    v.extend([wv / 2 - 1, wv / 2, wv - 1]);
    v.extend(EDGES.iter().map(|x| *x as i128));
    v.extend(extra.iter().map(|x| *x as i128));
    let mut out: Vec<i128> = v.iter().flat_map(|x| [*x, -*x]).map(norm).collect();
    out.sort_by_key(|x| (x.unsigned_abs(), *x < 0));
    out.dedup();
    out
}

impl<'a, 'm> Pass<'a, 'm> {
    /// The free values of the atoms (leaves, through operations, `ite` and pure calls' arguments),
    /// in id order; None if some value reads memory (a load, a memory-reading call).
    fn free_values(&self, atoms: &[&Atom]) -> Option<Vec<TermId>> {
        let mut roots = vec![];
        for a in atoms {
            roots.extend(self.atom_terms(a));
        }
        let mut seen = BTreeSet::new();
        let mut leaves = BTreeSet::new();
        while let Some(t) = roots.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.terms.key(t) {
                Key::Const(..) => {}
                Key::Leaf(_) => {
                    leaves.insert(t);
                }
                Key::Op(_, _, a) | Key::Float(_, a) => roots.extend(a.iter().copied()),
                Key::Call(_, a, ep) => {
                    if *ep != NO_EPOCH {
                        return None;
                    }
                    roots.extend(a.iter().copied());
                }
                Key::Ite(c, a, b) => roots.extend([*c, *a, *b]),
                Key::Load(..) => return None,
            }
        }
        Some(leaves.into_iter().collect())
    }

    fn atom_terms(&self, a: &Atom) -> Vec<TermId> {
        match a {
            Atom::Cmp { a, b, .. } => vec![*a, *b],
            Atom::Bool { t, .. } => vec![*t],
            Atom::Or(x, y) => {
                let mut v = self.atom_terms(x);
                v.extend(self.atom_terms(y));
                v
            }
            Atom::True | Atom::False => vec![],
        }
    }

    /// A term's value under an assignment of its free values.
    fn ev_term(
        &self,
        it: &mut Interp,
        t: TermId,
        env: &HashMap<TermId, u64>,
        memo: &mut HashMap<TermId, u64>,
    ) -> Result<u64, Ev> {
        if let Some(v) = memo.get(&t).or_else(|| env.get(&t)) {
            return Ok(*v);
        }
        let v = match self.terms.key(t).clone() {
            Key::Const(_, b) => b,
            Key::Leaf(_) | Key::Load(..) => return Err(Ev::Stuck),
            Key::Op(op, w, args) => {
                let vals: Vec<u64> = args
                    .iter()
                    .map(|a| self.ev_term(it, *a, env, memo))
                    .collect::<Result<_, _>>()?;
                match eval_iop(op, w, &vals) {
                    Ok(v) => v,
                    Err(EvalErr::Trap(_)) => return Err(Ev::Trap),
                    Err(_) => return Err(Ev::Stuck),
                }
            }
            Key::Ite(c, a, b) => {
                let c = self.ev_term(it, c, env, memo)?;
                self.ev_term(it, if c != 0 { a } else { b }, env, memo)?
            }
            Key::Float(name, args) => {
                let vals: Vec<u64> = args
                    .iter()
                    .map(|a| self.ev_term(it, *a, env, memo))
                    .collect::<Result<_, _>>()?;
                match eval_fop(&name, &vals) {
                    Ok(v) => v,
                    Err(true) => return Err(Ev::Trap),
                    Err(false) => return Err(Ev::Stuck),
                }
            }
            Key::Call(f, args, ep) => {
                if ep != NO_EPOCH {
                    return Err(Ev::Stuck);
                }
                let vals: Vec<u64> = args
                    .iter()
                    .map(|a| self.ev_term(it, *a, env, memo))
                    .collect::<Result<_, _>>()?;
                match it.call(f as usize, &vals) {
                    Ok(r) => *r.first().ok_or(Ev::Stuck)?,
                    Err(EvalErr::Trap(_)) => return Err(Ev::Trap),
                    Err(_) => return Err(Ev::Stuck),
                }
            }
        };
        memo.insert(t, v);
        Ok(v)
    }

    /// An atom's truth under an assignment; a fact that traps is false.
    fn ev_atom(
        &self,
        it: &mut Interp,
        a: &Atom,
        env: &HashMap<TermId, u64>,
        memo: &mut HashMap<TermId, u64>,
    ) -> Result<bool, Ev> {
        let r = match a {
            Atom::True => Ok(true),
            Atom::False => Ok(false),
            Atom::Bool { t, neg } => self.ev_term(it, *t, env, memo).map(|v| (v != 0) != *neg),
            Atom::Or(x, y) => match self.ev_atom(it, x, env, memo)? {
                true => Ok(true),
                false => self.ev_atom(it, y, env, memo),
            },
            Atom::Cmp {
                rel,
                signed: sg,
                a,
                b,
            } => {
                let ty = self.terms.ty(*a);
                if !ty.is_int() {
                    return Err(Ev::Stuck);
                }
                let w = ty.bits();
                let x = self.ev_term(it, *a, env, memo);
                let y = self.ev_term(it, *b, env, memo);
                match (x, y) {
                    (Ok(x), Ok(y)) => {
                        let (x, y) = if *sg {
                            (signed(x, w), signed(y, w))
                        } else {
                            (x as i128, y as i128)
                        };
                        Ok(match rel {
                            Rel::Eq => x == y,
                            Rel::Ne => x != y,
                            Rel::Lt => x < y,
                            Rel::Le => x <= y,
                        })
                    }
                    (Err(Ev::Stuck), _) | (_, Err(Ev::Stuck)) => Err(Ev::Stuck),
                    _ => Err(Ev::Trap),
                }
            }
        };
        match r {
            Err(Ev::Trap) => Ok(false),
            r => r,
        }
    }

    /// Do the facts hold and the goal fail under `env`? Some(memo of the values) if so.
    fn refutes(
        &self,
        steps: &mut u32,
        hyps: &[Atom],
        goal: &Atom,
        env: &HashMap<TermId, u64>,
    ) -> Result<Option<HashMap<TermId, u64>>, Ev> {
        let mut it = Interp::new(self.cx.m);
        let mut memo = HashMap::new();
        let r = (|| {
            for h in hyps {
                if !self.ev_atom(&mut it, h, env, &mut memo)? {
                    return Ok(false);
                }
            }
            Ok(!self.ev_atom(&mut it, goal, env, &mut memo)?)
        })();
        *steps = steps.saturating_add(it.steps);
        Ok(if r? { Some(memo) } else { None })
    }

    /// Check the solver's countermodel by evaluation; if it is not a real counterexample, look
    /// for one among boundary values (§6.3's edges among them).
    pub(super) fn countermodel(
        &mut self,
        hyps: &[Atom],
        goal: &Atom,
        model: &[(TermId, i128)],
    ) -> Found {
        let atoms: Vec<&Atom> = hyps.iter().chain([goal]).collect();
        let Some(free) = self.free_values(&atoms) else {
            return Found::Unevaluable;
        };
        if free.is_empty() {
            return Found::Unevaluable;
        }
        let mut steps = 0u32;
        let fill = |t: TermId, v: Option<i128>| -> u64 {
            let term = self.terms.get(t);
            let lo = term.range.map_or(0, |r| r.0 as u64);
            v.map_or(lo, |v| v as u64) & mask(term.ty)
        };
        // the solver's model, on the free values only (its values for other terms are ignored:
        // they are computed)
        let env: HashMap<TermId, u64> = free
            .iter()
            .map(|t| {
                let v = model.iter().find(|(u, _)| u == t).map(|x| x.1);
                (*t, fill(*t, v))
            })
            .collect();
        let size = |env: &HashMap<TermId, u64>| {
            free.iter()
                .map(|t| signed(env[t], self.terms.ty(*t).bits()).unsigned_abs())
                .max()
                .unwrap_or(0)
        };
        let checked = match self.refutes(&mut steps, hyps, goal, &env) {
            Ok(Some(memo)) => Some((env, memo)),
            Err(Ev::Stuck) => return Found::Unevaluable,
            _ => None,
        };
        // the search may find a smaller counterexample than the solver's (a boundary value
        // such as 2³⁰ reads better than −2³¹); it is only tried below the model's size
        let found = if free.len() > MAX_FREE {
            None
        } else {
            self.search(
                &free,
                hyps,
                goal,
                &mut steps,
                checked.as_ref().map(|c| size(&c.0)),
            )
        };
        match found.or(checked) {
            Some((env, memo)) => Found::Cex(self.cex_of(&free, &env, &memo, &atoms)),
            None => Found::Nothing,
        }
    }

    /// The boundary search: assignments of boundary values to the free values, smallest first;
    /// only assignments smaller than `below` (in the largest magnitude) when it is given.
    fn search(
        &self,
        free: &[TermId],
        hyps: &[Atom],
        goal: &Atom,
        steps: &mut u32,
        below: Option<u128>,
    ) -> Option<(HashMap<TermId, u64>, HashMap<TermId, u64>)> {
        // the boundary search
        let extra = module_consts(self.cx.m);
        let lists: Vec<Vec<u64>> = free
            .iter()
            .map(|t| {
                let term = self.terms.get(*t);
                let w = term.ty.bits();
                let mut l: Vec<u64> = boundary_values(w, &extra)
                    .into_iter()
                    .map(|v| (v as u64) & mask(term.ty))
                    .filter(|u| {
                        term.range
                            .is_none_or(|(lo, hi)| (*u as u128) >= lo && (*u as u128) <= hi)
                    })
                    .collect();
                if let Some((lo, hi)) = term.range {
                    for b in [lo as u64, hi as u64] {
                        if !l.contains(&b) {
                            l.push(b);
                        }
                    }
                }
                l
            })
            .collect();
        let n = free.len();
        let mut k = 1usize;
        while (k + 1)
            .checked_pow(n as u32)
            .is_some_and(|p| p <= SEARCH_BUDGET)
        {
            k += 1;
        }
        let kmax = lists.iter().map(|l| l.len()).max().unwrap_or(0).min(k);
        // shells: every assignment whose largest index is s, for s = 0, 1, …
        for s in 0..kmax {
            let mut idx = vec![0usize; n];
            loop {
                if idx.contains(&s) && idx.iter().zip(&lists).all(|(i, l)| *i < l.len()) {
                    let env: HashMap<TermId, u64> = free
                        .iter()
                        .zip(&idx)
                        .zip(&lists)
                        .map(|((t, i), l)| (*t, l[*i]))
                        .collect();
                    let small = below.is_none_or(|b| {
                        free.iter()
                            .all(|t| signed(env[t], self.terms.ty(*t).bits()).unsigned_abs() < b)
                    });
                    if small {
                        match self.refutes(steps, hyps, goal, &env) {
                            Ok(Some(memo)) => return Some((env, memo)),
                            Err(Ev::Stuck) => return None,
                            _ => {}
                        }
                    }
                    if *steps > SEARCH_STEPS {
                        return None;
                    }
                }
                // next index tuple in [0, s]ⁿ
                let mut j = 0;
                while j < n {
                    if idx[j] < s {
                        idx[j] += 1;
                        break;
                    }
                    idx[j] = 0;
                    j += 1;
                }
                if j == n {
                    break;
                }
            }
        }
        None
    }

    /// The counterexample's display: its values, the intermediate values that wrap, and the
    /// sentence on the first wrap.
    fn cex_of(
        &self,
        free: &[TermId],
        env: &HashMap<TermId, u64>,
        memo: &HashMap<TermId, u64>,
        atoms: &[&Atom],
    ) -> Cex {
        let vals = free
            .iter()
            .map(|t| {
                (
                    self.terms.show(*t),
                    signed(env[t], self.terms.ty(*t).bits()),
                )
            })
            .collect();
        let inputs = free.iter().all(|t| self.entry.contains(t));
        // the wrapping operations among the atoms' terms, in id order
        let mut ops = BTreeSet::new();
        let mut roots: Vec<TermId> = atoms.iter().flat_map(|a| self.atom_terms(a)).collect();
        while let Some(t) = roots.pop() {
            if let Key::Op(_, _, a) | Key::Float(_, a) = self.terms.key(t) {
                if ops.insert(t) {
                    roots.extend(a.iter().copied());
                }
            } else if let Key::Ite(c, a, b) = self.terms.key(t) {
                roots.extend([*c, *a, *b]);
            }
        }
        let mut wraps = vec![];
        let mut why = None;
        for t in ops {
            let Key::Op(op, w, args) = self.terms.key(t).clone() else {
                continue;
            };
            if !matches!(op, IOp::Add | IOp::Sub | IOp::Mul | IOp::Shl) || args.len() != 2 {
                continue;
            }
            let val = |x: TermId| {
                memo.get(&x)
                    .or(env.get(&x))
                    .copied()
                    .or(self.terms.as_const(x))
            };
            let (Some(r), Some(a), Some(b)) = (val(t), val(args[0]), val(args[1])) else {
                continue;
            };
            let bits = w.bits();
            let half = 1i128 << (bits - 1);
            let exact = |x: i128, y: i128| match op {
                IOp::Add => Some(x + y),
                IOp::Sub => Some(x - y),
                IOp::Mul => x.checked_mul(y),
                _ => Some(x << (y as u32 % bits)),
            };
            let (sa, sb) = (signed(a, bits), signed(b, bits));
            let Some(se) = exact(sa, if op == IOp::Shl { b as i128 } else { sb }) else {
                continue;
            };
            let signed_wrap = se < -half || se >= half;
            let unsigned_wrap = exact(a as i128, b as i128).is_some_and(|e| e >= 2 * half);
            if !signed_wrap && !unsigned_wrap {
                continue;
            }
            let shown = if signed_wrap {
                signed_text(signed(r, bits))
            } else {
                r.to_string()
            };
            if wraps.len() < 2 {
                wraps.push(format!("{} wraps to {shown}", self.terms.show(t)));
            }
            if why.is_none() && signed_wrap {
                why = self.wrap_why(t, op, &args, bits, se >= half);
            }
        }
        Cex {
            vals,
            inputs,
            wraps,
            why,
        }
    }

    /// `x·2 wraps past 2³¹ when x ≥ 2³⁰`: for an operation with one constant operand, the
    /// values of the other at which it leaves the signed range (on the side it left).
    fn wrap_why(&self, t: TermId, op: IOp, args: &[TermId], bits: u32, up: bool) -> Option<String> {
        let half = 1i128 << (bits - 1);
        let sc = |x: TermId| self.terms.as_const(x).map(|c| signed(c, bits));
        let (x, k) = match (sc(args[0]), sc(args[1])) {
            (None, Some(c)) => (args[0], c),
            (Some(c), None) if matches!(op, IOp::Add | IOp::Mul) => (args[1], c),
            _ => return None,
        };
        let pm = |v: i128| {
            if v < 0 {
                format!("−{}", num(v.unsigned_abs()))
            } else {
                num(v as u128)
            }
        };
        let xs = self.terms.show(x);
        // the boundary value and the relation: x ≥ T (up) or x < T (down)
        let thr = match op {
            IOp::Mul | IOp::Shl => {
                let k = if op == IOp::Shl {
                    1i128 << (k as u32 % bits)
                } else {
                    k
                };
                if k <= 0 {
                    return None;
                }
                if up {
                    -(-half).div_euclid(k) // ⌈2ʷ⁻¹ / k⌉
                } else {
                    -(half.div_euclid(k)) // x·k < −2ʷ⁻¹ ⇔ x < −⌊2ʷ⁻¹ / k⌋
                }
            }
            IOp::Add | IOp::Sub => {
                let c = if op == IOp::Sub { -k } else { k };
                if up { half - c } else { -half - c }
            }
            _ => return None,
        };
        Some(if up {
            format!(
                "{} wraps past {} when {xs} ≥ {}",
                self.terms.show(t),
                pm(half),
                pm(thr)
            )
        } else {
            format!(
                "{} wraps past {} when {xs} < {}",
                self.terms.show(t),
                pm(-half),
                pm(thr)
            )
        })
    }
}
