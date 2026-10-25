//! A short human account of a successful `prove` (design 16 §3), for the editor: which
//! hypotheses the proof needs, whether they contradict each other (ex falso), and for each case
//! the procedure closed, the split that made the case and what closed it (an empty interval, a
//! constraint whose range excludes it, two opposite constraints, a parity/gcd argument, or
//! Fourier–Motzkin). A direct proof is told forward instead, from the facts to the goal, when
//! every case of the procedure closes that way (see "Forward accounts" below). Explaining never
//! changes a verdict: it re-runs the procedure on fresh
//! solvers with tracing on, after the kernel has already decided.

use super::*;

/// What the editor shows under a `prove` line.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Explanation {
    /// indices into the given hypotheses that the proof needs (a minimal subset, found greedily
    /// by dropping one at a time; all of them when there are more than 8)
    pub used: Vec<usize>,
    /// the used hypotheses alone are contradictory: the goal is proved ex falso
    pub ex_falso: bool,
    /// at most three short lines, in the kernel's rendering of terms
    pub lines: Vec<String>,
    /// the functions whose definitions the proof unfolded (a fact about a call can rest on what
    /// the called function computes, not only on facts in scope)
    pub unfolded: Vec<String>,
}

/// An `Env` that records which functions' bodies the procedure unfolds.
struct Unfolds<'e> {
    inner: &'e mut dyn Env,
    funcs: Vec<u32>,
}

impl Env for Unfolds<'_> {
    fn unfold(&mut self, terms: &mut Terms, call: TermId) -> Option<TermId> {
        let r = self.inner.unfold(terms, call);
        if r.is_some()
            && let Key::Call(fi, ..) = terms.key(call)
            && !self.funcs.contains(fi)
        {
            self.funcs.push(*fi);
        }
        r
    }
    fn eval_call(&mut self, terms: &Terms, call: TermId) -> Option<u64> {
        self.inner.eval_call(terms, call)
    }
    fn is_real(&self, t: TermId) -> bool {
        self.inner.is_real(t)
    }
}

/// A constraint `Σ kᵢxᵢ ≤ n/g` as (the kᵢ, divided by their gcd g; n; g).
type Normed = (Vec<(VarId, i128)>, i128, i128);

/// One closed case of the traced run.
#[derive(Clone, Debug)]
struct Case {
    splits: Vec<String>,
    close: String,
    notes: Vec<String>,
    /// closed by the range of a term alone (`x ≥ 0`): not worth a line of its own
    trivial: bool,
}

#[derive(Default)]
pub(super) struct Trace {
    /// a label per hypothesis (`①`, …), in the order given to `prove`
    labels: Vec<String>,
    /// the atom being asserted: Some(hypothesis index) or None (the negated goal)
    cur: Option<usize>,
    splits: Vec<String>,
    close: Option<String>,
    trivial: bool,
    /// the case's contradiction needs integrality modulo this g
    int_g: Option<i128>,
    /// the goal is False (its negation adds nothing)
    goal_false: bool,
    cases: Vec<Case>,
    /// the procedure's unknowns named as letters, with their defining ranges, in order of first
    /// use: (what the variable stands for, letter, definition); by meaning, not id, since a
    /// variable's id differs from case to case
    pub(super) letters: std::cell::RefCell<Vec<(VarDesc, String, String)>>,
    /// names the letters must not take (the program's)
    pub(super) avoid: Vec<String>,
}

const LETTERS: [&str; 12] = ["a", "h", "k", "m", "q", "t", "w", "z", "p", "j", "e", "g"];

impl Solver<'_> {
    /// The letter for a quotient or carry unknown of a traced run, defined on first use.
    pub(super) fn letter(&self, v: VarId) -> Option<String> {
        let t = self.trace.as_ref()?;
        let desc = &self.vars[v as usize].desc;
        if !matches!(desc, VarDesc::Div(_) | VarDesc::SDiv(_) | VarDesc::Wrap(_)) {
            return None;
        }
        if let Some(x) = t.letters.borrow().iter().find(|x| x.0 == *desc) {
            return Some(x.1.clone());
        }
        let taken: Vec<String> = t.letters.borrow().iter().map(|x| x.1.clone()).collect();
        let l = LETTERS
            .iter()
            .map(|s| s.to_string())
            .find(|s| !taken.contains(s) && !t.avoid.contains(s))
            .unwrap_or_else(|| format!("u{}", taken.len()));
        let def = self.definition(desc, &l);
        t.letters.borrow_mut().push((desc.clone(), l.clone(), def));
        Some(l)
    }

    /// What a letter stands for, in the program's terms.
    fn definition(&self, d: &VarDesc, l: &str) -> String {
        let sh = |t: TermId| self.terms.show(t);
        let arg_c = |t: TermId| -> Option<(TermId, i128, IOp)> {
            let Key::Op(op, w, a) = self.terms.key(t) else {
                return None;
            };
            let c = self.terms.as_const(*a.get(1)?)? as i128;
            let c = match op {
                IOp::ShrU | IOp::ShrS => 1i128 << (c as u32 % w.bits()),
                IOp::And => c + 1,
                _ => c,
            };
            Some((a[0], c, *op))
        };
        let k = |c: i128| if c == 1 { String::new() } else { num(c) };
        match d {
            VarDesc::Div(t) | VarDesc::SDiv(t) => match arg_c(*t) {
                Some((x, c, IOp::RemU | IOp::And)) => format!(
                    "{} = {}{l} + {}, with 0 ≤ {} ≤ {}",
                    sh(x),
                    k(c),
                    sh(*t),
                    sh(*t),
                    num(c - 1)
                ),
                Some((x, c, op)) => {
                    let xr = if op == IOp::ShrS {
                        format!("s({})", sh(x))
                    } else {
                        sh(x)
                    };
                    format!(
                        "{} = {l}, so {}{l} ≤ {xr} ≤ {}{l} + {}",
                        sh(*t),
                        k(c),
                        k(c),
                        num(c - 1)
                    )
                }
                None => format!("{l} is the quotient in {}", sh(*t)),
            },
            VarDesc::Wrap(t) => {
                let w = self.terms.ty(*t).bits();
                format!("{l} = how many times {} wraps past 2{}", sh(*t), sup(w))
            }
            _ => String::new(),
        }
    }
}

fn sup(n: u32) -> String {
    const D: [char; 10] = ['⁰', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹'];
    n.to_string()
        .chars()
        .map(|c| D[c.to_digit(10).unwrap_or(0) as usize])
        .collect()
}

/// A number as a student reads it: powers of two (and one less) from 2⁸ up as `2ⁿ`.
pub(super) fn num(c: i128) -> String {
    let a = c.unsigned_abs();
    let sign = if c < 0 { "−" } else { "" };
    if a >= 256 && a.is_power_of_two() {
        return format!("{sign}2{}", sup(a.trailing_zeros()));
    }
    if a >= 255 && (a + 1).is_power_of_two() {
        return format!("{sign}(2{}−1)", sup((a + 1).trailing_zeros()));
    }
    format!("{sign}{a}")
}

/// Is `cases` worth a line: the ones with the most informative closes first.
fn rank(c: &Case) -> u8 {
    if !c.notes.is_empty() {
        0
    } else if c.close.starts_with("needs") {
        1
    } else if c.close.contains(" needs ") || c.close.contains("no integer") {
        2
    } else if c.close.starts_with("Fourier") {
        3
    } else {
        4
    }
}

/// Decide `hyps ⇒ goal` on a fresh solver.
fn valid(terms: &mut Terms, env: &mut dyn Env, hyps: &[Atom], goal: &Atom) -> bool {
    matches!(
        Solver::new(terms, env).prove(hyps, goal),
        Outcome::Valid { .. }
    )
}

/// Explain a `prove` that is already known to be valid. `labels` names each hypothesis
/// (`①`, `②`, …) for the lines.
pub fn explain(
    terms: &mut Terms,
    env: &mut dyn Env,
    hyps: &[Atom],
    goal: &Atom,
    labels: &[String],
) -> Explanation {
    let mut used: Vec<usize> = (0..hyps.len()).collect();
    if hyps.len() <= 8 {
        let mut i = 0;
        while i < used.len() {
            let trial: Vec<usize> = used.iter().copied().filter(|j| *j != used[i]).collect();
            let hs: Vec<Atom> = trial.iter().map(|j| hyps[*j].clone()).collect();
            if valid(terms, env, &hs, goal) {
                used = trial;
            } else {
                i += 1;
            }
        }
    }
    let hs: Vec<Atom> = used.iter().map(|j| hyps[*j].clone()).collect();
    let ex_falso = !hs.is_empty() && (*goal == Atom::False || valid(terms, env, &hs, &Atom::False));
    let g = if ex_falso { Atom::False } else { goal.clone() };
    let unfolded: Vec<String> = {
        let mut rec = Unfolds {
            inner: env,
            funcs: vec![],
        };
        let _ = Solver::new(terms, &mut rec).prove(&hs, &g);
        rec.funcs
            .iter()
            .filter_map(|fi| terms.fnames.get(*fi as usize))
            .map(|n| n.trim_start_matches('$').to_string())
            .collect()
    };
    let used_labels: Vec<String> = used
        .iter()
        .map(|j| {
            labels
                .get(*j)
                .cloned()
                .unwrap_or_else(|| format!("#{}", j + 1))
        })
        .collect();
    // a direct proof: the argument forward from the facts, when every case closes that way
    if !ex_falso && let Some(lines) = forward(terms, env, &hs, &g, used_labels.clone()) {
        return Explanation {
            used,
            ex_falso,
            lines,
            unfolded,
        };
    }
    let avoid = program_names(terms);
    let mut s = Solver::new(terms, env);
    s.trace = Some(Box::new(Trace {
        labels: used_labels,
        goal_false: g == Atom::False,
        avoid,
        ..Default::default()
    }));
    let out = s.prove(&hs, &g);
    let t = s.trace.take().unwrap_or_default();
    let who = t.labels.concat();
    let mut lines = vec![];
    if !matches!(out, Outcome::Valid { .. }) {
        // cannot happen for a valid prove (the subset was checked), but never invent a reason
        return Explanation {
            used,
            ex_falso,
            lines,
            unfolded,
        };
    }
    let mut cases: Vec<&Case> = t.cases.iter().filter(|c| !c.trivial).collect();
    if cases.is_empty() {
        cases = t.cases.iter().collect();
    }
    cases.sort_by_key(|c| rank(c));
    let mut seen: Vec<String> = vec![];
    for c in &cases {
        let line = plain_case(c, ex_falso, &who);
        if !seen.contains(&line) {
            seen.push(line);
        }
    }
    let defs: Vec<String> = t.letters.borrow().iter().map(|x| x.2.clone()).collect();
    if !defs.is_empty() {
        lines.push(format!("Let {}.", defs.join("; ")));
    }
    let shown = seen.len().min(3 - lines.len());
    lines.extend(seen.iter().take(shown).cloned());
    let rest = seen.len() - shown;
    if rest > 0
        && let Some(l) = lines.last_mut()
    {
        let _ = std::fmt::Write::write_fmt(
            l,
            format_args!(
                " ({rest} more case{} the same way)",
                if rest == 1 { "" } else { "s" }
            ),
        );
    }
    if lines.is_empty() && t.cases.is_empty() {
        lines.push("every case is impossible".into());
    }
    Explanation {
        used,
        ex_falso,
        lines,
        unfolded,
    }
}

/// The tracing hooks the procedure calls; each is a no-op unless `explain` is running (and
/// during the interval pre-pass, whose aborted runs are not cases).
impl Solver<'_> {
    fn tracing(&self) -> bool {
        self.trace.is_some() && !self.pre
    }

    pub(super) fn t_reset(&mut self) {
        if let Some(t) = self.trace.as_mut() {
            t.cur = None;
            t.splits.clear();
            t.close = None;
            t.trivial = false;
            t.int_g = None;
        }
    }

    pub(super) fn t_atom(&mut self, i: Option<usize>) {
        if let Some(t) = self.trace.as_mut() {
            t.cur = i;
        }
    }

    /// The label of the atom being asserted: `①` or `¬goal`.
    fn t_label(&self) -> String {
        match self.trace.as_ref() {
            Some(t) => match t.cur {
                Some(i) => t
                    .labels
                    .get(i)
                    .cloned()
                    .unwrap_or_else(|| format!("#{}", i + 1)),
                None => "¬goal".into(),
            },
            None => String::new(),
        }
    }

    pub(super) fn t_split(&mut self, f: impl FnOnce(&Self) -> String) {
        if self.tracing() {
            let s = format!("{}: {}", self.t_label(), f(self));
            self.trace.as_mut().unwrap().splits.push(s);
        }
    }

    /// Record why the current case is infeasible (the first reason wins).
    pub(super) fn t_fail(&mut self, f: impl FnOnce(&Self) -> String) -> Stop {
        if self.tracing() && self.trace.as_ref().unwrap().close.is_none() {
            let s = f(self);
            self.trace.as_mut().unwrap().close = Some(s);
        }
        Stop::Infeasible
    }

    /// As `t_fail`, for a reason that needs integrality modulo g.
    pub(super) fn t_fail_mod(&mut self, g: i128, f: impl FnOnce(&Self) -> String) -> Stop {
        if self.tracing() && self.trace.as_ref().unwrap().close.is_none() {
            let s = f(self);
            let t = self.trace.as_mut().unwrap();
            t.close = Some(s);
            t.int_g = Some(g);
        }
        Stop::Infeasible
    }

    /// A variable whose interval (after the pre-pass) is empty.
    pub(super) fn t_empty(&self, d: &VarDesc) -> String {
        let what = match d {
            VarDesc::Term(t) | VarDesc::Res(t) => format!("u({})", self.terms.show(*t)),
            VarDesc::Wrap(t) => format!("the wrap of {}", self.terms.show(*t)),
            VarDesc::Div(t) | VarDesc::SDiv(t) => {
                format!("the quotient in {}", self.terms.show(*t))
            }
            VarDesc::Mono(_) | VarDesc::TermMono(_) => "a product".into(),
        };
        let by = match self.trace.as_ref() {
            Some(t) if t.goal_false => "the hypotheses' bounds",
            _ => "the bounds of the hypotheses and the negated goal",
        };
        format!("{by} leave {what} no value")
    }

    pub(super) fn t_const_false(&self) -> String {
        match self.trace.as_ref().and_then(|t| t.cur) {
            Some(_) => format!("{} is false", self.t_label()),
            None => "here the goal reduces to true".into(),
        }
    }

    /// A linear form with the procedure's variable names.
    pub(super) fn lin_str(&self, l: &Lin) -> String {
        let mut s = String::new();
        let mut ts = l.ts.clone();
        ts.sort_by_key(|(_, k)| *k < 0);
        for (v, k) in &ts {
            let name = self.render_var(*v);
            let a = k.unsigned_abs() as i128;
            let single = name.chars().count() == 1 || name.ends_with('₀');
            let coef = if a == 1 {
                String::new()
            } else if single {
                num(a)
            } else {
                format!("{}·", num(a))
            };
            let sign = if *k < 0 { "−" } else { "+" };
            if s.is_empty() {
                s = format!("{}{coef}{name}", if *k < 0 { "−" } else { "" });
            } else {
                s = format!("{s} {sign} {coef}{name}");
            }
        }
        if s.is_empty() {
            return num(l.c);
        }
        if l.c != 0 {
            let sign = if l.c < 0 { "−" } else { "+" };
            s = format!("{s} {sign} {}", num(l.c.abs()));
        }
        s
    }

    /// `k·v + c ≤ 0` (or `= 0`) empties v's interval `old`.
    pub(super) fn t_interval(&self, v: VarId, old: (i128, i128), l: &Lin, eq: bool) -> String {
        let (_, k) = l.ts[0];
        let name = self.render_var(v);
        let need = if eq {
            format!("{name} = {}", num(-l.c / k))
        } else if k > 0 {
            format!("{name} ≤ {}", num(fdiv(-l.c, k)))
        } else {
            format!("{name} ≥ {}", num(-fdiv(-l.c, -k)))
        };
        let has = if old.0 == old.1 {
            format!("{name} = {}", num(old.0))
        } else {
            format!("{name} ∈ [{}, {}]", num(old.0), num(old.1))
        };
        format!("{} needs {need}, but {has}", self.t_label())
    }

    /// `L ≤ 0` (or `= 0`) is impossible: L's range from its variables' intervals excludes it.
    pub(super) fn t_range(&self, l: &Lin, bound: i128, eq: bool) -> String {
        let (lo, hi) = self.range(l).unwrap_or((bound, bound));
        let r = if lo == hi {
            num(lo)
        } else {
            format!("[{}, {}]", num(lo), num(hi))
        };
        let rel = if eq { "=" } else { "≤" };
        format!(
            "{} needs {} {rel} 0, but it ranges over {r}",
            self.t_label(),
            self.lin_str(l)
        )
    }

    /// `L = 0` has no integer solution: g divides every coefficient but not the constant.
    pub(super) fn t_gcd(&self, l: &Lin, g: i128) -> String {
        format!(
            "{} = 0 has no integer solution: every coefficient is a multiple of {}",
            self.lin_str(l),
            num(g)
        )
    }

    /// A `≠` split: record the side taken, and close the case at once if that side contradicts
    /// the two terms' ranges (a valid reason, though the procedure may close it later).
    pub(super) fn t_ne_split(
        &mut self,
        a: TermId,
        b: TermId,
        signed: bool,
        gt: bool,
        x: (i128, i128),
        y: (i128, i128),
    ) {
        if !self.tracing() {
            return;
        }
        let r = |s: &Self, t: TermId| {
            let n = s.terms.show(t);
            if signed { format!("s({n})") } else { n }
        };
        let (ra, rb) = (r(self, a), r(self, b));
        let side = format!("{ra} {} {rb}", if gt { ">" } else { "<" });
        let impossible = if gt { x.1 < y.0 + 1 } else { x.0 + 1 > y.1 };
        self.t_split(|_| side.clone());
        if impossible && self.trace.as_ref().unwrap().close.is_none() {
            let (t, (lo, hi)) = if self.terms.is_const(a) {
                (rb, y)
            } else {
                (ra, x)
            };
            let t2 = self.trace.as_mut().unwrap();
            t2.close = Some(format!(
                "{side} is impossible: {t} ∈ [{}, {}]",
                num(lo),
                num(hi)
            ));
            t2.trivial = true;
        }
    }

    /// Before elimination: two opposite constraints `T ≤ d₁`, `T ≥ e` with e > d₁ after
    /// dividing each by the gcd of its coefficients, a direct contradiction (and, when the
    /// rational bounds alone would allow it, an integrality argument modulo the gcd).
    pub(super) fn t_omega(&mut self, ineqs: &[Lin]) {
        if !self.tracing() || self.trace.as_ref().unwrap().close.is_some() {
            return;
        }
        // Σ k x + c ≤ 0  ⇔  Σ (k/g) x ≤ −c/g  (rational), ⌊−c/g⌋ (integer)
        let norm: Vec<Normed> = ineqs
            .iter()
            .filter(|l| !l.ts.is_empty())
            .map(|l| {
                let g = l.ts.iter().fold(0i128, |g, (_, k)| gcd(g, *k));
                (l.ts.iter().map(|(v, k)| (*v, k / g)).collect(), -l.c, g)
            })
            .collect();
        for (i, (ts, n1, g1)) in norm.iter().enumerate() {
            let neg: Vec<(VarId, i128)> = ts.iter().map(|(v, k)| (*v, -k)).collect();
            for (ts2, n2, g2) in norm.iter().skip(i + 1) {
                if *ts2 != neg {
                    continue;
                }
                // T ≤ n1/g1 and −T ≤ n2/g2
                let (d1, d2) = (fdiv(*n1, *g1), fdiv(*n2, *g2));
                if d1 + d2 >= 0 {
                    continue;
                }
                // the rational bounds: n1/g1 + n2/g2 ≥ 0 ⇔ n1·g2 + n2·g1 ≥ 0
                let rational_ok = n1 * g2 + n2 * g1 >= 0;
                let flip = ts.iter().filter(|(_, k)| *k < 0).count() * 2 > ts.len();
                let (ts, lo, hi) = if flip {
                    (neg.clone(), -d1, d2)
                } else {
                    (ts.clone(), -d2, d1)
                };
                let tl = self.lin_str(&Lin { ts, c: 0 });
                let msg = format!("needs {tl} ≥ {} and ≤ {}", num(lo), num(hi));
                let t = self.trace.as_mut().unwrap();
                t.close = Some(msg);
                if rational_ok {
                    t.int_g = Some((*g1).max(*g2));
                }
                return;
            }
        }
        let t = self.trace.as_mut().unwrap();
        t.close = Some("Fourier–Motzkin: the linear constraints have no common solution".into());
    }

    /// Close the current case: with an integrality argument modulo g, name the program terms
    /// that are ≡ r (mod g) in this case (their linear forms have only multiples of g).
    pub(super) fn t_end_case(&mut self) {
        if !self.tracing() {
            return;
        }
        let mut notes = vec![];
        if let Some(g) = self.trace.as_ref().unwrap().int_g {
            let mut ids: Vec<TermId> = self.memo.keys().copied().collect();
            ids.sort();
            let mut first = true;
            for t in ids {
                if !matches!(self.terms.key(t), Key::Op(..)) {
                    continue;
                }
                let tr = &self.memo[&t];
                if tr.lin.ts.is_empty() || tr.lin.ts.iter().any(|(_, k)| k % g != 0) {
                    continue;
                }
                let r = tr.lin.c.rem_euclid(g);
                let name = self.terms.show(t);
                let what = if g == 2 {
                    if r == 0 { "even" } else { "odd" }.to_string()
                } else {
                    format!("≡ {r} (mod {})", num(g))
                };
                let v = tr.lo + (r - tr.lo).rem_euclid(g);
                let point = (tr.hi - tr.lo < g && v <= tr.hi).then_some(v);
                if first {
                    notes.push(format!(
                        "{name} is {what} ({name} = {})",
                        self.lin_str(&tr.lin)
                    ));
                    first = false;
                }
                if let Some(v) = point {
                    notes.push(format!("so {name} = {}", num(v)));
                }
                if notes.len() >= 3 {
                    break;
                }
            }
        }
        let t = self.trace.as_mut().unwrap();
        let close = t.close.take().unwrap_or_else(|| "infeasible".into());
        t.cases.push(Case {
            splits: std::mem::take(&mut t.splits),
            close,
            notes,
            trivial: t.trivial,
        });
    }
}

/// Names the letters must avoid: every local and leaf name the student sees.
fn program_names(terms: &Terms) -> Vec<String> {
    let mut v: Vec<String> = terms.view.values().cloned().collect();
    for t in &terms.terms {
        if let Some(n) = &t.name {
            v.push(n.trim_start_matches('$').to_string());
        }
    }
    v
}

/// A split in plain words: the hypothesis label and the negated-goal marker go.
fn plain_split(s: &str) -> String {
    if let Some(r) = s.strip_prefix("¬goal: ") {
        return plain_split(r);
    }
    if let Some(x) = s.strip_suffix(" does not wrap") {
        return format!("computing {x} does not wrap around");
    }
    if let Some(x) = s.strip_suffix(" wraps") {
        return format!("computing {x} wraps around");
    }
    match s.split_once(": ") {
        Some((l, r)) if l.chars().all(|c| !c.is_ascii()) => format!("{r} ({l})"),
        _ => s.to_string(),
    }
}

/// A closing reason in plain words, solver vocabulary glossed.
fn plain_close(s: &str) -> String {
    if let Some(r) = s.strip_prefix("needs ")
        && let Some((e, rest)) = r.split_once(" ≥ ")
        && let Some((lo, hi)) = rest.split_once(" and ≤ ")
    {
        return format!("then {e} would be ≥ {lo} and ≤ {hi} at once, which is impossible");
    }
    s.replace(
        "Fourier–Motzkin: the linear constraints have no common solution",
        "the inequalities cannot all hold (Fourier–Motzkin: adding inequalities to cancel the unknowns one by one leaves 0 ≤ −1)",
    )
    .replace(
        "the bounds of the hypotheses and the negated goal leave",
        "if the goal failed, the facts' bounds would leave",
    )
    .replace("the hypotheses' bounds leave", "the facts' bounds leave")
    .replace("¬goal needs", "the goal failing needs")
    .replace("here the goal reduces to true", "here the goal is simply true")
    .replace(" no value", " no possible value")
}

/// One closed case as a sentence.
fn plain_case(c: &Case, ex_falso: bool, who: &str) -> String {
    if !c.notes.is_empty() {
        let n = c.notes.join(", ");
        return if ex_falso {
            format!("{n}, which contradicts {who}.")
        } else if who.is_empty() {
            format!("{n}, so the goal cannot fail.")
        } else {
            format!("{n}; with {who} the goal cannot fail.")
        };
    }
    let close = plain_close(&c.close);
    // a case made by a wrap that the ranges close: say so, not the arithmetic behind it
    let wrap_case = c.splits.iter().any(|s| s.ends_with(" wraps"));
    if wrap_case && (c.close.contains("but it ranges over") || c.close.contains("no value")) {
        let n = c.splits.len();
        let sp: Vec<String> = c.splits[n.saturating_sub(2)..]
            .iter()
            .map(|s| plain_split(s))
            .collect();
        return format!(
            "If {}: impossible, the values' ranges rule it out.",
            sp.join(" and ")
        );
    }
    if c.splits.is_empty() {
        return format!("{}{}.", close[..1].to_uppercase(), &close[1..]);
    }
    let n = c.splits.len();
    let sp: Vec<String> = c.splits[n.saturating_sub(2)..]
        .iter()
        .map(|s| plain_split(s))
        .collect();
    format!("If {}: {close}.", sp.join(" and "))
}

// ---------------------------------------------------------------------------------------------
// Forward accounts (research/24 §8): for a direct proof, the argument from the facts to the goal
// (`x is even, so x = 2a. … which forces h = a. So (x>>1)·2 − x = 2h − 2a = 0.`), read off a
// run of the same procedure that asserts the facts and translates the goal *without* negating
// it. Each case of that run is closed forward: equalities with a unit coefficient are solved and
// substituted, two opposite inequalities that meet after integer tightening force an equality,
// and the goal's linear form must then be a constant that satisfies it, or be bounded by one
// fact or by the ranges. A case the facts rule out (a wrap, a sign) is said to be impossible,
// with the constraint that fails. If any case does not close this way the forward account is
// not given and the refutation account stands.
// ---------------------------------------------------------------------------------------------

/// What a goal conjunct asks of its linear form `L` (left side minus right side).
#[derive(Clone, Copy, Debug, PartialEq)]
enum FRel {
    /// L ≤ 0 (a strict `<` is stored as L + 1 ≤ 0)
    Le,
    Eq,
    Ne,
}

/// One comparison the goal needs, or one that is exactly a hypothesis.
#[derive(Clone, Debug)]
enum Conj {
    Cmp {
        rel: FRel,
        signed: bool,
        a: TermId,
        b: TermId,
        strict: bool,
    },
    /// the conjunct is hypothesis j itself
    Hyp(usize, Atom),
}

/// A constraint of a forward case: `lin ≤ 0` or `lin = 0`, from hypothesis `from` (None: from
/// translating the goal's terms), with the steps whose substitution changed it.
#[derive(Clone, Debug)]
struct FCon {
    lin: Lin,
    /// as the procedure first stated it
    orig: Lin,
    eq: bool,
    from: Option<usize>,
    touched: Vec<usize>,
}

/// A substitution the forward derivation made.
#[derive(Clone, Debug)]
enum Step {
    /// an equality fact solved for `v`
    Fact {
        v: VarId,
        sol: Lin,
        from: Option<usize>,
        deps: Vec<usize>,
    },
    /// two inequalities (as they stood) that force `v = sol`
    Forced {
        v: VarId,
        sol: Lin,
        pair: (Lin, Lin),
        deps: Vec<usize>,
    },
}

impl Step {
    fn deps(&self) -> &[usize] {
        match self {
            Step::Fact { deps, .. } | Step::Forced { deps, .. } => deps,
        }
    }
}

/// The comparisons a goal needs, unfolding predicate calls (as the procedure does) and reading
/// `c ? a : 0` as `c and a`; a conjunct that is literally a hypothesis is kept whole. None when
/// the goal is not a conjunction of comparisons.
fn conjuncts(
    terms: &mut Terms,
    env: &mut dyn Env,
    hyps: &[Atom],
    g: &Atom,
    depth: u32,
    out: &mut Vec<Conj>,
) -> bool {
    if let Some(j) = hyps.iter().position(|h| h == g) {
        out.push(Conj::Hyp(j, g.clone()));
        return true;
    }
    match g {
        Atom::True => true,
        Atom::Cmp { rel, signed, a, b } => {
            let (rel, strict) = match rel {
                Rel::Lt => (FRel::Le, true),
                Rel::Le => (FRel::Le, false),
                Rel::Eq => (FRel::Eq, false),
                Rel::Ne => (FRel::Ne, false),
            };
            // `0 = e` reads as `e = 0`
            let (a, b) = if matches!(rel, FRel::Eq | FRel::Ne)
                && terms.is_const(*a)
                && !terms.is_const(*b)
            {
                (*b, *a)
            } else {
                (*a, *b)
            };
            out.push(Conj::Cmp {
                rel,
                signed: *signed,
                a,
                b,
                strict,
            });
            true
        }
        Atom::Bool { t, neg } => {
            let t = *t;
            match terms.key(t).clone() {
                Key::Const(_, c) => (c != 0) != *neg,
                Key::Op(o, ..) if o.is_cmp() => {
                    let a = terms.atom_of(t, !*neg);
                    conjuncts(terms, env, hyps, &a, depth, out)
                }
                Key::Op(IOp::And, _, args)
                    if !*neg && terms.is_cmp(args[0]) && terms.is_cmp(args[1]) =>
                {
                    let (x, y) = (terms.atom_of(args[0], true), terms.atom_of(args[1], true));
                    conjuncts(terms, env, hyps, &x, depth, out)
                        && conjuncts(terms, env, hyps, &y, depth, out)
                }
                Key::Ite(c, a, b) if !*neg && terms.as_const(b) == Some(0) => {
                    let (x, y) = (
                        Atom::Bool { t: c, neg: false },
                        Atom::Bool { t: a, neg: false },
                    );
                    conjuncts(terms, env, hyps, &x, depth, out)
                        && conjuncts(terms, env, hyps, &y, depth, out)
                }
                Key::Call(..) if depth < UNFOLD_DEPTH => match env.unfold(terms, t) {
                    Some(body) => conjuncts(
                        terms,
                        env,
                        hyps,
                        &Atom::Bool { t: body, neg: *neg },
                        depth + 1,
                        out,
                    ),
                    None => false,
                },
                _ => false,
            }
        }
        _ => false,
    }
}

/// One goal comparison of a forward case: `lhs rel rhs` (`lhs − rhs + 1 ≤ 0` when strict),
/// with the forms `lhs` took as steps were substituted.
#[derive(Clone, Debug)]
struct FGoal {
    conj: usize,
    lhs: Lin,
    rhs: i128,
    rel: FRel,
    strict: bool,
    /// lhs is the difference of the two sides (the right side is not a constant): the sides
    diff: bool,
    sides: Option<(Lin, Lin)>,
    forms: Vec<Lin>,
    touched: Vec<usize>,
}

impl FGoal {
    /// L, with the goal `L ≤ 0`, `L = 0` or `L ≠ 0`.
    fn l(&self) -> Lin {
        let k = -self.rhs + if self.strict { 1 } else { 0 };
        Lin {
            ts: self.lhs.ts.clone(),
            c: self.lhs.c + k,
        }
    }
}

/// One case of the forward run, as translation left it.
#[derive(Clone, Debug)]
struct FCase {
    cons: Vec<FCon>,
    goals: Vec<FGoal>,
    vars: Vec<Var>,
    splits: Vec<String>,
    /// the terms whose range keeps them from wrapping: (term, its form, its width)
    nowrap: Vec<(TermId, Lin, u32)>,
    /// closed while translating (the facts rule the case out): the procedure's reason
    closed: Option<String>,
}

impl Solver<'_> {
    /// Assert the hypotheses and translate the goal's comparisons in the current case.
    /// `marks` gets the number of constraints after each hypothesis.
    fn f_run(
        &mut self,
        hyps: &[Atom],
        goal: &Atom,
        conj: &[Conj],
        marks: &mut Vec<usize>,
    ) -> R<Vec<FGoal>> {
        self.reset_run();
        marks.clear();
        for (i, h) in hyps.iter().enumerate() {
            self.t_atom(Some(i));
            self.defined(h, true)?;
            self.assert(h, true)?;
            marks.push(self.cons.len());
        }
        self.t_atom(None);
        // a goal that may trap: the forward account does not narrate the trap
        if !self.defined(goal, false)? {
            return Err(Stop::Cap("trap".into()));
        }
        let mut out = vec![];
        for (i, c) in conj.iter().enumerate() {
            let Conj::Cmp {
                rel,
                signed,
                a,
                b,
                strict,
            } = c
            else {
                continue;
            };
            let (x, y) = if *signed {
                (self.signed(*a)?, self.signed(*b)?)
            } else {
                (self.tr(*a)?, self.tr(*b)?)
            };
            let (lhs, rhs, diff) = match y.lin.as_const() {
                Some(k) => (x.lin.clone(), k, false),
                None => (x.lin.minus(&y.lin)?, 0, true),
            };
            let sides = diff.then(|| (x.lin.clone(), y.lin.clone()));
            out.push(FGoal {
                conj: i,
                forms: vec![lhs.clone()],
                lhs,
                rhs,
                rel: *rel,
                strict: *strict,
                diff,
                sides,
                touched: vec![],
            });
        }
        Ok(out)
    }

    /// The arithmetic terms of the current run that the procedure found cannot wrap, by range.
    fn f_nowrap(&self, conj: &[Conj]) -> Vec<(TermId, Lin, u32)> {
        // the goal's own arithmetic (not inside calls)
        let mut mine = std::collections::HashSet::new();
        let mut stack: Vec<TermId> = conj
            .iter()
            .flat_map(|c| match c {
                Conj::Cmp { a, b, .. } => vec![*a, *b],
                Conj::Hyp(..) => vec![],
            })
            .collect();
        while let Some(t) = stack.pop() {
            if mine.insert(t)
                && let Key::Op(_, _, args) = self.terms.key(t)
            {
                stack.extend(args.iter().copied());
            }
        }
        let mut v: Vec<(TermId, Lin, u32)> = self
            .memo
            .iter()
            .filter(|(t, _)| {
                mine.contains(*t)
                    && matches!(
                        self.terms.key(**t),
                        Key::Op(IOp::Add | IOp::Sub | IOp::Mul | IOp::Shl, ..)
                    )
                    && self
                        .wraps
                        .contains(&format!("{} does not wrap", self.terms.show(**t)))
            })
            .map(|(t, tr)| (*t, tr.lin.clone(), self.terms.ty(*t).bits()))
            .collect();
        v.sort_by_key(|x| x.0);
        v
    }

    /// The origin of each constraint of the current run: the hypothesis being asserted when
    /// it was added (None: the goal's terms).
    fn f_cons(&self, marks: &[usize]) -> Vec<FCon> {
        self.cons
            .iter()
            .enumerate()
            .map(|(k, c)| {
                let (lin, eq) = match c {
                    Con::Le(l) => (l.clone(), false),
                    Con::Eq(l) => (l.clone(), true),
                };
                FCon {
                    orig: lin.clone(),
                    lin,
                    eq,
                    from: marks.iter().position(|m| k < *m),
                    touched: vec![],
                }
            })
            .collect()
    }
}

impl Solver<'_> {
    /// Every case of the forward run, enumerated as `prove` does; None if a cap is hit or the
    /// goal may trap.
    fn f_cases(&mut self, hyps: &[Atom], goal: &Atom, conj: &[Conj]) -> Option<Vec<FCase>> {
        self.choices.clear();
        let mut out = vec![];
        let mut marks = vec![];
        loop {
            if out.len() as u32 >= CAP_CASES {
                return None;
            }
            let r = self.f_run(hyps, goal, conj, &mut marks);
            let t = self.trace.as_ref()?;
            let (splits, close) = (t.splits.clone(), t.close.clone());
            match r {
                Err(Stop::Cap(_)) => return None,
                Err(Stop::Infeasible) => out.push(FCase {
                    cons: vec![],
                    goals: vec![],
                    vars: vec![],
                    splits,
                    nowrap: vec![],
                    closed: Some(close.unwrap_or_default()),
                }),
                Ok(goals) => out.push(FCase {
                    cons: self.f_cons(&marks),
                    goals,
                    vars: self.vars.clone(),
                    splits,
                    nowrap: self.f_nowrap(conj),
                    closed: None,
                }),
            }
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
        Some(out)
    }
}

/// How a goal comparison is met at the end of a case.
#[derive(Clone, Debug)]
enum Met {
    /// its linear form is a constant that satisfies it
    Const,
    /// one constraint (index into the case's final constraints) bounds it
    Fact(usize),
    /// the variables' ranges bound it; the single-variable constraints on its variables
    Range(Vec<usize>),
}

/// The end of a forward case.
#[derive(Clone, Debug)]
enum Closed {
    Proved {
        steps: Vec<Step>,
        goals: Vec<(FGoal, Met)>,
        cons: Vec<FCon>,
    },
    /// the facts rule the case out: the constraints that fail (as they end)
    Impossible(Vec<FCon>),
    Stuck,
}

/// `l ≤ 0` as `T ≤ d`: T with the gcd of its coefficients divided out, d tightened to an integer.
fn norm(l: &Lin) -> (Vec<(VarId, i128)>, i128) {
    let g = l.ts.iter().fold(0i128, |g, (_, k)| gcd(g, *k)).max(1);
    (
        l.ts.iter().map(|(v, k)| (*v, k / g)).collect(),
        fdiv(-l.c, g),
    )
}

/// The variable to solve a linear form for: the most recent one with coefficient ±1.
fn unit(l: &Lin) -> Option<VarId> {
    l.ts.iter()
        .filter(|(_, k)| k.abs() == 1)
        .map(|(v, _)| *v)
        .max()
}

/// `l = 0` solved for v (its coefficient is ±1): v = sol.
fn solve(l: &Lin, v: VarId) -> R<Lin> {
    let k = l.coef(v);
    let rest = Lin {
        ts: l.ts.iter().filter(|(x, _)| *x != v).copied().collect(),
        c: l.c,
    };
    rest.scale(-k)
}

/// Two opposite inequalities that meet: (i, j, T − d) with T ≤ d and T ≥ d.
fn forced(cons: &[FCon]) -> Option<(usize, usize, Lin)> {
    for (i, a) in cons
        .iter()
        .enumerate()
        .filter(|(_, c)| !c.eq && !c.lin.ts.is_empty())
    {
        let (ta, da) = norm(&a.lin);
        let neg: Vec<(VarId, i128)> = ta.iter().map(|(v, k)| (*v, -k)).collect();
        for (j, b) in cons.iter().enumerate().skip(i + 1).filter(|(_, c)| !c.eq) {
            let (tb, db) = norm(&b.lin);
            if tb == neg && da + db == 0 {
                let l = Lin {
                    ts: ta.clone(),
                    c: -da,
                };
                if unit(&l).is_some() {
                    return Some((i, j, l));
                }
            }
        }
    }
    None
}

/// Two opposite inequalities that cannot both hold.
fn clash(cons: &[FCon]) -> Option<(usize, usize)> {
    for (i, a) in cons
        .iter()
        .enumerate()
        .filter(|(_, c)| !c.eq && !c.lin.ts.is_empty())
    {
        let (ta, da) = norm(&a.lin);
        let neg: Vec<(VarId, i128)> = ta.iter().map(|(v, k)| (*v, -k)).collect();
        for (j, b) in cons.iter().enumerate().skip(i + 1).filter(|(_, c)| !c.eq) {
            let (tb, db) = norm(&b.lin);
            if tb == neg && da + db < 0 {
                return Some((i, j));
            }
        }
    }
    None
}

/// Range of a linear form over the case's variable intervals (None on overflow).
fn f_range(l: &Lin, vars: &[Var]) -> Option<(i128, i128)> {
    let (mut lo, mut hi) = (l.c, l.c);
    for (v, k) in &l.ts {
        let x = vars.get(*v as usize)?;
        let (a, b) = (x.lo.checked_mul(*k)?, x.hi.checked_mul(*k)?);
        lo = lo.checked_add(a.min(b))?;
        hi = hi.checked_add(a.max(b))?;
    }
    Some((lo, hi))
}

/// Is a goal comparison met by the case's final constraints?
fn met(g: &FGoal, cons: &[FCon], vars: &[Var]) -> Option<Met> {
    let l = g.l();
    let ok = |lo: i128, hi: i128| match g.rel {
        FRel::Le => hi <= 0,
        FRel::Eq => lo == 0 && hi == 0,
        FRel::Ne => lo > 0 || hi < 0,
    };
    if let Some(k) = l.as_const() {
        return ok(k, k).then_some(Met::Const);
    }
    if let Some((lo, hi)) = f_range(&l, vars)
        && ok(lo, hi)
    {
        let on: Vec<usize> = cons
            .iter()
            .enumerate()
            .filter(|(_, c)| c.from.is_some() && c.lin.ts.len() == 1 && l.coef(c.lin.ts[0].0) != 0)
            .map(|(i, _)| i)
            .collect();
        return Some(Met::Range(on));
    }
    let (t, d) = norm(&l);
    let g0 = l.ts.iter().fold(0i128, |g, (_, k)| gcd(g, *k)).max(1);
    for (i, c) in cons.iter().enumerate().filter(|(_, c)| !c.eq) {
        let (tc, dc) = norm(&c.lin);
        let hit = match g.rel {
            // T ≤ dc ≤ d
            FRel::Le => tc == t && dc <= d,
            // L = g0·T + l.c ≠ 0 when T ≤ dc excludes the root, or T ≥ −dc does
            FRel::Ne => {
                let neg: Vec<(VarId, i128)> = t.iter().map(|(v, k)| (*v, -k)).collect();
                let root = (-l.c % g0 == 0).then_some(-l.c / g0);
                match root {
                    None => true,
                    Some(r) => (tc == t && r > dc) || (tc == neg && -r > dc),
                }
            }
            FRel::Eq => false,
        };
        if hit {
            return Some(Met::Fact(i));
        }
    }
    None
}

/// Close one forward case.
fn derive(case: &FCase) -> Closed {
    derive_r(case).unwrap_or(Closed::Stuck)
}

fn derive_r(case: &FCase) -> R<Closed> {
    let mut cons = case.cons.clone();
    let mut goals = case.goals.clone();
    let mut steps: Vec<Step> = vec![];
    let subst = |cons: &mut Vec<FCon>, goals: &mut Vec<FGoal>, k: usize, v: VarId, sol: &Lin| {
        for c in cons.iter_mut().filter(|c| c.lin.coef(v) != 0) {
            c.lin = c.lin.subst(v, sol)?;
            c.touched.push(k);
        }
        for g in goals.iter_mut().filter(|g| g.lhs.coef(v) != 0) {
            g.lhs = g.lhs.subst(v, sol)?;
            g.forms.push(g.lhs.clone());
            g.touched.push(k);
        }
        Ok::<(), Stop>(())
    };
    for _ in 0..2 * CAP_VARS {
        if let Some(i) = cons.iter().position(|c| c.eq && unit(&c.lin).is_some()) {
            let c = cons.remove(i);
            let v = unit(&c.lin).unwrap_or_default();
            let sol = solve(&c.lin, v)?;
            steps.push(Step::Fact {
                v,
                sol: sol.clone(),
                from: c.from,
                deps: c.touched.clone(),
            });
            subst(&mut cons, &mut goals, steps.len() - 1, v, &sol)?;
            continue;
        }
        if let Some((i, j, l)) = forced(&cons) {
            let (b, a) = (cons.remove(j), cons.remove(i));
            let v = unit(&l).unwrap_or_default();
            let sol = solve(&l, v)?;
            let mut deps = a.touched.clone();
            deps.extend(b.touched.iter().copied());
            steps.push(Step::Forced {
                v,
                sol: sol.clone(),
                pair: (a.lin, b.lin),
                deps,
            });
            subst(&mut cons, &mut goals, steps.len() - 1, v, &sol)?;
            continue;
        }
        break;
    }
    if let Some(c) = cons.iter().find(|c| match c.lin.as_const() {
        Some(k) => (c.eq && k != 0) || (!c.eq && k > 0),
        None => false,
    }) {
        return Ok(Closed::Impossible(vec![c.clone()]));
    }
    if let Some((i, j)) = clash(&cons) {
        return Ok(Closed::Impossible(vec![cons[i].clone(), cons[j].clone()]));
    }
    let mut out = vec![];
    for g in goals {
        let Some(m) = met(&g, &cons, &case.vars) else {
            return Ok(Closed::Stuck);
        };
        out.push((g, m));
    }
    Ok(Closed::Proved {
        steps,
        goals: out,
        cons,
    })
}

/// A hypothesis as a sentence's subject: `x is even` for `is_even(x)`, else in infix.
fn phrase(terms: &Terms, h: &Atom) -> String {
    if let Atom::Bool { t, neg: false } = h
        && let Key::Call(fi, args, _) = terms.key(*t)
        && let [x] = args.as_slice()
        && let Some(w) = terms
            .fnames
            .get(*fi as usize)
            .and_then(|n| n.trim_start_matches('$').strip_prefix("is_"))
    {
        return format!("{} is {}", terms.show(*x), w.replace('_', " "));
    }
    terms.show_atom(h)
}

impl Solver<'_> {
    /// `l ≤ 0` (or `= 0`) with each term on the side where it is positive: `2h + 1 ≤ x`.
    fn sides(&self, l: &Lin) -> (String, String) {
        let pos = Lin {
            ts: l.ts.iter().filter(|(_, k)| *k > 0).copied().collect(),
            c: l.c.max(0),
        };
        let neg = Lin {
            ts: l
                .ts
                .iter()
                .filter(|(_, k)| *k < 0)
                .map(|(v, k)| (*v, -k))
                .collect(),
            c: (-l.c).max(0),
        };
        (self.lin_str(&pos), self.lin_str(&neg))
    }

    fn ineq(&self, l: &Lin, eq: bool) -> String {
        let (a, b) = self.sides(l);
        format!("{a} {} {b}", if eq { "=" } else { "≤" })
    }

    /// Two inequalities as one chain where they share a side: `2h ≤ 2a ≤ 2h + 1`.
    fn chain(&self, a: &Lin, b: &Lin) -> String {
        let ((la, ra), (lb, rb)) = (self.sides(a), self.sides(b));
        if ra == lb {
            format!("{la} ≤ {ra} ≤ {rb}")
        } else if rb == la {
            format!("{lb} ≤ {rb} ≤ {ra}")
        } else {
            format!("{la} ≤ {ra} and {lb} ≤ {rb}")
        }
    }

    /// The label of hypothesis j, in parentheses (empty when there is only one, unless
    /// `always`: a bound derived from a fact names it).
    fn f_label(&self, j: Option<usize>, always: bool) -> String {
        match (j, self.trace.as_ref()) {
            (Some(j), Some(t)) if always || t.labels.len() > 1 => t
                .labels
                .get(j)
                .map(|l| format!(" ({l})"))
                .unwrap_or_default(),
            _ => String::new(),
        }
    }
}

/// Capitalize a sentence that starts with an English word (one that starts with code keeps
/// the code's case: `x is even`).
/// A bound in a goal, as the student wrote it: decimal up to 2¹⁶.
fn knum(c: i128) -> String {
    if c.unsigned_abs() <= 65536 {
        if c < 0 {
            format!("−{}", -c)
        } else {
            c.to_string()
        }
    } else {
        num(c)
    }
}

fn cap(s: &str) -> String {
    let word: String = s.chars().take_while(|c| c.is_alphabetic()).collect();
    let next = s.chars().nth(word.chars().count());
    const ENGLISH: [&str; 8] = [
        "this",
        "the",
        "that",
        "every",
        "here",
        "if",
        "then",
        "computing",
    ];
    if !ENGLISH.contains(&word.as_str()) || next.is_some_and(|c| c != ' ') {
        return s.to_string();
    }
    let mut c = s.chars();
    match c.next() {
        Some(f) => f.to_uppercase().chain(c).collect(),
        None => String::new(),
    }
}

/// The sentences of a proved forward case.
struct Told {
    /// what the facts say (`x is even, so x = 2a.`)
    facts: Vec<String>,
    /// how many letters the fact sentences introduced (their definitions go without saying)
    fact_letters: usize,
    /// the forced equalities and the goal
    rest: Vec<String>,
}

impl Solver<'_> {
    /// A goal comparison's subject, relation and bound (`(x>>1)·2 − x`, `=`, `0`), and the
    /// comparison as the goal states it (`s(h) + s(h) = s(x)`).
    fn f_goal_name(&self, g: &FGoal, c: &Conj) -> (String, &'static str, String, String) {
        let Conj::Cmp { a, b, .. } = c else {
            return Default::default();
        };
        let rel = match (g.rel, g.strict) {
            (FRel::Le, true) => "<",
            (FRel::Le, false) => "≤",
            (FRel::Eq, _) => "=",
            (FRel::Ne, _) => "≠",
        };
        let (x, y) = (self.terms.show(*a), self.terms.show(*b));
        let stmt = format!("{x} {rel} {y}");
        let name = if g.diff { format!("{x} − {y}") } else { x };
        (name, rel, knum(g.rhs), stmt)
    }

    /// `= f₀ = f₁ …`: the forms a goal's side took, without repeats or the name itself.
    fn f_forms(&self, name: &str, g: &FGoal) -> String {
        let mut seen: Vec<String> = vec![name.to_string()];
        for f in &g.forms {
            let s = self.lin_str(f);
            if !seen.contains(&s) {
                seen.push(s);
            }
        }
        seen.join(" = ")
    }
}

impl Solver<'_> {
    /// Tell one proved forward case: the facts, the forced equalities, the goal.
    fn f_tell(
        &mut self,
        case: &FCase,
        (steps, goals, cons): (&[Step], &[(FGoal, Met)], &[FCon]),
        conj: &[Conj],
        hyps: &[Atom],
    ) -> Told {
        self.vars = case.vars.clone();
        // the steps the goal rests on
        let mut need = vec![false; steps.len()];
        let mut stack: Vec<usize> = vec![];
        for (g, m) in goals {
            stack.extend(g.touched.iter().copied());
            let on: Vec<usize> = match m {
                Met::Fact(i) => vec![*i],
                Met::Range(on) => on.clone(),
                Met::Const => vec![],
            };
            for i in on {
                stack.extend(cons[i].touched.iter().copied());
            }
        }
        while let Some(k) = stack.pop() {
            if !need[k] {
                need[k] = true;
                stack.extend(steps[k].deps().iter().copied());
            }
        }
        let mut facts = vec![];
        for (k, st) in steps.iter().enumerate() {
            if let (true, Step::Fact { v, sol, from, .. }) = (need[k], st) {
                let eq = format!("{} = {}", self.render_var(*v), self.lin_str(sol));
                facts.push(match from {
                    Some(j) => format!(
                        "{}{}, so {eq}.",
                        cap(&phrase(self.terms, &hyps[*j])),
                        self.f_label(Some(*j), false)
                    ),
                    None => format!("{}.", cap(&eq)),
                });
            }
        }
        let fact_letters = self.trace.as_ref().map_or(0, |t| t.letters.borrow().len());
        let mut rest = vec![];
        for (k, st) in steps.iter().enumerate() {
            if let (true, Step::Forced { v, sol, pair, .. }) = (need[k], st) {
                rest.push(format!(
                    "So {}, which forces {} = {}.",
                    self.chain(&pair.0, &pair.1),
                    self.render_var(*v),
                    self.lin_str(sol)
                ));
            }
        }
        for (j, c) in conj.iter().enumerate() {
            if let Conj::Hyp(h, a) = c {
                let l = self.f_label(Some(*h), true);
                rest.push(format!("{} holds{l}.", cap(&self.terms.show_atom(a))));
                continue;
            }
            let Some((g, m)) = goals.iter().find(|(g, _)| g.conj == j) else {
                continue;
            };
            let (name, rel, rhs, stmt) = self.f_goal_name(g, c);
            let forms = self.f_forms(&name, g);
            let concl = if g.diff {
                stmt
            } else {
                format!("{name} {rel} {rhs}")
            };
            let last_const = g.lhs.as_const();
            rest.push(match m {
                Met::Const if g.rel == FRel::Eq && last_const == Some(g.rhs) => {
                    format!("So {forms}.")
                }
                // two sides that differ by a constant: say what each side is
                Met::Const
                    if forms.matches(" = ").count() == 1
                        && let (Some((x, y)), Conj::Cmp { a, b, .. }) = (&g.sides, c) =>
                {
                    let k = g.lhs.as_const().unwrap_or_default();
                    format!(
                        "{} = {} and {} = {}, which differ by {}, so {concl}.",
                        self.terms.show(*a),
                        self.lin_str(x),
                        self.terms.show(*b),
                        self.lin_str(y),
                        knum(k)
                    )
                }
                Met::Const => format!("So {forms} {rel} {rhs}."),
                Met::Fact(i) => {
                    let c = &cons[*i];
                    let by = format!("{}{}", self.ineq(&c.lin, false), self.f_label(c.from, true));
                    if forms == name {
                        format!("{} gives {concl}.", cap(&by))
                    } else {
                        format!("So {forms}, and {by}, so {concl}.")
                    }
                }
                Met::Range(on) => {
                    let by: Vec<String> = if on.is_empty() {
                        g.l()
                            .ts
                            .iter()
                            .map(|(v, _)| {
                                let x = &self.vars[*v as usize];
                                format!("{} ∈ [{}, {}]", self.render_var(*v), num(x.lo), num(x.hi))
                            })
                            .collect()
                    } else {
                        on.iter()
                            .map(|i| {
                                let c = &cons[*i];
                                format!("{}{}", self.ineq(&c.lin, c.eq), self.f_label(c.from, true))
                            })
                            .collect()
                    };
                    format!("{}, so {forms} {rel} {rhs}.", cap(&by.join(" and ")))
                }
            });
        }
        Told {
            facts,
            fact_letters,
            rest,
        }
    }
}

/// A traced split without its atom label (`①: x is negative` → `x is negative`).
fn bare(s: &str) -> &str {
    match s.split_once(": ") {
        Some((l, r)) if l == "¬goal" || l.chars().all(|c| !c.is_ascii()) => r,
        _ => s,
    }
}

/// Does `text` use the letter `l` as a name?
fn uses_letter(text: &str, l: &str) -> bool {
    let cs: Vec<char> = text.chars().collect();
    let lc: Vec<char> = l.chars().collect();
    let name = |c: char| c.is_ascii_alphanumeric() || c == '_' || c == '@' || c == '$';
    (0..cs.len()).any(|i| {
        cs[i..].starts_with(&lc)
            && (i == 0 || !(name(cs[i - 1]) && !cs[i - 1].is_ascii_digit()))
            && cs.get(i + lc.len()).is_none_or(|c| !name(*c))
    })
}

impl Solver<'_> {
    /// Why a case the facts rule out cannot happen, as a clause: `x − 1 would wrap only if
    /// x ≤ 0, but x ∈ [1, 2³²−1]`.
    fn f_ruled_out(&mut self, case: &FCase, closed: &Closed) -> String {
        let last = case.splits.last().map(|s| bare(s).to_string());
        let (would, cannot) = match &last {
            Some(s) if s.ends_with(" wraps") => {
                let x = s.trim_end_matches(" wraps");
                (format!("{x} would wrap"), format!("{x} cannot wrap"))
            }
            Some(s) if s.ends_with(" does not wrap") => {
                let x = s.trim_end_matches(" does not wrap");
                (format!("{x} would stay in range"), format!("{x} must wrap"))
            }
            Some(s) if s.ends_with(" is negative") => {
                let x = s.trim_end_matches(" is negative");
                (
                    format!("{x} would be negative"),
                    format!("{x} cannot be negative"),
                )
            }
            Some(s) => (
                format!("{} would hold", plain_split(s)),
                format!("{} cannot hold", plain_split(s)),
            ),
            None => ("this would happen".into(), "this cannot happen".into()),
        };
        if let Some(c) = &case.closed {
            if let Some((_, r)) = c.split_once(" needs ")
                && let Some((need, has)) = r.split_once(", but ")
            {
                return format!("{would} only if {need}, but {has}");
            }
            return format!("{cannot}: {}", plain_close(c));
        }
        self.vars = case.vars.clone();
        match closed {
            Closed::Impossible(cs) if cs.len() == 1 => {
                let c = &cs[0];
                let t0 = Lin {
                    ts: c.orig.ts.clone(),
                    c: -(c.lin.c - c.orig.c),
                };
                format!(
                    "{would} only if {}, but {}",
                    self.ineq(&c.orig, c.eq),
                    self.ineq(&t0, true)
                )
            }
            Closed::Impossible(cs) if cs.len() == 2 => format!(
                "{would} only if {} and {}, which cannot both hold",
                self.ineq(&cs[0].lin, false),
                self.ineq(&cs[1].lin, false)
            ),
            _ => cannot,
        }
    }
}

/// Is a case split a wrap or a sign (the unusual side of the arithmetic)?
fn unusual(s: &str) -> bool {
    s.ends_with(" wraps") || s.ends_with(" is negative")
}

/// Is a split of the goal's arithmetic (a wrap or a sign), which a forward account can name?
/// Splits on the value of a comparison or an `if` inside the goal are not: such a goal keeps
/// its refutation account.
fn arith(s: &str) -> bool {
    !s.starts_with("¬goal: ")
        || unusual(s)
        || s.ends_with(" does not wrap")
        || s.ends_with(" is non-negative")
}

/// The forward account of a direct proof of `goal` from `hyps` (each needed), in at most four
/// lines; None when some case does not close forward.
fn forward(
    terms: &mut Terms,
    env: &mut dyn Env,
    hyps: &[Atom],
    goal: &Atom,
    labels: Vec<String>,
) -> Option<Vec<String>> {
    let mut conj = vec![];
    if !conjuncts(terms, env, hyps, goal, 0, &mut conj) || conj.is_empty() {
        return None;
    }
    let avoid = program_names(terms);
    let unfolded = !matches!(goal, Atom::Cmp { .. });
    let mut s = Solver::new(terms, env);
    s.trace = Some(Box::new(Trace {
        labels,
        goal_false: true,
        avoid,
        ..Default::default()
    }));
    let cases = s.f_cases(hyps, goal, &conj)?;
    let closed: Vec<Closed> = cases
        .iter()
        .map(|c| match c.closed {
            Some(_) => Closed::Impossible(vec![]),
            None => derive(c),
        })
        .collect();
    if closed.iter().any(|c| matches!(c, Closed::Stuck)) {
        return None;
    }
    let proved: Vec<usize> = (0..cases.len())
        .filter(|i| matches!(closed[*i], Closed::Proved { .. }))
        .collect();
    let main = *proved
        .iter()
        .min_by_key(|i| cases[**i].splits.iter().filter(|s| unusual(s)).count())?;
    let Closed::Proved { steps, goals, cons } = &closed[main] else {
        return None;
    };
    let before = s.trace.as_ref()?.letters.borrow().len();
    let told = s.f_tell(&cases[main], (steps, goals, cons), &conj, hyps);
    // the other cases: those the facts rule out, and those that go the same way
    let mut nothing: Vec<String> = cases[main]
        .nowrap
        .iter()
        .map(|(t, l, w)| {
            let (n, f) = (s.terms.show(*t), s.lin_str(l));
            if n == f {
                format!("{n} stays below 2{}", sup(*w))
            } else {
                format!("{n} = {f} stays below 2{}", sup(*w))
            }
        })
        .collect();
    let mut other = vec![];
    // cases made by the facts' own splits (a ≠, an `if`) are the facts' business: counted only
    if cases.iter().any(|c| c.splits.iter().any(|s| !arith(s))) {
        return None;
    }
    let mut facts_own = 0;
    for (i, c) in cases.iter().enumerate() {
        if matches!(closed[i], Closed::Impossible(_)) {
            if !c.splits.last().is_some_and(|s| s.starts_with("¬goal: ")) {
                facts_own += 1;
                continue;
            }
            let r = s.f_ruled_out(c, &closed[i]);
            // one sentence per term (the same wrap in another case says nothing new)
            let subject = r.split(" would ").next().unwrap_or("").to_string();
            let dup = nothing
                .iter()
                .chain(&other)
                .any(|o| o.starts_with(&format!("{subject} would ")));
            if dup {
                continue;
            }
            if r.contains(" would wrap ") || r.contains(" cannot wrap") {
                nothing.push(r);
            } else {
                other.push(r);
            }
        }
    }
    let same: Vec<String> = proved
        .iter()
        .filter(|i| **i != main)
        .filter_map(|i| {
            cases[*i]
                .splits
                .iter()
                .rev()
                .find(|s| !cases[main].splits.contains(s))
        })
        .map(|s| plain_split(bare(s)))
        .fold(vec![], |mut v, s| {
            if !v.contains(&s) {
                v.push(s);
            }
            v
        });
    let mut tail = String::new();
    // the main case's own unusual side (a wrap, a sign) is said up front
    let when: Vec<String> = cases[main]
        .splits
        .iter()
        .filter(|s| s.starts_with("¬goal: ") && unusual(s))
        .map(|s| plain_split(bare(s)))
        .collect();
    if !nothing.is_empty() {
        nothing.dedup();
        tail = if when.iter().any(|w| w.contains("wraps")) {
            format!("{}.", cap(&nothing.join("; ")))
        } else {
            format!("Nothing wraps: {}.", nothing.join("; "))
        };
    }
    for o in other {
        if !tail.is_empty() {
            tail.push(' ');
        }
        tail.push_str(&cap(&o));
        tail.push('.');
    }
    if facts_own > 0 {
        if !tail.is_empty() {
            tail.push(' ');
        }
        tail.push_str(if facts_own == 1 {
            "The facts' other case is impossible."
        } else {
            "The facts' other cases are impossible."
        });
    }
    if !same.is_empty() {
        if !tail.is_empty() {
            tail.push(' ');
        }
        let n = same.len();
        let shown: Vec<String> = same.into_iter().take(2).collect();
        let more = if n > 2 {
            format!(" and {} more", n - 2)
        } else {
            String::new()
        };
        let _ = std::fmt::Write::write_fmt(
            &mut tail,
            format_args!(
                "The same argument covers the case{} {}{more}.",
                if n > 1 { "s" } else { "" },
                shown.join("; ")
            ),
        );
    }
    // what the letters mean, unless a fact sentence introduced them
    let mut head: Vec<String> = vec![];
    if unfolded {
        let parts: Vec<String> = conj
            .iter()
            .enumerate()
            .map(
                |(j, c)| match (c, goals.iter().find(|(g, _)| g.conj == j)) {
                    (Conj::Hyp(_, a), _) => s.terms.show_atom(a),
                    (Conj::Cmp { .. }, Some((g, _))) => s.f_goal_name(g, c).3,
                    _ => String::new(),
                },
            )
            .collect();
        head.push(format!(
            "{} means {}.",
            s.terms.show_atom(goal),
            parts.join(" and ")
        ));
    }
    head.extend(told.facts.iter().cloned());
    let text = format!("{} {} {tail}", head.join(" "), told.rest.join(" "));
    let t = s.trace.as_ref()?;
    let defs: Vec<String> = t
        .letters
        .borrow()
        .iter()
        .enumerate()
        .filter(|(i, x)| !(before..told.fact_letters).contains(i) && uses_letter(&text, &x.1))
        .map(|(_, x)| format!("{}.", cap(&x.2.replacen(", so ", " means ", 1))))
        .collect();
    head.extend(defs);
    let mut rest = told.rest.join(" ");
    if !when.is_empty() {
        rest = format!("When {}: {rest}", when.join(" and "));
    }
    let mut lines = vec![];
    for l in [head.join(" "), rest, tail] {
        if !l.is_empty() {
            lines.push(l);
        }
    }
    Some(lines)
}
