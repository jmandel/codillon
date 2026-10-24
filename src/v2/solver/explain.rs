//! A short human account of a successful `prove` (design 16 §3), for the editor: which
//! hypotheses the proof needs, whether they contradict each other (ex falso), and for each case
//! the procedure closed, the split that made the case and what closed it (an empty interval, a
//! constraint whose range excludes it, two opposite constraints, a parity/gcd argument, or
//! Fourier–Motzkin). Explaining never changes a verdict: it re-runs the procedure on fresh
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
    let mut s = Solver::new(terms, env);
    s.trace = Some(Box::new(Trace {
        labels: used
            .iter()
            .map(|j| {
                labels
                    .get(*j)
                    .cloned()
                    .unwrap_or_else(|| format!("#{}", j + 1))
            })
            .collect(),
        goal_false: g == Atom::False,
        ..Default::default()
    }));
    let out = s.prove(&hs, &g);
    let t = s.trace.take().unwrap_or_default();
    let who = if t.labels.is_empty() {
        "the negated goal".to_string()
    } else if ex_falso {
        t.labels.concat()
    } else {
        format!("{} and the negated goal", t.labels.concat())
    };
    let mut lines = vec![];
    if !matches!(out, Outcome::Valid { .. }) {
        // cannot happen for a valid prove (the subset was checked), but never invent a reason
        return Explanation {
            used,
            ex_falso,
            lines,
        };
    }
    let mut cases: Vec<&Case> = t.cases.iter().filter(|c| !c.trivial).collect();
    let trivial = t.cases.len() - cases.len();
    if cases.is_empty() {
        cases = t.cases.iter().collect();
    }
    cases.sort_by_key(|c| rank(c));
    let mut seen: Vec<String> = vec![];
    for c in &cases {
        let line = if !c.notes.is_empty() {
            format!("{} — contradicts {who}", c.notes.join(", "))
        } else if c.splits.is_empty() {
            c.close.clone()
        } else {
            // the last two splits made the case; earlier ones are context
            let n = c.splits.len();
            let lead = if n > 2 { "…, " } else { "" };
            format!(
                "case {lead}{}: {}",
                c.splits[n.saturating_sub(2)..].join(", "),
                c.close
            )
        };
        if !seen.contains(&line) {
            seen.push(line);
        }
    }
    let shown = seen.len().min(2);
    lines.extend(seen.iter().take(shown).cloned());
    let rest = seen.len() - shown;
    let mut tail = vec![];
    if rest > 0 {
        tail.push(format!(
            "{rest} more case{}",
            if rest == 1 { "" } else { "s" }
        ));
    }
    if trivial > 0 && trivial < t.cases.len() {
        tail.push(format!(
            "{trivial} case{} ruled out by ranges",
            if trivial == 1 { "" } else { "s" }
        ));
    }
    if !tail.is_empty()
        && let Some(l) = lines.last_mut()
    {
        let _ = std::fmt::Write::write_fmt(l, format_args!(" (+{})", tail.join(", ")));
    }
    if lines.is_empty() && t.cases.is_empty() {
        lines.push("every case is infeasible".into());
    }
    Explanation {
        used,
        ex_falso,
        lines,
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
            VarDesc::Term(t) | VarDesc::Res(t) => format!("u({})", self.terms.render(*t)),
            VarDesc::Wrap(t) => format!("the wrap of {}", self.terms.render(*t)),
            VarDesc::Div(t) | VarDesc::SDiv(t) => {
                format!("the quotient in {}", self.terms.render(*t))
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
        for (v, k) in &l.ts {
            let name = self.render_var(*v);
            let a = k.unsigned_abs() as i128;
            let coef = if a == 1 {
                String::new()
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
            let n = s.terms.render(t);
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
                let name = self.terms.render(t);
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
