//! R5a — automatic feeding (design 16 §2, research/24): a cup that lookup, evaluation and a
//! pending `prove` leave unfed is fed when the decision procedure (§3) proves its goal from the
//! in-scope facts relevant to it, minimized to the facts the proof uses.

use super::*;

/// Facts handed to the solver per auto attempt after a cap (what `prove 8` could see).
const FALLBACK: usize = 8;

/// What automatic feeding found for one cup.
pub(super) enum AutoOutcome {
    /// fed: the minimized feed, top of lane first (as `prove k` orders its hypotheses)
    Fed {
        used: Vec<Entry>,
        wraps: Vec<String>,
    },
    /// not fed: a short reason for the cup's diagnostic (None: nothing worth adding)
    Failed(Option<String>),
}

impl<'a, 'm> Pass<'a, 'm> {
    // ---- relevance ----

    /// The non-constant canonical ids reachable from a term (the term itself included).
    fn term_ids(&self, t: TermId, out: &mut BTreeSet<TermId>) {
        if self.terms.is_const(t) || !out.insert(t) {
            return;
        }
        match self.terms.key(t) {
            Key::Op(_, _, a) | Key::Float(_, a) => a.iter().for_each(|x| self.term_ids(*x, out)),
            Key::Call(_, a, _) => a.iter().for_each(|x| self.term_ids(*x, out)),
            Key::Load(.., a, _) => self.term_ids(*a, out),
            Key::Ite(c, a, b) => [c, a, b].iter().for_each(|x| self.term_ids(**x, out)),
            Key::Const(..) | Key::Leaf(_) => {}
        }
    }

    /// `ids(A)` of R5a step 2.
    pub(super) fn atom_ids(&self, a: &Atom) -> BTreeSet<TermId> {
        let mut out = BTreeSet::new();
        for t in self.terms.atom_args(a) {
            self.term_ids(t, &mut out);
        }
        out
    }

    /// R5a steps 1–2: the in-scope facts that share a value with the goal, closed transitively,
    /// in lane order (oldest first; a taken-edge fact last). Every candidate for `False`.
    fn relevant(&self, goal: &Atom, edge: Option<Entry>) -> Vec<Entry> {
        let cands: Vec<Entry> = self.lane.iter().copied().chain(edge).collect();
        let ids: Vec<BTreeSet<TermId>> = cands
            .iter()
            .map(|e| self.atom_ids(&self.facts[e.fact as usize].atom))
            .collect();
        if *goal == Atom::False {
            return cands;
        }
        let mut s = self.atom_ids(goal);
        let mut take = vec![false; cands.len()];
        loop {
            let mut grew = false;
            for (i, ids_i) in ids.iter().enumerate() {
                if !take[i] && !ids_i.is_disjoint(&s) {
                    take[i] = true;
                    s.extend(ids_i.iter().copied());
                    grew = true;
                }
            }
            if !grew {
                break;
            }
        }
        cands
            .into_iter()
            .zip(take)
            .filter_map(|(e, t)| t.then_some(e))
            .collect()
    }

    // ---- one solver call ----

    /// §3 on `hyps ⇒ goal`, hypotheses given top of lane first (as `prove k` gives them).
    pub(super) fn solve(&mut self, hyps: &[Entry], goal: &Atom) -> Outcome {
        let atoms: Vec<Atom> = hyps
            .iter()
            .map(|e| self.facts[e.fact as usize].atom.clone())
            .collect();
        let (terms, mut env) = self.solver_env();
        Solver::new(terms, &mut env).prove(&atoms, goal)
    }

    // ---- the R5a procedure ----

    /// R5a steps 1–5 for one cup goal.
    pub(super) fn auto_feed(&mut self, goal: &Atom, edge: Option<Entry>) -> AutoOutcome {
        let mut hyps = self.relevant(goal, edge);
        hyps.reverse(); // top of lane first
        let n = hyps.len();
        let mut out = self.solve(&hyps, goal);
        if matches!(out, Outcome::Cap(_) | Outcome::Inexact(_)) && n > FALLBACK {
            let recent = hyps[..FALLBACK].to_vec();
            let o2 = self.solve(&recent, goal);
            // keep the first failure unless the 8 recent facts succeed: a cap on the whole
            // relevant set is the useful message (it says to choose facts with `prove k`)
            if let Outcome::Valid { .. } = o2 {
                hyps = recent;
                out = o2;
            }
        }
        let Outcome::Valid { mut wraps } = out else {
            return AutoOutcome::Failed(match out {
                Outcome::Cap(c) => Some(format!(
                    "the {n} relevant facts exceed the solver's limits ({c}); choose facts with prove k"
                )),
                Outcome::Inexact(s) => Some(s),
                Outcome::NotImplied(m) if n > 0 && !m.is_empty() => {
                    let cm: Vec<String> = m.iter().map(|(v, x)| format!("{v}={x}")).collect();
                    Some(format!(
                        "{} about these values allow{} {}",
                        if n == 1 {
                            "the one fact".to_string()
                        } else {
                            format!("the {n} facts")
                        },
                        if n == 1 { "s" } else { "" },
                        cm.join(", ")
                    ))
                }
                _ => None,
            });
        };
        // minimize: drop facts oldest first while the goal still follows
        let mut j = hyps.len();
        while j > 0 {
            j -= 1;
            let mut fewer = hyps.clone();
            fewer.remove(j);
            if let Outcome::Valid { wraps: w } = self.solve(&fewer, goal) {
                hyps = fewer;
                wraps = w;
            }
        }
        AutoOutcome::Fed { used: hyps, wraps }
    }

    /// Do these facts contradict each other? (for the vericoding probe on locked lines)
    pub(super) fn contradictory(&mut self, hyps: &[Entry]) -> bool {
        !hyps.is_empty() && matches!(self.solve(hyps, &Atom::False), Outcome::Valid { .. })
    }
}
