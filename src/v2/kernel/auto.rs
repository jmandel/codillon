//! R5a — automatic feeding (design 16 §2, research/24): a cup that lookup, evaluation and a
//! pending `prove` leave unfed is fed when the decision procedure (§3) proves its goal from the
//! in-scope facts relevant to it, minimized to the facts the proof uses.

use super::super::solver::UNFOLD_DEPTH;
use super::*;

/// Facts handed to the solver after a cap: the 8 closest relevant facts (what `prove 8` sees).
const FALLBACK: usize = 8;
/// §3.1's atom cap: hypotheses plus the goal.
pub const CAP_ATOMS: usize = 32;
/// Solver cases R5a may enumerate in one function pass (research/24 §5): a deterministic
/// measure of work, about 0.1 s native at the worst observed cost per case.
pub const AUTO_BUDGET: u32 = 16384;

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

    /// The non-constant canonical ids reachable from a term (the term itself included), looking
    /// through R29 unfoldings to §3's depth, so a memory predicate reaches the loads it reads.
    fn term_ids(&mut self, t: TermId, depth: u32, out: &mut BTreeSet<TermId>) {
        if self.terms.is_const(t) || !out.insert(t) {
            return;
        }
        let kids: Vec<TermId> = match self.terms.key(t) {
            Key::Op(_, _, a) | Key::Float(_, a) => a.to_vec(),
            Key::Call(_, a, _) => a.to_vec(),
            Key::Load(.., a, _) => vec![*a],
            Key::Ite(c, a, b) => vec![*c, *a, *b],
            Key::Const(..) | Key::Leaf(_) => vec![],
        };
        for k in kids {
            self.term_ids(k, depth, out);
        }
        if depth < UNFOLD_DEPTH && matches!(self.terms.key(t), Key::Call(..)) {
            let body = {
                let (terms, mut env) = self.solver_env();
                env.unfold(terms, t)
            };
            if let Some(b) = body {
                self.term_ids(b, depth + 1, out);
            }
        }
    }

    /// `ids(A)` of R5a step 2.
    pub(super) fn atom_ids(&mut self, a: &Atom) -> BTreeSet<TermId> {
        fn roots(a: &Atom, v: &mut Vec<TermId>) {
            match a {
                Atom::Cmp { a, b, .. } => v.extend([*a, *b]),
                Atom::Bool { t, .. } => v.push(*t),
                Atom::Or(x, y) => {
                    roots(x, v);
                    roots(y, v);
                }
                Atom::True | Atom::False => {}
            }
        }
        let mut ts = vec![];
        roots(a, &mut ts);
        let mut out = BTreeSet::new();
        for t in ts {
            self.term_ids(t, 0, &mut out);
        }
        out
    }

    /// R5a steps 1–2: the in-scope facts that share a value with the goal, closed transitively,
    /// each with its ring (1 = shares a value with the goal, 2 = with a ring-1 fact, …), in lane
    /// order (oldest first; a taken-edge fact last). For `False`, every candidate, ring 1.
    fn relevant(&mut self, goal: &Atom, edge: Option<Entry>) -> Vec<(Entry, u32)> {
        let cands: Vec<Entry> = self.lane.iter().copied().chain(edge).collect();
        if *goal == Atom::False {
            return cands.into_iter().map(|e| (e, 1)).collect();
        }
        let ids: Vec<BTreeSet<TermId>> = cands
            .iter()
            .map(|e| {
                let a = self.facts[e.fact as usize].atom.clone();
                self.atom_ids(&a)
            })
            .collect();
        let mut s = self.atom_ids(goal);
        let mut ring = vec![0u32; cands.len()];
        let mut r = 0;
        loop {
            r += 1;
            // one ring: every fact touching the values known before this ring
            let hit: Vec<usize> = (0..cands.len())
                .filter(|&i| ring[i] == 0 && !ids[i].is_disjoint(&s))
                .collect();
            if hit.is_empty() {
                break;
            }
            for i in hit {
                ring[i] = r;
                s.extend(ids[i].iter().copied());
            }
        }
        cands
            .into_iter()
            .zip(ring)
            .filter(|(_, r)| *r > 0)
            .collect()
    }

    /// A fact whose derivation rests on no assumption and no runtime check, as far as the pass
    /// knows yet (S1: minimization prefers these).
    fn clean(&self, e: Entry) -> bool {
        let (checks, assumes) = self.closure(&[Dep::Fact(e.fact)]);
        checks.is_empty() && assumes.is_empty()
    }

    // ---- one solver call ----

    /// §3 on `hyps ⇒ goal`, hypotheses given top of lane first (as `prove k` gives them).
    pub(super) fn solve(&mut self, hyps: &[Entry], goal: &Atom) -> Outcome {
        self.solve_counted(hyps, goal).0
    }

    /// `solve`, also returning the number of cases enumerated.
    fn solve_counted(&mut self, hyps: &[Entry], goal: &Atom) -> (Outcome, u32) {
        let atoms: Vec<Atom> = hyps
            .iter()
            .map(|e| self.facts[e.fact as usize].atom.clone())
            .collect();
        let (terms, mut env) = self.solver_env();
        let mut s = Solver::new(terms, &mut env);
        let o = s.prove(&atoms, goal);
        (o, s.cases)
    }

    /// One R5a call: counted against the function's budget, and refused over the atom cap.
    fn auto_solve(&mut self, hyps: &[Entry], goal: &Atom) -> Outcome {
        if hyps.len() + 1 > CAP_ATOMS {
            return Outcome::Cap(format!("{} atoms (cap {CAP_ATOMS})", hyps.len() + 1));
        }
        if self.auto_calls >= AUTO_BUDGET {
            return Outcome::Cap(format!(
                "this function used its budget of {AUTO_BUDGET} automatic proof cases"
            ));
        }
        let (o, cases) = self.solve_counted(hyps, goal);
        self.auto_calls += cases;
        o
    }

    // ---- the R5a procedure ----

    /// R5a steps 1–5 for one cup goal. Hypotheses always go to §3 top of lane first.
    pub(super) fn auto_feed(&mut self, goal: &Atom, edge: Option<Entry>) -> AutoOutcome {
        let rel = self.relevant(goal, edge);
        let n = rel.len();
        let all: Vec<Entry> = rel.iter().rev().map(|x| x.0).collect();
        let clean: Vec<bool> = all.iter().map(|e| self.clean(*e)).collect();
        let ring: Vec<u32> = rel.iter().rev().map(|x| x.1).collect();
        let max_ring = ring.iter().copied().max().unwrap_or(1);
        let mut found: Option<(Vec<Entry>, Vec<String>)> = None;
        let mut first_fail = None;
        // deepen by ring (facts sharing a value with the goal, then with those, …): the first
        // stage that proves the goal is the one minimized. The last stage is the whole relevant
        // set, so this never fails where one call on the whole set would succeed.
        for r in 1..=max_ring {
            let stage: Vec<usize> = (0..n).filter(|&i| ring[i] <= r).collect();
            if r < max_ring && stage.len() == (0..n).filter(|&i| ring[i] <= r + 1).count() {
                continue;
            }
            let pick = |only_clean: bool| -> Vec<Entry> {
                stage
                    .iter()
                    .filter(|&&i| !only_clean || clean[i])
                    .map(|&i| all[i])
                    .collect()
            };
            // S1: when some fact rests on an assumption or a check, try without those first
            if stage.iter().any(|&i| !clean[i]) {
                let cs = pick(true);
                if let Outcome::Valid { wraps } = self.auto_solve(&cs, goal) {
                    found = Some((cs, wraps));
                    break;
                }
            }
            let st = pick(false);
            match self.auto_solve(&st, goal) {
                Outcome::Valid { wraps } => {
                    found = Some((st, wraps));
                    break;
                }
                o if r == max_ring => first_fail = Some(o),
                _ => {}
            }
        }
        // after a cap (or an inexact step): the 8 closest facts, by ring, ties to the most recent
        let mut near_fail = None;
        if found.is_none()
            && matches!(first_fail, Some(Outcome::Cap(_) | Outcome::Inexact(_)))
            && n > FALLBACK
        {
            let mut order: Vec<usize> = (0..n).collect();
            order.sort_by_key(|&i| (rel[i].1, std::cmp::Reverse(i)));
            let ring = rel[order[FALLBACK - 1]].1;
            let mut pick = order[..FALLBACK].to_vec();
            pick.sort_by_key(|&i| std::cmp::Reverse(i));
            let near: Vec<Entry> = pick.iter().map(|&i| rel[i].0).collect();
            match self.auto_solve(&near, goal) {
                Outcome::Valid { wraps } => found = Some((near, wraps)),
                o => near_fail = Some((o, ring)),
            }
        }
        let Some((mut hyps, mut wraps)) = found else {
            return AutoOutcome::Failed(auto_failure(n, first_fail, near_fail));
        };
        // minimize: drop facts resting on assumptions or checks first, then oldest first; a drop
        // is kept only when §3 still answers Valid (Cap, Inexact or NotImplied keep the fact)
        let drops: Vec<Entry> = hyps.iter().rev().copied().collect();
        let weak: Vec<bool> = drops.iter().map(|e| !self.clean(*e)).collect();
        let mut idx: Vec<usize> = (0..drops.len()).collect();
        idx.sort_by_key(|&i| !weak[i]);
        let drops: Vec<Entry> = idx.into_iter().map(|i| drops[i]).collect();
        for e in drops {
            let fewer: Vec<Entry> = hyps.iter().copied().filter(|x| *x != e).collect();
            if let Outcome::Valid { wraps: w } = self.auto_solve(&fewer, goal) {
                hyps = fewer;
                wraps = w;
            }
        }
        AutoOutcome::Fed { used: hyps, wraps }
    }

    /// Do these facts contradict each other?
    pub(super) fn contradictory(&mut self, hyps: &[Entry]) -> bool {
        !hyps.is_empty() && matches!(self.solve(hyps, &Atom::False), Outcome::Valid { .. })
    }

    /// Is some recorded contradictory feed still wholly in scope (in the lane, or `extra`)?
    pub(super) fn contra_in_scope(&self, extra: &[Entry]) -> bool {
        self.contras.iter().any(|set| {
            set.iter()
                .all(|e| self.lane.contains(e) || extra.contains(e))
        })
    }
}

fn model_text(m: &[(String, i128)]) -> String {
    m.iter()
        .map(|(v, x)| format!("{v}={x}"))
        .collect::<Vec<_>>()
        .join(", ")
}

/// The diagnostic of a failed R5a attempt (design 16 §3.7).
fn auto_failure(n: usize, first: Option<Outcome>, near: Option<(Outcome, u32)>) -> Option<String> {
    let facts = |n: usize| {
        if n == 1 {
            "the one fact".to_string()
        } else {
            format!("the {n} facts")
        }
    };
    match first? {
        Outcome::Cap(c) => Some(match near {
            Some((Outcome::NotImplied(m), ring)) if !m.is_empty() => format!(
                "{} about these values exceed the solver's limits ({c}); the 8 closest (up to ring {ring}) allow {}; choose facts with prove k",
                facts(n),
                model_text(&m)
            ),
            _ => format!(
                "{} about these values exceed the solver's limits ({c}); choose facts with prove k",
                facts(n)
            ),
        }),
        Outcome::Inexact(s) => Some(s),
        Outcome::NotImplied(m) if n > 0 && !m.is_empty() => Some(format!(
            "{} about these values allow{} {}",
            facts(n),
            if n == 1 { "s" } else { "" },
            model_text(&m)
        )),
        _ => None,
    }
}
