//! Semantic reachability for the editor: body regions that can never run because the solver
//! decides a branch condition (the fall-through of a `br_if` whose condition is always nonzero,
//! an `if` arm whose entry fact is unsatisfiable). The kernel's own dead-code notion (R22,
//! `dead_lines`) is syntactic and feeds verdicts; this one is informational only: nothing here
//! changes a cup, a verdict or an error, so it can be merged with (or replaced by) a semantic
//! dead-lines analysis on the judge's side without touching soundness.

use super::ast::Ins;
use super::out::NeverRuns;
use super::term::Atom;

/// The index just past the arm that starts at `from` (the arm's `else`/`end`, or the body end).
fn arm_end(body: &[(u32, Ins)], from: usize) -> usize {
    let mut depth = 0usize;
    for (i, (_, ins)) in body.iter().enumerate().skip(from) {
        match ins {
            Ins::Block(..) => depth += 1,
            Ins::End if depth == 0 => return i,
            Ins::End => depth -= 1,
            Ins::Else if depth == 0 => return i,
            _ => {}
        }
    }
    body.len()
}

/// The `if` that an `else` at index `at` belongs to.
fn if_of_else(body: &[(u32, Ins)], at: usize) -> Option<usize> {
    let mut depth = 0usize;
    for i in (0..at).rev() {
        match &body[i].1 {
            Ins::End => depth += 1,
            Ins::Block(..) if depth > 0 => depth -= 1,
            Ins::Block(..) => return Some(i),
            _ => {}
        }
    }
    None
}

/// Regions that never run. `facts` are the pass's facts as (birth line, rule kind, atom);
/// `unsat` decides whether an atom alone is unsatisfiable (`prove [a] ⊢ False`).
pub fn never_runs<'a>(
    body: &[(u32, Ins)],
    facts: impl IntoIterator<Item = (u32, &'a str, &'a Atom)>,
    mut unsat: impl FnMut(&Atom) -> bool,
) -> Vec<NeverRuns> {
    let mut out: Vec<NeverRuns> = vec![];
    for (line, kind, atom) in facts {
        let (start, why) = match kind {
            "br_if fall-through" => {
                let Some(pc) = body
                    .iter()
                    .position(|(l, i)| *l == line && matches!(i, Ins::BrIf(_)))
                else {
                    continue;
                };
                (pc + 1, format!("br_if on line {line} always branches"))
            }
            "if then-arm" => {
                let Some(pc) = body
                    .iter()
                    .position(|(l, i)| *l == line && matches!(i, Ins::Block(..)))
                else {
                    continue;
                };
                (
                    pc + 1,
                    format!("the condition of the if on line {line} is always false"),
                )
            }
            "if else-arm" => {
                let Some(pc) = body
                    .iter()
                    .position(|(l, i)| *l == line && matches!(i, Ins::Else))
                else {
                    continue;
                };
                let il = if_of_else(body, pc).map(|i| body[i].0).unwrap_or(line);
                (
                    pc + 1,
                    format!("the condition of the if on line {il} is always true"),
                )
            }
            _ => continue,
        };
        let stop = arm_end(body, start);
        if stop <= start {
            continue;
        }
        let (from, to) = (body[start].0, body[stop - 1].0);
        // inside a region already found: nothing new to say
        if out.iter().any(|r| r.from <= line && line <= r.to) {
            continue;
        }
        if !unsat(atom) {
            continue;
        }
        out.push(NeverRuns {
            from,
            to,
            cause: line,
            why,
        });
    }
    out
}
