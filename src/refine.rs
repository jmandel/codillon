// Refined shapes: what to draw for a value whose type is refined, `(i32 | P)`.
//
// The shape is a number line. `region` reads the simple facts that P states about its
// subject (bounds such as `0 <= $x < $n`, an exact value, a parity) so they can be drawn as
// a shaded region with fence posts and a comb; bounds may depend on other values
// (dependent refinements) and are evaluated at the current step. Whether the current value
// is admitted is decided by evaluating P itself, not the drawing, so a predicate the
// drawing cannot depict is still checked exactly.

use crate::spec::{self, BinOp, CmpOp, Define, Env, Expr, Val};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Bound {
    pub value: i128,
    pub inclusive: bool,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Region {
    pub lower: Option<Bound>,
    pub upper: Option<Bound>,
    pub parity: Option<i128>, // admitted residue mod 2
    pub depicted: bool,       // at least one fact was understood
}

impl Region {
    /// Smallest and largest admitted integers within [min, max] (ignoring parity).
    pub fn span(&self, min: i128, max: i128) -> Option<(i128, i128)> {
        let lo = match self.lower {
            Some(b) => b.value + if b.inclusive { 0 } else { 1 },
            None => min,
        }
        .max(min);
        let hi = match self.upper {
            Some(b) => b.value - if b.inclusive { 0 } else { 1 },
            None => max,
        }
        .min(max);
        (lo <= hi).then_some((lo, hi))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RefinedDraw {
    pub value: Option<i128>,
    pub region: Region,
    pub admitted: Option<bool>, // None: unknown (no value, or P could not be evaluated)
}

fn mentions(e: &Expr, subject: &str) -> bool {
    let mut found = false;
    e.walk(&mut |x| {
        if matches!(x, Expr::Var(v) if v == subject) {
            found = true
        }
    });
    found
}

fn conjuncts<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    match e {
        Expr::Bin(BinOp::And, a, b) => {
            conjuncts(a, out);
            conjuncts(b, out);
        }
        _ => out.push(e),
    }
}

fn flip(op: CmpOp) -> CmpOp {
    match op {
        CmpOp::Lt => CmpOp::Gt,
        CmpOp::Le => CmpOp::Ge,
        CmpOp::Gt => CmpOp::Lt,
        CmpOp::Ge => CmpOp::Le,
        o => o,
    }
}

// `$x % 2` ?
fn is_mod2_of(e: &Expr, subject: &str) -> bool {
    matches!(e, Expr::Bin(BinOp::Rem, a, b)
        if matches!(&**a, Expr::Var(v) if v == subject) && **b == Expr::Int(2))
}

/// The facts of `pred` about `$subject` that a number line can show.
pub fn region(pred: &Expr, subject: &str, env: &dyn Env) -> Region {
    let mut r = Region::default();
    let mut atoms = vec![];
    conjuncts(pred, &mut atoms);
    let eval = |e: &Expr| match spec::eval(e, env) {
        Ok(Val::Int(i)) => Some(i),
        _ => None,
    };
    for atom in atoms {
        let Expr::Chain(es, ops) = atom else {
            continue;
        };
        for (i, op) in ops.iter().enumerate() {
            let (l, rr) = (&es[i], &es[i + 1]);
            // parity: $x % 2 == c
            if *op == CmpOp::Eq {
                let (m, c) = if is_mod2_of(l, subject) {
                    (true, rr)
                } else if is_mod2_of(rr, subject) {
                    (true, l)
                } else {
                    (false, l)
                };
                if m && !mentions(c, subject) {
                    if let Some(c) = eval(c) {
                        r.parity = Some(c.rem_euclid(2));
                        r.depicted = true;
                    }
                    continue;
                }
            }
            let (op, other) = match (l, rr) {
                (Expr::Var(v), o) if v == subject && !mentions(o, subject) => (*op, o),
                (o, Expr::Var(v)) if v == subject && !mentions(o, subject) => (flip(*op), o),
                _ => continue,
            };
            let Some(c) = eval(other) else { continue };
            let mut set_lower = |b: Bound| {
                let tighter = match r.lower {
                    None => true,
                    Some(old) => b.value > old.value || (b.value == old.value && !b.inclusive),
                };
                if tighter {
                    r.lower = Some(b)
                }
            };
            match op {
                CmpOp::Gt => set_lower(Bound {
                    value: c,
                    inclusive: false,
                }),
                CmpOp::Ge => set_lower(Bound {
                    value: c,
                    inclusive: true,
                }),
                CmpOp::Eq => {
                    set_lower(Bound {
                        value: c,
                        inclusive: true,
                    });
                    r.upper = Some(Bound {
                        value: c,
                        inclusive: true,
                    });
                }
                _ => {}
            }
            let mut set_upper = |b: Bound| {
                let tighter = match r.upper {
                    None => true,
                    Some(old) => b.value < old.value || (b.value == old.value && !b.inclusive),
                };
                if tighter {
                    r.upper = Some(b)
                }
            };
            match op {
                CmpOp::Lt => set_upper(Bound {
                    value: c,
                    inclusive: false,
                }),
                CmpOp::Le => set_upper(Bound {
                    value: c,
                    inclusive: true,
                }),
                _ => {}
            }
            if op != CmpOp::Ne {
                r.depicted = true;
            }
        }
    }
    r
}

// An environment where `$subject` has a given value.
struct With<'a> {
    env: &'a dyn Env,
    subject: &'a str,
    value: i128,
}

impl Env for With<'_> {
    fn var(&self, name: &str) -> Option<Val> {
        if name == self.subject {
            Some(Val::Int(self.value))
        } else {
            self.env.var(name)
        }
    }
    fn old_var(&self, name: &str) -> Option<Val> {
        self.env.old_var(name)
    }
    fn width(&self, name: &str) -> u32 {
        self.env.width(name)
    }
    fn load(&self, addr: i128, bytes: u32) -> Result<u64, spec::EvalError> {
        self.env.load(addr, bytes)
    }
    fn define(&self, name: &str) -> Option<&Define> {
        self.env.define(name)
    }
}

/// Everything needed to draw a refined value at the current step.
pub fn refined_draw(pred: &Expr, subject: &str, value: Option<i128>, env: &dyn Env) -> RefinedDraw {
    let region = region(pred, subject, env);
    let admitted = value.and_then(|v| {
        spec::eval_bool(
            pred,
            &With {
                env,
                subject,
                value: v,
            },
        )
        .ok()
    });
    RefinedDraw {
        value,
        region,
        admitted,
    }
}

/// Position of `v` on a number line spanning [-1, 1]: linear for |v| <= 8 across the
/// middle 60%, logarithmic out to the walls (which stand for the extremes of i32).
pub fn number_line_pos(v: i128) -> f32 {
    let a = v.unsigned_abs() as f64;
    let s = if v < 0 { -1.0 } else { 1.0 };
    let f = if a <= 8.0 {
        0.6 * a / 8.0
    } else {
        let max = (1u64 << 31) as f64 / 8.0;
        0.6 + 0.4 * ((a / 8.0).ln() / max.ln()).min(1.0)
    };
    (s * f) as f32
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    struct E(HashMap<String, i128>, Vec<Define>);
    impl Env for E {
        fn var(&self, name: &str) -> Option<Val> {
            self.0.get(name).map(|v| Val::Int(*v))
        }
        fn define(&self, name: &str) -> Option<&Define> {
            self.1.iter().find(|d| d.name == name)
        }
    }
    fn env(vars: &[(&str, i128)]) -> E {
        E(
            vars.iter().map(|(k, v)| (k.to_string(), *v)).collect(),
            vec![],
        )
    }
    fn p(s: &str) -> Expr {
        spec::parse_expr(s).unwrap()
    }

    #[test]
    fn regions() {
        let e = env(&[("n", 10)]);
        let r = region(&p("0 <= $x"), "x", &e);
        assert_eq!(
            r.lower,
            Some(Bound {
                value: 0,
                inclusive: true
            })
        );
        assert_eq!(r.upper, None);
        assert!(r.depicted);
        // chains and dependent bounds
        let r = region(&p("0 <= $i < $n && $i != 3"), "i", &e);
        assert_eq!(r.span(-100, 100), Some((0, 9)));
        assert_eq!(
            r.upper,
            Some(Bound {
                value: 10,
                inclusive: false
            })
        );
        // tightest bound wins, either side
        let r = region(&p("$x > 2 && 5 >= $x && $x >= 0"), "x", &e);
        assert_eq!(r.span(-100, 100), Some((3, 5)));
        // exact (dependent) value
        let mut e2 = env(&[("a", 12), ("b", 8)]);
        e2.1 = match spec::parse_annotation(
            "(@define gcd($x, $y) = ($y == 0 ? $x : gcd($y, $x % $y)))",
        )
        .unwrap()
        {
            spec::Annotation::Define(d) => d,
            _ => panic!(),
        };
        let r = region(&p("$g == gcd($a, $b)"), "g", &e2);
        assert_eq!(r.span(-100, 100), Some((4, 4)));
        // parity
        let r = region(&p("$x % 2 == 0"), "x", &e);
        assert_eq!(r.parity, Some(0));
        assert_eq!(r.span(-5, 5), Some((-5, 5)));
        // facts the line cannot show
        let r = region(&p("$h + $h == $x"), "h", &e);
        assert!(!r.depicted);
        let r = region(&p("$x < 0 || $x > 5"), "x", &e);
        assert!(!r.depicted);
    }

    #[test]
    fn admission_uses_the_predicate() {
        let e = env(&[("x", 7)]);
        let d = refined_draw(&p("$h + $h == $x"), "h", Some(3), &e);
        assert_eq!(d.admitted, Some(false));
        let d = refined_draw(&p("$x % 2 == 0"), "x", Some(-4), &e);
        assert_eq!(d.admitted, Some(true));
        let d = refined_draw(&p("$x % 2 == 0"), "x", None, &e);
        assert_eq!(d.admitted, None);
        let d = refined_draw(&p("$y > $q"), "y", Some(1), &e);
        assert_eq!(d.admitted, None);
    }

    #[test]
    fn positions() {
        assert_eq!(number_line_pos(0), 0.0);
        assert!((number_line_pos(8) - 0.6).abs() < 1e-6);
        assert!((number_line_pos(-4) + 0.3).abs() < 1e-6);
        assert!((number_line_pos(i32::MAX as i128) - 1.0).abs() < 1e-3);
        assert!((number_line_pos(i32::MIN as i128) + 1.0).abs() < 1e-3);
        assert!(number_line_pos(100) < number_line_pos(1000));
        assert!(number_line_pos(i64::MAX as i128) <= 1.0);
    }
}
