// Drawing the v2 kernel's results (design 16 §8) in Codillon's idiom.
//
// This module is pure: from the kernel's `ModuleOut`, the editor's per-line geometry and the
// run's failed check (if any), it builds two SVG layers (wires under the fractions, cups and
// chips over them) and per-line annotations (hover text, commentary, header badges). The
// editor installs them; nothing here touches the DOM.
//
// Geometry (SVG coordinates, as in graphics.rs): line `idx` (0-based) is centred at
// y = idx·45 + 30.5; a line at indent i has its fraction centred at x = 159.5 + 25·i and its
// code starting at x = 201 + 25·i + LANE_PX. The LANE_PX gap between them is the fact lane:
// proof cups sit in the upper (input) row right of the value cups, fact chips in the lower row
// just left of the code, and each chip's wire runs down a trunk at the chip's x.

use crate::line::LANE_PX;
use crate::v2::out::{CupKind, CupOut, Feed, FuncOut, ModuleOut, Verdict, Witness};
use std::collections::HashMap;
use std::fmt::Write;

const LS: f32 = 45.0;
const HALF: f32 = 7.0; // half-diagonal of a proof cup
const STEP: f32 = 16.0; // spacing of proof cups
const CHIP: f32 = 4.6; // half-diagonal of a fact chip
const CHIP_STEP: f32 = 11.0;
const TRACK_GAP: f32 = 3.5;

pub const PURPLE: &str = "#6A5ACD";
pub const DARK_PURPLE: &str = "#483D8B";
const DARKRED: &str = "darkred";

/// What the editor knows about one line's layout (0-based by editor line).
#[derive(Clone, Debug, Default)]
pub struct LineGeom {
    pub indent: Option<u16>,
    /// right edge of the line's value input cups, if it has a fraction with inputs
    pub frac_right: Option<f32>,
    /// the line's instruction, as a consumer is named in a prove's goal line (`i32.add`,
    /// `call $f`, `unreachable`)
    pub op: Option<String>,
}

/// Per-line results for the text column (0-based by editor line).
#[derive(Clone, Debug, Default, PartialEq)]
pub struct LineProof {
    /// hover text: every proof cup on the line and its verdict
    pub title: Option<String>,
    /// darkred commentary (a violation: refuted cup, failed prove, kernel error)
    pub note: Option<String>,
    /// quiet commentary (a runtime-checked cup and why nothing feeds it)
    pub quiet: Option<String>,
    /// header badge: (text, class suffix: "verified" | "gradual")
    pub badge: Option<(String, &'static str)>,
    /// the code runs past the window's right edge: commentary is pinned to the edge (review 19 §1)
    pub wide: bool,
    /// vericoding mode: a student-owned line (locked while the implementation is written)
    pub locked: bool,
    /// vericoding commentary: (text, tone) with tone "lock" (a refused edit), "reject" (a
    /// rejected submission, darkred) or "mutant" (a surviving mutant)
    pub vnote: Option<(String, &'static str)>,
    /// always on, right of the code (research/24 §4): what each proof cup on the line needs and
    /// where it came from, and the facts the line gives (`gives (x·2)&1 ≠ 0 · needs x ≠ 0 ✓ line 8`)
    pub label: Option<String>,
    /// the label does not fit right of the code (a wide line, a long code comment, a long
    /// label): it goes in the gap below the line instead, in full (set by the editor, which
    /// knows the window)
    pub label_below: bool,
    /// for a label below: its width at the gap's font size and the right edge of the room for
    /// it, in the line's coordinates (the label shifts left of the code, over the lane, rather
    /// than wrap or run under the accounts column)
    pub label_fit: (f32, f32),
    /// the reason in brief (at most two sentences), shown under the label for every line when
    /// "show all proofs" is on
    pub brief: Option<String>,
    /// the account of the line's proofs, one sentence per line: what is needed, the facts used
    /// and where they came from, why it holds. Shown below the line for the cursor line, on
    /// hover, and for every line under "show all proofs"
    pub explain: Option<String>,
    /// the kernel shows this line can never run (a decided branch): drawn lightly greyed
    pub never: bool,
    /// hover text for the row's fact lane: the propositions on the chips and ribbons here
    pub lane: Option<String>,
}

#[derive(Default)]
pub struct Scene {
    pub under: String,
    pub over: String,
    pub lines: Vec<LineProof>,
}

/// A run's failed check: the 1-based kernel line of its cup and the message.
pub struct RunFailure {
    pub line: u32,
    pub message: String,
}

/// §8's runtime-check mark: a small gray stopwatch ("checked when run"), never a bomb (a bomb
/// means a check failed in this run).
fn stopwatch(cx: f32, cy: f32) -> String {
    format!(
        "<g class=\"pv-watch\"><circle cx=\"{cx:.1}\" cy=\"{cy:.1}\" r=\"3.1\"/>\
<path d=\"M{cx:.1} {:.1}v-1.4M{:.1} {:.1}h2.2M{cx:.1} {cy:.1}l1.5 -1.5\"/></g>",
        cy - 3.1,
        cx - 1.1,
        cy - 4.5
    )
}

/// Vericoding: a small padlock left of the code (a refused edit: quiet; a rejected submission:
/// darkred), in the proof layer's visual language.
pub fn lock_glyph(line: u32, indent: u16, red: bool) -> String {
    let x = code_x(indent) - 13.0;
    let y = y_mid(line) - 4.0;
    let col = if red { DARKRED } else { "#6c6880" };
    format!(
        "<g class=\"pv-lock\" stroke=\"{col}\" fill=\"none\" stroke-width=\"1.3\">\
<path d=\"M{:.1} {:.1}v-2.6a2.9 2.9 0 0 1 5.8 0v2.6\"/>\
<rect x=\"{:.1}\" y=\"{:.1}\" width=\"8.4\" height=\"6.6\" rx=\"1.2\" fill=\"#fffff0\"/>\
<circle cx=\"{:.1}\" cy=\"{:.1}\" r=\"0.9\" fill=\"{col}\" stroke=\"none\"/></g>",
        x - 2.9,
        y,
        x - 4.2,
        y,
        x,
        y + 3.2
    )
}

/// Vericoding: the wash behind a line whose surviving mutant is in focus, with the mutated text
/// as a ghost to its left (dashed purple-gray: a weakness of the spec, not a violation).
pub fn mutant_wash(line: u32, indent: u16, to: &str) -> String {
    let x = code_x(indent) - 6.0;
    let y = y_mid(line) - 19.0;
    format!(
        "<rect x=\"{x:.1}\" y=\"{y:.1}\" width=\"520\" height=\"38\" rx=\"6\" class=\"pv-mutant\"/>\
<text x=\"{:.1}\" y=\"{:.1}\" class=\"pv-mutant-text\">μ {}</text>",
        x + 4.0,
        y - 2.0,
        esc(to)
    )
}

pub fn y_mid(line: u32) -> f32 {
    (line.saturating_sub(1)) as f32 * LS + 30.5
}

pub fn code_x(indent: u16) -> f32 {
    201.0 + 25.0 * indent as f32 + LANE_PX as f32
}

pub fn frac_x(indent: u16) -> f32 {
    159.5 + 25.0 * indent as f32
}

pub fn esc(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

fn diamond(x: f32, y: f32, h: f32) -> String {
    format!(
        "M{:.1},{:.1}L{:.1},{:.1}L{:.1},{:.1}L{:.1},{:.1}Z",
        x,
        y - h,
        x + h,
        y,
        x,
        y + h,
        x - h,
        y
    )
}

/// How a cup is drawn.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Look {
    Proven,
    Assumed,
    Checked,
    Refuted,
    /// ghost/predicate code that nothing feeds: never run, so an error, but not a violation
    GhostUnfed,
}

fn look(c: &CupOut, failed_here: bool) -> Look {
    match c.verdict {
        Verdict::Refuted => Look::Refuted,
        Verdict::RuntimeChecked if failed_here => Look::Refuted,
        Verdict::RuntimeChecked if c.ghost => Look::GhostUnfed,
        Verdict::RuntimeChecked => Look::Checked,
        Verdict::Assumed => Look::Assumed,
        Verdict::Proven => Look::Proven,
    }
}

/// Defs used by the proof layers (patterns are document-global by id).
fn defs() -> String {
    format!(
        "<defs><pattern id=\"pv-hatch\" width=\"3\" height=\"3\" patternUnits=\"userSpaceOnUse\" patternTransform=\"rotate(45)\">\
<rect width=\"3\" height=\"3\" fill=\"#d9d4f3\"/><line x1=\"0\" y1=\"0\" x2=\"0\" y2=\"3\" stroke=\"{PURPLE}\" stroke-width=\"1.1\"/></pattern></defs>"
    )
}

struct CupMark {
    x: f32,
    y: f32,
    h: f32,
    look: Look,
    star: bool,
    eval: bool,
    false_cup: bool,
    label: Option<String>,
}

impl CupMark {
    fn socket(&self) -> bool {
        self.label.is_some()
    }
}

fn draw_cup(o: &mut String, m: &CupMark) {
    let d = diamond(m.x, m.y, m.h);
    let (x, y, h) = (m.x, m.y, m.h);
    match m.look {
        Look::Proven => {
            let _ = write!(
                o,
                "<path d=\"{d}\" fill=\"{PURPLE}\" stroke=\"{DARK_PURPLE}\" stroke-width=\"1\"/>"
            );
        }
        Look::Assumed => {
            let _ = write!(
                o,
                "<path d=\"{d}\" fill=\"url(#pv-hatch)\" stroke=\"{PURPLE}\" stroke-width=\"1\" opacity=\"0.7\"/>"
            );
            if !m.socket() {
                let _ = write!(
                    o,
                    "<circle cx=\"{:.1}\" cy=\"{:.1}\" r=\"2.3\" fill=\"none\" stroke=\"{PURPLE}\" stroke-width=\"0.9\"/>",
                    x + h + 1.5,
                    y - h + 0.5
                );
            }
        }
        Look::Checked => {
            let _ = write!(
                o,
                "<path d=\"{d}\" fill=\"url(#fade-up)\" stroke=\"#777\" stroke-width=\"1.2\" stroke-dasharray=\"2.2 1.6\"/>{}",
                stopwatch(x + h + 4.0, y - h + 0.5)
            );
        }
        Look::GhostUnfed => {
            let _ = write!(
                o,
                "<path d=\"{d}\" fill=\"#fffff0\" stroke=\"{DARKRED}\" stroke-width=\"1.2\" stroke-dasharray=\"2.2 1.6\"/>"
            );
        }
        Look::Refuted => {
            // a broken double rim: an outer outline with gaps and an inner one
            let _ = write!(
                o,
                "<path d=\"{d}\" fill=\"#fffff0\" stroke=\"{DARKRED}\" stroke-width=\"1.7\" stroke-dasharray=\"5.5 2.4\"/>\
<path d=\"{}\" fill=\"none\" stroke=\"{DARKRED}\" stroke-width=\"0.9\"/>",
                diamond(x, y, (h - 2.6).max(1.5))
            );
        }
    }
    let solid = matches!(m.look, Look::Proven);
    let ink = if solid {
        "#fff"
    } else if m.look == Look::Refuted {
        DARKRED
    } else {
        "#444"
    };
    if m.false_cup {
        let _ = write!(
            o,
            "<text x=\"{x:.1}\" y=\"{:.1}\" class=\"pv-in\" fill=\"{ink}\">⊥</text>",
            y + 0.3
        );
    } else if m.eval {
        let _ = write!(
            o,
            "<text x=\"{x:.1}\" y=\"{:.1}\" class=\"pv-in\" fill=\"{ink}\">=</text>",
            y + 0.3
        );
    } else if let Some(l) = &m.label {
        let _ = write!(
            o,
            "<text x=\"{x:.1}\" y=\"{:.1}\" class=\"pv-in\" fill=\"{ink}\">{}</text>",
            y + 0.4,
            esc(l)
        );
    }
    if m.star {
        let _ = write!(
            o,
            "<text x=\"{:.1}\" y=\"{:.1}\" class=\"pv-star\">*</text>",
            x + h + 1.0,
            y - h + 4.0
        );
    }
}

/// Byte ranges of the `(fact …)` clauses in a line (balanced parentheses).
pub fn fact_clauses(text: &str) -> Vec<(usize, usize)> {
    let mut ret = vec![];
    let mut from = 0;
    while let Some(p) = text[from..].find("(fact") {
        let start = from + p;
        let mut depth = 0i32;
        let mut end = text.len();
        for (i, ch) in text[start..].char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = start + i + 1;
                        break;
                    }
                }
                ';' if text[start + i..].starts_with(";;") => {
                    end = start + i;
                    break;
                }
                _ => {}
            }
        }
        ret.push((start, end));
        from = end;
    }
    ret
}

/// A quiet wash behind a spec clause, `x0..x1` measured from the line's code start.
pub fn clause_wash(line_idx: usize, indent: u16, x0: f32, x1: f32) -> String {
    let y = line_idx as f32 * LS + 30.5;
    format!(
        "<rect x=\"{:.1}\" y=\"{:.1}\" width=\"{:.1}\" height=\"30\" rx=\"6\" class=\"pv-clause\"/>",
        code_x(indent) - 3.0 + x0 - 2.0,
        y - 15.0,
        x1 - x0 + 4.0
    )
}

/// Rewrite kernel line references ("line 12", "lines 3, 4", "@45") to displayed line numbers.
pub fn renumber(text: &str, disp: &dyn Fn(u32) -> u32) -> String {
    thread_local! {
        static RE: regex::Regex =
            regex::Regex::new(r"(\w?)(@|\blines? )(\d+(?:(?:, | and )\d+)*)").unwrap();
        static NUM: regex::Regex = regex::Regex::new(r"\d+").unwrap();
    }
    RE.with(|re| {
        re.replace_all(text, |c: &regex::Captures| {
            let nums = NUM.with(|n| {
                n.replace_all(&c[3], |d: &regex::Captures| {
                    d[0].parse::<u32>()
                        .map(|v| disp(v).to_string())
                        .unwrap_or_else(|_| d[0].to_string())
                })
                .into_owned()
            });
            // `i@12` is a version name (the value i had from line 12): it keeps its `@`;
            // a bare `@22` after a fact names the line it came from
            let lead = match (&c[1], &c[2]) {
                ("", "@") => "line ",
                (_, "@") => "@",
                (_, l) => l,
            };
            format!("{}{lead}{nums}", &c[1])
        })
        .into_owned()
    })
}

fn join_lines(v: &[u32], disp: &dyn Fn(u32) -> u32) -> String {
    v.iter()
        .map(|l| disp(*l).to_string())
        .collect::<Vec<_>>()
        .join(", ")
}

/// A wire endpoint: the top of a cup or socket.
#[derive(Clone, Copy)]
struct Target {
    x: f32,
    y: f32,
    dashed: bool,
}

/// A prove line's hypotheses (fact ids), their lines, the goal cups it feeds, its wrap notes.
type ProveFeed = (Vec<u32>, Vec<u32>, Vec<usize>, String);

struct ChipDraw {
    line: u32,
    x: f32,
    y: f32,
    targets: Vec<Target>,
    /// the line where the fact goes stale, drawn as a fray
    fray: Option<u32>,
    /// a stale-fact hint points at this chip: (the fray line, the unfed cup it would have fed)
    hint: Option<(u32, f32, f32)>,
    text: String,
    origin: &'static str,
}

struct Ctx<'a> {
    geom: &'a [LineGeom],
}

impl Ctx<'_> {
    fn op(&self, line: u32) -> Option<&str> {
        self.geom
            .get(line.saturating_sub(1) as usize)
            .and_then(|g| g.op.as_deref())
    }
    fn indent(&self, line: u32) -> u16 {
        self.geom
            .get(line.saturating_sub(1) as usize)
            .and_then(|g| g.indent)
            .unwrap_or(1)
    }
    /// x of the first proof cup's left edge and the room up to the code
    fn cup_row(&self, line: u32, n: usize) -> (f32, f32, f32) {
        let ind = self.indent(line);
        let g = self.geom.get(line.saturating_sub(1) as usize);
        let end = code_x(ind) - 5.0;
        let x0 = match g.and_then(|g| g.frac_right) {
            Some(r) => r + 2.0,
            // no value inputs: start near the fraction's centre, further left only if needed
            None => (frac_x(ind) - 8.0)
                .min(end - STEP * n as f32)
                .max(frac_x(ind) - 52.0),
        };
        let room = end - x0;
        let step = if n == 0 {
            STEP
        } else {
            STEP.min(room / n as f32)
        };
        let h = HALF.min(step / 2.0 - 0.6).max(2.5);
        (x0, step, h)
    }
}

/// Per-line output beyond hover text and commentary (kernel lines, renumbered in `build`).
#[derive(Default)]
struct Extra {
    /// a line's account (goal, hypotheses, reason), one entry per drawn line
    explains: HashMap<u32, Vec<String>>,
    /// a line's always-on label parts
    labels: HashMap<u32, Vec<String>>,
    /// a line's brief reasons
    briefs: HashMap<u32, Vec<String>>,
    /// lines that never run
    never: std::collections::HashSet<u32>,
    /// the facts on the lane at each row (drawn chips whose ribbon covers it)
    lanes: HashMap<u32, Vec<String>>,
}

/// The longest line of a prove's account (the full text is the line's hover title).
const EXPLAIN_CHARS: usize = 150;

fn clip(s: &str, n: usize) -> String {
    if s.chars().count() <= n {
        s.to_string()
    } else {
        let mut t: String = s.chars().take(n - 1).collect();
        t.push('…');
        t
    }
}

/// ①, ②, … for the j-th hypothesis of a prove (as the solver's explanation labels them).
fn circled(j: usize) -> String {
    const C: [&str; 10] = ["①", "②", "③", "④", "⑤", "⑥", "⑦", "⑧", "⑨", "⑩"];
    C.get(j)
        .map(|c| c.to_string())
        .unwrap_or_else(|| format!("({})", j + 1))
}

/// Where a lane fact came from, for a student: "br_if on line 13 not taken".
fn origin_desc(origin: &str, line: u32) -> String {
    match origin {
        "br_if fall-through" => format!("br_if on line {line} not taken"),
        "br_if taken edge" => format!("br_if on line {line} taken"),
        "br_table edge" => format!("br_table on line {line}"),
        "if then-arm" => format!("if on line {line}, then-arm"),
        "if else-arm" => format!("else-arm, line {line}"),
        "prove" => format!("proved on line {line}"),
        "evaluation" => format!("evaluated on line {line}"),
        "call result" => format!("result of the call on line {line}"),
        "entry (parameter refinement)" => format!("the parameter's type, line {line}"),
        "entry (fact parameter)" => format!("fact parameter, line {line}"),
        "loop invariant" => format!("loop invariant, line {line}"),
        "loop parameter" => format!("loop parameter, line {line}"),
        "assume" => format!("assumed on line {line}"),
        "unfold" => format!("unfolded on line {line}"),
        o => format!("{o}, line {line}"),
    }
}

/// The cup a prove feeds, for a student: "feeds unreachable (line 15)", "feeds the i32.add cup
/// on line 20".
fn consumer_desc(c: &CupOut, op: Option<&str>) -> String {
    let l = c.line;
    let op = op.filter(|o| !o.is_empty());
    match (c.kind, op) {
        (CupKind::False, Some(o)) => format!("feeds {o} (line {l})"),
        (CupKind::ResultRefinement, _) => format!("feeds the function's result cup (line {l})"),
        (CupKind::BlockFact { .. }, _) => format!("feeds the block fact at line {l}"),
        (CupKind::LoopEntry, _) => format!("feeds the loop entry on line {l}"),
        (CupKind::BackEdge, _) => format!("feeds the back edge on line {l}"),
        (CupKind::Measure, _) => format!("feeds the measure on line {l}"),
        (CupKind::DivByZero, Some(o)) => format!("feeds the {o} divisor cup on line {l}"),
        (CupKind::Bounds, Some(o)) => format!("feeds the {o} bounds cup on line {l}"),
        (_, Some(o)) => format!("feeds the {o} cup on line {l}"),
        (_, None) => format!("feeds the cup on line {l}"),
    }
}

/// A prove's account: the goal it feeds, the hypotheses it takes (marking those the proof does
/// not need), and the solver's reason. `hyps` are (proposition, origin) in socket order.
fn prove_block(f: &FuncOut, ctx: &Ctx, goals: &[usize], hyps: &[(String, String)]) -> Vec<String> {
    let mut out = vec![];
    let Some(&g) = goals.first() else {
        return out;
    };
    let c = &f.cups[g];
    out.push(format!(
        "⊢ {} — {}",
        c.goal,
        consumer_desc(c, ctx.op(c.line))
    ));
    let e = c.explain.clone().unwrap_or_default();
    if hyps.is_empty() {
        out.push("using no hypotheses".into());
    } else {
        let parts: Vec<String> = hyps
            .iter()
            .enumerate()
            .map(|(j, (t, o))| {
                let unused = c.explain.is_some() && !e.used.contains(&(j as u8));
                let mark = if unused { " (not needed)" } else { "" };
                format!("{} {t} — {o}{mark}", circled(j))
            })
            .collect();
        out.push(format!("using {}", parts.join("; ")));
    }
    if e.ex_falso {
        out.push(if e.used.len() == 1 {
            "your hypothesis cannot hold: this line can never run".into()
        } else {
            "your hypotheses contradict each other: this line can never run".into()
        });
    }
    for (i, l) in e.lines.iter().enumerate() {
        out.push(if i == 0 {
            format!("why: {l}")
        } else {
            format!("        {l}")
        });
    }
    out
}

/// The cup's facts contradict each other (it is fed ex falso).
fn ex_falso(c: &CupOut) -> bool {
    c.explain.as_ref().is_some_and(|e| e.ex_falso)
}

fn lines_word(ls: &[u32]) -> String {
    let mut v = ls.to_vec();
    v.sort_unstable();
    v.dedup();
    format!(
        "line{} {}",
        if v.len() > 1 { "s" } else { "" },
        join_lines(&v, &|x| x)
    )
}

/// The always-on label of one proof cup: what it needs and how it is met.
fn cup_label(f: &FuncOut, c: &CupOut) -> String {
    let g = clip(&c.goal, 56);
    // an automatically fed cup names the birth lines of the facts its proof needs
    let auto_lines: Vec<u32> = match &c.feed {
        Feed::Auto {
            hyps, hyp_lines, ..
        } => hyps
            .iter()
            .zip(hyp_lines)
            .enumerate()
            .filter(|(j, _)| {
                c.explain
                    .as_ref()
                    .is_none_or(|e| e.used.contains(&(*j as u8)))
            })
            .map(|(_, (h, l))| f.chips.get(*h as usize).map_or(*l, |ch| ch.line))
            .collect(),
        _ => vec![],
    };
    let how = match &c.feed {
        _ if c.verdict == Verdict::Refuted => "✗ false".to_string(),
        Feed::Lookup { origin_line, .. } => format!("✓ fact of line {origin_line}"),
        Feed::Auto { .. } if ex_falso(c) && auto_lines.len() == 1 => format!(
            "⊥ the fact of {} cannot hold: this line never runs",
            lines_word(&auto_lines)
        ),
        Feed::Auto { .. } if ex_falso(c) => format!(
            "⊥ the facts of {} contradict each other: this line never runs",
            lines_word(&auto_lines)
        ),
        Feed::Auto { .. } if auto_lines.is_empty() => "✓ true for every value".into(),
        Feed::Auto { .. } => format!("✓ from {}", lines_word(&auto_lines)),
        Feed::Prove { prove_line, .. } if ex_falso(c) => {
            format!("⊥ by the prove on line {prove_line}: its facts contradict each other")
        }
        Feed::Prove { prove_line, .. } => format!("✓ by the prove on line {prove_line}"),
        Feed::Eval { .. } => "✓ evaluated".into(),
        Feed::DeadCode { .. } => "— never runs".into(),
        Feed::Unfed if c.ghost => "✗ not proved".into(),
        Feed::Unfed => "⏱ not proved: checked when run".into(),
    };
    let mut s = format!("needs {g} {how}");
    if c.verdict == Verdict::Assumed {
        let ls: Vec<u32> = c.assumptions.iter().map(|o| o.line).collect();
        let _ = write!(s, " (assuming {})", lines_word(&ls));
    }
    if !c.depends_on_checks.is_empty() && c.verdict != Verdict::RuntimeChecked {
        let _ = write!(
            s,
            " (relative to the check{} on {})",
            if c.depends_on_checks.len() > 1 {
                "s"
            } else {
                ""
            },
            lines_word(&c.depends_on_checks)
        );
    }
    s
}

/// The reason in brief, for "show all proofs": the solver's account for a found proof, the
/// matched fact for a lookup, what is missing for an unproved cup.
fn cup_brief(c: &CupOut) -> Option<String> {
    Some(match &c.feed {
        Feed::Auto { .. } | Feed::Prove { .. } => {
            let e = c.explain.as_ref()?;
            let why = e.lines.join(" ");
            if e.ex_falso {
                if e.used.len() == 1 {
                    format!("Never runs: its fact cannot hold. {why}")
                } else {
                    format!("Never runs: its facts contradict each other. {why}")
                }
            } else if why.is_empty() {
                return None;
            } else {
                why
            }
        }
        Feed::Unfed => match &c.diag {
            Some(d) => format!("Not proved: {d}"),
            None => "Not proved: no fact in scope implies it.".into(),
        },
        _ => return None,
    })
}

/// The account of one proof cup, below its line: what it needs, the facts used and where they
/// came from, and why it holds (for an automatically fed cup: the kernel found this proof).
fn cup_account(f: &FuncOut, ctx: &Ctx, c: &CupOut) -> Vec<String> {
    let what = consumer_desc(c, ctx.op(c.line));
    let what = what.strip_prefix("feeds ").unwrap_or(&what);
    let mut out = vec![format!("needs {} — {what}", c.goal)];
    match &c.feed {
        Feed::Auto {
            hyps, hyp_lines, ..
        } => {
            let e = c.explain.clone().unwrap_or_default();
            if hyps.is_empty() {
                out.push("using no facts: it holds for every value (found automatically)".into());
            } else {
                let parts: Vec<String> = hyps
                    .iter()
                    .zip(hyp_lines)
                    .enumerate()
                    .map(|(j, (h, l))| {
                        let ch = f.chips.get(*h as usize);
                        let t = e
                            .hyp_text
                            .get(j)
                            .cloned()
                            .or_else(|| ch.map(|c| c.text.clone()))
                            .unwrap_or_else(|| "?".into());
                        let o = origin_desc(
                            ch.map(|c| c.origin).unwrap_or("fact"),
                            ch.map_or(*l, |c| c.line),
                        );
                        // as the prove account does: a fact the proof turned out not to need
                        let unused = c.explain.is_some() && !e.used.contains(&(j as u8));
                        let mark = if unused { " (not needed)" } else { "" };
                        format!("{} {t} — {o}{mark}", circled(j))
                    })
                    .collect();
                let all = hyps.len() == e.used.len() || c.explain.is_none();
                out.push(format!(
                    "using {} (found automatically{})",
                    parts.join("; "),
                    if all { "; each is needed" } else { "" }
                ));
            }
            if e.ex_falso {
                out.push(if e.used.len() == 1 {
                    "this fact cannot hold, so this line never runs".into()
                } else {
                    "these facts cannot all hold together, so this line never runs".into()
                });
            }
            for (i, l) in e.lines.iter().enumerate() {
                out.push(if i == 0 {
                    format!("why: {l}")
                } else {
                    format!("        {l}")
                });
            }
        }
        Feed::Lookup { fact, origin_line } => {
            let o = f
                .chips
                .get(*fact as usize)
                .map(|c| c.origin)
                .unwrap_or("fact");
            out.push(format!(
                "exactly the fact {} — {}",
                f.chips
                    .get(*fact as usize)
                    .map(|c| c.text.as_str())
                    .unwrap_or("?"),
                origin_desc(o, *origin_line)
            ));
        }
        Feed::Prove { prove_line, .. } => out.push(format!(
            "proved by the prove on line {prove_line} (its account is there)"
        )),
        Feed::Eval { .. } => {
            out.push("true: every value in it is a constant, and it evaluates to true".into())
        }
        Feed::DeadCode { ended_at } => out.push(format!(
            "this line never runs (the arm ended at line {ended_at}), so there is nothing to prove"
        )),
        Feed::Unfed => out.push(match &c.diag {
            Some(d) => format!("not proved: {d}"),
            None => "not proved: no fact in scope implies it".into(),
        }),
    }
    out
}

/// How a consumer line is named in a prove's goal line: its opcode, with the target for calls,
/// locals and globals (`call $f`, `local.set $x`).
pub fn op_name(instr: &str) -> Option<String> {
    let mut w = instr.split_whitespace();
    let op = w.next()?;
    if op.starts_with('(') || op.starts_with(')') || op.starts_with(";;") {
        return None;
    }
    let with_arg = op == "call" || op.starts_with("local.") || op.starts_with("global.");
    Some(match (with_arg, w.next()) {
        (true, Some(a)) => format!("{op} {a}"),
        _ => op.to_string(),
    })
}

/// A row index (1-based line) from a y in SVG coordinates.
fn line_at(y: f32) -> u32 {
    (((y - 30.5) / LS).round().max(0.0) as u32) + 1
}

pub fn build(
    out: &ModuleOut,
    geom: &[LineGeom],
    failure: Option<&RunFailure>,
    disp: &dyn Fn(u32) -> u32,
) -> Scene {
    let mut scene = Scene {
        lines: vec![LineProof::default(); geom.len()],
        ..Default::default()
    };
    let ctx = Ctx { geom };
    let mut under = String::new();
    let mut over = defs();
    let mut titles: HashMap<u32, Vec<String>> = HashMap::new();
    let mut notes: HashMap<u32, Vec<String>> = HashMap::new();
    let mut quiets: HashMap<u32, Vec<String>> = HashMap::new();
    let mut extra = Extra::default();

    for f in &out.funcs {
        build_func(
            f,
            &ctx,
            failure,
            disp,
            &mut under,
            &mut over,
            &mut titles,
            &mut notes,
            &mut quiets,
            &mut extra,
        );
        // the header badge
        if let Some(lp) = scene
            .lines
            .get_mut(f.header_line.saturating_sub(1) as usize)
        {
            let checks = f
                .cups
                .iter()
                .filter(|c| c.verdict == Verdict::RuntimeChecked && !c.ghost)
                .count();
            // the instructor axioms a VERIFIED function rests on, so a hatched cup under the seal reads
            let axioms: std::collections::BTreeSet<u32> = f
                .cups
                .iter()
                .flat_map(|c| c.assumptions.iter())
                .filter(|o| o.kind == "axiom")
                .map(|o| o.line)
                .collect();
            lp.badge = Some(if f.verified && !axioms.is_empty() {
                (
                    format!(
                        "VERIFIED · {} axiom{}",
                        axioms.len(),
                        if axioms.len() == 1 { "" } else { "s" }
                    ),
                    "verified",
                )
            } else if f.verified {
                ("VERIFIED".into(), "verified")
            } else if f.line_errors.iter().any(|(_, e)| e.starts_with("strict: ")) {
                // strict mode (§4.1): what gradual mode would check at run time is an error here
                let n = f
                    .line_errors
                    .iter()
                    .filter(|(_, e)| e.starts_with("strict: "))
                    .count();
                (format!("strict: {n} unproven"), "strict")
            } else if checks == 1 {
                ("1 runtime check".into(), "gradual")
            } else if checks > 1 {
                (format!("{checks} runtime checks"), "gradual")
            } else {
                ("gradual".into(), "gradual")
            });
        }
        for (l, e) in &f.line_errors {
            let e = if e.starts_with("not implied") || e.starts_with("could not decide") {
                format!("prove failed: {e}")
            } else {
                e.clone()
            };
            notes.entry(*l).or_default().push(e);
        }
    }
    for (l, e) in &out.errors {
        notes.entry(*l).or_default().push(e.clone());
    }
    for (l, v) in titles {
        if let Some(lp) = scene.lines.get_mut(l.saturating_sub(1) as usize) {
            lp.title = Some(renumber(&v.join("\n"), disp));
        }
    }
    for (l, mut v) in notes {
        v.dedup();
        if let Some(lp) = scene.lines.get_mut(l.saturating_sub(1) as usize) {
            lp.note = Some(renumber(&v.join("; "), disp));
        }
    }
    for (l, mut v) in quiets {
        v.dedup();
        if let Some(lp) = scene.lines.get_mut(l.saturating_sub(1) as usize) {
            lp.quiet = Some(renumber(&v.join("; "), disp));
        }
    }
    for (l, v) in extra.explains {
        if let Some(lp) = scene.lines.get_mut(l.saturating_sub(1) as usize) {
            lp.explain = Some(renumber(&v.join("\n"), disp));
        }
    }
    for (l, mut v) in extra.briefs {
        v.dedup();
        if let Some(lp) = scene.lines.get_mut(l.saturating_sub(1) as usize) {
            lp.brief = Some(renumber(&v.join(" "), disp));
        }
    }
    for (l, mut v) in extra.labels {
        v.dedup();
        if let Some(lp) = scene.lines.get_mut(l.saturating_sub(1) as usize) {
            lp.label = Some(renumber(&v.join("  ·  "), disp));
        }
    }
    for l in extra.never {
        if let Some(lp) = scene.lines.get_mut(l.saturating_sub(1) as usize) {
            lp.never = true;
        }
    }
    for (l, mut v) in extra.lanes {
        v.dedup();
        if let Some(lp) = scene.lines.get_mut(l.saturating_sub(1) as usize) {
            lp.lane = Some(renumber(&format!("fact lane: {}", v.join("\n")), disp));
        }
    }
    scene.under = under;
    scene.over = over;
    scene
}

fn how(c: &CupOut, disp: &dyn Fn(u32) -> u32) -> String {
    let mut s = match &c.feed {
        Feed::Lookup { origin_line, .. } => format!("fed by the fact from line {origin_line}"),
        Feed::Prove {
            prove_line,
            hyp_lines,
            ..
        } => {
            if hyp_lines.is_empty() {
                format!("by the prove at line {prove_line}")
            } else {
                format!(
                    "by the prove at line {prove_line}, from line{} {}",
                    if hyp_lines.len() > 1 { "s" } else { "" },
                    hyp_lines
                        .iter()
                        .map(|l| l.to_string())
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
        Feed::Auto { hyp_lines, .. } => {
            if hyp_lines.is_empty() {
                "proved automatically (holds for every value)".into()
            } else {
                let mut ls: Vec<u32> = hyp_lines.to_vec();
                ls.sort_unstable();
                ls.dedup();
                format!(
                    "proved automatically from line{} {}",
                    if ls.len() > 1 { "s" } else { "" },
                    join_lines(&ls, &|x| x)
                )
            }
        }
        Feed::Eval { .. } => "by evaluation".into(),
        Feed::DeadCode { ended_at } => format!("dead code (the arm ended at line {ended_at})"),
        Feed::Unfed => c.diag.clone().unwrap_or_else(|| "nothing feeds it".into()),
    };
    if !c.assumptions.is_empty() {
        let ls: Vec<u32> = c.assumptions.iter().map(|o| o.line).collect();
        let _ = write!(
            s,
            "; assuming line{} {}",
            if ls.len() > 1 { "s" } else { "" },
            join_lines(&ls, &|x| x)
        );
    }
    if !c.depends_on_checks.is_empty() {
        let _ = write!(
            s,
            "; relative to checks at line{} {}",
            if c.depends_on_checks.len() > 1 {
                "s"
            } else {
                ""
            },
            join_lines(&c.depends_on_checks, &|x| x)
        );
    }
    let _ = disp;
    s
}

fn verdict_word(c: &CupOut, failed_here: bool) -> String {
    let star = if c.depends_on_checks.is_empty() {
        ""
    } else {
        "*"
    };
    match c.verdict {
        Verdict::RuntimeChecked if failed_here => "refuted by the run".into(),
        Verdict::RuntimeChecked if c.ghost => "unfed (ghost code is never checked)".into(),
        Verdict::RuntimeChecked => "checked when run".into(),
        Verdict::Refuted => "refuted".into(),
        Verdict::Proven => format!("proven{star}"),
        Verdict::Assumed => format!("assumed{star}"),
    }
}

/// The hypotheses a failed prove names: "[A @12, B @9]" → [(A, 12), (B, 9)].
fn parse_hyps(msg: &str) -> Vec<(String, u32)> {
    thread_local! {
        static RE: regex::Regex = regex::Regex::new(r" @(\d+)(, |\])").unwrap();
    }
    let Some(open) = msg.find('[') else {
        return vec![];
    };
    let mut start = open + 1;
    let mut ret = vec![];
    RE.with(|re| {
        for m in re.captures_iter(&msg[open..]) {
            let whole = m.get(0).unwrap();
            let (a, b) = (open + whole.start(), open + whole.end());
            if let Ok(l) = m[1].parse() {
                ret.push((msg[start..a].to_string(), l));
            }
            start = b;
            if &m[2] == "]" {
                break;
            }
        }
    });
    ret
}

/// "(line N) is about the old $x (set at line M)" in a stale-fact hint
fn parse_hint(diag: &str) -> Option<(u32, u32)> {
    thread_local! {
        static RE: regex::Regex =
            regex::Regex::new(r"\(line (\d+)\) is about the old .*?\(set at line (\d+)\)").unwrap();
    }
    RE.with(|re| {
        let c = re.captures(diag)?;
        Some((c[1].parse().ok()?, c[2].parse().ok()?))
    })
}

#[allow(clippy::too_many_arguments)]
fn build_func(
    f: &FuncOut,
    ctx: &Ctx,
    failure: Option<&RunFailure>,
    disp: &dyn Fn(u32) -> u32,
    under: &mut String,
    over: &mut String,
    titles: &mut HashMap<u32, Vec<String>>,
    notes: &mut HashMap<u32, Vec<String>>,
    quiets: &mut HashMap<u32, Vec<String>>,
    extra: &mut Extra,
) {
    // the cup a failed run check refutes (at most one)
    let failed_cup = failure.and_then(|fl| {
        let on_line = |c: &&CupOut| c.line == fl.line && c.verdict == Verdict::RuntimeChecked;
        f.cups
            .iter()
            .position(|c| on_line(&c) && fl.message.contains(&c.goal))
            .or_else(|| f.cups.iter().position(|c| on_line(&c)))
    });

    // cups by line, in operand order
    let mut by_line: HashMap<u32, Vec<usize>> = HashMap::new();
    for (i, c) in f.cups.iter().enumerate() {
        by_line.entry(c.line).or_default().push(i);
    }
    let mut cup_pos: Vec<(f32, f32, f32)> = vec![(0.0, 0.0, 0.0); f.cups.len()];
    for (line, ids) in by_line.iter_mut() {
        ids.sort_by_key(|i| (f.cups[*i].operand.map(|o| o as i32).unwrap_or(99), *i));
        let (x0, step, h) = ctx.cup_row(*line, ids.len());
        let y = y_mid(*line) - 6.5;
        for (k, i) in ids.iter().enumerate() {
            cup_pos[*i] = (x0 + step * (k as f32 + 0.5), y, h);
        }
    }

    // chips that are drawn: those that feed something, and those a stale hint points at
    let mut chip_targets: HashMap<u32, Vec<Target>> = HashMap::new();
    let mut hints: HashMap<u32, (u32, f32, f32)> = HashMap::new();
    // prove lines: (hyps, hyp lines, goal cups)
    let mut proves: HashMap<u32, ProveFeed> = HashMap::new();
    let mut dead_wires: Vec<(u32, usize)> = vec![];
    for (i, c) in f.cups.iter().enumerate() {
        let (x, y, h) = cup_pos[i];
        let dashed = c.verdict == Verdict::Assumed;
        match &c.feed {
            Feed::Lookup { fact, .. } => chip_targets.entry(*fact).or_default().push(Target {
                x,
                y: y - h,
                dashed,
            }),
            Feed::Prove {
                prove_line,
                hyps,
                hyp_lines,
                wraps_removed,
            } => {
                let e = proves.entry(*prove_line).or_insert_with(|| {
                    (
                        hyps.iter().copied().collect(),
                        hyp_lines.iter().copied().collect(),
                        vec![],
                        wraps_removed.join("; "),
                    )
                });
                e.2.push(i);
            }
            Feed::Auto { hyps, .. } => {
                for fact in hyps {
                    chip_targets.entry(*fact).or_default().push(Target {
                        x,
                        y: y - h,
                        dashed,
                    });
                }
            }
            Feed::DeadCode { ended_at } => dead_wires.push((*ended_at, i)),
            Feed::Unfed => {
                if let Some(d) = &c.diag
                    && let Some((chip_line, set_line)) = parse_hint(d)
                    && let Some(fid) = f
                        .chips
                        .iter()
                        .position(|ch| ch.line == chip_line && ch.frayed_at == Some(set_line))
                {
                    hints.insert(fid as u32, (set_line, x, y - h));
                }
            }
            Feed::Eval { .. } => {}
        }
    }

    let mut sockets = String::new();
    // prove sockets: k hypothesis cups on the prove line, wired from the hypotheses' chips
    for (pl, (hyps, hyp_lines, goals, wraps)) in &proves {
        let k = hyps.len();
        let (x0, step, h) = ctx.cup_row(*pl, k.max(1));
        let y = y_mid(*pl) - 6.5;
        let glook = goals
            .iter()
            .map(|g| look(&f.cups[*g], false))
            .find(|l| *l == Look::Assumed)
            .unwrap_or(Look::Proven);
        for (j, fact) in hyps.iter().enumerate() {
            let x = x0 + step * (j as f32 + 0.5);
            draw_cup(
                &mut sockets,
                &CupMark {
                    x,
                    y,
                    h,
                    look: glook,
                    star: false,
                    eval: false,
                    false_cup: false,
                    label: Some((j + 1).to_string()),
                },
            );
            chip_targets.entry(*fact).or_default().push(Target {
                x,
                y: y - h,
                dashed: glook == Look::Assumed,
            });
        }
        // the prove's output, below the rule, wired to the goal cup(s) on the next line
        let ox = if k > 0 {
            x0 + step * 0.5
        } else {
            frac_x(ctx.indent(*pl))
        };
        let oy = y_mid(*pl) + 7.5;
        for g in goals {
            let (gx, gy, gh) = cup_pos[*g];
            let _ = write!(
                under,
                "<path d=\"M{ox:.1},{oy:.1} C{ox:.1},{:.1} {gx:.1},{:.1} {gx:.1},{:.1}\" class=\"pv-wire{}\"/>",
                oy + 12.0,
                gy - gh - 12.0,
                gy - gh,
                if glook == Look::Assumed {
                    " pv-dash"
                } else {
                    ""
                }
            );
        }
        let _ = write!(
            sockets,
            "<path d=\"{}\" fill=\"{}\" stroke=\"{DARK_PURPLE}\" stroke-width=\"0.8\" {}/>",
            diamond(ox, oy, 4.2),
            if glook == Look::Assumed {
                "url(#pv-hatch)"
            } else {
                PURPLE
            },
            if glook == Look::Assumed {
                "opacity=\"0.7\""
            } else {
                ""
            }
        );
        let hyp_text: Vec<String> = hyps
            .iter()
            .zip(hyp_lines)
            .enumerate()
            .map(|(j, (h, l))| {
                let t = f
                    .chips
                    .get(*h as usize)
                    .map(|c| c.text.as_str())
                    .unwrap_or("?");
                format!("{}: ⟨{t}⟩ (line {l})", j + 1)
            })
            .collect();
        let goal_text: Vec<String> = goals
            .iter()
            .map(|g| format!("⟨{}⟩", f.cups[*g].goal))
            .collect();
        let mut t = format!(
            "prove {k}: {} ⟹ {}",
            if k == 0 {
                "no hypotheses".into()
            } else {
                hyp_text.join(", ")
            },
            goal_text.join(", ")
        );
        if !wraps.is_empty() {
            let _ = write!(t, "\nwraps: {wraps}");
        }
        titles.entry(*pl).or_default().push(t);
        // the account drawn beside the line (§3 contract, made legible): what it proves, from
        // what, and why
        // each fact as its chip prints it, from where it was born (a handle's `local.get` only
        // brings it back to the top of the lane)
        let words = goals
            .first()
            .and_then(|g| f.cups[*g].explain.as_ref())
            .map(|e| e.hyp_text.clone())
            .unwrap_or_default();
        let hyp_desc: Vec<(String, String)> = hyps
            .iter()
            .zip(hyp_lines)
            .enumerate()
            .map(|(j, (h, l))| {
                let ch = f.chips.get(*h as usize);
                (
                    words
                        .get(j)
                        .cloned()
                        .or_else(|| ch.map(|c| c.text.clone()))
                        .unwrap_or_else(|| "?".into()),
                    origin_desc(
                        ch.map(|c| c.origin).unwrap_or("fact"),
                        ch.map_or(*l, |c| c.line),
                    ),
                )
            })
            .collect();
        let block = prove_block(f, ctx, goals, &hyp_desc);
        titles.entry(*pl).or_default().push(block.join("\n"));
        if let Some(g) = goals.first() {
            extra.labels.entry(*pl).or_default().push(format!(
                "prove {k}: proves {} for line {}",
                clip(&f.cups[*g].goal, 56),
                f.cups[*g].line
            ));
        }
        extra.explains.insert(*pl, block.clone());
    }

    // failed proves: sockets for the hypotheses taken, wired from their chips, rimmed darkred
    for (pl, msg) in &f.line_errors {
        let hyps = parse_hyps(msg);
        if hyps.is_empty() || proves.contains_key(pl) {
            continue;
        }
        let (x0, step, h) = ctx.cup_row(*pl, hyps.len());
        let y = y_mid(*pl) - 6.5;
        for (j, (text, hl)) in hyps.iter().enumerate() {
            let x = x0 + step * (j as f32 + 0.5);
            draw_cup(
                &mut sockets,
                &CupMark {
                    x,
                    y,
                    h,
                    look: Look::GhostUnfed,
                    star: false,
                    eval: false,
                    false_cup: false,
                    label: Some((j + 1).to_string()),
                },
            );
            let fid = f
                .chips
                .iter()
                .position(|c| c.line == *hl && c.text == *text)
                .or_else(|| f.chips.iter().position(|c| c.line == *hl));
            if let Some(fid) = fid {
                chip_targets.entry(fid as u32).or_default().push(Target {
                    x,
                    y: y - h,
                    dashed: true,
                });
            }
        }
        // what it tried to prove and from what (the darkred note says why it failed)
        let tag = format!("the prove at line {pl} failed");
        if let Some(c) = f
            .cups
            .iter()
            .find(|c| c.diag.as_deref().is_some_and(|d| d.contains(&tag)))
        {
            let tried: Vec<String> = hyps
                .iter()
                .enumerate()
                .map(|(j, (t, l))| {
                    let o = f
                        .chips
                        .iter()
                        .find(|ch| ch.line == *l && ch.text == *t)
                        .map(|ch| ch.origin)
                        .unwrap_or("fact");
                    format!("{} {t} — {}", circled(j), origin_desc(o, *l))
                })
                .collect();
            let block = [
                format!(
                    "⊢ {} — {}, not proved",
                    c.goal,
                    consumer_desc(c, ctx.op(c.line))
                ),
                format!("tried {}", tried.join("; ")),
            ];
            titles.entry(*pl).or_default().push(block.join("\n"));
            extra
                .explains
                .insert(*pl, block.iter().map(|l| clip(l, EXPLAIN_CHARS)).collect());
        }
    }

    // place the drawn chips: lower row, right to left from the code
    let mut drawn: Vec<u32> = chip_targets.keys().chain(hints.keys()).copied().collect();
    drawn.sort();
    drawn.dedup();
    let mut per_line: HashMap<u32, usize> = HashMap::new();
    let mut chips: Vec<ChipDraw> = vec![];
    for fid in drawn {
        let Some(ch) = f.chips.get(fid as usize) else {
            continue;
        };
        let k = per_line.entry(ch.line).or_default();
        let x = code_x(ctx.indent(ch.line)) - 14.0 - CHIP_STEP * *k as f32;
        *k += 1;
        chips.push(ChipDraw {
            line: ch.line,
            x,
            y: y_mid(ch.line) + 8.0,
            targets: chip_targets.remove(&fid).unwrap_or_default(),
            fray: ch.frayed_at.filter(|m| *m > ch.line),
            hint: hints.get(&fid).copied(),
            text: ch.text.clone(),
            origin: ch.origin,
        });
    }

    // every drawn chip says what it is, on its own line (research/24 §4)
    for c in &chips {
        extra.labels.entry(c.line).or_default().push(format!(
            "gives {}{}{}",
            clip(&c.text, 56),
            match c.origin {
                "br_if fall-through" => " if not taken",
                "br_if taken edge" => " if taken",
                "if then-arm" => " in the then-arm",
                "if else-arm" => " in the else-arm",
                "loop invariant" => " (loop invariant)",
                "entry (parameter refinement)" | "entry (fact parameter)" => " (parameter)",
                _ => "",
            },
            match c.fray {
                Some(m) => format!(" — stale after line {m}"),
                None => String::new(),
            }
        ));
    }

    // the lane, readable on hover: each drawn chip's proposition on every row its ribbon covers
    for c in &chips {
        let last = c
            .targets
            .iter()
            .map(|t| line_at(t.y))
            .chain(c.fray)
            .fold(c.line, u32::max);
        let what = format!("⟨{}⟩ — {}", c.text, origin_desc(c.origin, c.line));
        for l in c.line..=last {
            extra.lanes.entry(l).or_default().push(what.clone());
        }
    }

    // trunks: one per chip; trunks at the same x whose spans overlap get side-by-side slots
    let span = |c: &ChipDraw| {
        let mut lo = c.y;
        let mut hi = c.y;
        for t in &c.targets {
            lo = lo.min(t.y - 14.0);
            hi = hi.max(t.y - 14.0);
        }
        if let Some(m) = c.fray {
            hi = hi.max(y_mid(m));
        }
        (lo, hi)
    };
    let mut order: Vec<usize> = (0..chips.len()).collect();
    order.sort_by(|a, b| span(&chips[*a]).0.total_cmp(&span(&chips[*b]).0));
    let mut slots: HashMap<i32, Vec<f32>> = HashMap::new(); // x → end y of each slot
    let mut trunk_x = vec![0.0f32; chips.len()];
    for i in order {
        let (lo, hi) = span(&chips[i]);
        let key = chips[i].x.round() as i32;
        let ends = slots.entry(key).or_default();
        let s = match ends.iter().position(|e| *e < lo - 3.0) {
            Some(s) => {
                ends[s] = hi;
                s
            }
            None => {
                ends.push(hi);
                ends.len() - 1
            }
        };
        trunk_x[i] = chips[i].x - TRACK_GAP * s as f32;
    }

    for (i, c) in chips.iter().enumerate() {
        let tx = trunk_x[i];
        let (lo, hi) = span(c);
        let all_dashed = !c.targets.is_empty() && c.targets.iter().all(|t| t.dashed);
        let long = (hi - lo) > 14.0 * LS;
        let _ = all_dashed;
        let cls = format!("pv-wire pv-trunk{}", if long { " pv-long" } else { "" });
        // trunk from the chip to the farthest hook
        let tlo = c.targets.iter().map(|t| t.y - 14.0).fold(c.y, f32::min);
        let thi = c.targets.iter().map(|t| t.y - 14.0).fold(c.y, f32::max);
        if !c.targets.is_empty() && (thi - tlo) > 0.5 {
            let _ = write!(
                under,
                "<path d=\"M{:.1},{:.1} L{tx:.1},{:.1} V{thi:.1} M{tx:.1},{:.1} V{tlo:.1}\" class=\"{cls}\"/>",
                c.x,
                c.y,
                c.y + 3.0,
                c.y + 3.0
            );
        }
        for t in &c.targets {
            let ty0 = t.y - 14.0;
            let _ = write!(
                under,
                "<path d=\"M{tx:.1},{ty0:.1} C{tx:.1},{:.1} {:.1},{:.1} {:.1},{:.1}\" class=\"pv-wire{}\"/>",
                ty0 + 8.0,
                t.x,
                t.y - 8.0,
                t.x,
                t.y,
                if t.dashed { " pv-dash" } else { "" }
            );
        }
        // fraying: the fact goes stale at a local.set/tee or store
        if let Some(m) = c.fray {
            let fy = y_mid(m) - 4.0;
            let bad = c.hint.is_some();
            // the ribbon carries on (faint, or solid when a cup needed it) to the fray
            let from = if c.targets.is_empty() {
                c.y
            } else {
                thi.max(c.y)
            };
            if fy - 11.0 > from {
                let _ = write!(
                    under,
                    "<path d=\"M{tx:.1},{from:.1} V{:.1}\" class=\"{}\"/>",
                    fy - 11.0,
                    if bad { "pv-wire" } else { "pv-ghost" }
                );
            }
            let mut d = String::new();
            for (a, len) in [
                (-0.95f32, 10.0f32),
                (-0.45, 12.0),
                (0.0, 9.0),
                (0.45, 12.0),
                (0.95, 10.0),
            ] {
                let (sx, sy) = (tx, fy - 11.0);
                let vx = a.sin();
                let vy = a.cos();
                let _ = write!(
                    d,
                    "M{sx:.1},{sy:.1} Q{:.1},{:.1} {:.1},{:.1} ",
                    sx + vx * len * 0.35,
                    sy + vy * len * 0.6,
                    sx + vx * len,
                    sy + vy * len
                );
            }
            let _ = write!(
                over,
                "<path d=\"{d}\" class=\"pv-fray{}\"/>",
                if bad { " pv-fray-bad" } else { "" }
            );
            if let Some((_, cx, cy)) = c.hint {
                // the dotted "bad" connection from the fray to the cup the stale fact could not feed
                let _ = write!(
                    under,
                    "<path d=\"M{tx:.1},{:.1} C{tx:.1},{:.1} {cx:.1},{:.1} {cx:.1},{cy:.1}\" class=\"pv-bad\"/>",
                    fy + 1.0,
                    fy + 20.0,
                    cy - 20.0
                );
            }
        }
        let _ = write!(
            over,
            "<path d=\"{}\" class=\"pv-chip\"/>",
            diamond(c.x, c.y, CHIP)
        );
        if c.origin == "axiom" || c.origin == "assume" {
            // §8: a small `A` on a chip born of an axiom or an assume
            let _ = write!(
                over,
                "<text x=\"{:.1}\" y=\"{:.1}\" class=\"pv-a\">A</text>",
                c.x - CHIP - 1.5,
                c.y - 2.0
            );
        }
        titles.entry(c.line).or_default().push(format!(
            "fact ⟨{}⟩ enters the lane ({}){}",
            c.text,
            c.origin,
            match c.fray {
                Some(m) => format!("; stale from line {m}"),
                None => String::new(),
            }
        ));
    }

    // dead-code feeds: a faint wire from the line that ended the arm
    for (ended, i) in dead_wires {
        let (x, y, h) = cup_pos[i];
        let sx = code_x(ctx.indent(ended)) - 14.0;
        let sy = y_mid(ended) + 8.0;
        let _ = write!(
            under,
            "<path d=\"M{sx:.1},{sy:.1} C{sx:.1},{:.1} {x:.1},{:.1} {x:.1},{:.1}\" class=\"pv-ghost\"/>",
            sy + 14.0,
            y - h - 14.0,
            y - h
        );
    }

    over.push_str(&sockets);

    // lines the kernel shows never run (a decided branch): greyed, with a quiet margin note on
    // the first one that has no prove account beside it
    for r in &f.never_runs {
        extra.never.extend(r.from..=r.to);
        let at = (r.from..=r.to)
            .find(|l| !extra.explains.contains_key(l))
            .unwrap_or(r.from);
        quiets
            .entry(at)
            .or_default()
            .insert(0, format!("never runs: {}", r.why));
        titles.entry(r.from).or_default().push(format!(
            "line {} to line {} never run: {}",
            r.from, r.to, r.why
        ));
    }

    // the cups themselves
    for (i, c) in f.cups.iter().enumerate() {
        let (x, y, h) = cup_pos[i];
        let failed_here = failed_cup == Some(i);
        let lk = look(c, failed_here);
        draw_cup(
            over,
            &CupMark {
                x,
                y,
                h,
                look: lk,
                star: !c.depends_on_checks.is_empty()
                    && matches!(c.verdict, Verdict::Proven | Verdict::Assumed),
                eval: matches!(c.feed, Feed::Eval { .. }),
                false_cup: c.kind == CupKind::False || ex_falso(c),
                label: None,
            },
        );
        if failed_here {
            let _ = write!(
                over,
                "<text x=\"{:.1}\" y=\"{:.1}\" class=\"pv-bomb\">💣</text>",
                x + h + 5.0,
                y - h + 3.0
            );
        }
        titles.entry(c.line).or_default().push(format!(
            "⟨{}⟩ {}: {}",
            c.goal,
            verdict_word(c, failed_here),
            how(c, disp)
        ));
        extra
            .labels
            .entry(c.line)
            .or_default()
            .push(cup_label(f, c));
        if let Some(b) = cup_brief(c) {
            extra.briefs.entry(c.line).or_default().push(b);
        }
        if !proves.contains_key(&c.line) {
            extra
                .explains
                .entry(c.line)
                .or_default()
                .extend(cup_account(f, ctx, c));
        }
        if failed_here
            && let Some(d) = &c.diag
            && let Some(h) = d.split("; ").find(|x| x.contains(" is about the old "))
        {
            // the run refuted a cup a stale fact could have fed: say which fact went stale
            notes.entry(c.line).or_default().push(h.to_string());
        }
        match lk {
            Look::Refuted if !failed_here => {
                let w = match &c.witness {
                    Some(Witness::Eval { value }) => {
                        format!("refuted: ⟨{}⟩ evaluates to {value}", c.goal)
                    }
                    Some(Witness::Run { args, .. }) => format!(
                        "refuted by a run on ({}): ⟨{}⟩",
                        args.iter()
                            .map(|a| a.to_string())
                            .collect::<Vec<_>>()
                            .join(", "),
                        c.goal
                    ),
                    None => c
                        .diag
                        .clone()
                        .unwrap_or_else(|| format!("refuted: ⟨{}⟩", c.goal)),
                };
                notes.entry(c.line).or_default().push(w);
            }
            Look::Checked => {
                let mut q = format!("⟨{}⟩ checked when run", c.goal);
                if let Some(d) = &c.diag {
                    if let Some(p) = d.find("(the prove at line") {
                        // the failed prove has its own darkred commentary
                        let _ = p;
                    } else if let Some(h) = d.split("; ").find(|x| x.contains(" is about the old "))
                    {
                        let _ = write!(q, " — {h}");
                    }
                }
                quiets.entry(c.line).or_default().push(q);
            }
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_failed_prove_hypotheses() {
        let h = parse_hyps(
            "not implied by [$gcd_ref($x, $y) = ite(eqz($y), $x, 1) @128, $x ≠ 0 @123]: u($x)=1",
        );
        assert_eq!(
            h,
            vec![
                ("$gcd_ref($x, $y) = ite(eqz($y), $x, 1)".to_string(), 128),
                ("$x ≠ 0".to_string(), 123)
            ]
        );
        assert!(parse_hyps("prove has nothing to feed").is_empty());
    }

    #[test]
    fn finds_fact_clauses() {
        let t = "block $done (fact (i32.eqz $y)) (fact (call $f $x)) ;; c";
        let r = fact_clauses(t);
        assert_eq!(r.len(), 2);
        assert_eq!(&t[r[0].0..r[0].1], "(fact (i32.eqz $y))");
        assert_eq!(&t[r[1].0..r[1].1], "(fact (call $f $x))");
    }

    #[test]
    fn renumbers_line_references() {
        let d = |k: u32| k - 1;
        assert_eq!(
            renumber("the prove at line 47 failed: [a @45]; lines 3, 4 and 9", &d),
            "the prove at line 46 failed: [a line 44]; lines 2, 3 and 8"
        );
        // a version name keeps its `@` (review B2)
        assert_eq!(renumber("u(i@12) < 8", &d), "u(i@11) < 8");
    }

    /// The user's program: `prove 1` after an always-taken `br_if` says what it proves, from
    /// what, and why; the lines after the br_if are greyed with a margin note; the lane reads.
    #[test]
    fn prove_line_is_legible() {
        let p = format!(
            "{}/public/examples/v2/prove-explain.wat",
            env!("CARGO_MANIFEST_DIR")
        );
        let src = std::fs::read_to_string(&p).unwrap();
        let out =
            crate::v2::kernel::check_module_with(&crate::v2::ast::Module::parse(&src), true, true);
        let geom: Vec<LineGeom> = src
            .lines()
            .map(|t| LineGeom {
                indent: Some(1),
                frac_right: None,
                op: op_name(t.trim()),
            })
            .collect();
        let s = build(&out, &geom, None, &|k| k);
        // no prove line any more (R5a): the account sits on the unreachable line (14)
        let block = s.lines[13]
            .explain
            .clone()
            .expect("an account on the unreachable line");
        let rows: Vec<&str> = block.lines().collect();
        assert_eq!(rows[0], "needs False — unreachable (line 14)");
        assert_eq!(
            rows[1],
            "using ① (x·2)&1 ≠ 0 — br_if on line 13 not taken (found automatically; each is needed)"
        );
        // one fact: it cannot hold (review 25 S4), not "they contradict each other"
        assert_eq!(rows[2], "this fact cannot hold, so this line never runs");
        assert!(rows[3].starts_with("why: "), "{block}");
        // always on: the br_if line says what it gives, the unreachable line what it needs, in words
        assert_eq!(
            s.lines[12].label.as_deref(),
            Some("gives (x·2)&1 ≠ 0 if not taken")
        );
        let l = s.lines[13].label.clone().unwrap();
        assert!(
            l.starts_with("needs False ⊥") && l.contains("the fact of line 13 cannot hold"),
            "{l}"
        );
        assert!(s.lines[13].never && !s.lines[12].never);
        assert_eq!(
            s.lines[13].quiet.as_deref(),
            Some("never runs: br_if on line 13 always branches")
        );
        assert!(
            s.lines[12]
                .lane
                .as_deref()
                .is_some_and(|l| l.contains("⟨(x·2)&1 ≠ 0⟩ — br_if on line 13 not taken"))
        );
    }

    #[test]
    fn names_consumer_lines() {
        assert_eq!(op_name("i32.add").as_deref(), Some("i32.add"));
        assert_eq!(op_name("call $f").as_deref(), Some("call $f"));
        assert_eq!(op_name("local.set $x").as_deref(), Some("local.set $x"));
        assert_eq!(op_name(")"), None);
    }

    /// A prove's facts are attributed to their birth lines, not to the `local.get` of a fact
    /// handle that brought them back to the top of the lane (primality's `prove 7`).
    #[test]
    fn prove_facts_name_their_birth_lines() {
        let p = format!(
            "{}/public/examples/v2/primality.wat",
            env!("CARGO_MANIFEST_DIR")
        );
        let src = std::fs::read_to_string(&p).unwrap();
        let out =
            crate::v2::kernel::check_module_with(&crate::v2::ast::Module::parse(&src), true, true);
        let geom = vec![LineGeom::default(); src.lines().count()];
        let s = build(&out, &geom, None, &|k| k);
        let pl = src
            .lines()
            .position(|l| l.trim().starts_with("prove 7"))
            .unwrap();
        let block = s.lines[pl].explain.clone().expect("the prove's account");
        let using = block.lines().find(|l| l.starts_with("using")).unwrap();
        for handle in [pl - 2, pl - 1, pl] {
            assert!(!using.contains(&format!("line {handle}")), "{using}");
        }
        assert!(using.contains("else-arm, line 125"), "{using}");
    }

    #[test]
    fn every_example_builds_a_scene() {
        for ex in [
            "hashtable",
            "hashtable-stale",
            "parity-bug-gate",
            "gcd-bug-guard",
            "primality",
        ] {
            let p = format!("{}/public/examples/v2/{ex}.wat", env!("CARGO_MANIFEST_DIR"));
            let src = std::fs::read_to_string(&p).unwrap();
            let out = crate::v2::kernel::check_module_with(
                &crate::v2::ast::Module::parse(&src),
                true,
                true,
            );
            let n = src.lines().count();
            let geom = vec![
                LineGeom {
                    indent: Some(1),
                    frac_right: None,
                    op: None,
                };
                n
            ];
            let t = std::time::Instant::now();
            let s = build(&out, &geom, None, &|k| k);
            eprintln!(
                "{ex}: {:?}, {} + {} bytes",
                t.elapsed(),
                s.under.len(),
                s.over.len()
            );
            assert_eq!(s.lines.len(), n);
            assert!(s.over.contains("pv-chip"), "{ex}");
            let badges = s.lines.iter().filter(|l| l.badge.is_some()).count();
            assert_eq!(badges, out.funcs.len(), "{ex}");
        }
    }
}
