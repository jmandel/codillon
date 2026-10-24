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
#[derive(Clone, Copy, Debug, Default)]
pub struct LineGeom {
    pub indent: Option<u16>,
    /// right edge of the line's value input cups, if it has a fraction with inputs
    pub frac_right: Option<f32>,
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
                "<path d=\"{d}\" fill=\"url(#pv-hatch)\" stroke=\"{PURPLE}\" stroke-width=\"1\" opacity=\"0.7\"/>\
<circle cx=\"{:.1}\" cy=\"{:.1}\" r=\"2.3\" fill=\"none\" stroke=\"{PURPLE}\" stroke-width=\"0.9\"/>",
                x + h + 1.5,
                y - h + 0.5
            );
        }
        Look::Checked => {
            let _ = write!(
                o,
                "<path d=\"{d}\" fill=\"url(#fade-up)\" stroke=\"#777\" stroke-width=\"1.2\" stroke-dasharray=\"2.2 1.6\"/>\
<text x=\"{:.1}\" y=\"{:.1}\" class=\"pv-bomb\" opacity=\"0.5\">💣</text>",
                x + h + 3.5,
                y - h + 2.5
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

/// Rewrite kernel line references ("line 12", "lines 3, 4", "@45") to displayed line numbers.
pub fn renumber(text: &str, disp: &dyn Fn(u32) -> u32) -> String {
    thread_local! {
        static RE: regex::Regex =
            regex::Regex::new(r"(@|\blines? )(\d+(?:(?:, | and )\d+)*)").unwrap();
        static NUM: regex::Regex = regex::Regex::new(r"\d+").unwrap();
    }
    RE.with(|re| {
        re.replace_all(text, |c: &regex::Captures| {
            let nums = NUM.with(|n| {
                n.replace_all(&c[2], |d: &regex::Captures| {
                    d[0].parse::<u32>()
                        .map(|v| disp(v).to_string())
                        .unwrap_or_else(|_| d[0].to_string())
                })
                .into_owned()
            });
            let lead = if &c[1] == "@" { "line " } else { &c[1] };
            format!("{lead}{nums}")
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
                .max(frac_x(ind) - 32.0),
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

    for f in &out.funcs {
        build_func(
            f, &ctx, failure, disp, &mut under, &mut over, &mut titles, &mut notes, &mut quiets,
        );
        // the header badge
        if let Some(lp) = scene.lines.get_mut(f.header_line.saturating_sub(1) as usize) {
            let checks = f
                .cups
                .iter()
                .filter(|c| c.verdict == Verdict::RuntimeChecked && !c.ghost)
                .count();
            lp.badge = Some(if f.verified {
                ("VERIFIED".into(), "verified")
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
        Feed::Eval { .. } => "by evaluation".into(),
        Feed::DeadCode { ended_at } => format!("dead code (the arm ended at line {ended_at})"),
        Feed::Unfed => c.diag.clone().unwrap_or_else(|| "nothing feeds it".into()),
    };
    if !c.assumptions.is_empty() {
        let ls: Vec<u32> = c.assumptions.iter().map(|o| o.line).collect();
        let _ = write!(s, "; assuming line{} {}", if ls.len() > 1 { "s" } else { "" }, join_lines(&ls, &|x| x));
    }
    if !c.depends_on_checks.is_empty() {
        let _ = write!(
            s,
            "; relative to checks at line{} {}",
            if c.depends_on_checks.len() > 1 { "s" } else { "" },
            join_lines(&c.depends_on_checks, &|x| x)
        );
    }
    let _ = disp;
    s
}

fn verdict_word(c: &CupOut, failed_here: bool) -> String {
    let star = if c.depends_on_checks.is_empty() { "" } else { "*" };
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
    let mut proves: HashMap<u32, (Vec<u32>, Vec<u32>, Vec<usize>, String)> = HashMap::new();
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
        let ox = if k > 0 { x0 + step * 0.5 } else { frac_x(ctx.indent(*pl)) };
        let oy = y_mid(*pl) + 7.5;
        for g in goals {
            let (gx, gy, gh) = cup_pos[*g];
            let _ = write!(
                under,
                "<path d=\"M{ox:.1},{oy:.1} C{ox:.1},{:.1} {gx:.1},{:.1} {gx:.1},{:.1}\" class=\"pv-wire{}\"/>",
                oy + 12.0,
                gy - gh - 12.0,
                gy - gh,
                if glook == Look::Assumed { " pv-dash" } else { "" }
            );
        }
        let _ = write!(
            sockets,
            "<path d=\"{}\" fill=\"{}\" stroke=\"{DARK_PURPLE}\" stroke-width=\"0.8\" {}/>",
            diamond(ox, oy, 4.2),
            if glook == Look::Assumed { "url(#pv-hatch)" } else { PURPLE },
            if glook == Look::Assumed { "opacity=\"0.7\"" } else { "" }
        );
        let hyp_text: Vec<String> = hyps
            .iter()
            .zip(hyp_lines)
            .enumerate()
            .map(|(j, (h, l))| {
                let t = f.chips.get(*h as usize).map(|c| c.text.as_str()).unwrap_or("?");
                format!("{}: ⟨{t}⟩ (line {l})", j + 1)
            })
            .collect();
        let goal_text: Vec<String> = goals.iter().map(|g| format!("⟨{}⟩", f.cups[*g].goal)).collect();
        let mut t = format!("prove {k}: {} ⟹ {}", if k == 0 { "no hypotheses".into() } else { hyp_text.join(", ") }, goal_text.join(", "));
        if !wraps.is_empty() {
            let _ = write!(t, "\nwraps: {wraps}");
        }
        titles.entry(*pl).or_default().push(t);
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
    }

    // place the drawn chips: lower row, right to left from the code
    let mut drawn: Vec<u32> = chip_targets
        .keys()
        .chain(hints.keys())
        .copied()
        .collect();
    drawn.sort();
    drawn.dedup();
    let mut per_line: HashMap<u32, usize> = HashMap::new();
    let mut chips: Vec<ChipDraw> = vec![];
    for fid in drawn {
        let Some(ch) = f.chips.get(fid as usize) else {
            continue;
        };
        let k = per_line.entry(ch.line).or_default();
        let x = code_x(ctx.indent(ch.line)) - 11.0 - CHIP_STEP * *k as f32;
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
        let cls = format!(
            "pv-wire{}{}",
            if all_dashed { " pv-dash" } else { "" },
            if long { " pv-long" } else { "" }
        );
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
            let from = if c.targets.is_empty() { c.y } else { thi.max(c.y) };
            if fy - 9.0 > from {
                let _ = write!(
                    under,
                    "<path d=\"M{tx:.1},{from:.1} V{:.1}\" class=\"{}\"/>",
                    fy - 9.0,
                    if bad { "pv-wire" } else { "pv-ghost" }
                );
            }
            let mut d = String::new();
            for (a, len) in [(-1.25f32, 7.0f32), (-0.6, 9.0), (0.0, 7.5), (0.6, 9.0), (1.25, 7.0)] {
                let (sx, sy) = (tx, fy - 9.0);
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
        let _ = c.line;
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
        let sx = code_x(ctx.indent(ended)) - 11.0;
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
                false_cup: c.kind == CupKind::False,
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
        titles
            .entry(c.line)
            .or_default()
            .push(format!("⟨{}⟩ {}: {}", c.goal, verdict_word(c, failed_here), how(c, disp)));
        match lk {
            Look::Refuted if !failed_here => {
                let w = match &c.witness {
                    Some(Witness::Eval { value }) => format!("refuted: ⟨{}⟩ evaluates to {value}", c.goal),
                    Some(Witness::Run { args, .. }) => format!(
                        "refuted by a run on ({}): ⟨{}⟩",
                        args.iter().map(|a| a.to_string()).collect::<Vec<_>>().join(", "),
                        c.goal
                    ),
                    None => c.diag.clone().unwrap_or_else(|| format!("refuted: ⟨{}⟩", c.goal)),
                };
                notes.entry(c.line).or_default().push(w);
            }
            Look::Checked => {
                let mut q = format!("⟨{}⟩ checked when run", c.goal);
                if let Some(d) = &c.diag {
                    if let Some(p) = d.find("(the prove at line") {
                        // the failed prove has its own darkred commentary
                        let _ = p;
                    } else if let Some(p) = d.find("; ⟨") {
                        let _ = write!(q, " — {}", &d[p + 2..]);
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
        let h = parse_hyps("not implied by [$gcd_ref($x, $y) = ite(eqz($y), $x, 1) @128, $x ≠ 0 @123]: u($x)=1");
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
    fn renumbers_line_references() {
        let d = |k: u32| k - 1;
        assert_eq!(
            renumber("the prove at line 47 failed: [a @45]; lines 3, 4 and 9", &d),
            "the prove at line 46 failed: [a line 44]; lines 2, 3 and 8"
        );
    }

    #[test]
    fn every_example_builds_a_scene() {
        for ex in ["hashtable", "hashtable-stale", "parity-bug-gate", "gcd-bug-guard", "primality"] {
            let p = format!("{}/public/examples/v2/{ex}.wat", env!("CARGO_MANIFEST_DIR"));
            let src = std::fs::read_to_string(&p).unwrap();
            let out = crate::v2::kernel::check_module(&crate::v2::ast::Module::parse(&src), true);
            let n = src.lines().count();
            let geom = vec![LineGeom { indent: Some(1), frac_right: None }; n];
            let t = std::time::Instant::now();
            let s = build(&out, &geom, None, &|k| k);
            eprintln!("{ex}: {:?}, {} + {} bytes", t.elapsed(), s.under.len(), s.over.len());
            assert_eq!(s.lines.len(), n);
            assert!(s.over.contains("pv-chip"), "{ex}");
            let badges = s.lines.iter().filter(|l| l.badge.is_some()).count();
            assert_eq!(badges, out.funcs.len(), "{ex}");
        }
    }
}
