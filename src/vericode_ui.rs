// Vericoding mode in the editor (design 16 §7): the ownership boundary on every edit, the
// adequacy panel (vacuity, mutation testing in the background), recorded sessions played
// through the real kernel, and an optional live LLM through OpenRouter. A child module of
// editor.rs (it extends `Editor`); the panel is plain DOM outside Codillon's component tree.

use super::{Editor, EditorHolder};
use crate::v2::adequacy::{Bench, Fate, Mutant, VacuityRow, fate, mutants, vacuity};
use crate::v2::llm::{self, Live, RoundOutcome, Script};
use crate::v2::vericode::{Owner, SessionStart, owner_reason};
use std::collections::BTreeMap;
use wasm_bindgen::{JsCast, JsValue, closure::Closure};

pub const SESSIONS: [(&str, &str); 3] = [
    ("isqrt", "isqrt · a loop invariant"),
    ("parity", "parity · half and its gate"),
    ("gcd", "gcd · Euclid against a reference"),
];
const KEY_STORE: &str = "codillon_openrouter_key";
const MODEL_STORE: &str = "codillon_openrouter_model";
const PRESET_STORE: &str = "codillon_openrouter_preset";
const FAST_STORE: &str = "codillon_openrouter_fast";
const SLICE_MS: f64 = 18.0;

/// One played round, as the transcript shows it.
pub struct TurnLog {
    pub who: &'static str,
    pub note: String,
    pub edits: Vec<(u32, u32, usize)>,
    pub kind: &'static str,
    pub summary: String,
    pub reasons: Vec<(u32, String)>,
    /// failing cups after the round: (line, goal, verdict, lane snapshot)
    pub cups: Vec<(u32, String, String, Vec<String>)>,
}

pub struct Player {
    pub name: String,
    pub script: Script,
    pub next: usize,
}

#[derive(Default)]
pub struct Adequacy {
    pub generation: u64,
    pub lines: Vec<String>,
    pub vacuity: Vec<VacuityRow>,
    pub mutants: Vec<Mutant>,
    pub fates: Vec<Option<Fate>>,
    pub bench: Option<Bench>,
    pub next: usize,
    /// per operator: (mutants, killed, ms)
    pub by_op: BTreeMap<&'static str, (u32, u32, f64)>,
    pub bench_ms: f64,
    pub vac_ms: f64,
    pub total_ms: f64,
    pub done: bool,
}

pub struct VcState {
    pub start: SessionStart,
    pub refused: Option<(usize, String)>,
    pub rejected: Vec<(usize, String)>,
    pub player: Option<Player>,
    pub log: Vec<TurnLog>,
    pub verdict: Option<(&'static str, String)>,
    pub adequacy: Adequacy,
    pub focus: Option<usize>,
    pub live: Option<Live>,
    pub busy: bool,
    pub llm_error: Option<String>,
    pub panel: Option<Panel>,
    pub collapsed: bool,
    /// a hand edit since the last verdict (the judge answers it once typing pauses)
    pub hand_edit: bool,
}

impl VcState {
    pub fn new(lines: &[String]) -> VcState {
        VcState {
            start: SessionStart::new(lines),
            refused: None,
            rejected: vec![],
            player: None,
            log: vec![],
            verdict: None,
            adequacy: Adequacy::default(),
            focus: None,
            live: None,
            busy: false,
            llm_error: None,
            panel: None,
            collapsed: false,
            hand_edit: false,
        }
    }
}

/// The panel's DOM root and its one delegated click handler.
pub struct Panel {
    pub root: web_sys::HtmlElement,
    _click: Closure<dyn FnMut(web_sys::Event)>,
}

fn storage() -> Option<web_sys::Storage> {
    web_sys::window().and_then(|w| w.local_storage().ok().flatten())
}

pub fn stored_key() -> Option<String> {
    storage()
        .and_then(|s| s.get_item(KEY_STORE).ok().flatten())
        .filter(|k| !k.trim().is_empty())
}

fn get(k: &str) -> Option<String> {
    storage()
        .and_then(|s| s.get_item(k).ok().flatten())
        .filter(|m| !m.trim().is_empty())
}

/// The custom model id (the free-text field).
pub fn stored_custom() -> String {
    get(MODEL_STORE).unwrap_or_default()
}

/// The active preset key (one of llm::PRESETS, or "custom"), and the model it asks for.
pub fn stored_choice() -> (String, llm::ModelChoice) {
    let preset = get(PRESET_STORE).unwrap_or_else(|| llm::PRESETS[0].0.to_string());
    if let Some((_, _, id, fast)) = llm::PRESETS.iter().find(|p| p.0 == preset) {
        return (
            preset,
            llm::ModelChoice {
                model: id.to_string(),
                fast: *fast,
            },
        );
    }
    let custom = stored_custom();
    if custom.is_empty() {
        return (llm::PRESETS[0].0.into(), llm::ModelChoice::default());
    }
    (
        "custom".into(),
        llm::ModelChoice {
            model: custom,
            fast: get(FAST_STORE).as_deref() == Some("1"),
        },
    )
}

fn input_checked(id: &str) -> bool {
    web_sys::window()
        .and_then(|w| w.document())
        .and_then(|d| d.get_element_by_id(id))
        .and_then(|e| e.dyn_into::<web_sys::HtmlInputElement>().ok())
        .is_some_and(|i| i.checked())
}

fn now() -> f64 {
    web_sys::window()
        .and_then(|w| w.performance())
        .map(|p| p.now())
        .unwrap_or(0.0)
}

fn input_value(id: &str) -> String {
    web_sys::window()
        .and_then(|w| w.document())
        .and_then(|d| d.get_element_by_id(id))
        .and_then(|e| e.dyn_into::<web_sys::HtmlInputElement>().ok())
        .map(|i| i.value())
        .unwrap_or_default()
}

pub fn later(f: impl FnOnce() + 'static) {
    set_timeout(f, 0);
}

fn set_timeout(f: impl FnOnce() + 'static, ms: i32) {
    if let Some(w) = web_sys::window() {
        let cb = Closure::once_into_js(f);
        let _ = w.set_timeout_with_callback_and_timeout_and_arguments_0(cb.unchecked_ref(), ms);
    }
}

fn body_class(on: bool) {
    if let Some(b) = web_sys::window()
        .and_then(|w| w.document())
        .and_then(|d| d.body())
    {
        let _ = if on {
            b.class_list().add_1("vc-on")
        } else {
            b.class_list().remove_1("vc-on")
        };
    }
}

/// The edits of a round, as (first line, last line, lines written) in the numbering they were
/// made against (shown with the gutter's numbers).
fn edits_desc(edits: &[crate::v2::vericode::Edit]) -> Vec<(u32, u32, usize)> {
    edits.iter().map(|e| (e.a, e.b, e.with.len())).collect()
}

/// Render edits with the gutter's numbers.
pub fn edits_text(e: &[(u32, u32, usize)], disp: &dyn Fn(u32) -> u32) -> String {
    let v: Vec<String> = e
        .iter()
        .map(|&(a, b, n)| {
            if b < a {
                format!("insert {n} line(s) before line {}", disp(a))
            } else if a == b {
                format!("line {} → {n} line(s)", disp(a))
            } else {
                format!("lines {}–{} → {n} line(s)", disp(a), disp(b))
            }
        })
        .collect();
    if v.is_empty() {
        "no edits".into()
    } else {
        v.join("; ")
    }
}

fn turn_log(
    who: &'static str,
    note: &str,
    edits: Vec<(u32, u32, usize)>,
    o: &RoundOutcome,
) -> TurnLog {
    let kind = llm::verdict_kind(o);
    let (summary, reasons) = match (&o.judgement, &o.error) {
        (_, Some(e)) => (format!("could not apply: {e}"), vec![]),
        (Some(j), _) => (
            j.summary(),
            if j.crossed() {
                // a rolled-back round: only why it crossed the boundary
                j.boundary
                    .iter()
                    .chain(&j.malformed)
                    .map(|r| (r.line, r.msg.clone()))
                    .collect()
            } else {
                j.strict.iter().map(|r| (r.line, r.msg.clone())).collect()
            },
        ),
        _ => (String::new(), vec![]),
    };
    let (cups, _) = llm::failing(&o.lines);
    let cups = cups
        .iter()
        .map(|c| {
            (
                c["line"].as_u64().unwrap_or(0) as u32,
                c["goal"].as_str().unwrap_or("").to_string(),
                c["verdict"].as_str().unwrap_or("").to_string(),
                c["lane"]
                    .as_array()
                    .map(|a| {
                        a.iter()
                            .map(|f| {
                                format!(
                                    "{} @{}",
                                    f["fact"].as_str().unwrap_or(""),
                                    f["line"].as_u64().unwrap_or(0)
                                )
                            })
                            .collect()
                    })
                    .unwrap_or_default(),
            )
        })
        .collect();
    TurnLog {
        who,
        note: note.to_string(),
        edits,
        kind,
        summary,
        reasons,
        cups,
    }
}

impl Editor {
    /// The gutter's number for each editor line (it numbers only some lines).
    pub(super) fn display_numbers(&self) -> Vec<u32> {
        let mut n = 0;
        self.text()
            .iter()
            .map(|l| {
                if l.is_numbered() {
                    n += 1;
                }
                n.max(1)
            })
            .collect()
    }

    /// The program as the kernel reads it (instruction and comment of every line).
    pub(super) fn program_lines(&self) -> Vec<String> {
        (0..self.text().len())
            .map(|i| {
                let l = self.line(i);
                format!("{}{}", l.instr().get(), l.comment().get())
            })
            .collect()
    }

    /// Replace the program with `new`, keeping the unchanged lines (no undo record; no lock
    /// check: submissions are judged by the kernel instead).
    pub(super) fn set_program_lines(&mut self, new: &[String]) -> bool {
        let old = self.program_lines();
        if old == new {
            return true;
        }
        let n = self.text().len();
        self.text_mut().remove_range(0, n);
        for l in new {
            self.push_line(l);
        }
        if self.text().is_empty() {
            self.push_line("");
        }
        if self.on_change().is_err() {
            // not a module the editor can run: put the old text back
            let n = self.text().len();
            self.text_mut().remove_range(0, n);
            for l in &old {
                self.push_line(l);
            }
            let _ = self.on_change();
            return false;
        }
        let height = super::LINE_SPACING * self.text().len();
        self.image_mut()
            .set_attribute("height", &height.to_string());
        true
    }

    /// The ownership guard on an edit (§7.1): the edited text must keep the frozen student zone.
    pub(super) fn vc_guard(&mut self, edited_line: usize) -> anyhow::Result<()> {
        let Some(vc) = self.vc.as_ref() else {
            return Ok(());
        };
        let lines = self.program_lines();
        if let Some(r) = vc.start.zone_violation(&lines) {
            let m0 = crate::v2::ast::Module::parse_lines(&vc.start.lines);
            let line = edited_line.min(vc.start.lines.len().saturating_sub(1));
            let why = owner_reason(&m0, &vc.start.bodies, line as u32 + 1);
            let vc = self.vc.as_mut().unwrap();
            vc.refused = Some((line, format!("locked: {why} — the student owns it")));
            anyhow::bail!("vericoding: {}", r.msg);
        }
        if let Some(vc) = self.vc.as_mut() {
            vc.refused = None;
            vc.rejected.clear();
            vc.hand_edit = true;
        }
        Ok(())
    }

    pub(super) fn vc_set_mode(&mut self, on: bool) {
        if on == self.vc.is_some() {
            return;
        }
        if on {
            let lines = self.program_lines();
            self.vc = Some(VcState::new(&lines));
            self.vc_build_panel();
            self.vc_restart_adequacy();
        } else {
            if let Some(p) = self.vc.take().and_then(|v| v.panel) {
                p.root.remove();
            }
            body_class(false);
            if let Some(b) = web_sys::window()
                .and_then(|w| w.document())
                .and_then(|d| d.body())
            {
                let _ = b.class_list().remove_1("vc-collapsed");
            }
        }
        self.draw_proofs();
        self.vc_render();
    }

    fn vc_build_panel(&mut self) {
        let Some(doc) = web_sys::window().and_then(|w| w.document()) else {
            return;
        };
        let Ok(root) = doc.create_element("aside") else {
            return;
        };
        let root: web_sys::HtmlElement = root.unchecked_into();
        root.set_class_name("vc-panel");
        root.set_id("vc-panel");
        let holder = self.holder();
        let click = Closure::<dyn FnMut(web_sys::Event)>::new(move |ev: web_sys::Event| {
            let Some(t) = ev
                .target()
                .and_then(|t| t.dyn_into::<web_sys::Element>().ok())
            else {
                return;
            };
            let Some(el) = t.closest("[data-act]").ok().flatten() else {
                return;
            };
            let act = el.get_attribute("data-act").unwrap_or_default();
            let arg = el.get_attribute("data-arg").unwrap_or_default();
            ev.prevent_default();
            let h = holder.clone();
            // act after the event (an action may replace the panel's own contents)
            set_timeout(move || h.borrow_mut().vc_act(&act, &arg), 0);
        });
        root.set_onclick(Some(click.as_ref().unchecked_ref()));
        if let Some(b) = doc.body() {
            let _ = b.append_child(&root);
        }
        body_class(true);
        if let Some(vc) = self.vc.as_mut() {
            vc.panel = Some(Panel {
                root,
                _click: click,
            });
        }
    }

    /// Keep what is typed in the custom model field and its throughput box.
    fn vc_save_custom(&self) {
        let Some(s) = storage() else { return };
        let model = input_value("vc-model");
        if !model.trim().is_empty() {
            let _ = s.set_item(MODEL_STORE, model.trim());
        }
        if web_sys::window()
            .and_then(|w| w.document())
            .and_then(|d| d.get_element_by_id("vc-fast"))
            .is_some()
        {
            let _ = s.set_item(FAST_STORE, if input_checked("vc-fast") { "1" } else { "0" });
        }
    }

    pub(super) fn vc_act(&mut self, act: &str, arg: &str) {
        match act {
            "close" => self.vc_set_mode(false),
            "collapse" => {
                if let Some(vc) = self.vc.as_mut() {
                    vc.collapsed = !vc.collapsed;
                }
            }
            "strict" => {
                self.link.strict = arg == "1";
                let _ = self.on_change();
            }
            "load" => self.vc_load_session(arg, None),
            "next" => self.vc_next_turn(),
            "all" => {
                while self
                    .vc
                    .as_ref()
                    .and_then(|v| v.player.as_ref())
                    .is_some_and(|p| p.next < p.script.turns.len())
                {
                    self.vc_next_turn();
                }
            }
            "restart" => {
                if let Some(name) = self
                    .vc
                    .as_ref()
                    .and_then(|v| v.player.as_ref())
                    .map(|p| p.name.clone())
                {
                    self.vc_load_session(&name, None);
                }
            }
            "focus" => {
                if let Some(vc) = self.vc.as_mut() {
                    let i: usize = arg.parse().unwrap_or(0);
                    vc.focus = if vc.focus == Some(i) { None } else { Some(i) };
                }
                self.draw_proofs();
                if let Some(l) = self
                    .vc
                    .as_ref()
                    .and_then(|v| v.focus.and_then(|i| v.adequacy.mutants.get(i)))
                    .map(|m| m.line)
                {
                    self.vc_scroll_to(l as usize - 1);
                }
            }
            "save-key" => {
                let key = input_value("vc-key");
                if let Some(s) = storage()
                    && !key.trim().is_empty()
                {
                    let _ = s.set_item(KEY_STORE, key.trim());
                }
                self.vc_save_custom();
            }
            "preset" => {
                if arg == "custom" {
                    self.vc_save_custom();
                }
                if let Some(s) = storage() {
                    let _ = s.set_item(PRESET_STORE, arg);
                }
            }
            "save-model" => {
                self.vc_save_custom();
                if let Some(s) = storage() {
                    let _ = s.set_item(PRESET_STORE, "custom");
                }
            }
            "forget-key" => {
                if let Some(s) = storage() {
                    let _ = s.remove_item(KEY_STORE);
                }
            }
            "ask" => self.vc_ask_llm(),
            "stop" => {
                if let Some(l) = self.vc.as_mut().and_then(|v| v.live.as_mut()) {
                    l.done = true;
                }
            }
            _ => {}
        }
        self.vc_render();
    }

    fn vc_scroll_to(&self, idx: usize) {
        let opts = web_sys::ScrollIntoViewOptions::new();
        opts.set_block(web_sys::ScrollLogicalPosition::Center);
        if let Some(el) = web_sys::window()
            .and_then(|w| w.document())
            .and_then(|d| d.query_selector_all(".textentry > .line").ok())
            .and_then(|nl| nl.item(idx as u32))
            .and_then(|n| n.dyn_into::<web_sys::Element>().ok())
        {
            el.scroll_into_view_with_scroll_into_view_options(&opts);
        }
    }

    /// Fetch a recorded session, load its start text, and play `turns` of it.
    pub(super) fn vc_load_session(&mut self, name: &str, turns: Option<usize>) {
        let url = format!("examples/v2/sessions/{name}.json");
        let holder = self.holder();
        let name = name.to_string();
        wasm_bindgen_futures::spawn_local(async move {
            let text = crate::jet::fetch_text(&url).await;
            let mut ed = holder.borrow_mut();
            let script = match text
                .map_err(|e| e.to_string())
                .and_then(|t| llm::parse_script(&t))
            {
                Ok(s) => s,
                Err(e) => {
                    if let Some(vc) = ed.vc.as_mut() {
                        vc.verdict = Some(("error", format!("session {name}: {e}")));
                    }
                    ed.vc_render();
                    return;
                }
            };
            if ed.vc.is_none() {
                ed.vc_set_mode(true);
            }
            let start = script.start.clone();
            ed.set_program_lines(&start);
            ed.action_history = Default::default();
            if let Some(vc) = ed.vc.as_mut() {
                vc.start = SessionStart::new(&start);
                vc.log.clear();
                vc.verdict = None;
                vc.refused = None;
                vc.rejected.clear();
                vc.focus = None;
                vc.live = None;
                vc.player = Some(Player {
                    name,
                    script,
                    next: 0,
                });
            }
            for _ in 0..turns.unwrap_or(0) {
                ed.vc_next_turn();
            }
            ed.vc_restart_adequacy();
            ed.draw_proofs();
            ed.vc_render();
        });
    }

    /// Apply a round: the real kernel judges it; a boundary crossing is rolled back and drawn.
    fn vc_apply_round(&mut self, o: &RoundOutcome, log: TurnLog) {
        if o.applied {
            self.set_program_lines(&o.lines);
        }
        let Some(vc) = self.vc.as_mut() else { return };
        vc.rejected.clear();
        vc.refused = None;
        if let Some(j) = &o.judgement
            && j.crossed()
        {
            for r in j.boundary.iter().chain(&j.malformed) {
                let idx = (r.line.max(1) as usize - 1).min(o.lines.len().saturating_sub(1));
                vc.rejected
                    .push((idx, format!("submission rejected: {}", r.msg)));
            }
        }
        vc.verdict = Some((log.kind, log.summary.clone()));
        vc.log.push(log);
        let first = vc.rejected.first().map(|r| r.0);
        self.draw_proofs();
        for i in vc_lines(self, |v| v.rejected.iter().map(|r| r.0).collect()) {
            self.line_mut(i).shake();
        }
        if let Some(i) = first {
            self.vc_scroll_to(i);
        }
        self.vc_restart_adequacy();
    }

    fn vc_next_turn(&mut self) {
        let lines = self.program_lines();
        let Some(vc) = self.vc.as_mut() else { return };
        let Some(p) = vc.player.as_mut() else { return };
        let Some(t) = p.script.turns.get(p.next).cloned() else {
            return;
        };
        p.next += 1;
        let o = llm::play_round(&vc.start, &lines, &t.edits);
        let log = turn_log("scripted LLM", &t.note, edits_desc(&t.edits), &o);
        self.vc_apply_round(&o, log);
    }

    /// The live session (§7.3): only on a click, only with a key, only to openrouter.ai.
    fn vc_ask_llm(&mut self) {
        let Some(key) = stored_key() else {
            if let Some(vc) = self.vc.as_mut() {
                vc.llm_error = Some("paste an OpenRouter key first".into());
            }
            return;
        };
        let lines = self.program_lines();
        let Some(vc) = self.vc.as_mut() else { return };
        if vc.busy {
            return;
        }
        let task = "make every function body VERIFIED (every cup proven) and every harness's ⊥ proven unreachable, without assume or axioms";
        let mut live = Live::new(&lines, task, llm::MAX_ROUNDS);
        live.start = vc.start.clone();
        vc.live = Some(live);
        vc.player = None;
        vc.log.clear();
        vc.llm_error = None;
        vc.busy = true;
        let holder = self.holder();
        wasm_bindgen_futures::spawn_local(async move {
            let choice = stored_choice().1;
            loop {
                let body = {
                    let mut ed = holder.borrow_mut();
                    let next = ed
                        .vc
                        .as_mut()
                        .and_then(|v| v.live.as_mut())
                        .and_then(|l| l.next_body(&choice));
                    ed.vc_render();
                    next
                };
                let Some(body) = body else { break };
                let reply = post_openrouter(&key, &body.to_string()).await;
                let mut ed = holder.borrow_mut();
                let reply = match reply {
                    Ok(r) => r,
                    Err(e) => {
                        if let Some(vc) = ed.vc.as_mut() {
                            vc.llm_error = Some(e);
                        }
                        break;
                    }
                };
                let Some(o) = ed
                    .vc
                    .as_mut()
                    .and_then(|v| v.live.as_mut())
                    .map(|l| l.on_reply(&reply))
                else {
                    break;
                };
                let note = ed
                    .vc
                    .as_ref()
                    .and_then(|v| v.live.as_ref())
                    .and_then(|l| l.turns.last())
                    .map(|t| (t.note.clone(), edits_desc(&t.edits)))
                    .unwrap_or_default();
                let log = turn_log("live LLM", &note.0, note.1, &o);
                ed.vc_apply_round(&o, log);
                if let Some(e) = &o.error
                    && let Some(vc) = ed.vc.as_mut()
                {
                    vc.llm_error = Some(e.clone());
                }
                ed.vc_render();
            }
            let mut ed = holder.borrow_mut();
            if let Some(vc) = ed.vc.as_mut() {
                vc.busy = false;
            }
            ed.vc_render();
        });
    }

    /// Start adequacy over (debounced by generation): vacuity now, mutation in the background.
    pub(super) fn vc_restart_adequacy(&mut self) {
        let lines = self.program_lines();
        let Some(vc) = self.vc.as_mut() else { return };
        if vc.adequacy.lines == lines && vc.adequacy.generation > 0 {
            return;
        }
        let generation = vc.adequacy.generation + 1;
        let t0 = now();
        let owners = vc.start.owners(&lines);
        let ms = mutants(&lines, &owners);
        let vac = vacuity(&lines);
        vc.adequacy = Adequacy {
            generation,
            fates: vec![None; ms.len()],
            mutants: ms,
            vacuity: vac,
            vac_ms: now() - t0,
            lines,
            ..Default::default()
        };
        if vc.focus.is_some_and(|f| f >= vc.adequacy.mutants.len()) {
            vc.focus = None;
        }
        self.draw_proofs();
        let holder = self.holder();
        set_timeout(
            move || holder.borrow_mut().vc_adequacy_step(generation),
            120,
        );
    }

    fn vc_adequacy_step(&mut self, generation: u64) {
        let Some(vc) = self.vc.as_mut() else { return };
        let a = &mut vc.adequacy;
        if a.generation != generation || a.done {
            return;
        }
        let t0 = now();
        if a.bench.is_none() {
            a.bench = Some(Bench::new(&a.lines, 48));
            a.bench_ms = now() - t0;
            a.total_ms += a.bench_ms;
        } else {
            let bench = a.bench.take().unwrap_or(Bench { runs: vec![] });
            while a.next < a.mutants.len() && now() - t0 < SLICE_MS {
                let t = now();
                let f = fate(&a.lines, &a.mutants[a.next], &bench);
                let e = a.by_op.entry(a.mutants[a.next].op).or_default();
                e.0 += 1;
                e.1 += matches!(f, Fate::Killed(_)) as u32;
                e.2 += now() - t;
                a.fates[a.next] = Some(f);
                a.next += 1;
            }
            a.bench = Some(bench);
            a.total_ms += now() - t0;
            if a.next >= a.mutants.len() {
                a.done = true;
                if let Some(w) = web_sys::window() {
                    let _ = js_sys::Reflect::set(
                        &w,
                        &"codillonMutationMs".into(),
                        &JsValue::from_f64(a.total_ms),
                    );
                }
            }
        }
        let more = !a.done;
        self.vc_render();
        if more {
            let holder = self.holder();
            set_timeout(move || holder.borrow_mut().vc_adequacy_step(generation), 0);
        }
    }

    /// What vericoding adds to the drawing: lock state, refused and rejected lines, the focused
    /// surviving mutant. Called from draw_proofs with its scene.
    pub(super) fn vc_decorate(&self, scene: &mut crate::proof_view::Scene) {
        let Some(vc) = self.vc.as_ref() else { return };
        let lines = self.program_lines();
        let owners = vc.start.owners(&lines);
        let numbers = self.display_numbers();
        let disp = |k: u32| {
            numbers
                .get(k.saturating_sub(1) as usize)
                .copied()
                .unwrap_or(k)
        };
        let rn = |t: &str| crate::proof_view::renumber(t, &disp);
        for (i, lp) in scene.lines.iter_mut().enumerate() {
            lp.locked = owners.get(i) == Some(&Owner::Student);
        }
        let lock_at = |scene: &mut crate::proof_view::Scene, i: usize, red: bool| {
            let indent = self.line(i).info().indent.unwrap_or(0);
            scene
                .over
                .push_str(&crate::proof_view::lock_glyph(i as u32 + 1, indent, red));
        };
        // a vacuous precondition, on the function's header (§7.2)
        if vc.adequacy.lines == lines {
            for r in vc
                .adequacy
                .vacuity
                .iter()
                .filter(|r| r.vacuous || r.witnesses == 0)
            {
                let i = r.header_line as usize - 1;
                if i < scene.lines.len() {
                    let text = if r.vacuous {
                        "vacuous spec: the kernel proves this precondition false, so every claim holds trivially"
                    } else {
                        "probably vacuous: no tried input satisfies this precondition"
                    };
                    scene.lines[i].vnote = Some((text.to_string(), "reject"));
                }
            }
        }
        if let Some((i, msg)) = &vc.refused
            && *i < scene.lines.len()
        {
            scene.lines[*i].vnote = Some((rn(msg), "lock"));
            lock_at(scene, *i, false);
        }
        for (i, msg) in &vc.rejected {
            if *i < scene.lines.len() {
                scene.lines[*i].vnote = Some((rn(msg), "reject"));
                lock_at(scene, *i, true);
            }
        }
        if let Some(m) = vc.focus.and_then(|f| vc.adequacy.mutants.get(f)) {
            let i = m.line as usize - 1;
            if i < scene.lines.len() && vc.adequacy.lines == lines {
                let still = matches!(
                    vc.adequacy.fates.get(vc.focus.unwrap()),
                    Some(Some(Fate::Survived { proven: true }))
                );
                scene.lines[i].vnote = Some((
                    format!(
                        "mutant {} survives: `{}` → `{}`{}",
                        m.op,
                        m.from,
                        m.to,
                        if still {
                            " (the kernel still proves it)"
                        } else {
                            ""
                        }
                    ),
                    "mutant",
                ));
                let indent = self.line(i).info().indent.unwrap_or(0);
                scene
                    .under
                    .push_str(&crate::proof_view::mutant_wash(i as u32 + 1, indent, &m.to));
            }
        }
    }

    pub(super) fn vc_render(&self) {
        let Some(vc) = self.vc.as_ref() else { return };
        let Some(p) = vc.panel.as_ref() else { return };
        // the page's body is (re)built by Codillon's component tree at startup: re-attach
        if !p.root.is_connected()
            && let Some(b) = web_sys::window()
                .and_then(|w| w.document())
                .and_then(|d| d.body())
        {
            let _ = b.append_child(&p.root);
        }
        body_class(true);
        if let Some(b) = web_sys::window()
            .and_then(|w| w.document())
            .and_then(|d| d.body())
        {
            let _ = if vc.collapsed {
                b.class_list().add_1("vc-collapsed")
            } else {
                b.class_list().remove_1("vc-collapsed")
            };
        }
        let lines = self.program_lines();
        let numbers = self.display_numbers();
        let disp = |k: u32| {
            numbers
                .get(k.saturating_sub(1) as usize)
                .copied()
                .unwrap_or(k)
        };
        let html = super::vericode_html::panel(vc, &lines, self.link.strict, &disp);
        p.root.set_inner_html(&html);
    }
}

impl Editor {
    /// After every change: redraw the panel now, re-run adequacy once typing pauses.
    pub(super) fn vc_touched(&mut self) {
        if self.vc.is_none() {
            return;
        }
        self.vc_touch += 1;
        let t = self.vc_touch;
        self.vc_render();
        let holder = self.holder();
        set_timeout(
            move || {
                let mut ed = holder.borrow_mut();
                if ed.vc_touch == t {
                    ed.vc_restart_adequacy();
                    ed.vc_judge_hand_edit();
                }
            },
            400,
        );
    }

    /// A hand edit in the implementation zone gets the judge's verdict too (§7.1), as if the
    /// student had submitted it.
    fn vc_judge_hand_edit(&mut self) {
        let lines = self.program_lines();
        let Some(vc) = self.vc.as_mut() else { return };
        if !std::mem::take(&mut vc.hand_edit) {
            return;
        }
        let j = vc.start.judge(&lines);
        let kind = if j.accepted {
            "accepted"
        } else if j.crossed() {
            "rejected"
        } else {
            "not-accepted"
        };
        let first = j
            .boundary
            .iter()
            .chain(&j.malformed)
            .chain(&j.strict)
            .next()
            .map(|r| format!(" — line {}: {}", r.line, r.msg))
            .unwrap_or_default();
        vc.verdict = Some((kind, format!("your edit: {}{first}", j.summary())));
        self.vc_render();
    }

    /// The small "vericode" switch at the top right (hidden in embeds by CSS).
    pub(super) fn vc_install_toggle(&mut self) {
        // after the body's children are installed (they replace whatever is there at init)
        let holder = self.holder();
        set_timeout(move || holder.borrow_mut().vc_install_toggle_now(), 0);
    }

    fn vc_install_toggle_now(&mut self) {
        let Some(doc) = web_sys::window().and_then(|w| w.document()) else {
            return;
        };
        let Ok(b) = doc.create_element("button") else {
            return;
        };
        let b: web_sys::HtmlElement = b.unchecked_into();
        b.set_class_name("vc-toggle");
        b.set_inner_text("vericode");
        b.set_title("vericoding mode: lock the spec, judge submissions, check adequacy");
        let holder = self.holder();
        let click = Closure::<dyn FnMut()>::new(move || {
            let h = holder.clone();
            set_timeout(
                move || {
                    let mut ed = h.borrow_mut();
                    let on = ed.vc.is_none();
                    ed.vc_set_mode(on);
                },
                0,
            );
        });
        b.set_onclick(Some(click.as_ref().unchecked_ref()));
        click.forget(); // lives as long as the page
        if let Some(body) = doc.body() {
            let _ = body.append_child(&b);
        }
    }
}

fn vc_lines(ed: &Editor, f: impl Fn(&VcState) -> Vec<usize>) -> Vec<usize> {
    ed.vc.as_ref().map(f).unwrap_or_default()
}

/// POST one round to OpenRouter (the only network call vericoding ever makes).
async fn post_openrouter(key: &str, body: &str) -> Result<String, String> {
    use wasm_bindgen_futures::JsFuture;
    let w = web_sys::window().ok_or("no window")?;
    let init = web_sys::RequestInit::new();
    init.set_method("POST");
    init.set_body(&JsValue::from_str(body));
    let headers = js_sys::Object::new();
    let set = |k: &str, v: &str| {
        let _ = js_sys::Reflect::set(&headers, &k.into(), &v.into());
    };
    set("Authorization", &format!("Bearer {key}"));
    set("Content-Type", "application/json");
    set("X-Title", "Codillon vericoding");
    init.set_headers(&headers);
    let resp = JsFuture::from(w.fetch_with_str_and_init(llm::ENDPOINT, &init))
        .await
        .map_err(|e| format!("network error: {}", js_err(&e)))?;
    let resp: web_sys::Response = resp.dyn_into().map_err(|_| "not a response")?;
    let status = resp.status();
    let text = JsFuture::from(resp.text().map_err(|e| js_err(&e))?)
        .await
        .map_err(|e| js_err(&e))?
        .as_string()
        .unwrap_or_default();
    if !resp.ok() {
        // the API's own message, if it sent one
        return Err(match llm::reply_content(&text) {
            Err(m) => format!("HTTP {status}: {m}"),
            Ok(_) => format!("HTTP {status}"),
        });
    }
    Ok(text)
}

fn js_err(e: &JsValue) -> String {
    e.as_string()
        .or_else(|| {
            js_sys::Reflect::get(e, &"message".into())
                .ok()
                .and_then(|m| m.as_string())
        })
        .unwrap_or_else(|| "error".into())
}

#[allow(dead_code)]
fn _holder_is_used(_: EditorHolder) {}
