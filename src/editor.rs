// The Codillon code editor

use crate::{
    action_history::{ActionHistory, Edit},
    autocomplete::Autocomplete,
    debug::{ExecutionState, ExecutionStatus, RUN_LOG, RunArg, TerminationType, run_binary},
    dom_canvas::DomCanvas,
    dom_struct::DomStruct,
    dom_vec::DomVec,
    graphics::{DomImage, FractionInfo},
    jet::{
        AccessToken, Component, ControlHandlers, DocumentHandle, ElementFactory, InputEventHandle,
        NodeRef, RangeLike, ReactiveComponent, StorageHandle, WebOffset, WindowHandle, WithElement,
        compare_document_position, fetch_text, get_selection, now_ms, set_selection_range,
    },
    line::{Activity, CodeLine, LineInfo, Position, PositionRange},
    link::{LinkParams, ProgramSource, StepRequest, args_fragment, decode_program, share_fragment},
    save_status::SaveStatus,
    share::ShareButton,
    slider::Slider,
    syntax::{
        FrameInfo, FrameInfosMut, InstrKind, LineInfos, LineInfosMut, LineKind, SyntheticWasm,
        fix_syntax,
    },
    utils::{
        AnimationRequest, AnnotatedOperatorType, ConnectionSource, FmtError, FunctionIdCache,
        OperatorType, RawModule, SlotConnections, SlotInfo, TypedModule, ValidModule,
        find_connections, indent_and_frame, str_to_binary,
    },
};
use anyhow::{Context, Result, bail};
use itertools::zip_eq;
use regex::Regex;
use std::{
    cell::{Ref, RefCell, RefMut},
    cmp::min,
    collections::{HashMap, HashSet},
    rc::{Rc, Weak},
};
use wasm_bindgen::JsCast;
use wasm_bindgen::{closure::Closure, prelude::ScopedClosure};
use web_sys::{BeforeUnloadEvent, HtmlDivElement, console::log_1};

pub type Body = DomStruct<(EditorHolder, ()), web_sys::HtmlBodyElement>;
pub type Document = DocumentHandle<Body>;
type TextType = DomVec<CodeLine, HtmlDivElement>;
type ComponentType = DomStruct<
    (
        ReactiveComponent<Slider>,
        (
            DomImage,
            (
                ReactiveComponent<TextType>,
                (
                    DomCanvas,
                    (
                        Autocomplete,
                        (SaveStatus, (ReactiveComponent<ShareButton>, ())),
                    ),
                ),
            ),
        ),
    ),
    HtmlDivElement,
>;

macro_rules! get {
    ($comp:expr,$field:ident) => {
        &field!($field $comp.get())
    };
}

macro_rules! get_mut {
    ($comp:expr,$field:ident) => {
        &mut field!($field $comp.get_mut())
    };
}

macro_rules! field {
    (slider $comp:expr) => {
        $comp.0
    };
    (image $comp:expr) => {
        $comp.1.0
    };
    (textbox $comp:expr) => {
        $comp.1.1.0
    };
    (canvas $comp:expr) => {
        $comp.1.1.1.0
    };
    (autocomplete $comp:expr) => {
        $comp.1.1.1.1.0
    };
    (save_status $comp:expr) => {
        $comp.1.1.1.1.1.0
    };
    (share $comp:expr) => {
        $comp.1.1.1.1.1.1.0
    };
}

#[path = "vericode_html.rs"]
mod vericode_html;
#[path = "vericode_ui.rs"]
mod vericode_ui;

pub const LINE_SPACING: usize = 45;
const STORAGE_ID: &str = "codillon_content";
const SCHEDULE_STORE_MS: i32 = 500;
const RETRY_STORE_MS: i32 = 2000;

#[derive(Default)]
struct PendingAnimations {
    live_info: AnimationRequest,
    arrow: AnimationRequest,
    lines: HashSet<usize>,
}

impl PendingAnimations {
    fn has_pending(&self) -> bool {
        self.live_info.0 || self.arrow.0 || !self.lines.is_empty()
    }
}

struct Editor {
    component: ComponentType,
    factory: ElementFactory,
    action_history: ActionHistory,
    storage: Option<StorageHandle>,
    pending_binary: Option<(Vec<u8>, usize, Vec<RunArg>)>,
    main_params: Vec<wasmparser::ValType>, // the parameter types of $main
    /// the v2 kernel's result for the current text (design 16): per-cup verdicts, chips, the
    /// runtime-check plan of gradual mode. Phase D draws from this.
    v2: Option<Rc<V2State>>,
    /// vericoding mode (design 16 §7), when on
    vc: Option<vericode_ui::VcState>,
    vc_touch: u64,
    /// the line the caret is on (its proof account is shown below it)
    cursor_line: Option<usize>,
    previous_instrumented_binary_hash: u64,
    worker_running: bool,
    pending_save: Option<Closure<dyn Fn()>>,
    version: usize,
    slot_connections: SlotConnections,
    execution_state: ExecutionState,
    scroll_on_next_input: bool,
    window: WindowHandle,
    holder: Weak<RefCell<Self>>,
    input_filter: Regex,
    animation_handler: ScopedClosure<'static, dyn Fn(f64)>,
    animation_pending: bool,
    animations: PendingAnimations,
    function_identity_cache: FunctionIdCache,
    link: LinkState,
}

// State derived from the URL fragment (see link.rs).
#[derive(Default)]
struct LinkState {
    embed: bool,
    storage_key: Option<String>, // None: the user's own program (STORAGE_ID)
    example: Option<String>,     // name of the loaded example, if any
    loaded_text: String,         // the program text as loaded from the link
    pending_step: Option<StepRequest>,
    load_generation: usize,
    args: Option<Vec<i128>>,                             // #args=… for $main
    strict: bool, // #strict=1: runtime-checked cups are errors (§4.1)
    pending_vc: Option<(Option<String>, Option<usize>)>, // #mode=vericode / #session=, #turn=
}

/// The v2 kernel's view of the current text.
pub struct V2State {
    pub out: std::cell::RefCell<crate::v2::out::ModuleOut>,
    pub plan: Rc<crate::v2::runtime::RuntimePlan>,
}

impl V2State {
    /// Runtime checks the instrumenter could not compile are errors on their cups (never
    /// silently "runtime-checked"); the run stops at them.
    pub fn mark_uncompiled(&self) {
        let bad = self.plan.uncompiled.borrow().clone();
        if bad.is_empty() {
            return;
        }
        let mut out = self.out.borrow_mut();
        for f in out.funcs.iter_mut().filter(|f| bad.contains(&f.func)) {
            let mut lines = vec![];
            for c in f
                .cups
                .iter_mut()
                .filter(|c| c.verdict == crate::v2::out::Verdict::RuntimeChecked && !c.ghost)
            {
                c.diag = Some(format!(
                    "error: this runtime check could not be compiled into the run ({})",
                    c.diag.clone().unwrap_or_default()
                ));
                lines.push(c.line);
            }
            for l in lines {
                f.line_errors
                    .push((l, "runtime check could not be compiled".into()));
            }
            f.strict_clean = false;
            f.verified = false;
        }
    }
}

/// The width of code text in Codillon's code font (for placing marks behind parts of a line).
fn measure_code(text: &str) -> Option<f32> {
    measure_in(text, "24pt MLMRoman12-Regular")
}

/// The width of `text` in a CSS font (canvas measurement).
fn measure_in(text: &str, font: &str) -> Option<f32> {
    use wasm_bindgen::JsCast;
    thread_local! {
        static CTX: Option<web_sys::CanvasRenderingContext2d> = (|| {
            let doc = web_sys::window()?.document()?;
            let canvas = doc
                .create_element("canvas")
                .ok()?
                .dyn_into::<web_sys::HtmlCanvasElement>()
                .ok()?;
            canvas
                .get_context("2d")
                .ok()??
                .dyn_into::<web_sys::CanvasRenderingContext2d>()
                .ok()
        })();
    }
    CTX.with(|c| {
        let c = c.as_ref()?;
        c.set_font(font);
        c.measure_text(text).ok().map(|m| m.width() as f32)
    })
}

#[derive(Clone)]
pub struct EditorHolder(Rc<RefCell<Editor>>);

impl EditorHolder {
    pub fn new(factory: ElementFactory) -> Result<Self> {
        let ret = Self(Rc::new(RefCell::new(Editor::new(factory)?)));
        ret.borrow_mut().init(Rc::downgrade(&ret.0));
        Ok(ret)
    }

    fn borrow(&self) -> Ref<'_, Editor> {
        self.0.borrow()
    }

    fn borrow_mut(&self) -> RefMut<'_, Editor> {
        self.0.borrow_mut()
    }
}

impl LineInfos for Editor {
    fn is_empty(&self) -> bool {
        self.text().is_empty()
    }

    fn len(&self) -> usize {
        self.text().len()
    }

    fn info(&self, index: usize) -> &LineInfo {
        self.line(index).info()
    }
}

impl LineInfosMut for Editor {
    fn set_active_status(&mut self, index: usize, new_val: Activity) {
        self.line_mut(index).set_active_status(new_val)
    }

    fn set_synthetic_before(&mut self, index: usize, synth: SyntheticWasm) {
        self.line_mut(index).set_synthetic_before(synth);
    }

    fn push(&mut self) {
        let newline = CodeLine::new("", &self.factory);
        self.text_mut().push(newline);
    }

    fn set_invalid(&mut self, index: usize, reason: Option<String>) {
        self.line_mut(index).set_invalid(reason)
    }

    fn set_runtime_error(&mut self, index: usize, msg: Option<String>) {
        self.line_mut(index).set_runtime_error(msg)
    }
}

impl FrameInfosMut for Editor {
    fn set_indent(&mut self, index: usize, num: u16) {
        if self.line_mut(index).set_indent(num).0 {
            // animation should be triggered
            self.animations.lines.insert(index);
        }
    }

    fn set_frames(&mut self, frames: HashMap<u32, FrameInfo>) {
        let animated_indents = self.animated_indents();
        let line_count = self.len();
        self.image_mut()
            .set_frames(frames, animated_indents, line_count);
    }
}

impl WithElement for EditorHolder {
    type Element = HtmlDivElement;
    fn with_element<T, F: FnMut(&HtmlDivElement) -> T>(&self, f: F, g: AccessToken) -> T {
        self.0.borrow().component.with_element(f, g)
    }
}

impl Component for EditorHolder {
    #[cfg(debug_assertions)]
    fn audit(&self) {
        self.0.borrow().audit()
    }
}

impl Editor {
    #[cfg(debug_assertions)]
    fn audit(&self) {
        use crate::jet::WithNode;

        self.component.audit();
        self.window.audit();

        if self.component.is_connected() {
            // the wasm-bindgen in-browser tests don't attach the Editor to the entire body
            #[cfg(not(all(test, target_arch = "wasm32")))]
            self.component.elem().assert_is_entire_body();
        }
    }

    fn textbox(&self) -> &ReactiveComponent<TextType> {
        get!(self.component, textbox)
    }

    fn textbox_mut(&mut self) -> &mut ReactiveComponent<TextType> {
        get_mut!(self.component, textbox)
    }

    fn image(&self) -> &DomImage {
        get!(self.component, image)
    }

    fn image_mut(&mut self) -> &mut DomImage {
        get_mut!(self.component, image)
    }

    fn text(&self) -> &TextType {
        self.textbox().inner()
    }

    fn text_mut(&mut self) -> &mut TextType {
        self.textbox_mut().inner_mut()
    }

    fn line(&self, idx: usize) -> &CodeLine {
        &self.text()[idx]
    }

    fn line_mut(&mut self, idx: usize) -> &mut CodeLine {
        &mut self.text_mut()[idx]
    }

    fn slider(&self) -> &ReactiveComponent<Slider> {
        get!(self.component, slider)
    }

    fn slider_mut(&mut self) -> &mut ReactiveComponent<Slider> {
        get_mut!(self.component, slider)
    }

    fn autocomplete(&self) -> &Autocomplete {
        get!(self.component, autocomplete)
    }

    fn autocomplete_mut(&mut self) -> &mut Autocomplete {
        get_mut!(self.component, autocomplete)
    }

    fn save_status(&self) -> &SaveStatus {
        get!(self.component, save_status)
    }

    fn save_status_mut(&mut self) -> &mut SaveStatus {
        get_mut!(self.component, save_status)
    }

    fn share_mut(&mut self) -> &mut ReactiveComponent<ShareButton> {
        get_mut!(self.component, share)
    }

    fn update_live_info(
        &mut self,
        step_count: usize,
        current_step: Option<usize>,
        source_changed: bool,
    ) {
        self.animations.live_info = AnimationRequest(false);
        assert!(step_count > 0);
        let current_step = current_step.unwrap_or(self.current_step());
        // a failed v2 runtime check stops the run: its step is the last one
        let failures: Vec<usize> = if RUN_LOG.with(|r| r.v2_failure()).is_some() {
            vec![step_count - 1]
        } else {
            vec![]
        };
        if step_count > 1 {
            self.slider_mut().inner_mut().show();
            self.slider_mut().inner_mut().build_ticks(
                step_count - 1,
                current_step,
                &RUN_LOG.with(|r| r.termination_type()),
                &failures,
            )
        } else {
            self.slider_mut().inner_mut().hide();
        }

        fn find_error(state: &ExecutionState) -> Option<(usize, &str)> {
            Some(match &state.status {
                ExecutionStatus {
                    line_num: Some(line_num),
                    termination: TerminationType::Error,
                    error: Some(msg),
                    ..
                } => (*line_num, msg),
                _ => return None,
            })
        }

        // clear runtime error
        if let Some((line_no, _)) = find_error(&self.execution_state) {
            self.line_mut(line_no).set_runtime_error(None);
        };

        // compute the state for the desired step
        RUN_LOG.with(|log| {
            self.execution_state.goto_step(
                log,
                &self.slot_connections,
                current_step,
                Some(get_mut!(self.component, canvas)),
            )
        });

        for (slot_idx, value) in self.execution_state.slots.iter().enumerate() {
            let value = value.last().unwrap_or(&None);
            if let ConnectionSource::Written(coord) =
                &self.slot_connections.connections[slot_idx].written
            {
                get_mut!(self.component, image).set_slot_value(coord, false, value);
            }

            if let Some(coord) = &self.slot_connections.connections[slot_idx].read {
                get_mut!(self.component, image).set_slot_value(coord, true, value);
            }
        }

        let mut loops_taken = HashSet::new();
        for (block_idx, block) in self.slot_connections.blocks.iter().enumerate() {
            if let Some(taken) = self
                .execution_state
                .backwards_branches_taken()
                .get(block_idx)
                && *taken
            {
                loops_taken.insert(2 * block.0);
            }
        }
        get_mut!(self.component, image).set_loops_taken(&loops_taken);

        if step_count > 1
            && let ExecutionStatus {
                line_num: Some(line_num),
                below_line,
                ..
            } = &self.execution_state.status
            && let Some(indent) = &self.text()[*line_num].info().indent.clone()
        {
            self.animations.arrow = get_mut!(self.component, image).set_arrow_location(
                !source_changed,
                Some((*line_num, *below_line, *indent as usize)),
            );
            if self.scroll_on_next_input {
                get_mut!(self.component, image).scroll_to_arrow();
                self.scroll_on_next_input = false;
            }
        } else {
            self.animations.arrow = get_mut!(self.component, image).set_arrow_location(false, None);
        }

        // display runtime error (and HitBadImport)
        let Self {
            execution_state,
            component,
            ..
        } = self;
        if let Some((line_no, msg)) = find_error(execution_state) {
            get_mut!(component, textbox).inner_mut()[line_no]
                .set_runtime_error(Some(msg.to_string()));
        }

        self.schedule_animation_if_needed();
    }

    fn current_step(&self) -> usize {
        self.slider().inner().value_as_number().round() as usize
    }

    fn execute(&mut self, binary: &[u8], version: usize) {
        self.pending_binary = Some((binary.to_vec(), version, self.run_args()));
        if self.worker_running {
            return;
        }
        self.worker_running = true;

        let holder = self.holder();

        wasm_bindgen_futures::spawn_local(async move {
            loop {
                let Some((binary, version, args)) = holder.borrow_mut().pending_binary.take()
                else {
                    break;
                };
                run_binary(&binary, &args)
                    .await
                    .unwrap_or_else(|e| log_1(&format!("Codillon runtime error: {e}").into()));

                let mut ed = holder.borrow_mut();
                if version != ed.version {
                    continue;
                }

                let mut slider_step = ed.current_step();
                let step_count = RUN_LOG.with(|r| r.step_count());
                ed.recheck_proofs();
                // Move slider to the end if binary changed and it's in the middle
                if step_count == 0 {
                    ed.slider_mut().inner_mut().hide();
                    ed.animations.arrow = ed.image_mut().set_arrow_location(false, None);
                    break;
                }

                if ed.slider().inner().is_visible() {
                    if slider_step != 0 {
                        slider_step = step_count - 1;
                    }
                } else {
                    slider_step = step_count - 1;
                }

                // A deep link may ask for a particular step after the first run.
                if let Some(req) = ed.link.pending_step.take() {
                    slider_step = match req {
                        StepRequest::Number(n) => min(n, step_count - 1),
                        StepRequest::Last => step_count - 1,
                        StepRequest::Fail => ed.first_failure_step().unwrap_or(step_count - 1),
                    };
                    ed.scroll_on_next_input = !ed.link.embed;
                }

                ed.reset_execution_state();
                ed.update_live_info(step_count, Some(slider_step), true);
                ed.slider_mut()
                    .inner_mut()
                    .set_value_as_number(slider_step as f64);
            }
            holder.borrow_mut().worker_running = false;
        });
    }

    // The arguments $main is called with: #args= from the link, else zeros.
    fn run_args(&self) -> Vec<RunArg> {
        let vals = self.link.args.as_deref().unwrap_or_default();
        self.main_params
            .iter()
            .enumerate()
            .map(|(i, ty)| {
                let x = vals.get(i).copied().unwrap_or(0);
                match ty {
                    wasmparser::ValType::I64 => RunArg::I64(x as i64),
                    wasmparser::ValType::F32 | wasmparser::ValType::F64 => {
                        RunArg::F64((x as f64).to_bits())
                    }
                    _ => RunArg::I32(x as i32),
                }
            })
            .collect()
    }

    // Re-evaluate what the proof kernel says against the current run (called after each run,
    // and when an edit leaves the binary unchanged). The kernel itself runs in `run_v2_kernel`;
    // a failed runtime check is already the run's error (RUN_LOG). Drawing is phase D.
    fn recheck_proofs(&mut self) {
        self.draw_proofs();
    }

    /// Draw the v2 kernel's results (design 16 §8): proof cups, fact chips and wires in the
    /// image; hover text, commentary and header badges on the lines.
    fn draw_proofs(&mut self) {
        let Some(v2) = self.v2.clone() else {
            return;
        };
        let perf = web_sys::window().and_then(|w| w.performance());
        let t0 = perf.as_ref().map(|p| p.now());
        let edges = self.image().input_right_edges();
        let geom: Vec<crate::proof_view::LineGeom> = self
            .text()
            .iter()
            .enumerate()
            .map(|(i, l)| crate::proof_view::LineGeom {
                indent: l.info().indent,
                frac_right: edges.get(&i).copied(),
                op: crate::proof_view::op_name(l.instr().get()),
            })
            .collect();
        // kernel lines are 1-based editor lines; the gutter numbers only some of them
        let mut numbers = Vec::with_capacity(geom.len());
        let mut n = 0;
        for l in self.text().iter() {
            if l.is_numbered() {
                n += 1;
            }
            numbers.push(n.max(1));
        }
        let disp = |k: u32| {
            numbers
                .get(k.saturating_sub(1) as usize)
                .copied()
                .unwrap_or(k)
        };
        let failure = RUN_LOG
            .with(|r| r.v2_failure())
            .map(|f| crate::proof_view::RunFailure {
                line: f.line,
                message: f.message,
            });
        let mut scene = {
            let out = v2.out.borrow();
            crate::proof_view::build(&out, &geom, failure.as_ref(), &disp)
        };
        // spec clauses on code lines, e.g. `block $done (fact …)`: a quiet wash behind them
        let mut washes = String::new();
        for (i, l) in self.text().iter().enumerate() {
            let t = l.instr().get();
            let Some(indent) = l.info().indent else {
                continue;
            };
            for (a, b) in crate::proof_view::fact_clauses(t) {
                if let (Some(x0), Some(x1)) = (measure_code(&t[..a]), measure_code(&t[..b])) {
                    washes.push_str(&crate::proof_view::clause_wash(i, indent, x0, x1));
                }
            }
        }
        scene.under.insert_str(0, &washes);
        // lines whose code runs past the window: their commentary is pinned to the right edge
        // (the room is the code column's: the window less the vericoding panel, if any)
        let te_rect = web_sys::window()
            .and_then(|w| w.document())
            .and_then(|d| d.query_selector(".textentry").ok().flatten())
            .map(|e| e.get_bounding_client_rect());
        let right = te_rect
            .as_ref()
            .map(|r| r.right())
            .filter(|r| *r > 0.0)
            .unwrap_or(1400.0) as f32;
        let te_left = te_rect.as_ref().map_or(0.0, |r| r.left() as f32);
        let room = right - 120.0;
        // wide windows keep the accounts in a column at the right (no account covers code);
        // the labels then stop short of it
        let notes = notes_width(right, self.link.embed);
        let label_right = right - notes.map_or(16.0, |w| w + 24.0);
        let (mut prev_below, mut prev_comment) = (false, false);
        for (i, l) in self.text().iter().enumerate() {
            let indent = l.info().indent.unwrap_or(0);
            let end =
                crate::proof_view::code_x(indent) + measure_code(l.instr().get()).unwrap_or(0.0);
            // a code comment shares the row with the label
            let comment = l.comment().get();
            let end_all = end
                + if comment.trim().is_empty() {
                    0.0
                } else {
                    measure_in(comment, "18pt MLMSansDemiCond10-Regular").unwrap_or(0.0) + 8.0
                };
            if let Some(lp) = scene.lines.get_mut(i) {
                lp.wide = end > room;
                // a long code comment pushes the commentary onto the top of the next row
                let commented = lp.note.is_some() || lp.quiet.is_some();
                let pushed = commented && end_all > label_right - 200.0;
                // a wide line's commentary sits in the gap below it, over the top of the next
                // row: the next row's label goes below that row instead
                let (gap_busy, gap_comment) = (prev_below, prev_comment);
                // the line above's commentary covers the right of this row: a quiet note here
                // would print under it, and the label already says "checked when run"
                if gap_comment && lp.label.is_some() {
                    lp.quiet = None;
                }
                // the label right of the code wraps to two lines at most; if it would need
                // more (or there is no room at all) it goes in the gap below the line
                if let Some(t) = &lp.label {
                    let w = measure_in(t, "13pt MLMSansDemiCond10-Regular").unwrap_or(0.0);
                    let avail = label_right - end_all - 30.0;
                    // a two-line label would meet the label in the gap above it: below too
                    // a line with commentary keeps its row for the commentary
                    lp.label_below = lp.wide
                        || lp.note.is_some()
                        || lp.quiet.is_some()
                        || avail < 140.0
                        || w > 1.85 * avail
                        || gap_comment
                        || (gap_busy && w > 0.95 * avail);
                    lp.label_fit = (
                        measure_in(t, "10pt MLMSansDemiCond10-Regular").unwrap_or(0.0) + 14.0,
                        label_right - te_left,
                    );
                }
                prev_below = lp.label.is_some() && lp.label_below;
                prev_comment = (lp.wide || pushed) && commented;
            }
        }
        self.vc_decorate(&mut scene);
        self.image_mut().set_proof_layers(&scene.under, &scene.over);
        for (i, lp) in scene.lines.into_iter().enumerate() {
            self.line_mut(i).set_proof(lp);
        }
        self.sync_notes(notes, &disp);
        // the drawing's cost, for the QA harness (window.codillonProofMs)
        if let (Some(p), Some(t0)) = (perf, t0)
            && let Some(w) = web_sys::window()
        {
            let _ = js_sys::Reflect::set(&w, &"codillonProofMs".into(), &(p.now() - t0).into());
        }
    }

    /// The v2 kernel's output for the current text, if it has been checked (for phase D).
    #[allow(dead_code)]
    pub fn v2(&self) -> Option<&V2State> {
        self.v2.as_deref()
    }

    /// Whole-document v2 erasure (§1.8): lines whose erasure depends on context (lemma bodies,
    /// fact-handle get/set/tee) are re-classified by their erased text. Per-line erasure already
    /// happened when each line's text changed.
    fn apply_v2_erasure(&mut self) {
        let texts: Vec<String> = (0..self.len())
            .map(|i| self.line(i).instr().get().to_string())
            .collect();
        let doc = crate::v2::erase::erase_lines(&texts);
        for (i, e) in doc.iter().enumerate() {
            let code = crate::v2::sexpr::split_comment(e).0.trim_end().to_string();
            let want = if code.trim() == texts[i].trim() {
                None
            } else {
                Some(code)
            };
            if self.line(i).info().erased != want {
                self.line_mut(i).set_erasure(want);
            }
        }
    }

    /// Run the v2 kernel on the current text (one pass per function; deterministic).
    fn run_v2_kernel(&mut self) -> Rc<V2State> {
        let texts: Vec<String> = (0..self.len())
            .map(|i| {
                let l = self.line(i);
                format!("{}{}", l.instr().get(), l.comment().get())
            })
            .collect();
        let module = crate::v2::ast::Module::parse_lines(&texts);
        // with explanations (why each prove holds, lines that never run): drawn by proof_view
        let out = crate::v2::kernel::check_module_with(&module, !self.link.strict, true);
        let plan = Rc::new(crate::v2::runtime::RuntimePlan::new(&module, &out));
        let state = Rc::new(V2State {
            out: std::cell::RefCell::new(out),
            plan,
        });
        self.v2 = Some(state.clone());
        state
    }

    fn reset_execution_state(&mut self) {
        self.execution_state.reset(&self.slot_connections);
    }

    fn get_lines_and_positions(&self, range: &impl RangeLike) -> Result<PositionRange> {
        let (start_line, start_pos) =
            self.find_idx_and_pos(range.node1().unwrap(), range.offset1())?;

        let (end_line, end_pos) = self.find_idx_and_pos(range.node2().unwrap(), range.offset2())?;

        Ok(PositionRange {
            start_line,
            start_pos,
            end_line,
            end_pos,
        })
    }

    // Replace a given range (currently within a single line) with new text
    fn handle_edit(&mut self, target_range: &impl RangeLike, new_str: &str) -> Result<()> {
        if new_str.chars().any(|x| x.is_control() && x != '\n') {
            bail!("unhandled control char in input");
        }

        let saved_selection = self.get_lines_and_positions(&get_selection())?; // in case we need to revert
        let target = self.get_lines_and_positions(target_range)?;
        self.replace_range(&target, &saved_selection, new_str, true)
    }

    fn replace_range(
        &mut self,
        target: &PositionRange,
        saved_selection: &PositionRange,
        new_str: &str,
        record_for_undo: bool,
    ) -> Result<()> {
        let PositionRange {
            start_line,
            start_pos,
            end_line,
            end_pos,
        } = *target;

        let mut backup = Vec::new();
        for i in start_line..end_line + 1 {
            backup.push(self.line(i).suffix(Position::begin())?);
        }

        // disable animations; will be re-enabled if any indentation changes
        self.component.remove_attribute("class");

        let mut new_cursor_pos = if start_line == end_line {
            // Single-line edit.
            let was_structured = self.line(start_line).info().is_structured();
            let old_instr = self.line(start_line).instr().get().to_string();
            // Do the replacement.
            let new_pos = self
                .line_mut(start_line)
                .replace_range(start_pos, end_pos, new_str)?;

            // Should we add a "courtesy" `end` (because of a newly added structured instruction)?
            let is_structured = self.line(start_line).info().is_structured();
            let is_if = self.line(start_line).info().kind == LineKind::Instr(InstrKind::If);

            if !was_structured
                && is_structured
                && !old_instr.starts_with(self.line(start_line).instr().get())
            {
                // search for existing deactivated matching `end` (or `else` if the new instr is `if`)
                let mut need_end = true;
                for i in start_line + 1..self.text().len() {
                    if self.line(i).info().kind == LineKind::Instr(InstrKind::End)
                        && !self.line(i).info().is_active()
                    {
                        need_end = false;
                    }
                    if is_if
                        && self.line(i).info().kind == LineKind::Instr(InstrKind::Else)
                        && !self.line(i).info().is_active()
                    {
                        need_end = false;
                    }
                }
                if need_end {
                    let matching_end = CodeLine::new("end", &self.factory);
                    self.text_mut().insert(start_line + 1, matching_end);
                    self.line_mut(start_line + 1).reveal();
                }
            } else if was_structured && !is_structured {
                // Should we delete an unnecessary subsequent `end` (because of a removed structured instr)?
                if self.text().len() > start_line + 1
                    && self.line(start_line + 1).info().is_active()
                    && self.line(start_line + 1).info().kind == LineKind::Instr(InstrKind::End)
                    && self.line(start_line + 1).comment().is_empty()
                {
                    self.text_mut().remove(start_line + 1);
                    self.line_mut(start_line).fly_end();
                }
            }

            // Return new cursor position
            new_pos
        } else if start_line < end_line {
            // Multi-line edit.

            if self.line(start_line).all_whitespace() {
                self.line_mut(start_line).unset_indent();
            }

            // Step 1: Add surviving portion of end line to the start line.
            let end_pos_in_line = self.line(start_line).end_position();
            let s = self.line(end_line).suffix(end_pos)?;

            // Special case: if end line contributes 100% of the text, preserve its ID
            if end_pos == Position::begin() && start_pos == Position::begin() {
                let (l1, l2) = self.text_mut().get_two_mut(start_line, end_line);
                l1.swap_ids(l2);
            }

            // Save absolute offset for use later, because changing the line can
            // move text between instr and comment and will invalidate existing Position.
            let start_pos_absolute = self
                .line(start_line)
                .position_to_absolute_offset(start_pos)?;

            self.line_mut(start_line)
                .replace_range(start_pos, end_pos_in_line, &s)?;

            // Recompute start_pos based on new line contents
            let start_pos = self
                .line(start_line)
                .absolute_offset_to_position(start_pos_absolute)?;

            // Step 2: Remove all lines after the start.
            self.text_mut().remove_range(start_line + 1, end_line + 1);

            // Step 3: Insert the new text into the (remaining) start line.
            self.line_mut(start_line)
                .replace_range(start_pos, start_pos, new_str)?
        } else {
            bail!(
                "unhandled reversed target range {start_line}@{:?} .. {end_line}@{:?}",
                start_pos,
                end_pos
            )
        };

        // Split the start line if it contains newline chars.
        let mut fixup_line = start_line;
        let mut absolute_new_cursor_pos = self
            .line(fixup_line)
            .position_to_absolute_offset(new_cursor_pos)?;
        loop {
            let pos: Option<Position> = self.line(fixup_line).first_newline();
            match pos {
                None => break,
                Some(pos) => {
                    let the_line = self.line_mut(fixup_line);

                    let rest = the_line.suffix(pos)?;
                    let end_pos = the_line.end_position();

                    let olen = the_line.position_to_absolute_offset(end_pos)?;
                    the_line.replace_range(pos, end_pos, "")?;

                    let mut newline = CodeLine::new(&rest[1..], &self.factory);
                    let nlen = newline.position_to_absolute_offset(newline.end_position())?;
                    // may truncate initial whitespace

                    absolute_new_cursor_pos = absolute_new_cursor_pos.saturating_sub(olen - nlen);

                    // preserve identity in one special case
                    if pos == Position::begin() {
                        newline.swap_ids(self.line_mut(fixup_line));
                    }

                    fixup_line += 1;
                    self.text_mut().insert(fixup_line, newline);
                }
            }
        }
        new_cursor_pos = self
            .line(fixup_line)
            .absolute_offset_to_position(absolute_new_cursor_pos)?;

        // Is the new module well-formed and "validizable"? Otherwise, revert this entire change.
        // In vericoding mode, an edit that changes the student's spec is refused the same way.
        match self.vc_guard(start_line).and_then(|_| self.on_change()) {
            Ok(()) => {
                self.line(fixup_line).set_cursor_position(new_cursor_pos)?;
                // Store new edit
                if record_for_undo {
                    let mut new_lines = Vec::new();
                    for i in start_line..=fixup_line {
                        new_lines.push(self.line(i).suffix(Position::begin())?);
                    }
                    self.action_history.store_edit(Edit {
                        start_line,
                        old_lines: backup,
                        new_lines,
                        selection_before: saved_selection.clone(),
                        selection_after: PositionRange {
                            start_line: fixup_line,
                            start_pos: new_cursor_pos,
                            end_line: fixup_line,
                            end_pos: new_cursor_pos,
                        },
                        time_ms: now_ms(),
                    });
                }
            }
            Err(e) => {
                log_1(&format!("reverting after {e}").into());

                // restore backup
                self.text_mut().remove_range(start_line, fixup_line + 1);
                for (i, contents) in backup.iter().enumerate() {
                    let mut line = CodeLine::new(contents, &self.factory);
                    line.shake();
                    self.text_mut().insert(start_line + i, line);
                }

                self.on_change().expect("well-formed after restore");

                // restore selection
                let start_line = self.line(saved_selection.start_line);
                let (new_start_node, new_start_off) =
                    start_line.position_to_node_and_weboffset(saved_selection.start_pos)?;
                let end_line = self.line(saved_selection.end_line);
                let (new_end_node, new_end_off) =
                    end_line.position_to_node_and_weboffset(saved_selection.end_pos)?;

                set_selection_range(new_start_node, new_start_off, new_end_node, new_end_off);
            }
        }

        Ok(())
    }

    // The input handler.
    fn handle_input(&mut self, ev: InputEventHandle) -> Result<()> {
        ev.prevent_default();

        let target_range = ev.get_first_target_range()?;

        match &ev.input_type() as &str {
            "insertText" => self.handle_edit(&target_range, &ev.data().context("no data")?),
            "insertFromPaste" => self.handle_edit(
                &target_range,
                &self.input_filter.replace_all(
                    &ev.data_transfer()
                        .context("no data transfer")?
                        .get_data("text/plain")
                        .fmt_err()?,
                    "",
                ),
            ),
            "deleteContentBackward" | "deleteContentForward" | "deleteByCut" => {
                self.handle_edit(&target_range, "")
            }
            "insertParagraph" | "insertLineBreak" => self.handle_edit(&target_range, "\n"),
            _ => bail!(format!(
                "unhandled input type {}, data {:?}",
                ev.input_type(),
                ev.data()
            )),
        }?;

        if self.vc.as_ref().is_some_and(|v| v.refused.is_some()) {
            // a refused edit on a locked line: no completion popup under the refusal
            self.autocomplete_mut().update("");
        } else {
            self.show_autocomplete()?;
        }

        Ok(())
    }

    // Keydown helpers. Firefox has trouble advancing to the next line if there is an ::after pseudo-element
    // later in the line. It also has trouble deleting if the cursor position is at the end of the surrounding
    // div, so try to prevent this. And it skips lines on ArrowLeft if the previous line is completely empty.
    fn handle_keydown(&mut self, ev: web_sys::KeyboardEvent) -> Result<()> {
        if ev.key().starts_with("Arrow") || ev.key() == "Escape" {
            self.autocomplete_mut().update("");
        }

        match ev.key().as_str() {
            "ArrowRight" => {
                let selection = get_selection();
                if selection.is_collapsed() {
                    let (line_idx, pos) = self.find_idx_and_pos(
                        selection.focus_node().context("focus")?,
                        selection.focus_offset(),
                    )?;
                    if line_idx + 1 < self.text().len() && pos == self.line(line_idx).end_position()
                    {
                        ev.prevent_default();
                        self.line(line_idx + 1)
                            .set_cursor_position(Position::begin())?;
                    }
                }
            }

            "ArrowDown" => {
                let selection = get_selection();
                if selection.is_collapsed() {
                    let (line_idx, _) = self.find_idx_and_pos(
                        selection.focus_node().context("focus")?,
                        selection.focus_offset(),
                    )?;
                    if line_idx + 1 == self.text().len() {
                        ev.prevent_default();
                        self.line(line_idx)
                            .set_cursor_position(self.line(line_idx).end_position())?;
                    }
                }
            }

            "ArrowLeft" => {
                let selection = get_selection();
                if selection.is_collapsed() {
                    let (line_idx, pos) = self.find_idx_and_pos(
                        selection.focus_node().context("focus")?,
                        selection.focus_offset(),
                    )?;
                    if line_idx > 0 && pos == Position::begin() {
                        ev.prevent_default();
                        self.line(line_idx - 1)
                            .set_cursor_position(self.line(line_idx - 1).end_position())?;
                    }
                }
            }

            "z" | "Z" if ev.ctrl_key() || ev.meta_key() => {
                ev.prevent_default();
                if ev.shift_key() {
                    self.redo()?;
                } else {
                    self.undo()?;
                }
            }

            "Tab" => {
                let accepted = self.autocomplete().first_suggestion().map(String::from);
                if let Some(accepted) = accepted {
                    self.accept_autocomplete(&accepted)?;
                }
                ev.prevent_default();
            }
            _ => {}
        }

        Ok(())
    }

    // Given a node and offset, find the line index and position within that line.
    // There are several possibilities for the node (e.g. the div element, the span element,
    // or the text node).
    fn find_idx_and_pos(&self, node: NodeRef, offset: WebOffset) -> Result<(usize, Position)> {
        // If the position is "in" the div element, make sure the offset matches expectations
        // (either 0 for the very beginning, or #lines for the very end).
        if node.is_same_node(self.text()) {
            let line_count = self.text().len();
            return Ok(if offset.u32() == 0 {
                (0, Position::begin())
            } else if offset.usize() < line_count {
                (offset.usize(), Position::begin())
            } else if offset.usize() == line_count {
                let last_line_idx = line_count.checked_sub(1).context("last line idx")?;
                (last_line_idx, self.line(last_line_idx).end_position())
            } else {
                bail!("unexpected offset {offset:?} in textentry div")
            });
        }

        // Otherwise, find the line that hosts the position via binary search.
        // (This seems to be sub-millisecond for documents up to 10,000 lines.)
        let line_idx = self
            .text()
            .binary_search_by(|probe| compare_document_position(probe, &node))
            .fmt_err()?;

        Ok((line_idx, self.line(line_idx).get_position(node, offset)?))
    }

    fn on_change(&mut self) -> Result<()> {
        // v2: erase proof syntax by context, then check proofs
        self.apply_v2_erasure();
        let v2 = self.run_v2_kernel();

        // repair syntax
        fix_syntax(self);

        let wasm_bin = str_to_binary(self.active_as_text())?;
        let raw_module = RawModule::new(self, &wasm_bin)?;
        let validized = raw_module.fix_validity(self, &wasm_bin)?;
        let types = validized.to_types_table(&wasm_bin)?;

        // indent operators and find frames
        let current_cache = std::mem::take(&mut self.function_identity_cache);
        self.function_identity_cache =
            indent_and_frame(self, &validized, &types, Some(current_cache));

        // update visual types of params, locals, and operators
        self.scroll_on_next_input = false; // edit to text buffer -> don't scroll to arrow
        self.slot_connections = find_connections(&validized, &types);
        self.update_displayed_types(&validized, &types)?;
        self.draw_proofs();
        self.main_params = validized
            .functions
            .first()
            .map(|f| f.params.iter().map(|p| p.inner).collect())
            .unwrap_or_default();

        // instrumentation
        // gradual mode: unfed cups become runtime checks in the instrumented run (R35)
        RUN_LOG.with(|r| r.set_v2_plan(Some(v2.plan.clone())));
        let instrumented_binary =
            &validized.build_instrumented_binary_with_checks(&types, Some(&v2.plan))?;
        v2.mark_uncompiled();
        let instrumented_binary_hash = self.run_hash(instrumented_binary);
        let step_count = RUN_LOG.with(|r| r.step_count());
        if self.previous_instrumented_binary_hash != instrumented_binary_hash {
            self.version += 1;
            self.execute(instrumented_binary, self.version);
            self.previous_instrumented_binary_hash = instrumented_binary_hash;
        } else if step_count > 0 {
            // same binary and arguments: the run stands, but checks may have changed
            self.recheck_proofs();
            self.update_live_info(step_count, None, false);
        } else {
            self.animations.arrow = self.image_mut().set_arrow_location(false, None);
        }

        self.vc_touched();
        self.schedule_save(); // schedule save to local storage
        self.share_mut().inner_mut().reset_label();
        self.schedule_animation_if_needed();

        #[cfg(debug_assertions)]
        self.audit();

        Ok(())
    }

    fn schedule_animation_if_needed(&mut self) {
        if self.animation_pending {
            return;
        }
        if self.animations.has_pending() || self.image().has_pending_animation() {
            self.window.request_animation_frame(&self.animation_handler);
            self.animation_pending = true;
        }
    }

    fn animate(&mut self, t: f64) {
        debug_assert!(self.animation_pending);
        self.animation_pending = false;
        if self.animations.live_info.0 {
            self.update_live_info(RUN_LOG.with(|r| r.step_count()), None, false);
            debug_assert!(!self.animations.live_info.0);
        }
        self.animations.lines.retain(|idx| {
            get_mut!(self.component, textbox).inner_mut()[*idx]
                .animate(t)
                .0
        });
        let animated_indents = self.animated_indents();
        self.image_mut().animate_frames(t, &animated_indents);
        self.image_mut().animate_types(t, &animated_indents);
        self.image_mut().animate_connections(t);
        self.animations.arrow = self.image_mut().animate_arrow(t, &animated_indents);
        self.schedule_animation_if_needed();
    }

    // get the user-entered text buffer (doesn't include synthetic Wasm)
    fn buffer_as_text(&self) -> String {
        let mut ret = String::new();
        for line in self.text().iter() {
            ret.push_str(line.instr().get());
            ret.push_str(line.comment().get());
            ret.push('\n');
        }
        ret
    }

    // get the active, well-formed line contents
    fn active_as_text(&self) -> String {
        let mut ret = String::new();
        for line in self.text().iter() {
            for i in 0..line.info().num_well_formed_strs() {
                ret.push_str(line.well_formed_str(i));
                ret.push(' ');
            }
        }
        ret
    }

    fn update_displayed_types<'a>(
        &mut self,
        validized: &ValidModule<'a>,
        types: &TypedModule,
    ) -> Result<()> {
        let type_count = types.globals.len()
            + types
                .funcs
                .iter()
                .map(|f| f.locals.len() + f.ops.len())
                .sum::<usize>();
        let mut tagged_types = HashMap::with_capacity(type_count);

        // set types of globals
        for (global, global_type) in zip_eq(&validized.globals, &types.globals) {
            tagged_types.insert(
                global.position_id,
                FractionInfo {
                    line_no: global.line_idx,
                    indent: 0,
                    ty: AnnotatedOperatorType {
                        inputs: vec![],
                        outputs: vec![SlotInfo {
                            slot: types.slots[global_type.usize()].clone(),
                            used: true,
                        }],
                    },
                },
            );
        }

        for (func, func_types) in zip_eq(&validized.functions, &types.funcs) {
            // set types of params
            if !func_types.params.is_empty() {
                let param_types: Vec<SlotInfo> = func_types
                    .params
                    .iter()
                    .map(|x| SlotInfo {
                        slot: types.slots[x.usize()].clone(),
                        used: true,
                    })
                    .collect();
                tagged_types.insert(
                    func.positions.0,
                    FractionInfo {
                        line_no: func.lines.0,
                        indent: 0,
                        ty: AnnotatedOperatorType {
                            inputs: param_types,
                            outputs: vec![],
                        },
                    },
                );
            }

            // set types of locals
            {
                let mut local_line_idx: Option<usize> = None;
                let mut local_slots = vec![];
                for (local, slot_idx) in zip_eq(&func.locals, &func_types.locals) {
                    match local_line_idx {
                        Some(line_idx) if line_idx == local.line_idx => local_slots.push(*slot_idx),
                        None => {
                            local_line_idx = Some(local.line_idx);
                            debug_assert!(local_slots.is_empty());
                            local_slots.push(*slot_idx);
                        }
                        Some(line_idx) => {
                            // flush
                            let indent = self.line(line_idx).info().indent.unwrap_or(0);
                            tagged_types.insert(
                                self.line(line_idx).id(),
                                FractionInfo {
                                    line_no: line_idx,
                                    indent,
                                    ty: AnnotatedOperatorType {
                                        inputs: vec![],
                                        outputs: local_slots
                                            .iter()
                                            .map(|x| SlotInfo {
                                                slot: types.slots[x.usize()].clone(),
                                                used: true,
                                            })
                                            .collect(),
                                    },
                                },
                            );

                            local_line_idx = Some(local.line_idx);
                            local_slots.clear();
                            local_slots.push(*slot_idx);
                        }
                    }
                }
                // flush
                if let Some(local_line_idx) = local_line_idx {
                    let indent = self.line(local_line_idx).info().indent.unwrap_or(0);
                    tagged_types.insert(
                        self.line(local_line_idx).id(),
                        FractionInfo {
                            line_no: local_line_idx,
                            indent,
                            ty: AnnotatedOperatorType {
                                inputs: vec![],
                                outputs: local_slots
                                    .iter()
                                    .map(|x| SlotInfo {
                                        slot: types.slots[x.usize()].clone(),
                                        used: true,
                                    })
                                    .collect(),
                            },
                        },
                    );
                }
            }

            // set types of ops
            for (i, (op, OperatorType { inputs, outputs })) in
                zip_eq(&func.operators, &func_types.ops).enumerate()
            {
                let inputs: Vec<SlotInfo> = inputs
                    .iter()
                    .map(|x| SlotInfo {
                        slot: types.slots[x.usize()].clone(),
                        used: matches!(
                            self.slot_connections.connections[x.usize()].written,
                            ConnectionSource::Written(_)
                        ),
                    })
                    .collect();
                let mut all_used = true;
                let outputs: Vec<SlotInfo> = outputs
                    .iter()
                    .map(|x| SlotInfo {
                        slot: types.slots[x.usize()].clone(),
                        used: {
                            let is_used = i + 1 == func.operators.len()
                                || self.slot_connections.connections[x.usize()].read.is_some();
                            all_used &= is_used;
                            is_used
                        },
                    })
                    .collect();

                if !all_used && self.line(op.line_idx).info().invalid.is_none() {
                    self.line_mut(op.line_idx).set_invalid(Some(String::new()));
                }

                let indent = self.line(op.line_idx).info().indent.unwrap_or(0);

                if !func_types.params.is_empty() && op.line_idx == func.lines.0 {
                    // special case: for an empty func, don't override the param types with the function end type
                    if !inputs.is_empty() {
                        bail!("unexpected non-empty end op on same line as function start");
                    }
                } else {
                    tagged_types.insert(
                        op.position_id,
                        FractionInfo {
                            line_no: op.line_idx,
                            indent,
                            ty: AnnotatedOperatorType { inputs, outputs },
                        },
                    );
                }
            }
        }

        let animated_indents = self.animated_indents();
        let line_count = self.len();
        get_mut!(self.component, image).set_types(tagged_types, animated_indents);
        get_mut!(self.component, image)
            .set_connections(&self.slot_connections.connections, line_count);
        Ok(())
    }

    fn storage_key(&self) -> String {
        self.link
            .storage_key
            .clone()
            .unwrap_or_else(|| STORAGE_ID.to_string())
    }

    fn schedule_save(&mut self) {
        if self.link.embed {
            return; // embedded editors never write to storage
        }
        self.save_status_mut().mark_dirty();
        if self.pending_save.is_some() {
            // A save or retry already in flight
            return;
        }
        self.attempt_save(SCHEDULE_STORE_MS);
    }

    fn attempt_save(&mut self, delay_ms: i32) {
        let holder = Rc::clone(&self.holder.upgrade().unwrap());
        let closure = Closure::new(move || {
            let mut editor = holder.borrow_mut();
            let saved_version = editor.save_status().get_version();
            let content = editor.buffer_as_text();
            let success = {
                editor.pending_save = None;
                // Currently synchronous and atomic but could be asynchronous in the future
                let key = editor.storage_key();
                editor
                    .storage
                    .as_ref()
                    .map(|s| s.try_set_item(&key, &content))
                    .unwrap_or(false)
            };
            editor
                .save_status_mut()
                .notify_save_result(success, saved_version);

            if success {
                // Schedule save again if version number was updated during save
                if editor.save_status().is_dirty() {
                    editor.schedule_save();
                }
            } else {
                // Retry if unsuccessful
                editor.attempt_save(RETRY_STORE_MS);
            }
        });
        self.window.set_timeout_with_callback(&closure, delay_ms);
        self.pending_save = Some(closure);
    }

    // A run is determined by the binary and $main's arguments.
    fn run_hash(&self, binary: &[u8]) -> u64 {
        use std::hash::{DefaultHasher, Hash, Hasher};
        let mut hasher = DefaultHasher::new();
        binary.hash(&mut hasher);
        self.run_args().hash(&mut hasher);
        hasher.finish()
    }

    fn apply_selection(
        &mut self,
        start_line: usize,
        remove_len: usize,
        insert_lines: &[String],
        selection_after: &PositionRange,
    ) -> Result<()> {
        let document_length = self.text().len();
        if start_line >= document_length {
            bail!("start_line {start_line} out of range");
        }
        let end_line = min(start_line + remove_len, document_length) - 1;
        let target = PositionRange {
            start_line,
            start_pos: Position::begin(),
            end_line,
            end_pos: self.line(end_line).end_position(),
        };
        let new_str = insert_lines.join("\n");
        self.replace_range(&target, selection_after, &new_str, false)?;
        let document_length = self.text().len().saturating_sub(1);
        let start_index = min(selection_after.start_line, document_length);
        let end_index = min(selection_after.end_line, document_length);
        // Restore caret position
        let (start_node, start_off) = self
            .line(start_index)
            .position_to_node_and_weboffset(selection_after.start_pos)?;
        let (end_node, end_off) = self
            .line(end_index)
            .position_to_node_and_weboffset(selection_after.end_pos)?;
        set_selection_range(start_node, start_off, end_node, end_off);
        Ok(())
    }

    // Undo the most recent edit.
    pub fn undo(&mut self) -> Result<()> {
        if let Some(edit) = self.action_history.undo_stack.pop() {
            self.apply_selection(
                edit.start_line,
                edit.new_lines.len(),
                &edit.old_lines,
                &edit.selection_before,
            )?;
            self.action_history.redo_stack.push(edit);
            self.action_history.last_time_ms = 0.0;
        }
        Ok(())
    }

    // Re-apply most recently undone edit
    pub fn redo(&mut self) -> Result<()> {
        if let Some(edit) = self.action_history.redo_stack.pop() {
            self.apply_selection(
                edit.start_line,
                edit.old_lines.len(),
                &edit.new_lines,
                &edit.selection_after,
            )?;
            self.action_history.undo_stack.push(edit);
            self.action_history.last_time_ms = 0.0;
        }
        Ok(())
    }

    fn accept_autocomplete(&mut self, accepted: &str) -> Result<()> {
        let selection = get_selection();
        if selection.is_collapsed() {
            let (_, pos) = self.find_idx_and_pos(
                selection.focus_node().context("focus")?,
                selection.focus_offset(),
            )?;

            if pos.in_instr && pos.offset < accepted.len() {
                self.handle_edit(&selection, &accepted[pos.offset..])?;
            }
        }
        self.autocomplete_mut().update("");
        Ok(())
    }

    fn show_autocomplete(&mut self) -> Result<()> {
        let selection = get_selection();
        if !selection.is_collapsed() {
            self.autocomplete_mut().update("");
            return Ok(());
        }

        let (line_idx, pos) = self.find_idx_and_pos(
            selection.focus_node().context("focus")?,
            selection.focus_offset(),
        )?;
        if !pos.in_instr {
            self.autocomplete_mut().update("");
            return Ok(());
        }

        let prefix = self.line(line_idx).instr().get()[..pos.offset].to_string();
        self.autocomplete_mut().update(&prefix);
        Ok(())
    }

    fn animated_indents(&self) -> HashMap<usize, f64> {
        self.animations
            .lines
            .iter()
            .map(|idx| (*idx, self.line(*idx).animated_indent().unwrap()))
            .collect()
    }

    fn new(factory: ElementFactory) -> Result<Self> {
        let mut ret = Self {
            component: DomStruct::new(
                (
                    ReactiveComponent::new(Slider::new(factory.clone())),
                    (
                        DomImage::new(factory.clone()),
                        (
                            ReactiveComponent::new(DomVec::new(factory.div())),
                            (
                                DomCanvas::new(factory.canvas())?,
                                (
                                    Autocomplete::new(&factory),
                                    (
                                        SaveStatus::new(&factory),
                                        (ReactiveComponent::new(ShareButton::new(&factory)), ()),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
                factory.div(),
            ),
            factory,
            action_history: ActionHistory::default(),
            storage: StorageHandle::new(),
            pending_binary: None,
            main_params: vec![],
            v2: None,
            vc: None,
            cursor_line: None,
            vc_touch: 0,
            previous_instrumented_binary_hash: 0,
            worker_running: false,
            pending_save: None,
            version: 0,
            slot_connections: SlotConnections::default(),
            execution_state: ExecutionState::default(),
            scroll_on_next_input: false,
            window: WindowHandle::default(),
            holder: Weak::new(),
            input_filter: Regex::new("\r")?,
            animation_handler: Closure::new(|_| {}),
            animation_pending: false,
            animations: Default::default(),
            function_identity_cache: Default::default(),
            link: Default::default(),
        };

        let text = ret.textbox_mut();
        text.inner_mut().set_attribute("class", "textentry");
        text.inner_mut().set_attribute(
            "style",
            &format!("--codillon-line-spacing: {}px;", LINE_SPACING),
        );
        text.inner_mut().set_attribute("contenteditable", "true");
        text.inner_mut().set_attribute("spellcheck", "false");

        ret.image_mut().set_attribute("class", "annotations");

        Ok(ret)
    }

    fn holder(&self) -> EditorHolder {
        EditorHolder(self.holder.upgrade().unwrap())
    }

    fn init(&mut self, holder: Weak<RefCell<Editor>>) {
        self.holder = holder;

        let e = self.holder();
        self.animation_handler = Closure::new(move |t| e.borrow_mut().animate(t));

        let e = self.holder();
        self.textbox_mut()
            .set_onbeforeinput(move |ev| e.borrow_mut().handle_input(ev).unwrap());

        let e = self.holder();
        self.textbox_mut()
            .set_onkeydown(move |ev| e.borrow_mut().handle_keydown(ev).unwrap());

        let e = self.holder();
        self.textbox_mut()
            .set_onmousedown(move |_| e.borrow_mut().autocomplete_mut().update(""));

        let e = self.holder();
        self.autocomplete_mut()
            .set_handler(move |accepted| e.borrow_mut().accept_autocomplete(accepted).unwrap());

        let e = self.holder();
        self.slider_mut().set_oninput(move |ev| {
            let mut e = e.borrow_mut();
            e.animations.live_info = AnimationRequest(true);
            e.schedule_animation_if_needed();
            ev.prevent_default();
        });

        let e = self.holder();
        self.slider_mut()
            .set_onkeydown(move |_| e.borrow_mut().scroll_on_next_input = true);

        let e = self.holder();
        self.window
            .set_onbeforeunload(move |ev: BeforeUnloadEvent| {
                if e.borrow().save_status().is_dirty() {
                    ev.prevent_default();
                }
            });

        let e = self.holder();
        self.share_mut().set_onmousedown(move |ev| {
            ev.prevent_default();
            e.borrow_mut().share_link();
        });

        let e = self.holder();
        self.window
            .set_onhashchange(move || e.borrow_mut().load_from_location(false));

        self.vc_install_toggle();
        self.install_proofs_toggle();
        self.install_cursor_tracking();
        self.load_from_location(true);

        let height = LINE_SPACING * self.text().len();
        self.image_mut()
            .set_attribute("height", &height.to_string());
    }

    /// The caret's line shows its proof account (research/24 §4): follow `selectionchange`.
    fn install_cursor_tracking(&mut self) {
        let Some(doc) = web_sys::window().and_then(|w| w.document()) else {
            return;
        };
        let e = self.holder();
        let cb = Closure::<dyn FnMut()>::new(move || {
            if let Ok(mut ed) = e.0.try_borrow_mut() {
                ed.mark_cursor_line();
            }
        });
        let _ =
            doc.add_event_listener_with_callback("selectionchange", cb.as_ref().unchecked_ref());
        cb.forget(); // lives as long as the page
        // the accounts column: a hovered line shows its note; a resize re-measures the column
        let hover = Closure::<dyn FnMut(web_sys::MouseEvent)>::new(|ev: web_sys::MouseEvent| {
            let line = ev
                .target()
                .and_then(|t| t.dyn_into::<web_sys::Element>().ok())
                .and_then(|e| e.closest(".textentry > .line").ok().flatten())
                .and_then(|e| {
                    let p = e.parent_element()?;
                    let rows = p.children();
                    (0..rows.length()).find(|k| rows.item(*k).as_ref() == Some(&e))
                })
                .map(|k| k as usize);
            focus_note("hover", line);
        });
        let _ = doc.add_event_listener_with_callback("mouseover", hover.as_ref().unchecked_ref());
        hover.forget();
        let e = self.holder();
        let resize = Closure::<dyn FnMut()>::new(move || {
            if let Ok(mut ed) = e.0.try_borrow_mut() {
                ed.draw_proofs();
            }
        });
        if let Some(w) = web_sys::window() {
            let _ = w.add_event_listener_with_callback("resize", resize.as_ref().unchecked_ref());
        }
        resize.forget();
        // `#cursor=N` (a link or a screenshot): show line N's account as if the caret were there
        let hash = web_sys::window()
            .and_then(|w| w.location().hash().ok())
            .unwrap_or_default();
        if let Some(n) = hash
            .split(['#', '&'])
            .find_map(|p| p.strip_prefix("cursor="))
            .and_then(|v| v.parse::<usize>().ok())
        {
            let e = self.holder();
            vericode_ui::set_timeout(
                move || {
                    let mut ed = e.borrow_mut();
                    if n >= 1 && n <= ed.text().len() {
                        ed.line_mut(n - 1).set_cursor(true);
                        ed.cursor_line = Some(n - 1);
                        focus_note("cursor", Some(n - 1));
                    }
                },
                1500,
            );
        }
    }

    fn mark_cursor_line(&mut self) {
        let sel = get_selection();
        let line = if sel.anchor_node().is_some() {
            self.get_lines_and_positions(&sel)
                .ok()
                .map(|p| p.start_line)
        } else {
            None
        };
        if line == self.cursor_line {
            return;
        }
        if let Some(old) = self.cursor_line
            && old < self.text().len()
        {
            self.line_mut(old).set_cursor(false);
        }
        if let Some(n) = line
            && n < self.text().len()
        {
            self.line_mut(n).set_cursor(true);
        }
        self.cursor_line = line;
        focus_note("cursor", line);
    }

    /// "show all proofs": every line's proof account at once (body class `show-proofs`),
    /// remembered per viewer; `#proofs=all` turns it on for a link.
    fn install_proofs_toggle(&mut self) {
        vericode_ui::set_timeout(install_proofs_toggle_now, 0);
    }

    // Load the program named by the URL fragment (#ex= or #src=), or else (at startup)
    // the user's own program from localStorage, or else the default program.
    fn load_from_location(&mut self, startup: bool) {
        let params = LinkParams::parse(&self.window.location_hash());
        if !startup && params.source.is_none() && self.link.storage_key.is_none() {
            // fragment changed without naming a program: keep the current one
            self.link.embed = params.embed;
            self.share_mut().inner_mut().set_embed(params.embed);
            return;
        }

        self.flush_save();
        self.link.load_generation += 1;
        self.link.embed = params.embed;
        self.link.args = params.args.clone();
        self.link.strict = params.strict;
        self.link.pending_vc = params
            .vericode
            .then(|| (params.session.clone(), params.turn));
        if let Some(name) = params.session.clone() {
            // a recorded session brings its own program
            self.link.example = None;
            self.set_contents(&format!(";; loading session {name}"), None);
            self.vc_load_session(&name, params.turn);
            self.link.pending_vc = None;
            return;
        }
        self.link.storage_key = params.storage_key(STORAGE_ID);
        self.link.example = None;
        self.share_mut().inner_mut().set_embed(params.embed);

        match params.source {
            None => {
                let saved = StorageHandle::new().and_then(|s| s.get_item(STORAGE_ID));
                match saved {
                    Some(content) => self.set_contents(&content, params.step),
                    None => {
                        self.set_default_contents();
                        self.link.pending_step = params.step;
                        self.after_load();
                    }
                }
            }
            Some(ProgramSource::Inline(payload)) => match decode_program(&payload) {
                Ok(text) => self.set_contents(&text, params.step),
                Err(e) => self.set_contents(&format!(";; could not read this link: {e}"), None),
            },
            Some(ProgramSource::Example(name)) => {
                let url = format!("examples/{name}.wat");
                self.set_contents(&format!(";; loading {url}"), None);
                self.link.example = Some(name);
                let generation = self.link.load_generation;
                let holder = self.holder();
                let step = params.step;
                wasm_bindgen_futures::spawn_local(async move {
                    let result = fetch_text(&url).await;
                    let mut ed = holder.borrow_mut();
                    if ed.link.load_generation != generation {
                        return; // superseded by a later navigation
                    }
                    match result {
                        Ok(text) => ed.set_contents(&text, step),
                        Err(e) => ed.set_contents(&format!(";; could not load {url}: {e}"), None),
                    }
                });
            }
        }
    }

    // Replace the whole buffer with `content` (undo history is reset).
    fn set_contents(&mut self, content: &str, step: Option<StepRequest>) {
        let len = self.text().len();
        self.text_mut().remove_range(0, len);
        for line_str in content.lines() {
            self.push_line(line_str);
        }
        if self.text().is_empty() {
            self.push_line("");
        }
        self.link.pending_step = step;
        if self.on_change().is_err() {
            self.set_default_contents();
        }
        self.after_load();
    }

    fn after_load(&mut self) {
        self.action_history = ActionHistory::default();
        self.previous_instrumented_binary_hash = 0; // force a fresh run (for the step request)
        self.on_change().expect("well-formed initial contents");
        self.link.loaded_text = self.buffer_as_text();
        if self.link.pending_vc.take().is_some() || self.vc.is_some() {
            // vericoding starts from what was just loaded: that is the student's spec
            self.vc_set_mode(false);
            self.vc_set_mode(true);
            // (at startup the body is rebuilt after this: draw the panel again once it is)
            let holder = self.holder();
            vericode_ui::later(move || holder.borrow().vc_render());
        }
        let height = LINE_SPACING * self.text().len();
        self.image_mut()
            .set_attribute("height", &height.to_string());
    }

    // Save immediately if a save is pending (used before switching programs).
    fn flush_save(&mut self) {
        if self.pending_save.is_some() && self.save_status().is_dirty() {
            let key = self.storage_key();
            let content = self.buffer_as_text();
            if let Some(s) = self.storage.as_ref() {
                s.try_set_item(&key, &content);
            }
        }
    }

    // The step to show for `step=fail`: the first failed check (none are reported until a
    // proof kernel is wired in), or else the final step (where a trap, if any, is shown).
    fn first_failure_step(&self) -> Option<usize> {
        let count = RUN_LOG.with(|r| r.step_count());
        (count > 0).then(|| count - 1)
    }

    // Copy (or, when embedded, open) a link to the current program at the current step.
    fn share_link(&mut self) {
        let step_count = RUN_LOG.with(|r| r.step_count());
        let current = self.current_step();
        let step = if step_count <= 1 {
            None
        } else if current + 1 >= step_count {
            Some(StepRequest::Last)
        } else {
            Some(StepRequest::Number(current))
        };
        let text = self.buffer_as_text();
        let fragment = match &self.link.example {
            Some(name) if text == self.link.loaded_text => {
                let mut f = format!("#ex={name}");
                match step {
                    Some(StepRequest::Number(n)) => f.push_str(&format!("&step={n}")),
                    Some(StepRequest::Last) => f.push_str("&step=last"),
                    _ => {}
                }
                f + &args_fragment(&self.link.args)
            }
            _ => share_fragment(&text, step, false) + &args_fragment(&self.link.args),
        };
        let url = self.window.location_without_hash() + &fragment;
        if self.link.embed {
            self.window.open_in_new_tab(&url);
        } else {
            self.window.copy_to_clipboard(&url);
            let share = self.share_mut().inner_mut();
            share.flash("\u{2713}");
            share.set_link(&url);
        }
    }

    fn push_line(&mut self, string: &str) {
        let newline = CodeLine::new(string, &self.factory);
        self.text_mut().push(newline);
    }

    fn set_default_contents(&mut self) {
        let len = self.text().len();
        self.text_mut().remove_range(0, len);
        self.link.pending_step = None;
        self.push_line("(func");
        self.push_line("i32.const 5");
        self.push_line("i32.const 6");
        self.push_line("i32.add");
        self.push_line("drop");
        self.push_line(")");
    }
}

#[cfg(all(test, target_arch = "wasm32"))]
mod browser_tests {
    use super::*;
    use crate::jet::wasm_bindgen_test_harness_body;
    use wasm_bindgen_test::{wasm_bindgen_test, wasm_bindgen_test_configure};
    wasm_bindgen_test_configure!(run_in_browser);

    thread_local! {
        static TEST_EDITOR: EditorHolder = make_test_editor();
    }

    fn make_test_editor() -> EditorHolder {
        let editor = EditorHolder::new(Document::default().element_factory()).expect("editor");
        let test_harness_body = wasm_bindgen_test_harness_body().expect("body");
        test_harness_body.append_node(&editor);
        std::mem::forget(test_harness_body); // don't delete body from the document
        editor
    }

    fn get_editor_holder() -> EditorHolder {
        TEST_EDITOR.with(|test_editor| test_editor.borrow_mut().holder())
    }

    fn set_editor_content(editor: &mut Editor, content: &str) {
        let line_count = editor.text().len();
        editor.text_mut().remove_range(0, line_count);
        assert!(editor.buffer_as_text().is_empty());
        for line in content.lines() {
            editor.push_line(line);
        }
        assert_eq!(editor.buffer_as_text(), content);
        editor.on_change().expect("usable contents");
    }

    #[wasm_bindgen_test]
    fn action_history_courtesy_end() -> Result<()> {
        const EMPTY_FUNCTION: &str = "(func\n\n)\n";
        const BLOCK_INSERTED_FUNCTION: &str = "(func\nblock\nend\n)\n";

        let holder = get_editor_holder();
        let mut editor = holder.borrow_mut();

        // Undo and redo preserves added block courtesy end
        {
            set_editor_content(&mut editor, EMPTY_FUNCTION);

            let (node, offset) = editor
                .line(1)
                .position_to_node_and_weboffset(Position::begin())?;
            set_selection_range(&node, offset, &node, offset);
            editor.handle_edit(&get_selection(), "block")?;
            assert_eq!(editor.buffer_as_text(), BLOCK_INSERTED_FUNCTION);

            editor.undo()?;
            assert_eq!(editor.buffer_as_text(), EMPTY_FUNCTION);

            editor.redo()?;
            assert_eq!(editor.buffer_as_text(), BLOCK_INSERTED_FUNCTION);
        }

        // Undo and redo preserves deleted block courtesy end
        {
            set_editor_content(&mut editor, BLOCK_INSERTED_FUNCTION);

            let (start_node, start_offset) = editor
                .line(1)
                .position_to_node_and_weboffset(Position::begin())?;
            let (end_node, end_offset) = editor
                .line(1)
                .position_to_node_and_weboffset(editor.line(1).end_position())?;
            set_selection_range(&start_node, start_offset, &end_node, end_offset);
            editor.handle_edit(&get_selection(), "")?;
            assert_eq!(editor.buffer_as_text(), EMPTY_FUNCTION);

            editor.undo()?;
            assert_eq!(editor.buffer_as_text(), BLOCK_INSERTED_FUNCTION);

            editor.redo()?;
            assert_eq!(editor.buffer_as_text(), EMPTY_FUNCTION);
        }
        Ok(())
    }

    #[wasm_bindgen_test]
    fn local_fractions() -> Result<()> {
        let holder = get_editor_holder();
        let mut editor = holder.borrow_mut();
        set_editor_content(&mut editor, "(func\n(local f64)\n(local f64)\n)\n");

        assert!(editor.image().is_fraction_at_pos(editor.line(1).id()));
        assert!(editor.image().is_fraction_at_pos(editor.line(2).id()));
        Ok(())
    }
}

const PROOFS_KEY: &str = "codillon-show-proofs";

fn install_proofs_toggle_now() {
    let Some(w) = web_sys::window() else { return };
    let Some(doc) = w.document() else { return };
    let Some(body) = doc.body() else { return };
    let from_link = w.location().hash().is_ok_and(|h| h.contains("proofs=all"));
    let remembered = w
        .local_storage()
        .ok()
        .flatten()
        .and_then(|s| s.get_item(PROOFS_KEY).ok().flatten())
        .is_some_and(|v| v == "1");
    if from_link || remembered {
        let _ = body.class_list().add_1("show-proofs");
    }
    let Ok(b) = doc.create_element("button") else {
        return;
    };
    let b: web_sys::HtmlElement = b.unchecked_into();
    b.set_class_name("proofs-toggle");
    b.set_inner_text("show all proofs");
    b.set_title("show every line's proof account (what it needs, the facts used, why)");
    let click = Closure::<dyn FnMut()>::new(move || {
        let Some(w) = web_sys::window() else { return };
        let Some(body) = w.document().and_then(|d| d.body()) else {
            return;
        };
        let on = body.class_list().toggle("show-proofs").unwrap_or(false);
        if let Ok(Some(s)) = w.local_storage() {
            let _ = s.set_item(PROOFS_KEY, if on { "1" } else { "0" });
        }
        layout_notes();
    });
    b.set_onclick(Some(click.as_ref().unchecked_ref()));
    click.forget();
    let _ = body.append_child(&b);
}

/// The accounts column's width (research/24 §4, polish): wide windows keep every account in a
/// column at the right, aligned with its line, so no account covers code; None when the window
/// is too narrow or the editor is embedded (the account then shows below the caret's line).
fn notes_width(right: f32, embed: bool) -> Option<f32> {
    (!embed && right >= 1150.0).then(|| (right * 0.34).clamp(380.0, 560.0))
}

/// One account as a note: a row per part (needs, using, why), each fact used on its own line.
fn note_html(text: &str, line: u32) -> String {
    use std::fmt::Write;
    let mut rows: Vec<(&str, Vec<String>)> = vec![];
    for l in text.lines() {
        if l.starts_with("        ") {
            if let Some(r) = rows.last_mut() {
                r.1.push(l.trim().to_string());
            }
            continue;
        }
        let (k, rest) = [
            ("needs", "needs "),
            ("proves", "⊢ "),
            ("using", "using "),
            ("why", "why: "),
        ]
        .iter()
        .find_map(|(k, p)| l.strip_prefix(p).map(|r| (*k, r)))
        .unwrap_or(("", l));
        let parts = if k == "using" {
            // "① a — origin; ② b — origin": one fact per line
            let mut v: Vec<String> = vec![];
            for p in rest.split("; ") {
                match v.last_mut() {
                    Some(last)
                        if !p.starts_with(['①', '②', '③', '④', '⑤', '⑥', '⑦', '⑧', '⑨', '⑩']) =>
                    {
                        last.push_str("; ");
                        last.push_str(p);
                    }
                    _ => v.push(p.to_string()),
                }
            }
            v
        } else {
            vec![rest.to_string()]
        };
        rows.push((k, parts));
    }
    let mut out = format!("<div class=\"pv-tag\">line {line}</div>");
    for (i, (k, parts)) in rows.iter().enumerate() {
        let sep = if i > 0 && matches!(*k, "needs" | "proves") {
            " pv-sep"
        } else {
            ""
        };
        let _ = write!(
            out,
            "<div class=\"pv-row{sep}\"><span class=\"pv-k\">{k}</span><div class=\"pv-v\">"
        );
        for p in parts {
            let _ = write!(out, "<div>{}</div>", crate::proof_view::esc(p));
        }
        out.push_str("</div></div>");
    }
    out
}

/// Place the visible notes: each at its line, pushed down below the one before it (all of
/// them under "show all proofs", else only the caret's and the hovered line's).
fn layout_notes() {
    use wasm_bindgen::JsCast;
    let Some(doc) = web_sys::window().and_then(|w| w.document()) else {
        return;
    };
    let Some(b) = doc.get_element_by_id("pv-notes") else {
        return;
    };
    let all = doc
        .body()
        .is_some_and(|b| b.class_list().contains("show-proofs"));
    let notes = b.children();
    let mut bottom = f64::MIN;
    for k in 0..notes.length() {
        let Some(n) = notes
            .item(k)
            .and_then(|e| e.dyn_into::<web_sys::HtmlElement>().ok())
        else {
            continue;
        };
        let cl = n.class_list();
        if !(all || cl.contains("cursor") || cl.contains("hover")) {
            continue;
        }
        let y: f64 = n
            .get_attribute("data-y")
            .and_then(|v| v.parse().ok())
            .unwrap_or(0.0);
        let top = if all { y.max(bottom + 6.0) } else { y };
        let _ = n.style().set_property("top", &format!("{top:.0}px"));
        bottom = top + n.offset_height() as f64;
    }
}

/// Mark the note of editor line `line` with `class` ("cursor" or "hover"), unmarking the rest.
fn focus_note(class: &str, line: Option<usize>) {
    let Some(doc) = web_sys::window().and_then(|w| w.document()) else {
        return;
    };
    let Some(b) = doc.get_element_by_id("pv-notes") else {
        return;
    };
    let notes = b.children();
    let want = line.map(|l| l.to_string());
    for k in 0..notes.length() {
        if let Some(n) = notes.item(k) {
            let on = want.is_some() && n.get_attribute("data-line") == want;
            let _ = n.class_list().toggle_with_force(class, on);
        }
    }
    layout_notes();
}

impl Editor {
    /// Rebuild the accounts column from the lines' accounts (None: no column).
    fn sync_notes(&self, width: Option<f32>, disp: &dyn Fn(u32) -> u32) {
        use wasm_bindgen::JsCast;
        let Some(w) = web_sys::window() else { return };
        let Some(doc) = w.document() else { return };
        let Some(body) = doc.body() else { return };
        let notes = match doc.get_element_by_id("pv-notes") {
            Some(e) => e,
            None => {
                let Ok(e) = doc.create_element("div") else {
                    return;
                };
                e.set_id("pv-notes");
                let _ = body.append_child(&e);
                e
            }
        };
        notes.set_inner_html("");
        let Some(width) = width else {
            let _ = body.class_list().remove_1("notes-col");
            return;
        };
        let _ = body.class_list().add_1("notes-col");
        let _ = body
            .style()
            .set_property("--notes-w", &format!("{width:.0}px"));
        let Some(te) = doc.query_selector(".textentry").ok().flatten() else {
            return;
        };
        let r = te.get_bounding_client_rect();
        let (sx, sy) = (w.scroll_x().unwrap_or(0.0), w.scroll_y().unwrap_or(0.0));
        if let Ok(n) = notes.clone().dyn_into::<web_sys::HtmlElement>() {
            let st = n.style();
            let _ = st.set_property("left", &format!("{:.0}px", r.right() + sx - width as f64));
            let _ = st.set_property("top", &format!("{:.0}px", r.top() + sy));
            let _ = st.set_property("width", &format!("{width:.0}px"));
        }
        let rows = te.children();
        for (i, l) in self.text().iter().enumerate() {
            let Some(t) = &l.info().proof.explain else {
                continue;
            };
            let y = rows
                .item(i as u32)
                .map(|e| e.get_bounding_client_rect().top() - r.top())
                .unwrap_or((i * LINE_SPACING) as f64);
            let Ok(n) = doc.create_element("div") else {
                continue;
            };
            n.set_class_name(if self.cursor_line == Some(i) {
                "pv-note cursor"
            } else {
                "pv-note"
            });
            let _ = n.set_attribute("data-line", &i.to_string());
            let _ = n.set_attribute("data-y", &format!("{:.0}", y + 2.0));
            n.set_inner_html(&note_html(t, disp(i as u32 + 1)));
            let _ = notes.append_child(&n);
        }
        layout_notes();
    }
}
