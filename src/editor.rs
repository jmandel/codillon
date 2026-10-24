// The Codillon code editor

use crate::{
    action_history::{ActionHistory, Edit},
    autocomplete::Autocomplete,
    checker::{
        CheckKind, CheckResults, Outcome, RefinedSlot, Seed, SlotEnv, SpecPlan, StreamingCheck,
        Verdict, WITNESS_BUDGET, build_plan, candidates, check_run_from, refined_slots,
        search_targets,
    },
    debug::{
        ExecutionState, ExecutionStatus, RUN_LOG, RunArg, TerminationType, compile_module,
        run_binary, run_witness,
    },
    dom_canvas::DomCanvas,
    dom_struct::DomStruct,
    dom_vec::DomVec,
    graphics::{DomImage, FractionInfo, refined_row_extra},
    jet::{
        AccessToken, Component, ControlHandlers, DocumentHandle, ElementFactory, InputEventHandle,
        NodeRef, RangeLike, ReactiveComponent, StorageHandle, WebOffset, WindowHandle, WithElement,
        compare_document_position, fetch_text, get_selection, now_ms, set_selection_range,
    },
    line::{Activity, CodeLine, LineInfo, Position, PositionRange, ProofMark, SpecMark},
    link::{LinkParams, ProgramSource, StepRequest, args_fragment, decode_program, share_fragment},
    prover::{LineSnapshot, SolverState, solver_state},
    refine::refined_draw,
    save_status::SaveStatus,
    share::ShareButton,
    slider::Slider,
    syntax::{
        FrameInfo, FrameInfosMut, InstrKind, LineInfos, LineInfosMut, LineKind, SyntheticWasm,
        fix_syntax,
    },
    utils::{
        AnimationRequest, AnnotatedOperatorType, ConnectionSource, FmtError, FunctionIdCache,
        InstrumentOptions, OperatorType, RawModule, SlotConnections, SlotInfo, TypedModule,
        ValidModule, find_connections, indent_and_frame, str_to_binary,
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
use thousands::Separable;
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

// A run to make: binary, version, entry, arguments, and the state it starts from.
type PendingRun = (Vec<u8>, usize, String, Vec<RunArg>, Option<Rc<Seed>>);

struct Editor {
    component: ComponentType,
    factory: ElementFactory,
    action_history: ActionHistory,
    storage: Option<StorageHandle>,
    pending_binary: Option<PendingRun>,
    current_binary: Rc<Vec<u8>>,
    replay: Option<(usize, Vec<i128>)>, // a witness loaded as the run: (function, input)
    replay_seed: Option<Rc<Seed>>,      // … and the state it starts from (a solver's model)
    witness: WitnessSearch,
    witness_version: usize, // the version the search ran (or runs) for
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
    spec_plan: Rc<SpecPlan>,
    spec_results: Rc<CheckResults>,
    refined_slots: Vec<RefinedSlot>,
    proofs: Proofs,
}

/// The static half: the program's obligations (vc.rs) and what Z3 says of each.
#[derive(Default)]
struct Proofs {
    generation: usize, // bumped by every edit; a proof of an older generation stops
    request: Option<(usize, Rc<ProofInput>)>,
    requested_at: f64,
    running: bool,
    obligations: Rc<Vec<crate::vc::Obligation>>,
    verdicts: Vec<Option<crate::vc::Verdict>>,
    cache: HashMap<u64, crate::vc::Verdict>, // by query hash, across edits
    started_at: f64,
    first_at: Option<f64>,
    finished_at: Option<f64>,
    queries: usize,
    generate_ms: f64,
}

struct ProofInput {
    lines: LineSnapshot,
    wasm: Vec<u8>,
    plan: Rc<SpecPlan>,
}

/// How long typing must pause before the obligations are generated and proved.
const PROOF_DELAY_MS: f64 = 350.0;

// State derived from the URL fragment (see link.rs).
#[derive(Default)]
struct LinkState {
    embed: bool,
    storage_key: Option<String>, // None: the user's own program (STORAGE_ID)
    example: Option<String>,     // name of the loaded example, if any
    loaded_text: String,         // the program text as loaded from the link
    pending_step: Option<StepRequest>,
    load_generation: usize,
    args: Option<Vec<i128>>, // #args=… for $main
}

/// What the input search has found for the current version of the program.
#[derive(Default, Clone)]
enum WitnessSearch {
    #[default]
    Idle,
    Searching {
        tried: usize,
    },
    NoneFound {
        tried: usize,
        funcs: usize,
    },
    Found(Witness),
}

#[derive(Clone)]
struct Witness {
    func: usize,
    args: Vec<i128>,
    verdict: Verdict,
}

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
        if step_count > 1 {
            self.slider_mut().inner_mut().show();
            let failures = self.spec_results.failure_steps();
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

        self.draw_refined_slots();

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
            let extra = self.text()[*line_num].extra_px();
            self.animations.arrow = get_mut!(self.component, image).set_arrow_location(
                !source_changed,
                Some((*line_num, *below_line, *indent as usize, extra)),
            );
            if self.scroll_on_next_input {
                get_mut!(self.component, image).scroll_to_arrow();
                self.scroll_on_next_input = false;
            }
        } else {
            self.animations.arrow = get_mut!(self.component, image).set_arrow_location(false, None);
        }

        self.apply_spec_marks(current_step);

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

    // Draw each refined slot's number line for the current step: the admitted region
    // (with bounds evaluated at this step), and the value, spilling if it is outside.
    fn draw_refined_slots(&mut self) {
        if self.refined_slots.is_empty() {
            return;
        }
        let plan = self.spec_plan.clone();
        let refined = std::mem::take(&mut self.refined_slots);
        {
            let state = &self.execution_state;
            let value_of_slot = |slot: usize| -> Option<i128> {
                let contents = state.slots.get(slot)?.last().copied().flatten()?;
                match contents.val {
                    crate::debug::WasmValue::I32(v) => Some(v as i128),
                    crate::debug::WasmValue::I64(v) => Some(v as i128),
                    _ => None,
                }
            };
            for r in &refined {
                let env = SlotEnv {
                    plan: &plan,
                    func: r.func,
                    value_of_slot: &value_of_slot,
                };
                let draw = refined_draw(&r.pred, &r.subject, value_of_slot(r.slot), &env);
                get_mut!(self.component, image).set_refined_slot(&r.coord, r.is_input, Some(&draw));
            }
        }
        self.refined_slots = refined;
    }

    // Re-evaluate the specification checks along the current run log.
    fn recheck_specs(&mut self) {
        let plan = self.spec_plan.clone();
        let seed = self.replay.as_ref().and(self.replay_seed.clone());
        self.spec_results =
            Rc::new(RUN_LOG.with(|log| check_run_from(&plan, log, seed.as_deref())));
    }

    // Show what the checks say as of `step`: ⚖ on failed spec lines (with the predicate,
    // values substituted, as commentary) and on the instructions where they were checked,
    // and a slategray count of the checks that held so far.
    fn apply_spec_marks(&mut self, step: usize) {
        let results = self.spec_results.clone();
        let plan = self.spec_plan.clone();
        let mut marks: HashMap<usize, SpecMark> = HashMap::new();
        let mut at_labels: HashMap<usize, Vec<String>> = HashMap::new();
        for e in results.events.iter().take_while(|e| e.step <= step) {
            let m = marks.entry(e.spec_line).or_default();
            if e.kind == CheckKind::Assume {
                m.assumed = true;
            }
            match e.outcome {
                Outcome::Held => m.held += 1,
                Outcome::Unknown => m.unknown = Some(e.message.clone()),
                Outcome::Failed => {
                    m.failed = Some(e.message.clone());
                    if e.at_line != e.spec_line {
                        let f = plan
                            .funcs
                            .get(e.func)
                            .map(|f| f.display_name())
                            .unwrap_or_default();
                        let label = match e.kind {
                            CheckKind::Requires | CheckKind::ParamRefinement => {
                                format!("precondition of {f} fails at this call")
                            }
                            CheckKind::Ensures | CheckKind::ResultRefinement => {
                                format!("postcondition of {f} fails at this return")
                            }
                            CheckKind::LocalRefinement => {
                                "a refined local is set to a value outside its type".to_string()
                            }
                            CheckKind::Invariant => "loop invariant fails here".to_string(),
                            CheckKind::Decreases => "loop measure fails here".to_string(),
                            CheckKind::Assert | CheckKind::Assume => {
                                format!("@{} above fails here", e.kind.label())
                            }
                        };
                        let labels = at_labels.entry(e.at_line).or_default();
                        if !labels.contains(&label) {
                            labels.push(label);
                        }
                    }
                }
            }
        }
        // a run that hit the step budget says so where it stopped
        let count = RUN_LOG.with(|r| r.step_count());
        if count > 0
            && step + 1 >= count
            && RUN_LOG.with(|r| r.termination_type()) == TerminationType::TooManySteps
            && let Some(line) = self.execution_state.status.line_num
        {
            marks.entry(line).or_default().note = Some(format!(
                "the run stopped here, at the {}-step budget",
                crate::debug::MAX_STEPS.separate_with_commas()
            ));
        }
        for (line, labels) in at_labels {
            let m = marks.entry(line).or_default();
            if m.failed.is_none() {
                m.failed = Some(labels.join("; "));
            }
        }
        self.overlay_proofs(&mut marks);
        for idx in 0..self.text().len() {
            let mark = marks.remove(&idx).unwrap_or_default();
            if *self.line(idx).spec_mark() != mark {
                self.line_mut(idx).set_spec_mark(mark);
            }
        }
    }

    fn current_step(&self) -> usize {
        self.slider().inner().value_as_number().round() as usize
    }

    fn execute(&mut self, binary: &[u8], version: usize) {
        let (entry, args) = self.run_config();
        let seed = self.replay.as_ref().and(self.replay_seed.clone());
        self.pending_binary = Some((binary.to_vec(), version, entry, args, seed));
        if self.worker_running {
            return;
        }
        self.worker_running = true;

        let holder = self.holder();

        wasm_bindgen_futures::spawn_local(async move {
            loop {
                let Some((binary, version, entry, args, seed)) =
                    holder.borrow_mut().pending_binary.take()
                else {
                    break;
                };
                run_binary(&binary, &entry, &args, seed.as_deref())
                    .await
                    .unwrap_or_else(|e| log_1(&format!("Codillon runtime error: {e}").into()));

                let mut ed = holder.borrow_mut();
                if version != ed.version {
                    continue;
                }

                let mut slider_step = ed.current_step();
                let step_count = RUN_LOG.with(|r| r.step_count());
                ed.recheck_specs();
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
                ed.start_witness_search();
            }
            holder.borrow_mut().worker_running = false;
        });
    }

    // The function a run calls, and its arguments: $main (with #args=, else its (@run …),
    // else zeros), or a witness that was loaded as the run.
    fn run_config(&self) -> (String, Vec<RunArg>) {
        let plan = &self.spec_plan;
        let to_args = |func: usize, vals: &[i128]| -> Vec<RunArg> {
            let Some(fp) = plan.funcs.get(func) else {
                return vec![];
            };
            fp.vars[..fp.nparams]
                .iter()
                .enumerate()
                .map(|(i, v)| {
                    let x = vals.get(i).copied().unwrap_or(0);
                    if v.width == 64 {
                        RunArg::I64(x as i64)
                    } else {
                        RunArg::I32(x as i32)
                    }
                })
                .collect()
        };
        if let Some((f, args)) = &self.replay
            && *f < plan.funcs.len()
        {
            return (format!("f{f}"), to_args(*f, args));
        }
        let vals = self
            .link
            .args
            .clone()
            .or_else(|| plan.run_args.as_ref().map(|(_, a)| a.clone()))
            .unwrap_or_default();
        ("main".to_string(), to_args(0, &vals))
    }

    fn run_hash(&self, binary: &[u8]) -> u64 {
        use std::hash::{DefaultHasher, Hash, Hasher};
        let mut hasher = DefaultHasher::new();
        binary.hash(&mut hasher);
        self.run_config().hash(&mut hasher);
        hasher.finish()
    }

    // Run the current binary again (the run's function or arguments changed).
    fn rerun(&mut self, step: Option<StepRequest>) {
        self.version += 1;
        self.witness_version = self.version; // same program: keep the search's result
        self.link.pending_step = step;
        let binary = self.current_binary.clone();
        self.previous_instrumented_binary_hash = self.run_hash(&binary);
        self.execute(&binary, self.version);
    }

    fn func_label(&self, func: usize, args: &[i128]) -> String {
        let name = self
            .spec_plan
            .funcs
            .get(func)
            .map(|f| f.display_name())
            .unwrap_or_default();
        let args: Vec<String> = args.iter().map(|a| a.to_string()).collect();
        format!("{name}({})", args.join(", "))
    }

    // Show the state of the input search above the slider.
    fn show_witness(&mut self) {
        use crate::witness_track::TrackState;
        let budget = crate::debug::MAX_STEPS;
        let proof = self.proof_status();
        let (state, text, title) = match (&self.witness, &self.replay) {
            (_, Some((f, args))) if self.replay_seed.is_some() => (
                TrackState::Replayed,
                format!(
                    "\u{2696} replaying the solver's counterexample {} \u{2014} click to return to your run",
                    self.func_label(*f, args)
                ),
                "A state the specification allows, set up in a fresh instance (memory, globals and ghosts from the solver's model)".to_string(),
            ),
            // with obligations, the proofs speak for the program (unless a run found a witness)
            (WitnessSearch::Idle | WitnessSearch::Searching { .. } | WitnessSearch::NoneFound { .. }, None)
                if proof.is_some() =>
            {
                proof.unwrap()
            }
            (WitnessSearch::Found(w), Some((f, args))) => {
                let call = self.func_label(*f, args);
                match &w.verdict {
                    Verdict::Refuted { step, .. } if *step >= budget => (
                        TrackState::Replayed,
                        format!(
                            "\u{2696} counterexample {call} \u{b7} replayed up to the {}-step budget; it fails at step {} \u{2014} click to return to your run",
                            budget.separate_with_commas(),
                            step.separate_with_commas()
                        ),
                        String::new(),
                    ),
                    _ => (
                        TrackState::Replayed,
                        format!(
                            "\u{2696} counterexample {call} \u{b7} replayed \u{2014} click to return to your run"
                        ),
                        String::new(),
                    ),
                }
            }
            (_, Some(_)) => (TrackState::Hidden, String::new(), String::new()),
            (WitnessSearch::Idle, None) => (TrackState::Hidden, String::new(), String::new()),
            (WitnessSearch::Searching { tried }, None) => (
                TrackState::Note,
                format!("searching inputs\u{2026} {tried} tried"),
                String::new(),
            ),
            (WitnessSearch::NoneFound { tried, funcs }, None) => (
                TrackState::Note,
                format!(
                    "\u{2218} no counterexample among {tried} inputs to {funcs} function{} (held on these inputs, not proven)",
                    if *funcs == 1 { "" } else { "s" }
                ),
                String::new(),
            ),
            (WitnessSearch::Found(w), None) => {
                let call = self.func_label(w.func, &w.args);
                match &w.verdict {
                    Verdict::Refuted { step, message, .. } if *step >= budget => (
                        TrackState::NotReplayed,
                        format!(
                            "\u{2696} input {call} fails at step {} \u{b7} not replayed: beyond the {}-step budget",
                            step.separate_with_commas(),
                            budget.separate_with_commas()
                        ),
                        format!(
                            "{message}\nA replay stops at step {} before the failure; click to replay up to there",
                            budget.separate_with_commas()
                        ),
                    ),
                    Verdict::Refuted { message, .. } => (
                        TrackState::NotReplayed,
                        format!(
                            "\u{2696} input {call} fails \u{b7} not replayed \u{2014} click to replay"
                        ),
                        message.clone(),
                    ),
                    Verdict::Trapped(msg) => (
                        TrackState::NotReplayed,
                        format!(
                            "\u{2696} input {call} traps \u{b7} not replayed \u{2014} click to replay"
                        ),
                        msg.clone(),
                    ),
                    _ => (TrackState::Hidden, String::new(), String::new()),
                }
            }
        };
        self.slider_mut()
            .inner_mut()
            .track_mut()
            .inner_mut()
            .set(state, &text, &title);
        // the solver's counterexample, drawn when the track shows it (or it is the run)
        let showing_static = self.replay_seed.is_some()
            || (self.replay.is_none()
                && !matches!(self.witness, WitnessSearch::Found(_))
                && self.proofs.verdicts.iter().all(|v| v.is_some()));
        let card = if showing_static {
            self.static_witness()
                .and_then(|(_, m)| crate::prover::state_card(&self.spec_plan, m))
        } else {
            None
        };
        self.slider_mut().inner_mut().card_mut().set(card);
    }

    // Clicking the witness track: replay the witness, or return to the user's run.
    fn toggle_replay(&mut self) {
        if self.replay.is_some() {
            self.replay = None;
            self.replay_seed = None;
            self.rerun(None);
        } else if let WitnessSearch::Found(w) = &self.witness {
            self.replay = Some((w.func, w.args.clone()));
            self.replay_seed = None;
            self.rerun(Some(StepRequest::Fail));
        } else if let Some((i, _)) = self.static_witness()
            && let Some((f, args, seed)) = self.static_replay(i)
        {
            self.replay = Some((f, args));
            self.replay_seed = Some(Rc::new(seed));
            self.rerun(Some(StepRequest::Fail));
        } else {
            return;
        }
        self.show_witness();
    }

    // The first refuted obligation, and the model the solver gave for it.
    fn static_witness(&self) -> Option<(usize, &crate::vc::Model)> {
        let p = &self.proofs;
        p.verdicts.iter().enumerate().find_map(|(i, v)| match v {
            Some(crate::vc::Verdict::Refuted(m)) => Some((i, m)),
            _ => None,
        })
    }

    // A refuted obligation's model as a run: the function, its arguments, and the state
    // to set up first (function-entry states only; a loop-head state is not replayable).
    fn static_replay(&self, i: usize) -> Option<(usize, Vec<i128>, Seed)> {
        let ob = self.proofs.obligations.get(i)?;
        let Some(crate::vc::Verdict::Refuted(m)) = self.proofs.verdicts.get(i)?.as_ref() else {
            return None;
        };
        if ob.cut != crate::vc::Cut::Entry {
            return None;
        }
        let fp = self.spec_plan.funcs.get(ob.func)?;
        if fp.vars[..fp.nparams].iter().any(|v| v.width == 0) {
            return None; // float parameters
        }
        let args: Vec<i128> = fp.vars[..fp.nparams]
            .iter()
            .map(|v| {
                v.name
                    .as_ref()
                    .and_then(|n| m.vars.iter().find(|(x, _)| x == n))
                    .map(|(_, val)| *val)
                    .unwrap_or(0)
            })
            .collect();
        let ghost_names: Vec<&String> = self
            .spec_plan
            .ghost_globals
            .iter()
            .map(|(n, _)| n)
            .collect();
        let mut ghosts: Vec<(String, crate::spec::Val)> = m
            .ghosts
            .iter()
            .filter(|(n, _)| ghost_names.contains(&n))
            .map(|(n, v)| (n.clone(), crate::spec::Val::Int(*v)))
            .collect();
        for (n, map) in &m.maps {
            if ghost_names.contains(&n) {
                ghosts.push((n.clone(), crate::spec::Val::Map(Rc::new(map.clone()))));
            }
        }
        let seed = Seed {
            words: m.words.iter().map(|(a, v)| (*a, *v)).collect(),
            globals: m.globals.iter().map(|(g, _, v)| (*g, *v)).collect(),
            ghosts,
        };
        Some((ob.func, args, seed))
    }

    // After a run of a new version: search edge inputs for a counterexample, one fresh
    // instance per input, each checked as it runs (debug::run_witness).
    fn start_witness_search(&mut self) {
        if self.witness_version == self.version || self.replay.is_some() {
            return;
        }
        self.witness_version = self.version;
        let plan = self.spec_plan.clone();
        let targets = search_targets(&plan);
        if targets.is_empty() {
            self.witness = WitnessSearch::Idle;
            self.show_witness();
            return;
        }
        self.witness = WitnessSearch::Searching { tried: 0 };
        self.show_witness();
        let version = self.version;
        let binary = self.current_binary.clone();
        let holder = self.holder();
        wasm_bindgen_futures::spawn_local(async move {
            let Ok(module) = compile_module(&binary).await else {
                return;
            };
            let mut tried = 0;
            for &f in &targets {
                for args in candidates(&plan, f) {
                    let run_args: Vec<RunArg> = plan.funcs[f].vars[..plan.funcs[f].nparams]
                        .iter()
                        .zip(&args)
                        .map(|(v, x)| {
                            if v.width == 64 {
                                RunArg::I64(*x as i64)
                            } else {
                                RunArg::I32(*x as i32)
                            }
                        })
                        .collect();
                    if holder.borrow().witness_version != version {
                        return; // the program changed
                    }
                    let check = StreamingCheck::new(plan.clone(), WITNESS_BUDGET);
                    let Ok(run) = run_witness(&module, &format!("f{f}"), &run_args, check).await
                    else {
                        continue;
                    };
                    let mut ed = holder.borrow_mut();
                    if ed.witness_version != version {
                        return;
                    }
                    match run.verdict {
                        Verdict::NotAdmitted => continue,
                        Verdict::Refuted { .. } | Verdict::Trapped(_) => {
                            ed.witness = WitnessSearch::Found(Witness {
                                func: f,
                                args,
                                verdict: run.verdict,
                            });
                            ed.show_witness();
                            return;
                        }
                        Verdict::Held | Verdict::Budget => {
                            tried += 1;
                            if tried % 8 == 0 {
                                ed.witness = WitnessSearch::Searching { tried };
                                ed.show_witness();
                            }
                        }
                    }
                }
            }
            let mut ed = holder.borrow_mut();
            if ed.witness_version == version {
                ed.witness = WitnessSearch::NoneFound {
                    tried,
                    funcs: targets.len(),
                };
                ed.show_witness();
            }
        });
    }

    // ---------------------------------------------------------------------------------
    // Proofs

    // After an edit: prove the program's obligations once typing pauses.
    fn request_proofs(&mut self, lines: LineSnapshot, wasm: Vec<u8>) {
        let plan = self.spec_plan.clone();
        let p = &mut self.proofs;
        p.generation += 1;
        if !plan.has_checks() {
            p.request = None;
            p.obligations = Rc::new(vec![]);
            p.verdicts.clear();
            return;
        }
        p.request = Some((p.generation, Rc::new(ProofInput { lines, wasm, plan })));
        p.requested_at = now_ms();
        if !p.running {
            p.running = true;
            self.run_prover();
        }
    }

    fn run_prover(&self) {
        let holder = self.holder();
        wasm_bindgen_futures::spawn_local(async move {
            'requests: loop {
                // wait for typing to pause
                loop {
                    crate::prover::sleep(PROOF_DELAY_MS).await;
                    let ed = holder.borrow();
                    if ed.proofs.request.is_none()
                        || now_ms() - ed.proofs.requested_at >= PROOF_DELAY_MS
                    {
                        break;
                    }
                }
                let Some((generation, input)) = holder.borrow_mut().proofs.request.take() else {
                    holder.borrow_mut().proofs.running = false;
                    return;
                };
                let t_gen = now_ms();
                let obs = crate::prover::obligations(&input.lines, &input.wasm, &input.plan)
                    .unwrap_or_default();
                let gen_ms = now_ms() - t_gen;
                let obs = Rc::new(obs);
                {
                    let mut ed = holder.borrow_mut();
                    if ed.proofs.generation != generation {
                        continue;
                    }
                    let p = &mut ed.proofs;
                    p.verdicts = obs
                        .iter()
                        .map(|ob| p.cache.get(&ob.hash).cloned())
                        .collect();
                    p.obligations = obs.clone();
                    p.started_at = now_ms();
                    // (verdicts from the cache count as immediate)
                    p.first_at = p
                        .verdicts
                        .iter()
                        .any(|v| v.is_some())
                        .then_some(p.started_at);
                    p.finished_at = None;
                    p.queries = 0;
                    p.generate_ms = gen_ms;
                    ed.refresh_proofs();
                }
                for (i, ob) in obs.iter().enumerate() {
                    if holder
                        .borrow()
                        .proofs
                        .verdicts
                        .get(i)
                        .is_some_and(|v| v.is_some())
                    {
                        continue;
                    }
                    let mut proof = crate::vc::Proof::new(ob);
                    while let Some(q) = proof.next(ob) {
                        let out = crate::prover::solve(&q).await;
                        let mut ed = holder.borrow_mut();
                        if ed.proofs.generation != generation {
                            continue 'requests; // edited: start over (finished verdicts are cached)
                        }
                        match out {
                            Ok(out) => {
                                ed.proofs.queries += 1;
                                proof.feed(ob, &out);
                            }
                            Err(_) => {
                                // the solver failed to load: verdicts stay pending
                                ed.refresh_proofs();
                                ed.proofs.running = false;
                                return;
                            }
                        }
                    }
                    let mut ed = holder.borrow_mut();
                    if ed.proofs.generation != generation {
                        continue 'requests;
                    }
                    if let Some(v) = proof.verdict().cloned() {
                        if ed.proofs.cache.len() > 4000 {
                            ed.proofs.cache.clear();
                        }
                        ed.proofs.cache.insert(ob.hash, v.clone());
                        ed.proofs.verdicts[i] = Some(v);
                    }
                    if ed.proofs.first_at.is_none() {
                        ed.proofs.first_at = Some(now_ms());
                    }
                    ed.refresh_proofs();
                }
                let mut ed = holder.borrow_mut();
                if ed.proofs.generation == generation {
                    ed.proofs.finished_at = Some(now_ms());

                    ed.refresh_proofs();
                }
            }
        });
    }

    fn refresh_proofs(&mut self) {
        let step = self.current_step();
        self.apply_spec_marks(step);
        self.show_witness();
        self.schedule_animation_if_needed();
    }

    // What the solver says, onto the lines: proven is silence (no count), refuted is ⚖
    // with the state the spec allows, undecided is an indigo ?, and pending leaves the
    // run's marks as they are.
    fn overlay_proofs(&self, marks: &mut HashMap<usize, SpecMark>) {
        let p = &self.proofs;
        if p.obligations.is_empty() {
            return;
        }
        let plan = &self.spec_plan;
        let mut by_line: HashMap<usize, Vec<usize>> = HashMap::new();
        for (i, ob) in p.obligations.iter().enumerate() {
            by_line
                .entry(ob.spec_line.unwrap_or(ob.at_line))
                .or_default()
                .push(i);
        }
        let mut at_labels: Vec<(usize, String)> = vec![];
        for (line, idxs) in by_line {
            let m = marks.entry(line).or_default();
            let refuted = idxs.iter().find_map(|&i| match p.verdicts.get(i) {
                Some(Some(crate::vc::Verdict::Refuted(model))) => Some((i, model)),
                _ => None,
            });
            if let Some((i, model)) = refuted {
                let ob = &p.obligations[i];
                m.proof = ProofMark::Refuted;
                if m.failed.is_none() {
                    m.failed = Some(crate::prover::refuted_text(
                        plan,
                        ob,
                        model,
                        self.shown_line_number(ob.at_line),
                    ));
                }
                if ob.at_line != line {
                    at_labels.push((
                        ob.at_line,
                        format!("\u{2696} {}", crate::prover::refuted_phrase(ob)),
                    ));
                }
            } else if idxs
                .iter()
                .any(|&i| !matches!(p.verdicts.get(i), Some(Some(_))))
            {
                m.proof = ProofMark::Pending;
            } else if let Some(why) = idxs.iter().find_map(|&i| match p.verdicts.get(i) {
                Some(Some(crate::vc::Verdict::Unknown(w))) => Some(w.clone()),
                _ => None,
            }) {
                m.proof = ProofMark::Unknown(format!("not proven: {why}"));
            } else {
                m.proof = ProofMark::Proven;
            }
        }
        for (line, label) in at_labels {
            let m = marks.entry(line).or_default();
            if m.failed.is_none() {
                m.failed = Some(label);
                m.proof = ProofMark::Refuted;
            }
        }
    }

    // The number the gutter shows for a line (blank and comment lines are not numbered).
    fn shown_line_number(&self, idx: usize) -> usize {
        (0..=idx.min(self.len().saturating_sub(1)))
            .filter(|&i| !matches!(self.info(i).kind, LineKind::Empty))
            .count()
    }

    // The proofs, in a line of the witness track (None: nothing to say).
    fn proof_status(&self) -> Option<(crate::witness_track::TrackState, String, String)> {
        use crate::witness_track::TrackState;
        let p = &self.proofs;
        let n = p.obligations.len();
        if n == 0 {
            return None;
        }
        let done = p.verdicts.iter().filter(|v| v.is_some()).count();
        let count = |f: &dyn Fn(&crate::vc::Verdict) -> bool| {
            p.verdicts.iter().flatten().filter(|v| f(v)).count()
        };
        let proven = count(&|v| matches!(v, crate::vc::Verdict::Proven));
        let refuted = count(&|v| matches!(v, crate::vc::Verdict::Refuted(_)));
        let unknown = count(&|v| matches!(v, crate::vc::Verdict::Unknown(_)));
        let plural = |k: usize, w: &str| format!("{k} {w}{}", if k == 1 { "" } else { "s" });
        let timing = match (p.first_at, p.finished_at) {
            (Some(first), Some(end)) => format!(
                " \u{b7} solver loaded in {:.0} ms \u{b7} {n} obligations generated in {:.0} ms; {} queries; first verdict after {:.0} ms, all after {:.0} ms",
                crate::prover::z3_load_ms(),
                p.generate_ms,
                p.queries,
                first - p.started_at,
                end - p.started_at
            ),
            _ => String::new(),
        };
        let text = match solver_state() {
            SolverState::Failed(why) if done < n => format!(
                "{why} \u{b7} {} not yet proven (checked on runs only)",
                plural(n - done, "obligation")
            ),
            SolverState::Loading | SolverState::Idle if done < n => {
                format!(
                    "loading the solver\u{2026} {} to prove",
                    plural(n - done, "obligation")
                )
            }
            _ if done < n => format!("proving\u{2026} {done} of {}", plural(n, "obligation")),
            _ if proven == n => format!("all {} proven", plural(n, "obligation")),
            _ if refuted > 0 => {
                let (i, m) = self.static_witness()?;
                let ob = &p.obligations[i];
                let state = crate::prover::state_text(&self.spec_plan, ob, m);
                let summary = format!(
                    "{proven} of {} proven, {refuted} refuted, {unknown} not decided",
                    n
                );
                return Some(if self.static_replay(i).is_some() {
                    (
                        TrackState::NotReplayed,
                        format!(
                            "\u{2696} the spec allows {state}, and then {} \u{b7} not replayed \u{2014} click to replay",
                            crate::prover::refuted_where(ob, self.shown_line_number(ob.at_line))
                        ),
                        format!(
                            "{summary}. A state the solver found; a run may never reach it.{timing}"
                        ),
                    )
                } else {
                    (
                        TrackState::NotReplayed,
                        format!(
                            "\u{2696} at the loop head the spec allows {state}, and then {} \u{b7} a mid-run state, not replayable",
                            crate::prover::refuted_where(ob, self.shown_line_number(ob.at_line))
                        ),
                        format!(
                            "{summary}. A state the solver found; a run may never reach it.{timing}"
                        ),
                    )
                });
            }
            _ => {
                let mut parts = vec![format!("{proven} proven")];
                if refuted > 0 {
                    parts.push(format!("{refuted} refuted"));
                }
                if unknown > 0 {
                    parts.push(format!("{unknown} not decided"));
                }
                format!(
                    "{} \u{b7} {}",
                    plural(n, "obligation"),
                    parts.join(" \u{b7} ")
                )
            }
        };
        Some((
            TrackState::Note,
            text,
            format!("Z3 5.3.1 (WebAssembly, in a worker){timing}"),
        ))
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
        self.replay = None; // an edit returns to the user's own run
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
        match self.on_change() {
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

        self.show_autocomplete()?;

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
        // repair syntax
        fix_syntax(self);
        let lines = LineSnapshot((0..self.len()).map(|i| self.info(i).clone()).collect());

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

        // specifications: where each predicate is checked (and what is wrong with them)
        let plan = build_plan(self, &validized, &types);
        for (line, msg) in &plan.errors {
            if self.line(*line).info().invalid.is_none() {
                self.line_mut(*line).set_invalid(Some(msg.clone()));
            }
        }
        self.refined_slots = refined_slots(&plan, &validized, &types, &self.slot_connections);
        self.spec_plan = Rc::new(plan);
        self.request_proofs(lines, wasm_bin.clone());

        self.update_displayed_types(&validized, &types)?;

        // instrumentation
        let options = InstrumentOptions {
            record_stores: self.spec_plan.uses_memory,
            export_all: self.spec_plan.has_checks(),
        };
        let instrumented_binary = &validized.build_instrumented_binary_with(&types, &options)?;
        self.current_binary = Rc::new(instrumented_binary.clone());
        let instrumented_binary_hash = self.run_hash(instrumented_binary);
        let step_count = RUN_LOG.with(|r| r.step_count());
        if self.previous_instrumented_binary_hash != instrumented_binary_hash {
            self.version += 1;
            self.execute(instrumented_binary, self.version);
            self.previous_instrumented_binary_hash = instrumented_binary_hash;
        } else if step_count > 0 {
            // same binary (e.g. only a spec changed): re-evaluate the checks on the same run
            self.recheck_specs();
            self.update_live_info(step_count, None, false);
        } else {
            self.animations.arrow = self.image_mut().set_arrow_location(false, None);
        }

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
        // (slot, drawn as an input) pairs to draw as refined number lines
        let refined_set: HashSet<(usize, bool)> = self
            .refined_slots
            .iter()
            .map(|r| (r.slot, r.is_input))
            .collect();

        // set types of globals
        for (global, global_type) in zip_eq(&validized.globals, &types.globals) {
            tagged_types.insert(
                global.position_id,
                FractionInfo {
                    extra: 0,
                    line_no: global.line_idx,
                    indent: 0,
                    ty: AnnotatedOperatorType {
                        inputs: vec![],
                        outputs: vec![SlotInfo {
                            slot: types.slots[global_type.usize()].clone(),
                            used: true,
                            refined: false,
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
                        refined: refined_set.contains(&(x.usize(), true)),
                    })
                    .collect();
                tagged_types.insert(
                    func.positions.0,
                    FractionInfo {
                        extra: 0,
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
                                    extra: 0,
                                    line_no: line_idx,
                                    indent,
                                    ty: AnnotatedOperatorType {
                                        inputs: vec![],
                                        outputs: local_slots
                                            .iter()
                                            .map(|x| SlotInfo {
                                                slot: types.slots[x.usize()].clone(),
                                                used: true,
                                                refined: refined_set.contains(&(x.usize(), false)),
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
                            extra: 0,
                            line_no: local_line_idx,
                            indent,
                            ty: AnnotatedOperatorType {
                                inputs: vec![],
                                outputs: local_slots
                                    .iter()
                                    .map(|x| SlotInfo {
                                        slot: types.slots[x.usize()].clone(),
                                        used: true,
                                        refined: refined_set.contains(&(x.usize(), false)),
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
                        refined: refined_set.contains(&(x.usize(), true)),
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
                        refined: refined_set.contains(&(x.usize(), false)),
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
                            extra: 0,
                            line_no: op.line_idx,
                            indent,
                            ty: AnnotatedOperatorType { inputs, outputs },
                        },
                    );
                }
            }
        }

        // rows with a number line are wider: their code shifts right to make room
        let mut line_extra: HashMap<usize, u16> = HashMap::new();
        for info in tagged_types.values_mut() {
            info.extra = refined_row_extra(&info.ty);
            if info.extra > 0 {
                let e = line_extra.entry(info.line_no).or_default();
                *e = (*e).max(info.extra);
            }
        }
        for idx in 0..self.len() {
            let extra = line_extra.get(&idx).copied().unwrap_or(0);
            if self.line(idx).extra_px() != extra {
                self.line_mut(idx).set_extra_px(extra);
            }
        }
        get_mut!(self.component, image).set_frame_extras(&line_extra);

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
            current_binary: Default::default(),
            replay: None,
            replay_seed: None,
            witness: Default::default(),
            witness_version: 0,
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
            spec_plan: Default::default(),
            spec_results: Default::default(),
            refined_slots: vec![],
            proofs: Default::default(),
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
        self.slider_mut()
            .inner_mut()
            .track_mut()
            .set_onmousedown(move |ev| {
                ev.prevent_default();
                e.borrow_mut().toggle_replay();
            });

        let e = self.holder();
        self.share_mut().set_onmousedown(move |ev| {
            ev.prevent_default();
            e.borrow_mut().share_link();
        });

        let e = self.holder();
        self.window
            .set_onhashchange(move || e.borrow_mut().load_from_location(false));

        self.load_from_location(true);

        let height = LINE_SPACING * self.text().len();
        self.image_mut()
            .set_attribute("height", &height.to_string());
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
        self.replay = None;
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

    // The step to show for `step=fail`: the first failed check, or else the final step
    // (where a trap, if any, is shown).
    fn first_failure_step(&self) -> Option<usize> {
        let count = RUN_LOG.with(|r| r.step_count());
        self.spec_results
            .first_failure_step()
            .or((count > 0).then(|| count - 1))
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
