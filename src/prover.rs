// The editor's prover: the obligations of vc.rs, decided by Z3 running in a Web Worker.
//
// The solver sits behind one narrow interface, `solve(smtlib) -> output`: SMT-LIB text in,
// Z3's text out. Everything else (verification conditions, encoding, the stages of a
// proof, reading models) is in Rust. Z3 is the single-threaded WebAssembly build
// (public/z3/), loaded the first time a program with specifications needs it, in a module
// worker: no SharedArrayBuffer and no cross-origin isolation, so nothing is asked of the
// page that embeds the editor. Queries are bounded by `(set-option :rlimit N)`.

use crate::{
    checker::SpecPlan,
    line::LineInfo,
    syntax::{LineInfos, LineInfosMut, SyntheticWasm},
    utils::RawModule,
    vc::Obligation,
};
use anyhow::Result;
use wasm_bindgen::prelude::*;

#[wasm_bindgen(inline_js = r#"
let worker = null, ready = null, state = 'idle', failure = '', nextId = 1, startedAt = 0, loadMs = -1;
const pending = new Map();
function fail(why) {
  state = 'failed';
  failure = why;
  for (const p of pending.values()) p.reject(new Error(why));
  pending.clear();
  if (worker) { try { worker.terminate(); } catch (e) {} }
  worker = null;
}
function start() {
  state = 'loading';
  startedAt = performance.now();
  ready = new Promise((resolve, reject) => {
    try {
      worker = new Worker(new URL('z3/z3w-worker.js', document.baseURI), { type: 'module' });
    } catch (e) {
      fail('the solver could not start: ' + e);
      reject(new Error(failure));
      return;
    }
    worker.onmessage = (e) => {
      const d = e.data || {};
      if ('ready' in d) {
        if (d.ready) { state = 'ready'; loadMs = performance.now() - startedAt; resolve(); }
        else { fail('the solver did not load: ' + d.error); reject(new Error(failure)); }
        return;
      }
      const p = pending.get(d.id);
      if (p) { pending.delete(d.id); p.resolve(String(d.output)); }
    };
    worker.onerror = (e) => {
      if (e && e.preventDefault) e.preventDefault();
      fail('the solver did not load' + (e && e.message ? ': ' + e.message : ''));
      reject(new Error(failure));
    };
  });
  ready.catch(() => {});
  return ready;
}
export function z3_solve(text) {
  if (state === 'failed') return Promise.reject(new Error(failure));
  if (!ready) start();
  return ready.then(() => new Promise((resolve, reject) => {
    const id = nextId++;
    pending.set(id, { resolve, reject });
    // a fresh context for each query ((reset) in the text does not forget recursive functions)
    worker.postMessage({ id: nextId++, reset: true });
    worker.postMessage({ id, smtlib: text });
  }));
}
export function z3_state() { return state; }
export function z3_load_ms() { return loadMs; }
export function z3_failure() { return failure; }
export function z3_now() { return performance.now(); }
export function z3_sleep(ms) { return new Promise((r) => setTimeout(r, ms)); }
"#)]
extern "C" {
    fn z3_solve(text: &str) -> js_sys::Promise;
    fn z3_state() -> String;
    /// How long the solver took to load (worker, module and instance), or -1.
    pub fn z3_load_ms() -> f64;
    fn z3_failure() -> String;
    pub fn z3_now() -> f64;
    fn z3_sleep(ms: f64) -> js_sys::Promise;
}

/// Z3's output for a query (each query runs in a fresh context).
pub async fn solve(smtlib: &str) -> Result<String, String> {
    match wasm_bindgen_futures::JsFuture::from(z3_solve(smtlib)).await {
        Ok(v) => Ok(v.as_string().unwrap_or_default()),
        Err(e) => Err(js_sys::Error::from(e).message().into()),
    }
}

pub async fn sleep(ms: f64) {
    let _ = wasm_bindgen_futures::JsFuture::from(z3_sleep(ms)).await;
}

#[derive(Debug, Clone, PartialEq)]
pub enum SolverState {
    Idle,
    Loading,
    Ready,
    Failed(String),
}

pub fn solver_state() -> SolverState {
    match z3_state().as_str() {
        "loading" => SolverState::Loading,
        "ready" => SolverState::Ready,
        "failed" => SolverState::Failed(z3_failure()),
        _ => SolverState::Idle,
    }
}

/// The lines of the program as they were when it was last edited, so that the
/// obligations can be generated later (after typing pauses) without the editor.
#[derive(Clone)]
pub struct LineSnapshot(pub Vec<LineInfo>);

impl LineInfos for LineSnapshot {
    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    #[allow(refining_impl_trait)]
    fn info(&self, index: usize) -> &LineInfo {
        &self.0[index]
    }
}

impl LineInfosMut for LineSnapshot {
    fn set_active_status(&mut self, index: usize, new_val: crate::line::Activity) {
        self.0[index].active = new_val
    }

    fn set_synthetic_before(&mut self, index: usize, synth: SyntheticWasm) {
        self.0[index].synthetic_before = synth
    }

    fn set_invalid(&mut self, index: usize, reason: Option<String>) {
        self.0[index].invalid = reason
    }

    fn set_runtime_error(&mut self, _index: usize, _msg: Option<String>) {}

    fn push(&mut self) {
        self.0.push(LineInfo::default())
    }
}

/// The obligations of a program, from its lines (before validity repair) and its binary.
pub fn obligations(
    lines: &LineSnapshot,
    wasm_bin: &[u8],
    plan: &SpecPlan,
) -> Result<Vec<Obligation>> {
    let mut lines = lines.clone();
    let raw = RawModule::new(&lines, wasm_bin)?;
    let validized = raw.fix_validity(&mut lines, wasm_bin)?;
    let types = validized.to_types_table(wasm_bin)?;
    Ok(crate::vc::generate(plan, &validized, &types))
}

// ---------------------------------------------------------------------------------------
// Words for verdicts

use crate::vc::{Cut, Model, ObKind, TrapKind};

/// What can go wrong, with where (for the witness track).
pub fn refuted_where(ob: &Obligation, at: usize) -> String {
    match ob.kind {
        ObKind::Requires => format!("the callee's precondition can fail at the call on line {at}"),
        ObKind::Ensures => format!("the postcondition can fail at the return on line {at}"),
        _ => format!("{} (line {at})", refuted_phrase(ob)),
    }
}

/// What can go wrong, for an obligation that was refuted (said at the instruction).
pub fn refuted_phrase(ob: &Obligation) -> String {
    match ob.kind {
        ObKind::Requires => "the callee's precondition can fail at this call".into(),
        ObKind::Ensures => "the postcondition can fail at this return".into(),
        ObKind::InvariantEntry => "the invariant can fail on entry to the loop".into(),
        ObKind::InvariantKept => "an iteration can break the invariant".into(),
        ObKind::MeasureEntry => "the measure can be negative on entry to the loop".into(),
        ObKind::Measure => "an iteration can fail to decrease the measure".into(),
        ObKind::Assert => "the assertion can fail".into(),
        ObKind::LocalRefinement => "the local can leave its refinement".into(),
        ObKind::NoTrap(TrapKind::DivideByZero) => "this can divide by zero".into(),
        ObKind::NoTrap(TrapKind::Overflow) => "this division can overflow".into(),
        ObKind::NoTrap(TrapKind::OutOfBounds) => "this access can be out of bounds".into(),
        ObKind::Unreachable => "this unreachable can be reached".into(),
    }
}

// The same, said on the spec line itself (which names what fails).
fn short_phrase(ob: &Obligation, at: usize) -> String {
    match ob.kind {
        ObKind::Requires => format!("fails at the call on line {at}"),
        ObKind::Ensures => format!("fails at the return on line {at}"),
        ObKind::InvariantEntry => "fails on entry".into(),
        ObKind::InvariantKept => "an iteration breaks it".into(),
        ObKind::MeasureEntry => "negative on entry".into(),
        ObKind::Measure => "an iteration does not decrease it".into(),
        ObKind::Assert | ObKind::LocalRefinement => "can fail".into(),
        _ => refuted_phrase(ob),
    }
}

fn map_text(m: &std::collections::BTreeMap<i128, i128>) -> String {
    if m.is_empty() {
        return "{}".into();
    }
    if m.len() > 3 {
        return format!("({} keys)", m.len());
    }
    let parts: Vec<String> = m.iter().map(|(k, v)| format!("{k} \u{21a6} {v}")).collect();
    format!("{{{}}}", parts.join(", "))
}

/// The state a model describes: a call at function entry, or values at a loop head.
pub fn state_text(plan: &SpecPlan, ob: &Obligation, m: &Model) -> String {
    let fname = plan
        .funcs
        .get(ob.func)
        .map(|f| f.display_name())
        .unwrap_or_default();
    let head = match ob.cut {
        Cut::Entry => {
            let args: Vec<String> = m.vars.iter().map(|(_, v)| v.to_string()).collect();
            format!("{fname}({})", args.join(", "))
        }
        Cut::LoopHead(_) => {
            let vars: Vec<String> = m.vars.iter().map(|(n, v)| format!("${n} = {v}")).collect();
            vars.join(", ")
        }
    };
    let mut parts: Vec<String> = vec![];
    for (_, n, v) in &m.globals {
        parts.push(format!("${n} = {v}"));
    }
    for (n, v) in &m.ghosts {
        // (at function entry, ghost locals are still at their initial value)
        let global = plan.ghost_globals.iter().any(|(g, _)| g == n);
        if global || ob.cut != Cut::Entry {
            parts.push(format!("${n} = {v}"));
        }
    }
    for (n, map) in &m.maps {
        parts.push(format!("${n} = {}", map_text(map)));
    }
    if !m.words.is_empty() {
        parts.push("memory as on the card".into());
    }
    match (head.is_empty(), parts.is_empty()) {
        (_, true) => head,
        (true, false) => parts.join(", "),
        (false, false) => format!("{head} with {}", parts.join(", ")),
    }
}

/// The commentary of a refuted obligation, on its spec line.
/// (`at` is the number the gutter shows for the obligation's instruction line.)
pub fn refuted_text(plan: &SpecPlan, ob: &Obligation, m: &Model, at: usize) -> String {
    format!(
        "\u{2696} {} from {} \u{b7} allowed by the spec",
        short_phrase(ob, at),
        state_text(plan, ob, m)
    )
}

// ---------------------------------------------------------------------------------------
// The state card: a model's memory as a strip of slots, and its ghost maps

/// A cell of the card: its text and its class.
pub type CardCell = (String, &'static str);

// The address a one-parameter define loads at, for an argument (if it is a single load).
fn load_address(plan: &SpecPlan, d: &crate::spec::Define, arg: i128) -> Option<i128> {
    use crate::spec::{Env, EvalError, Expr, Val};
    type EResult<T> = Result<T, EvalError>;
    struct Rec<'a>(&'a SpecPlan, std::cell::RefCell<Vec<(i128, u32)>>);
    impl Env for Rec<'_> {
        fn var(&self, _name: &str) -> Option<Val> {
            None
        }
        fn load(&self, addr: i128, bytes: u32) -> EResult<u64> {
            self.1.borrow_mut().push((addr, bytes));
            Ok(0)
        }
        fn define(&self, name: &str) -> Option<&crate::spec::Define> {
            self.0.defines.iter().find(|d| d.name == name)
        }
    }
    let env = Rec(plan, Default::default());
    crate::spec::eval(&Expr::Call(d.name.clone(), vec![Expr::Int(arg)]), &env).ok()?;
    match env.1.borrow().as_slice() {
        [(a, 4)] => Some(*a),
        _ => None,
    }
}

// Names for a field's values: the constants it is compared with (st($s) in {EMPTY, …}).
fn vocabulary(plan: &SpecPlan, field: &str) -> Vec<(i128, String)> {
    use crate::spec::Expr;
    let mut names = vec![];
    for d in &plan.defines {
        d.body.walk(&mut |e| {
            if let Expr::InSet(a, es) = e
                && matches!(a.as_ref(), Expr::Call(n, _) if n == field)
            {
                for x in es {
                    if let Expr::Name(n) = x
                        && !names.contains(n)
                    {
                        names.push(n.clone());
                    }
                }
            }
        });
    }
    names
        .into_iter()
        .filter_map(|n| {
            let d = plan
                .defines
                .iter()
                .find(|d| d.name == n && d.params.is_empty())?;
            match &d.body {
                crate::spec::Expr::Int(v) => Some((*v, n)),
                _ => None,
            }
        })
        .collect()
}

/// The card for a model: (columns, cells), or None if it shows no memory or maps.
pub fn state_card(plan: &SpecPlan, m: &Model) -> Option<(usize, Vec<CardCell>)> {
    // fields: one-parameter defines that load a word at base + stride * $s
    let mut fields: Vec<(String, i128, i128)> = vec![]; // name, base, stride
    for d in plan.defines.iter().filter(|d| d.params.len() == 1) {
        let (Some(a0), Some(a1)) = (load_address(plan, d, 0), load_address(plan, d, 1)) else {
            continue;
        };
        if a1 > a0 && m.words.contains_key(&(a0 as u32)) {
            fields.push((d.name.clone(), a0, a1 - a0));
        }
    }
    fields.sort_by_key(|f| f.1);
    let slots = fields
        .iter()
        .map(|(_, a0, stride)| {
            (0..64)
                .take_while(|s| m.words.contains_key(&((a0 + s * stride) as u32)))
                .count()
        })
        .max()
        .unwrap_or(0);
    let mut cells: Vec<CardCell> = vec![];
    let columns = slots + 1;
    if slots > 0 {
        cells.push(("slot".into(), "card-head"));
        for s in 0..slots {
            cells.push((s.to_string(), "card-head"));
        }
        for (name, a0, stride) in &fields {
            let vocab = vocabulary(plan, name);
            cells.push((format!("{name}($s)"), "card-field"));
            for s in 0..slots as i128 {
                match m.words.get(&((a0 + s * stride) as u32)) {
                    Some(v) => match vocab.iter().find(|(x, _)| x == v) {
                        Some((_, n)) => cells.push((n.clone(), "card-named")),
                        None => cells.push((v.to_string(), "card-value")),
                    },
                    None => cells.push(("\u{b7}".into(), "card-value")),
                }
            }
        }
    }
    let empty = std::collections::BTreeMap::new();
    for (n, ty) in &plan.ghost_globals {
        if *ty != crate::spec::GhostType::Map {
            continue;
        }
        let map = m.maps.get(n).unwrap_or(&empty);
        let entries: Vec<String> = map
            .iter()
            .map(|(k, v)| format!("{k} \u{21a6} {v}"))
            .collect();
        cells.push((format!("${n} = {{{}}}", entries.join(", ")), "card-map"));
    }
    if cells.is_empty() {
        return None;
    }
    Some((columns.max(1), cells))
}
