//! Per-cup and per-function kernel output (design 16 §4.3). This is the API the editor draws from.

use super::term::{Atom, Terms};
use smallvec::SmallVec;

pub type FactId = u32;
pub type FuncIdx = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Proven,
    Refuted,
    RuntimeChecked,
    Assumed,
}

impl Verdict {
    pub fn name(self) -> &'static str {
        match self {
            Verdict::Proven => "proven",
            Verdict::Refuted => "refuted",
            Verdict::RuntimeChecked => "runtime-checked",
            Verdict::Assumed => "assumed",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CupKind {
    Bounds,
    DivByZero,
    DivOverflow,
    /// R13 call argument (param index), R7 local.set/tee (local index), R9 global.set (global index)
    Refinement {
        param: u32,
    },
    ResultRefinement,
    /// R16/R18 exit fact (br or end); `label` is the frame depth from the function frame
    BlockFact {
        label: u32,
    },
    LoopEntry,
    BackEdge,
    FactParam {
        param: u32,
    },
    Measure,
    False,
    Conversion,
    CallIndirect,
    LocalInit,
}

impl CupKind {
    pub fn name(self) -> &'static str {
        match self {
            CupKind::Bounds => "Bounds",
            CupKind::DivByZero => "DivByZero",
            CupKind::DivOverflow => "DivOverflow",
            CupKind::Refinement { .. } => "Refinement",
            CupKind::ResultRefinement => "ResultRefinement",
            CupKind::BlockFact { .. } => "BlockFact",
            CupKind::LoopEntry => "LoopEntry",
            CupKind::BackEdge => "BackEdge",
            CupKind::FactParam { .. } => "FactParam",
            CupKind::Measure => "Measure",
            CupKind::False => "False",
            CupKind::Conversion => "Conversion",
            CupKind::CallIndirect => "CallIndirect",
            CupKind::LocalInit => "LocalInit",
        }
    }
}

/// A note on a wrap removed (or kept) by the interval pre-pass, shown on hover of a `prove`.
pub type WrapNote = String;

#[derive(Clone, Debug, PartialEq)]
pub enum Feed {
    Lookup {
        fact: FactId,
        origin_line: u32,
    },
    /// `hyp_lines`: the lane-entry line of each hypothesis (top of lane first), parallel to `hyps`
    Prove {
        prove_line: u32,
        hyps: SmallVec<[FactId; 8]>,
        hyp_lines: SmallVec<[u32; 8]>,
        wraps_removed: SmallVec<[WrapNote; 4]>,
    },
    /// R5a: fed automatically by the decision procedure from the relevant in-scope facts,
    /// minimized to the ones the proof uses (lane order, parallel `hyp_lines`)
    Auto {
        hyps: SmallVec<[FactId; 8]>,
        hyp_lines: SmallVec<[u32; 8]>,
        wraps_removed: SmallVec<[WrapNote; 4]>,
    },
    Eval {
        steps: u32,
    },
    DeadCode {
        ended_at: u32,
    },
    Unfed,
}

impl Feed {
    pub fn by(&self) -> &'static str {
        match self {
            Feed::Lookup { .. } => "lookup",
            Feed::Prove { .. } => "prove",
            Feed::Auto { .. } => "auto",
            Feed::Eval { .. } => "eval",
            Feed::DeadCode { .. } => "dead",
            Feed::Unfed => "none",
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Witness {
    Eval {
        value: i64,
    },
    Run {
        func: FuncIdx,
        args: Vec<u64>,
        step: u32,
    },
}

/// Where a fact came from: a line and what kind of rule produced it.
#[derive(Clone, Debug, PartialEq)]
pub struct Origin {
    pub line: u32,
    pub kind: &'static str,
}

#[derive(Clone, Debug)]
pub struct CupOut {
    pub line: u32,
    /// the value operand the cup sits beside (pop order, 0 = deepest); None = line-level
    pub operand: Option<u8>,
    pub kind: CupKind,
    /// rendered with program names
    pub goal: String,
    pub verdict: Verdict,
    pub feed: Feed,
    /// non-empty iff Assumed: the assume/axiom/unproven-lemma origins this derivation rests on
    pub assumptions: SmallVec<[Origin; 2]>,
    /// runtime-checked cup lines this derivation rests on (§4.1)
    pub depends_on_checks: SmallVec<[u32; 2]>,
    pub witness: Option<Witness>,
    pub diag: Option<String>,
    /// the cup's atom over this function's canonical ids (for runtime checks)
    pub atom: Atom,
    /// ghost or predicate code: never run, so never runtime-checked
    pub ghost: bool,
    /// for a taken-edge cup of br_if/br_table: the edge condition (the check runs only if it holds)
    pub guard: Option<Atom>,
    /// for an unfed cup: the lane snapshot where it sits (in-scope facts, top first, with birth lines)
    pub lane: Vec<(u32, String)>,
    /// for a cup fed by a `prove`: why the solver accepted it (editor only; see `check_module_with`)
    pub explain: Option<ProveExplain>,
    /// for an unfed cup: values, checked by concrete evaluation, under which its facts hold and
    /// its goal fails (never the solver's unchecked model)
    pub cex: Option<Cex>,
}

/// A counterexample the kernel checked by evaluating the cup's facts and goal (kernel/cex.rs).
#[derive(Clone, Debug, PartialEq)]
pub struct Cex {
    /// each free value (parameter, local version, call result, …) and its value, signed for
    /// display: `x = 1073741824`
    pub vals: Vec<(String, i128)>,
    /// every value is a parameter of the function: the values are an input it fails for
    pub inputs: bool,
    /// intermediate values that wrap under these values: `x·2 wraps to −2147483648`
    pub wraps: Vec<String>,
    /// one plain sentence on the wrap behind the failure: `x·2 wraps past 2³¹ when x ≥ 2³⁰`
    pub why: Option<String>,
}

impl Cex {
    /// `x = 1073741824, y = −1`
    pub fn vals_text(&self) -> String {
        self.vals
            .iter()
            .map(|(n, v)| format!("{n} = {}", signed_text(*v)))
            .collect::<Vec<_>>()
            .join(", ")
    }
}

/// An integer with a typographic minus.
pub fn signed_text(v: i128) -> String {
    if v < 0 {
        format!("−{}", v.unsigned_abs())
    } else {
        v.to_string()
    }
}

/// Why a `prove` succeeded, for the editor (design 16 §3.3: "shown on hover of the `prove`").
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ProveExplain {
    /// positions in `Feed::Prove::hyps` / `Feed::Auto::hyps` that the proof needs (a minimal subset)
    pub used: SmallVec<[u8; 8]>,
    /// the used hypotheses contradict each other: the goal holds ex falso, and the prove line
    /// can never run
    pub ex_falso: bool,
    /// at most three short lines: the case split, the bounds or parity argument, what is contradicted
    pub lines: Vec<String>,
    /// each hypothesis given, as a student reads it: a predicate fact with its meaning,
    /// `x is even (x&1 = 0)` (parallel to the feed's `hyps`)
    pub hyp_text: Vec<String>,
    /// the functions whose definitions the proof unfolded
    pub unfolded: Vec<String>,
}

/// Body lines the kernel shows can never run, because a branch condition is decided by the
/// solver (the fall-through of an always-taken `br_if`, an `if` arm whose entry fact is false).
/// Informational only: no verdict depends on it (see `reach.rs`).
#[derive(Clone, Debug, PartialEq)]
pub struct NeverRuns {
    /// first and last line of the region (inclusive)
    pub from: u32,
    pub to: u32,
    /// the branching line
    pub cause: u32,
    /// e.g. "br_if on line 13 always branches"
    pub why: String,
}

#[derive(Clone, Debug)]
pub struct ChipOut {
    pub line: u32,
    pub text: String,
    pub origin: &'static str,
    /// the line where a `local.set` or store makes this fact stale (R7, R11), if any
    pub frayed_at: Option<u32>,
}

/// How the instrumented program captures an opaque value when it is born (for runtime checks).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Capture {
    /// at function entry: the value of value-local (parameter) `i`
    Param(u32),
    /// right after the line's instruction: the value on top of the stack
    Top,
    /// right after the line's instruction: the value of value-local `i` (a φ at a join or loop head)
    Local(u32),
    /// right after the line's instruction: the value of global `i`
    Global(u32),
}

/// An opaque value (parameter, φ, load, impure call result, …) and where it is born.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Birth {
    pub term: u32,
    /// the line after whose instruction it is captured (the header line for entry captures)
    pub line: u32,
    pub how: Capture,
}

#[derive(Clone, Debug)]
pub struct FuncOut {
    pub name: String,
    pub header_line: u32,
    pub end_line: u32,
    /// strict-clean and all callees verified (§4.1)
    pub verified: bool,
    pub strict_clean: bool,
    pub cups: Vec<CupOut>,
    /// prove failures, predicate purity, stale-handle errors, …
    pub line_errors: Vec<(u32, String)>,
    pub chips: Vec<ChipOut>,
    /// the value numbering of this function's pass (cups' atoms refer to it)
    pub terms: Terms,
    /// canonical id of every value slot produced by a body line: (line, output id)
    pub slot_ids: Vec<(u32, u32)>,
    /// births of opaque values, in pass order
    pub births: Vec<Birth>,
    /// module function index
    pub func: u32,
    /// body lines control never reaches (R22)
    pub dead_lines: Vec<u32>,
    /// probed lines (`check_module_probing`) reached only with a contradictory context: the
    /// kernel proves False there, so every cup on them is discharged ex falso
    pub false_ctx_lines: Vec<u32>,
    /// regions a decided branch condition makes unreachable (editor only, `check_module_with`)
    pub never_runs: Vec<NeverRuns>,
}

#[derive(Clone, Debug, Default)]
pub struct ModuleOut {
    pub funcs: Vec<FuncOut>,
    /// syntax errors and module-level errors: (1-based line, message)
    pub errors: Vec<(u32, String)>,
}

impl ModuleOut {
    pub fn cups(&self) -> impl Iterator<Item = &CupOut> {
        self.funcs.iter().flat_map(|f| f.cups.iter())
    }
    /// The function containing a 1-based line.
    pub fn func_at(&self, line: u32) -> Option<&FuncOut> {
        self.funcs
            .iter()
            .find(|f| f.header_line <= line && line <= f.end_line)
    }
}
