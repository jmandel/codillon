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
    Refinement { param: u32 },
    ResultRefinement,
    /// R16/R18 exit fact (br or end); `label` is the frame depth from the function frame
    BlockFact { label: u32 },
    LoopEntry,
    BackEdge,
    FactParam { param: u32 },
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
    Lookup { fact: FactId, origin_line: u32 },
    /// `hyp_lines`: the lane-entry line of each hypothesis (top of lane first), parallel to `hyps`
    Prove { prove_line: u32, hyps: SmallVec<[FactId; 8]>, hyp_lines: SmallVec<[u32; 8]>, wraps_removed: SmallVec<[WrapNote; 4]> },
    Eval { steps: u32 },
    DeadCode { ended_at: u32 },
    Unfed,
}

impl Feed {
    pub fn by(&self) -> &'static str {
        match self {
            Feed::Lookup { .. } => "lookup",
            Feed::Prove { .. } => "prove",
            Feed::Eval { .. } => "eval",
            Feed::DeadCode { .. } => "dead",
            Feed::Unfed => "none",
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Witness {
    Eval { value: i64 },
    Run { func: FuncIdx, args: Vec<u64>, step: u32 },
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
        self.funcs.iter().find(|f| f.header_line <= line && line <= f.end_line)
    }
}
