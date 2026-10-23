// Runtime checking of refinement specifications.
//
// `build_plan` reads the spec lines and refined headers of a (valid) module and decides
// where each predicate is checked: at function entry (requires, param refinements, the
// initial value of refined locals), at function exit (ensures, result refinements), on
// arrival at a loop head (invariant, decreases), at `@assert`/`@assume` lines, and at each
// `local.set`/`local.tee` of a refined local. Misplaced annotations and unknown names are
// reported per line (shown as invalid lines).
//
// `check_run` replays Codillon's run log (the values recorded by the `codillon_debug`
// instrumentation) with a shadow call stack of params and locals, and evaluates each
// checkpoint host-side. A check that passed is only "held on this run"; nothing here
// proves anything.

use crate::{
    debug::{CallFrameOp, RunLog, WasmValue},
    spec::{
        self, Annotation, DeclKind, Define, Env, Expr, LineSpec, Val, explain_false, is_builtin,
        show_value,
    },
    syntax::{InstrKind, LineInfos, LineKind},
    utils::{TypedModule, ValidModule},
};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckKind {
    Requires,
    ParamRefinement,
    Ensures,
    ResultRefinement,
    LocalRefinement,
    Invariant,
    Decreases,
    Assert,
    Assume,
}

impl CheckKind {
    pub fn label(&self) -> &'static str {
        match self {
            CheckKind::Requires => "requires",
            CheckKind::ParamRefinement => "parameter refinement",
            CheckKind::Ensures => "ensures",
            CheckKind::ResultRefinement => "result refinement",
            CheckKind::LocalRefinement => "local refinement",
            CheckKind::Invariant => "invariant",
            CheckKind::Decreases => "decreases",
            CheckKind::Assert => "assert",
            CheckKind::Assume => "assume",
        }
    }
}

#[derive(Debug, Clone)]
pub struct Check {
    pub kind: CheckKind,
    pub spec_line: usize,
    pub expr: Expr,
    pub subject: Option<String>, // the refined name, for refinements
}

#[derive(Debug, Clone)]
pub struct VarInfo {
    pub name: Option<String>,
    pub slot: u32,
    pub width: u32, // 32 or 64; 0 for floats
}

#[derive(Debug, Clone, Default)]
pub struct LoopPlan {
    pub loop_line: usize,
    pub block_idx: usize,
    pub invariants: Vec<Check>,
    pub decreases: Option<Check>,
}

#[derive(Debug, Clone, Default)]
pub struct FuncPlan {
    pub name: Option<String>,
    pub lines: (usize, usize, usize),
    pub nparams: usize,
    pub vars: Vec<VarInfo>, // params, then locals
    pub results: Vec<(Option<String>, u32)>,
    pub entry_checks: Vec<Check>,
    pub exit_checks: Vec<Check>,
    pub local_checks: HashMap<usize, Vec<Check>>, // var index -> refinement checks
    pub loops: Vec<LoopPlan>,
    pub asserts: HashMap<usize, Vec<Check>>, // instruction line -> checks made on arrival
}

impl FuncPlan {
    pub fn display_name(&self) -> String {
        match &self.name {
            Some(n) => format!("${n}"),
            None => "this function".to_string(),
        }
    }
}

#[derive(Debug, Default)]
pub struct SpecPlan {
    pub defines: Vec<Define>,
    pub funcs: Vec<FuncPlan>,
    pub global_names: Vec<Option<String>>,
    pub global_slots: Vec<u32>,
    pub global_widths: Vec<u32>,
    pub errors: Vec<(usize, String)>, // line -> semantic problem
    pub notes: Vec<(usize, String)>,  // line -> status note (e.g. not checked yet)
    pub spec_lines: Vec<usize>,       // lines carrying checkable specs
    pub uses_memory: bool,            // some predicate reads memory: record stores
    store_ops: Vec<(u64, u32)>,       // (offset, width) of each store, in module order
    slot_owner: HashMap<u32, (usize, usize)>, // slot -> (func, var index)
    global_of_slot: HashMap<u32, usize>,
    call_output: HashMap<u32, (usize, usize)>, // slot -> (caller func, result position)
    loop_of_block: HashMap<usize, (usize, usize)>, // block idx -> (func, loop idx)
}

impl SpecPlan {
    pub fn has_checks(&self) -> bool {
        self.funcs.iter().any(|f| {
            !f.entry_checks.is_empty()
                || !f.exit_checks.is_empty()
                || !f.local_checks.is_empty()
                || !f.loops.is_empty()
                || !f.asserts.is_empty()
        })
    }
}

fn width_of(ty: &wasmparser::ValType) -> u32 {
    match ty {
        wasmparser::ValType::I32 => 32,
        wasmparser::ValType::I64 => 64,
        _ => 0,
    }
}

// Which `$names` a predicate may use at a given kind of checkpoint.
struct Scope<'a> {
    func: Option<&'a FuncPlan>,
    params: bool,
    locals: bool,
    results: bool,
    old: bool,
    globals: &'a [Option<String>],
    ghosts: &'a [String],
}

impl Scope<'_> {
    fn var_ok(&self, v: &str) -> Result<(), String> {
        if self.globals.iter().flatten().any(|g| g == v) || self.ghosts.iter().any(|g| g == v) {
            return Ok(());
        }
        if let Some(f) = self.func {
            for (i, var) in f.vars.iter().enumerate() {
                if var.name.as_deref() == Some(v) {
                    let is_param = i < f.nparams;
                    if (is_param && self.params) || (!is_param && self.locals) {
                        return Ok(());
                    }
                    return Err(if is_param {
                        format!("${v} is not in scope here")
                    } else {
                        format!("the local ${v} is not in scope here")
                    });
                }
            }
            if f.results.iter().any(|(n, _)| n.as_deref() == Some(v)) {
                return if self.results {
                    Ok(())
                } else {
                    Err(format!(
                        "the result ${v} is only known when the function returns"
                    ))
                };
            }
        }
        Err(format!("unknown name ${v}"))
    }
}

fn check_names(
    e: &Expr,
    scope: &Scope,
    defines: &HashMap<String, usize>,
    bound: &mut Vec<String>,
) -> Result<(), String> {
    match e {
        Expr::Var(v) => {
            if bound.contains(v) {
                Ok(())
            } else {
                scope.var_ok(v)
            }
        }
        Expr::Name(n) => {
            if bound.contains(n) {
                Ok(())
            } else {
                match defines.get(n) {
                    Some(0) => Ok(()),
                    Some(_) => Err(format!("{n} needs arguments")),
                    None => Err(format!("unknown name {n}")),
                }
            }
        }
        Expr::Call(n, args) => {
            if n == "old" && !scope.old {
                return Err("old(…) is only meaningful after entry".to_string());
            }
            let arity = if is_builtin(n) {
                Some(match n.as_str() {
                    "min" | "max" | "remove" => 2,
                    _ if n.starts_with("i32.") => 2,
                    _ => 1,
                })
            } else {
                defines.get(n).copied()
            };
            match arity {
                None => return Err(format!("unknown function {n}")),
                Some(k) if k != args.len() => {
                    return Err(format!("{n} takes {k} argument(s)"));
                }
                _ => {}
            }
            for a in args {
                check_names(a, scope, defines, bound)?;
            }
            Ok(())
        }
        Expr::Quant(_, x, dom, body) => {
            match dom {
                spec::Domain::Range(lo, hi) => {
                    check_names(lo, scope, defines, bound)?;
                    check_names(hi, scope, defines, bound)?;
                }
                spec::Domain::MapKeys(m) => check_names(m, scope, defines, bound)?,
            }
            bound.push(x.clone());
            let r = check_names(body, scope, defines, bound);
            bound.pop();
            r
        }
        _ => {
            for c in children(e) {
                check_names(c, scope, defines, bound)?;
            }
            Ok(())
        }
    }
}

fn children(e: &Expr) -> Vec<&Expr> {
    match e {
        Expr::Int(_) | Expr::Bool(_) | Expr::Var(_) | Expr::Name(_) | Expr::MapEmpty => vec![],
        Expr::Neg(a) | Expr::Not(a) => vec![a],
        Expr::Bin(_, a, b) | Expr::Index(a, b) | Expr::InMap(a, b) => vec![a, b],
        Expr::Chain(es, _) | Expr::Call(_, es) => es.iter().collect(),
        Expr::Ite(a, b, c) | Expr::Update(a, b, c) => vec![a, b, c],
        Expr::Quant(_, _, dom, body) => {
            let mut v: Vec<&Expr> = match dom {
                spec::Domain::Range(lo, hi) => vec![lo, hi],
                spec::Domain::MapKeys(m) => vec![m],
            };
            v.push(body);
            v
        }
        Expr::InSet(a, es) => std::iter::once(&**a).chain(es.iter()).collect(),
    }
}

/// Decide what to check where. `lines` must be the same lines the module was built from.
pub fn build_plan(lines: &impl LineInfos, module: &ValidModule, types: &TypedModule) -> SpecPlan {
    let mut plan = SpecPlan::default();

    // globals
    for (g, global) in module.globals.iter().enumerate() {
        let name = lines
            .info(global.line_idx)
            .symbols
            .defined_global()
            .map(String::from);
        plan.global_names.push(name);
        let slot = types.globals[g].usize() as u32;
        plan.global_slots.push(slot);
        plan.global_widths.push(
            types.slots[slot as usize]
                .ty()
                .map(|t| width_of(&t))
                .unwrap_or(0),
        );
        plan.global_of_slot.insert(slot, g);
    }

    // collect annotations, defines and ghosts
    let mut ghosts: Vec<String> = vec![];
    let mut annotations: Vec<(usize, &Annotation)> = vec![];
    for line in 0..lines.len() {
        let info = lines.info(line);
        if info.kind != LineKind::Spec {
            continue;
        }
        if let Some(LineSpec::Annotation(a)) = info.spec.as_deref() {
            match a {
                Annotation::Define(ds) => {
                    for d in ds {
                        if plan.defines.iter().any(|x| x.name == d.name) {
                            plan.errors
                                .push((line, format!("{} is already defined", d.name)));
                        } else {
                            plan.defines.push(d.clone());
                        }
                    }
                }
                Annotation::Ghost { name, .. } => ghosts.push(name.clone()),
                _ => {}
            }
            annotations.push((line, a));
        }
    }
    let define_arity: HashMap<String, usize> = plan
        .defines
        .iter()
        .map(|d| (d.name.clone(), d.params.len()))
        .collect();

    // check define bodies: their own parameters, globals, ghosts and other defines
    for (line, a) in &annotations {
        if let Annotation::Define(ds) = a {
            for d in ds {
                let scope = Scope {
                    func: None,
                    params: false,
                    locals: false,
                    results: false,
                    old: true,
                    globals: &plan.global_names,
                    ghosts: &ghosts,
                };
                let mut bound = d.params.clone();
                if let Err(e) = check_names(&d.body, &scope, &define_arity, &mut bound) {
                    plan.errors.push((*line, format!("in {}: {e}", d.name)));
                }
            }
        }
    }

    // call outputs (their values are the callee's results)
    for (f, (func, tys)) in module.functions.iter().zip(&types.funcs).enumerate() {
        for (op, ty) in func.operators.iter().zip(&tys.ops) {
            if op.inner.is_call() {
                for (pos, slot) in ty.outputs.iter().enumerate() {
                    plan.call_output.insert(slot.usize() as u32, (f, pos));
                }
            }
        }
    }

    // functions
    let block_of_pos: HashMap<u32, usize> = types
        .blocks
        .iter()
        .enumerate()
        .map(|(i, (pos, _, _))| (*pos, i))
        .collect();

    let mut claimed_lines: Vec<bool> = vec![false; lines.len()];

    for (f, (func, tys)) in module.functions.iter().zip(&types.funcs).enumerate() {
        let (start, first_op, end) = func.lines;
        let mut fp = FuncPlan {
            name: lines.info(start).symbols.defined_func().map(String::from),
            lines: func.lines,
            nparams: func.params.len(),
            ..Default::default()
        };

        // declarations from the header lines
        let mut param_decls = vec![];
        let mut result_decls = vec![];
        let mut local_decls = vec![];
        for line in start..=first_op.min(end) {
            let info = lines.info(line);
            if !info.is_active() || !matches!(info.kind, LineKind::Other(_)) {
                continue;
            }
            if let Some(spec) = info.spec.as_deref() {
                for d in spec.decls() {
                    match d.kind {
                        DeclKind::Param => param_decls.push((line, d)),
                        DeclKind::Result => result_decls.push((line, d)),
                        DeclKind::Local => local_decls.push((line, d)),
                    }
                }
            }
        }
        let names_ok =
            param_decls.len() == func.params.len() && local_decls.len() == func.locals.len();
        for (i, slot) in tys.params.iter().enumerate() {
            fp.vars.push(VarInfo {
                name: if names_ok {
                    param_decls[i].1.name.clone()
                } else {
                    None
                },
                slot: slot.usize() as u32,
                width: width_of(&func.params[i].inner),
            });
        }
        for (i, slot) in tys.locals.iter().enumerate() {
            fp.vars.push(VarInfo {
                name: if names_ok {
                    local_decls[i].1.name.clone()
                } else {
                    None
                },
                slot: slot.usize() as u32,
                width: width_of(&func.locals[i].inner),
            });
        }
        let result_types = module.types[func.type_idx as usize].results().to_vec();
        for (i, ty) in result_types.iter().enumerate() {
            let name = if result_decls.len() == result_types.len() {
                result_decls[i].1.name.clone()
            } else {
                None
            };
            fp.results.push((name, width_of(ty)));
        }
        for (i, var) in fp.vars.iter().enumerate() {
            plan.slot_owner.insert(var.slot, (f, i));
        }

        // refinements in the header
        let mut pending: Vec<(Check, u8)> = vec![]; // (check, scope kind)
        const SC_ENTRY: u8 = 0;
        const SC_EXIT: u8 = 1;
        const SC_LOCAL: u8 = 2;
        if names_ok {
            for (line, d) in &param_decls {
                if let Some(r) = &d.refinement {
                    pending.push((
                        Check {
                            kind: CheckKind::ParamRefinement,
                            spec_line: *line,
                            expr: r.clone(),
                            subject: d.name.clone(),
                        },
                        SC_ENTRY,
                    ));
                }
            }
            for (line, d) in &local_decls {
                if let Some(r) = &d.refinement {
                    pending.push((
                        Check {
                            kind: CheckKind::LocalRefinement,
                            spec_line: *line,
                            expr: r.clone(),
                            subject: d.name.clone(),
                        },
                        SC_LOCAL,
                    ));
                }
            }
        } else if param_decls
            .iter()
            .chain(&local_decls)
            .any(|(_, d)| d.refinement.is_some())
        {
            plan.errors.push((
                start,
                "cannot match the declarations to the module".to_string(),
            ));
        }
        for (line, d) in &result_decls {
            if let Some(r) = &d.refinement {
                pending.push((
                    Check {
                        kind: CheckKind::ResultRefinement,
                        spec_line: *line,
                        expr: r.clone(),
                        subject: d.name.clone(),
                    },
                    SC_EXIT,
                ));
            }
        }

        // annotation lines in this function
        for &(line, a) in &annotations {
            if line < start || line > end {
                continue;
            }
            claimed_lines[line] = true;
            let mk = |kind, expr: &Expr| Check {
                kind,
                spec_line: line,
                expr: expr.clone(),
                subject: None,
            };
            match a {
                Annotation::Requires(e) | Annotation::Ensures(e) => {
                    if line > first_op {
                        plan.errors.push((
                            line,
                            format!("@{} belongs with the function header", a.keyword()),
                        ));
                        continue;
                    }
                    if let Annotation::Requires(_) = a {
                        pending.push((mk(CheckKind::Requires, e), SC_ENTRY));
                    } else {
                        pending.push((mk(CheckKind::Ensures, e), SC_EXIT));
                    }
                }
                Annotation::Invariant(e) | Annotation::Decreases(e) => {
                    // find the loop line above (skipping other spec, empty and comment lines)
                    let mut l = line;
                    let mut loop_line = None;
                    while l > start {
                        l -= 1;
                        let info = lines.info(l);
                        match &info.kind {
                            LineKind::Spec | LineKind::Empty | LineKind::Malformed(_) => continue,
                            LineKind::Instr(InstrKind::Loop) if info.is_active() => {
                                loop_line = Some(l)
                            }
                            _ => {}
                        }
                        break;
                    }
                    let Some(loop_line) = loop_line else {
                        plan.errors.push((
                            line,
                            format!("@{} belongs right after a loop line", a.keyword()),
                        ));
                        continue;
                    };
                    let Some(block_idx) = block_of_pos.get(&lines.info(loop_line).id).copied()
                    else {
                        plan.errors
                            .push((line, "this loop is not in the module".to_string()));
                        continue;
                    };
                    let idx = match fp.loops.iter().position(|lp| lp.loop_line == loop_line) {
                        Some(i) => i,
                        None => {
                            fp.loops.push(LoopPlan {
                                loop_line,
                                block_idx,
                                ..Default::default()
                            });
                            fp.loops.len() - 1
                        }
                    };
                    if let Annotation::Invariant(_) = a {
                        fp.loops[idx].invariants.push(mk(CheckKind::Invariant, e));
                    } else if fp.loops[idx].decreases.is_some() {
                        plan.errors
                            .push((line, "this loop already has a @decreases".to_string()));
                    } else {
                        fp.loops[idx].decreases = Some(mk(CheckKind::Decreases, e));
                    }
                }
                Annotation::Assert(e) | Annotation::Assume(e) => {
                    if line < first_op {
                        plan.errors.push((
                            line,
                            format!("@{} belongs in the function body", a.keyword()),
                        ));
                        continue;
                    }
                    // checked when control reaches the next instruction
                    let mut at = end;
                    for l in line + 1..end {
                        if lines.info(l).is_instr() {
                            at = l;
                            break;
                        }
                    }
                    let kind = if let Annotation::Assert(_) = a {
                        CheckKind::Assert
                    } else {
                        CheckKind::Assume
                    };
                    fp.asserts.entry(at).or_default().push(mk(kind, e));
                }
                Annotation::Ghost { .. } | Annotation::Set { .. } | Annotation::Run(_) => {
                    plan.notes
                        .push((line, "ghost state and @run come in phase 4".to_string()));
                }
                Annotation::Define(_) => {}
            }
        }

        // validate names in every predicate of this function
        let check_scope = |kind: u8| -> (bool, bool, bool, bool) {
            // (params, locals, results, old)
            match kind {
                SC_ENTRY => (true, false, false, false),
                SC_EXIT => (true, true, true, true),
                _ => (true, true, false, true),
            }
        };
        let mut accepted: Vec<(Check, u8)> = vec![];
        for (c, kind) in pending {
            let (params, locals, results, old) = check_scope(kind);
            let scope = Scope {
                func: Some(&fp),
                params,
                locals,
                results,
                old,
                globals: &plan.global_names,
                ghosts: &ghosts,
            };
            match check_names(&c.expr, &scope, &define_arity, &mut vec![]) {
                Ok(()) => accepted.push((c, kind)),
                Err(e) => plan.errors.push((c.spec_line, e)),
            }
        }
        let mut loop_errors = vec![];
        for lp in &fp.loops {
            for c in lp.invariants.iter().chain(lp.decreases.iter()) {
                let scope = Scope {
                    func: Some(&fp),
                    params: true,
                    locals: true,
                    results: false,
                    old: true,
                    globals: &plan.global_names,
                    ghosts: &ghosts,
                };
                if let Err(e) = check_names(&c.expr, &scope, &define_arity, &mut vec![]) {
                    loop_errors.push((c.spec_line, e));
                }
            }
        }
        let mut assert_errors = vec![];
        for cs in fp.asserts.values() {
            for c in cs {
                let scope = Scope {
                    func: Some(&fp),
                    params: true,
                    locals: true,
                    results: false,
                    old: true,
                    globals: &plan.global_names,
                    ghosts: &ghosts,
                };
                if let Err(e) = check_names(&c.expr, &scope, &define_arity, &mut vec![]) {
                    assert_errors.push((c.spec_line, e));
                }
            }
        }
        let bad: Vec<usize> = loop_errors
            .iter()
            .chain(&assert_errors)
            .map(|(l, _)| *l)
            .collect();
        for lp in fp.loops.iter_mut() {
            lp.invariants.retain(|c| !bad.contains(&c.spec_line));
            if lp
                .decreases
                .as_ref()
                .is_some_and(|c| bad.contains(&c.spec_line))
            {
                lp.decreases = None;
            }
        }
        for cs in fp.asserts.values_mut() {
            cs.retain(|c| !bad.contains(&c.spec_line));
        }
        fp.asserts.retain(|_, cs| !cs.is_empty());
        plan.errors.extend(loop_errors);
        plan.errors.extend(assert_errors);

        for (c, kind) in accepted {
            match kind {
                SC_ENTRY => fp.entry_checks.push(c),
                SC_EXIT => fp.exit_checks.push(c),
                _ => {
                    // a refined local: check at entry (its initial 0) and at every set
                    let var = fp
                        .vars
                        .iter()
                        .position(|v| v.name.is_some() && v.name == c.subject)
                        .expect("refined local");
                    fp.local_checks.entry(var).or_default().push(c.clone());
                }
            }
        }

        for c in fp
            .entry_checks
            .iter()
            .chain(&fp.exit_checks)
            .chain(fp.local_checks.values().flatten())
            .chain(
                fp.loops
                    .iter()
                    .flat_map(|l| l.invariants.iter().chain(&l.decreases)),
            )
            .chain(fp.asserts.values().flatten())
        {
            if !plan.spec_lines.contains(&c.spec_line) {
                plan.spec_lines.push(c.spec_line);
            }
        }
        for (i, lp) in fp.loops.iter().enumerate() {
            plan.loop_of_block.insert(lp.block_idx, (f, i));
        }
        plan.funcs.push(fp);
    }

    // annotations outside every function
    for &(line, a) in &annotations {
        if claimed_lines[line] {
            continue;
        }
        match a {
            Annotation::Define(_) | Annotation::Ghost { .. } => {}
            Annotation::Set { .. } | Annotation::Run(_) => {
                plan.errors
                    .push((line, format!("@{} belongs inside a function", a.keyword())));
            }
            _ => plan
                .errors
                .push((line, format!("@{} belongs inside a function", a.keyword()))),
        }
    }

    plan.spec_lines.sort();

    // does any predicate read memory? then the run must record stores
    let mut uses_memory = false;
    let mut look = |e: &Expr| {
        e.walk(&mut |x| {
            if matches!(x, Expr::Call(n, _) if n == "load" || n == "load8") {
                uses_memory = true;
            }
        })
    };
    for d in &plan.defines {
        look(&d.body);
    }
    for f in &plan.funcs {
        for c in f
            .entry_checks
            .iter()
            .chain(&f.exit_checks)
            .chain(f.local_checks.values().flatten())
            .chain(
                f.loops
                    .iter()
                    .flat_map(|l| l.invariants.iter().chain(&l.decreases)),
            )
            .chain(f.asserts.values().flatten())
        {
            look(&c.expr);
        }
    }
    plan.uses_memory = uses_memory && !module.memory.is_empty();
    if plan.uses_memory {
        plan.store_ops = crate::utils::store_ops(module);
    }
    plan
}

// ---------------------------------------------------------------------------------------
// Replaying a run

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    Held,
    Failed,
    Unknown, // could not be evaluated (e.g. needs ghost state or memory)
}

#[derive(Debug, Clone)]
pub struct CheckEvent {
    pub step: usize,      // the step at which the check is shown (arrow on `at_line`)
    pub spec_line: usize, // where the predicate is written
    pub at_line: usize,   // the instruction at which it was checked
    pub kind: CheckKind,
    pub outcome: Outcome,
    pub message: String,
    pub func: usize,
}

#[derive(Debug, Default)]
pub struct CheckResults {
    pub events: Vec<CheckEvent>, // in step order
    pub truncated: bool,
}

impl CheckResults {
    pub fn first_failure_step(&self) -> Option<usize> {
        self.events
            .iter()
            .filter(|e| e.outcome == Outcome::Failed)
            .map(|e| e.step)
            .min()
    }

    pub fn failure_steps(&self) -> Vec<usize> {
        let mut v: Vec<usize> = self
            .events
            .iter()
            .filter(|e| e.outcome == Outcome::Failed)
            .map(|e| e.step)
            .collect();
        v.sort();
        v.dedup();
        v
    }
}

const MAX_EVENTS: usize = 200_000;

struct Frame {
    func: usize,
    vals: Vec<Option<i128>>,
    entry_vals: Vec<Option<i128>>,
    entry_globals: Vec<Option<i128>>,
    measures: HashMap<usize, i128>, // loop idx -> measure at the previous arrival
    caller_line: Option<usize>,     // the call instruction (step before entry)
    entered: bool,                  // params and locals recorded
}

struct FrameEnv<'a> {
    plan: &'a SpecPlan,
    func: &'a FuncPlan,
    frame: &'a Frame,
    globals: &'a [Option<i128>],
    results: Option<&'a [Option<i128>]>,
    memory: &'a HashMap<u64, u8>,
}

impl Env for FrameEnv<'_> {
    fn var(&self, name: &str) -> Option<Val> {
        if let Some(results) = self.results {
            for (i, (n, _)) in self.func.results.iter().enumerate() {
                if n.as_deref() == Some(name) {
                    return results.get(i).copied().flatten().map(Val::Int);
                }
            }
        }
        for (i, v) in self.func.vars.iter().enumerate() {
            if v.name.as_deref() == Some(name) {
                return self.frame.vals[i].map(Val::Int);
            }
        }
        for (g, n) in self.plan.global_names.iter().enumerate() {
            if n.as_deref() == Some(name) {
                return self.globals[g].map(Val::Int);
            }
        }
        None
    }

    fn old_var(&self, name: &str) -> Option<Val> {
        for (i, v) in self.func.vars.iter().enumerate() {
            if v.name.as_deref() == Some(name) {
                return self.frame.entry_vals[i].map(Val::Int);
            }
        }
        for (g, n) in self.plan.global_names.iter().enumerate() {
            if n.as_deref() == Some(name) {
                return self.frame.entry_globals[g].map(Val::Int);
            }
        }
        None
    }

    fn width(&self, name: &str) -> u32 {
        for (n, w) in &self.func.results {
            if n.as_deref() == Some(name) {
                return *w;
            }
        }
        for v in &self.func.vars {
            if v.name.as_deref() == Some(name) {
                return v.width.max(32);
            }
        }
        32
    }

    fn load(&self, addr: i128, bytes: u32) -> Result<u64, spec::EvalError> {
        if !self.plan.uses_memory {
            return Err(spec::EvalError("memory is not recorded".to_string()));
        }
        if addr < 0 || addr > u32::MAX as i128 {
            return Err(spec::EvalError(format!("address {addr} is out of range")));
        }
        let mut v = 0u64;
        for i in 0..bytes as u64 {
            let b = *self.memory.get(&(addr as u64 + i)).unwrap_or(&0);
            v |= (b as u64) << (8 * i);
        }
        Ok(v)
    }

    fn define(&self, name: &str) -> Option<&Define> {
        self.plan.defines.iter().find(|d| d.name == name)
    }
}

fn bits_of(v: &WasmValue) -> u64 {
    match v {
        WasmValue::I32(x) => *x as u32 as u64,
        WasmValue::I64(x) => *x as u64,
        WasmValue::F32(x) => x.to_bits() as u64,
        WasmValue::F64(x) => x.to_bits(),
    }
}

fn int_of(v: &WasmValue) -> Option<i128> {
    match v {
        WasmValue::I32(x) => Some(*x as i128),
        WasmValue::I64(x) => Some(*x as i128),
        _ => None,
    }
}

struct Replay<'a> {
    plan: &'a SpecPlan,
    results: CheckResults,
    memory: HashMap<u64, u8>, // linear memory as written so far (it starts all zero)
}

impl Replay<'_> {
    #[allow(clippy::too_many_arguments)]
    fn evaluate(
        &mut self,
        check: &Check,
        func: usize,
        frame: &Frame,
        globals: &[Option<i128>],
        results: Option<&[Option<i128>]>,
        step: usize,
        at_line: usize,
        context: &str,
    ) {
        if self.results.events.len() >= MAX_EVENTS {
            self.results.truncated = true;
            return;
        }
        let fp = &self.plan.funcs[func];
        let env = FrameEnv {
            plan: self.plan,
            func: fp,
            frame,
            globals,
            results,
            memory: &self.memory,
        };
        let (outcome, message) = match spec::eval_bool(&check.expr, &env) {
            Ok(true) => (Outcome::Held, String::new()),
            Ok(false) => {
                let why = explain_false(&check.expr, &env);
                (
                    Outcome::Failed,
                    if context.is_empty() {
                        why
                    } else {
                        format!("{context}: {why}")
                    },
                )
            }
            Err(e) => (Outcome::Unknown, format!("not checked: {}", e.0)),
        };
        self.results.events.push(CheckEvent {
            step,
            spec_line: check.spec_line,
            at_line,
            kind: check.kind,
            outcome,
            message,
            func,
        });
    }

    #[allow(clippy::too_many_arguments)]
    fn evaluate_measure(
        &mut self,
        check: &Check,
        func: usize,
        loop_idx: usize,
        frame: &mut Frame,
        globals: &[Option<i128>],
        step: usize,
        at_line: usize,
        back_edge: bool,
    ) {
        if self.results.events.len() >= MAX_EVENTS {
            self.results.truncated = true;
            return;
        }
        let fp = &self.plan.funcs[func];
        let env = FrameEnv {
            plan: self.plan,
            func: fp,
            frame,
            globals,
            results: None,
            memory: &self.memory,
        };
        let value = spec::eval_int(&check.expr, &env);
        let previous = frame.measures.get(&loop_idx).copied();
        let (outcome, message) = match &value {
            Err(e) => (Outcome::Unknown, format!("not checked: {}", e.0)),
            Ok(m) => {
                let m = *m;
                let shown = show_value(&check.expr, &env);
                if m < 0 {
                    (
                        Outcome::Failed,
                        format!("{} : {shown} < 0 \u{2717}", check.expr),
                    )
                } else if back_edge && previous.is_some_and(|p| m >= p) {
                    (
                        Outcome::Failed,
                        format!(
                            "{} did not decrease : {} \u{2192} {m} \u{2717}",
                            check.expr,
                            previous.unwrap()
                        ),
                    )
                } else {
                    (Outcome::Held, String::new())
                }
            }
        };
        if let Ok(m) = value {
            frame.measures.insert(loop_idx, m);
        }
        self.results.events.push(CheckEvent {
            step,
            spec_line: check.spec_line,
            at_line,
            kind: check.kind,
            outcome,
            message,
            func,
        });
    }
}

/// Evaluate every checkpoint of `plan` along the run recorded in `log`.
pub fn check_run(plan: &SpecPlan, log: &RunLog) -> CheckResults {
    let mut replay = Replay {
        plan,
        results: CheckResults::default(),
        memory: HashMap::new(),
    };
    let mut store_addr: HashMap<u32, u64> = HashMap::new();
    if !plan.has_checks() {
        return replay.results;
    }
    let mut globals: Vec<Option<i128>> = vec![None; plan.global_names.len()];
    let mut frames: Vec<Frame> = vec![];
    let mut prev_line: Option<usize> = None;
    let step_count = log.step_count();

    for step in 0..step_count {
        let (line_word, assignments, ops) = log.with_step(step, |line, a, o| {
            (
                line,
                a.to_vec(),
                o.iter()
                    .map(|op| match op {
                        CallFrameOp::EnterFunc(f) => CallFrameOp::EnterFunc(*f),
                        CallFrameOp::BeforeCall => CallFrameOp::BeforeCall,
                        CallFrameOp::AfterCall(f) => CallFrameOp::AfterCall(*f),
                        CallFrameOp::BeforeTailCall => CallFrameOp::BeforeTailCall,
                        CallFrameOp::EnterBlock(b) => CallFrameOp::EnterBlock(*b),
                    })
                    .collect::<Vec<_>>(),
            )
        });
        let line = (line_word & 0x7fff_ffff) as usize;
        let below = line_word & 0x8000_0000 != 0;

        let mut entered: Option<usize> = None; // frame index entered at this step
        let mut returned: Option<Frame> = None;
        let mut arrivals: Vec<usize> = vec![]; // block indices
        for op in &ops {
            match op {
                CallFrameOp::EnterFunc(f) => {
                    let f = *f as usize;
                    let nvars = plan.funcs.get(f).map(|fp| fp.vars.len()).unwrap_or(0);
                    frames.push(Frame {
                        func: f,
                        vals: vec![None; nvars],
                        entry_vals: vec![],
                        entry_globals: vec![],
                        measures: HashMap::new(),
                        caller_line: if frames.is_empty() { None } else { prev_line },
                        entered: false,
                    });
                    entered = Some(frames.len() - 1);
                }
                CallFrameOp::AfterCall(_) => {
                    returned = frames.pop();
                }
                CallFrameOp::BeforeTailCall => {
                    // the frame is replaced by the callee; its exit is not observed
                    frames.pop();
                }
                CallFrameOp::EnterBlock(b) => arrivals.push(*b as usize),
                CallFrameOp::BeforeCall => {}
            }
        }

        let mut call_results: Vec<(usize, i128)> = vec![];
        let mut local_sets: Vec<usize> = vec![]; // var indices of the top frame
        for (slot, value) in &assignments {
            use crate::utils::{STORE_ADDR_TAG, STORE_SEQ_MASK, STORE_VALUE_TAG};
            if *slot & STORE_VALUE_TAG == STORE_VALUE_TAG {
                let seq = *slot & STORE_SEQ_MASK;
                if let (Some(addr), Some((_, width))) =
                    (store_addr.remove(&seq), plan.store_ops.get(seq as usize))
                {
                    let bits = bits_of(value);
                    for i in 0..*width as u64 {
                        replay.memory.insert(addr + i, (bits >> (8 * i)) as u8);
                    }
                }
                continue;
            }
            if *slot & STORE_VALUE_TAG == STORE_ADDR_TAG {
                let seq = *slot & STORE_SEQ_MASK;
                if let (WasmValue::I32(base), Some((offset, _))) =
                    (value, plan.store_ops.get(seq as usize))
                {
                    store_addr.insert(seq, *base as u32 as u64 + offset);
                }
                continue;
            }
            if let Some(&g) = plan.global_of_slot.get(slot) {
                globals[g] = int_of(value);
            } else if let Some(&(f, var)) = plan.slot_owner.get(slot) {
                if let Some(frame) = frames.iter_mut().rev().find(|fr| fr.func == f) {
                    frame.vals[var] = int_of(value);
                    if frame.entered {
                        local_sets.push(var);
                    }
                }
            } else if let Some(&(_, pos)) = plan.call_output.get(slot)
                && let Some(v) = int_of(value)
            {
                call_results.push((pos, v));
            }
        }

        // function entry: requires, param refinements, initial values of refined locals
        if let Some(idx) = entered {
            let (head, rest) = frames.split_at_mut(idx);
            let _ = head;
            let frame = &mut rest[0];
            frame.entered = true;
            frame.entry_vals = frame.vals.clone();
            frame.entry_globals = globals.clone();
            let f = frame.func;
            if let Some(fp) = plan.funcs.get(f) {
                let (show_step, at_line) = match frame.caller_line {
                    Some(call_line) if step > 0 => (step - 1, call_line),
                    _ => (step, fp.lines.0),
                };
                let context = if frame.caller_line.is_some() {
                    format!("at the call of {}", fp.display_name())
                } else {
                    String::new()
                };
                for c in &fp.entry_checks {
                    replay.evaluate(c, f, frame, &globals, None, show_step, at_line, &context);
                }
                let mut vars: Vec<&usize> = fp.local_checks.keys().collect();
                vars.sort();
                for var in vars {
                    for c in &fp.local_checks[var] {
                        replay.evaluate(c, f, frame, &globals, None, step, fp.lines.0, "initially");
                    }
                }
            }
        }

        // function exit: ensures and result refinements, with the call's outputs
        if let Some(frame) = returned
            && let Some(fp) = plan.funcs.get(frame.func)
            && !fp.exit_checks.is_empty()
        {
            let mut results: Vec<Option<i128>> = vec![None; fp.results.len()];
            for (pos, v) in &call_results {
                if *pos < results.len() {
                    results[*pos] = Some(*v);
                }
            }
            let show_step = step.saturating_sub(1);
            let at_line = prev_line.unwrap_or(fp.lines.2);
            for c in &fp.exit_checks {
                replay.evaluate(
                    c,
                    frame.func,
                    &frame,
                    &globals,
                    Some(&results),
                    show_step,
                    at_line,
                    "",
                );
            }
        }

        // a refined local was written by the previous instruction
        if let Some(frame) = frames.last()
            && let Some(fp) = plan.funcs.get(frame.func)
        {
            for var in local_sets {
                if let Some(cs) = fp.local_checks.get(&var) {
                    let at_line = prev_line.unwrap_or(line);
                    for c in cs {
                        replay.evaluate(
                            c,
                            frame.func,
                            frame,
                            &globals,
                            None,
                            step.saturating_sub(1),
                            at_line,
                            "",
                        );
                    }
                }
            }
        }

        // arrival at a loop head (on entry from the loop line, or by a branch back)
        for b in arrivals {
            if let Some(&(f, l)) = plan.loop_of_block.get(&b)
                && let Some(frame) = frames.last_mut()
                && frame.func == f
            {
                let lp = &plan.funcs[f].loops[l];
                let from = prev_line.unwrap_or(lp.loop_line);
                let back_edge = from != lp.loop_line;
                let context = if back_edge {
                    "after an iteration"
                } else {
                    "on entry"
                };
                let show_step = step.saturating_sub(1);
                for c in &lp.invariants {
                    replay.evaluate(c, f, frame, &globals, None, show_step, from, context);
                }
                if let Some(c) = &lp.decreases {
                    replay.evaluate_measure(c, f, l, frame, &globals, show_step, from, back_edge);
                }
            }
        }

        // @assert / @assume lines, on arrival at the instruction that follows them
        if !below
            && let Some(frame) = frames.last()
            && let Some(fp) = plan.funcs.get(frame.func)
            && let Some(cs) = fp.asserts.get(&line)
        {
            for c in cs {
                replay.evaluate(c, frame.func, frame, &globals, None, step, line, "");
            }
        }

        prev_line = Some(line);
    }

    replay.results.events.sort_by_key(|e| e.step);
    replay.results
}

/// Per-line summary of the checks up to (and including) a step of the run.
#[derive(Debug, Default, Clone, PartialEq)]
pub struct LineStatus {
    pub held: usize,
    pub unknown: usize,
    pub failed: Option<String>, // message of the most recent failure
    pub failed_here: bool,      // the failure is at exactly this step
}

pub fn status_at(
    results: &CheckResults,
    step: usize,
) -> (HashMap<usize, LineStatus>, HashMap<usize, String>) {
    let mut spec: HashMap<usize, LineStatus> = HashMap::new();
    let mut at: HashMap<usize, String> = HashMap::new(); // instruction line -> short label
    for e in results.events.iter().take_while(|e| e.step <= step) {
        let s = spec.entry(e.spec_line).or_default();
        match e.outcome {
            Outcome::Held => s.held += 1,
            Outcome::Unknown => s.unknown += 1,
            Outcome::Failed => {
                s.failed = Some(e.message.clone());
                s.failed_here = e.step == step;
                at.insert(e.at_line, e.kind.label().to_string());
            }
        }
    }
    (spec, at)
}

/// A slot whose value is drawn as a refined number line.
#[derive(Debug, Clone)]
pub struct RefinedSlot {
    pub slot: usize,
    pub func: usize,
    pub subject: String, // the name the predicate uses for this value
    pub pred: Expr,
    pub is_input: bool, // drawn as an input cup (else as an output)
    pub coord: crate::utils::Coordinate,
}

/// The slots to draw as refined number lines: refined params (header), refined locals
/// (declaration), refined results (the function's closing line), and the values read and
/// written by `local.get` / `local.set` / `local.tee` of refined params and locals.
pub fn refined_slots(
    plan: &SpecPlan,
    module: &ValidModule,
    types: &TypedModule,
    cx: &crate::utils::SlotConnections,
) -> Vec<RefinedSlot> {
    use crate::utils::{ConnectionSource, LocalAccess};
    let mut out = vec![];
    let i32_slot = |slot: usize| {
        matches!(
            types.slots.get(slot).and_then(|s| s.ty()),
            Some(wasmparser::ValType::I32)
        )
    };
    let read_at = |slot: usize| cx.connections.get(slot).and_then(|c| c.read.clone());
    let written_at = |slot: usize| match cx.connections.get(slot).map(|c| &c.written) {
        Some(ConnectionSource::Written(c)) => Some(c.clone()),
        _ => None,
    };
    for (f, (fp, (func, tys))) in plan
        .funcs
        .iter()
        .zip(module.functions.iter().zip(&types.funcs))
        .enumerate()
    {
        // the refinement of each var (params and locals), by var index
        let mut var_pred: HashMap<usize, (String, Expr)> = HashMap::new();
        for c in &fp.entry_checks {
            if c.kind == CheckKind::ParamRefinement
                && let Some(name) = &c.subject
                && let Some(i) = fp.vars.iter().position(|v| v.name.as_ref() == Some(name))
            {
                var_pred.insert(i, (name.clone(), c.expr.clone()));
            }
        }
        for (var, cs) in &fp.local_checks {
            if let Some(c) = cs.first()
                && let Some(name) = &c.subject
            {
                var_pred.insert(*var, (name.clone(), c.expr.clone()));
            }
        }
        let mut push = |slot: usize, is_input: bool, subject: &str, pred: &Expr| {
            let coord = if is_input {
                read_at(slot)
            } else {
                written_at(slot)
            };
            if let Some(coord) = coord
                && i32_slot(slot)
            {
                out.push(RefinedSlot {
                    slot,
                    func: f,
                    subject: subject.to_string(),
                    pred: pred.clone(),
                    is_input,
                    coord,
                });
            }
        };
        for (var, (name, pred)) in &var_pred {
            let slot = fp.vars[*var].slot as usize;
            push(slot, *var < fp.nparams, name, pred);
        }
        // results, at the function's end
        if let (Some(end_op), Some(end_ty)) = (func.operators.last(), tys.ops.last()) {
            let _ = end_op;
            for c in &fp.exit_checks {
                if c.kind == CheckKind::ResultRefinement
                    && let Some(name) = &c.subject
                    && let Some(j) = fp
                        .results
                        .iter()
                        .position(|(n, _)| n.as_ref() == Some(name))
                    && let Some(slot) = end_ty.inputs.get(j)
                {
                    push(slot.usize(), true, name, &c.expr);
                }
            }
        }
        // reads and writes of refined vars
        for (op, ty) in func.operators.iter().zip(&tys.ops) {
            let Some((idx, access)) = op.inner.local_access() else {
                continue;
            };
            let Some((name, pred)) = var_pred.get(&(idx as usize)) else {
                continue;
            };
            let is_param = (idx as usize) < fp.nparams;
            match access {
                LocalAccess::Get => {
                    if let Some(s) = ty.outputs.first() {
                        push(s.usize(), false, name, pred);
                    }
                }
                LocalAccess::Set | LocalAccess::Tee if !is_param => {
                    if let Some(s) = ty.inputs.first() {
                        push(s.usize(), true, name, pred);
                    }
                    if access == LocalAccess::Tee
                        && let Some(s) = ty.outputs.first()
                    {
                        push(s.usize(), false, name, pred);
                    }
                }
                _ => {}
            }
        }
    }
    out
}

/// Program values at the current step, for drawing refined slots.
pub struct SlotEnv<'a> {
    pub plan: &'a SpecPlan,
    pub func: usize,
    pub value_of_slot: &'a dyn Fn(usize) -> Option<i128>,
}

impl Env for SlotEnv<'_> {
    fn var(&self, name: &str) -> Option<Val> {
        let fp = self.plan.funcs.get(self.func)?;
        if let Some(v) = fp.vars.iter().find(|v| v.name.as_deref() == Some(name)) {
            return (self.value_of_slot)(v.slot as usize).map(Val::Int);
        }
        let g = self
            .plan
            .global_names
            .iter()
            .position(|n| n.as_deref() == Some(name))?;
        (self.value_of_slot)(self.plan.global_slots[g] as usize).map(Val::Int)
    }

    fn define(&self, name: &str) -> Option<&Define> {
        self.plan.defines.iter().find(|d| d.name == name)
    }
}
