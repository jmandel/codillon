//! The LLM protocol of vericoding mode (design 16 §7.3) and its recorded form, the scripted
//! session. The model never talks to the kernel: the editor builds each round's request from the
//! kernel's failing cups, applies the model's edits, and judges them (vericode.rs). The same
//! round driver replays a recorded session offline or runs a live one through a transport.

use super::kernel::check_module;
use super::out::Verdict;
use super::vericode::{Edit, Judgement, SessionStart, apply_edits, locked_ranges};
use serde_json::{Value, json};

pub const DEFAULT_MODEL: &str = "anthropic/claude-opus-5.5";
/// Output cap per round (within every preset's limit; DeepSeek V4.1 Flash allows 65.5K).
pub const MAX_TOKENS: u32 = 32_000;

/// The model presets of the settings: (key, label, OpenRouter id, prefer fastest throughput).
pub const PRESETS: [(&str, &str, &str, bool); 2] = [
    ("opus", "Claude Opus 5.5", DEFAULT_MODEL, false),
    (
        "deepseek-flash",
        "DeepSeek V4.1 Flash (fast)",
        "deepseek/deepseek-v4.1-flash-1017",
        true,
    ),
];

/// The model a live session asks: an OpenRouter id, and whether to route for throughput.
#[derive(Clone, Debug, PartialEq)]
pub struct ModelChoice {
    pub model: String,
    pub fast: bool,
}

impl Default for ModelChoice {
    fn default() -> Self {
        ModelChoice {
            model: DEFAULT_MODEL.into(),
            fast: false,
        }
    }
}
pub const ENDPOINT: &str = "https://openrouter.ai/api/v1/chat/completions";
pub const MAX_ROUNDS: u32 = 6;

pub const SYSTEM_PROMPT: &str = "You write the implementation and the proofs of a WebAssembly \
program in Refined Codillon v2 text syntax, one instruction per line. A deterministic kernel checks \
every proof obligation (a \"cup\"): division by zero, memory bounds, refinements on calls, \
local.set and results, loop entry and back-edge facts, and harness `unreachable` (goal False). \
Facts live in a lane: branch arms, block/loop fact clauses `(fact P)`, call results and `prove k` \
lines enter facts; `prove k` uses the top k lane facts as hypotheses and proves the next \
instruction's first unfed cup (linear integer arithmetic over i32/i64 with wraparound). \
`unfold $p args` enters a predicate's body as a fact; `lemma $l args` calls a lemma function \
(export \"lemma:...\"). A local.set makes facts about the old value stale; a store ends facts \
about memory. OWNERSHIP: the student owns every function header (except lemma headers), the \
bodies of predicates, measures, harnesses and $main, axioms, assume lines and declarations; \
these line ranges are listed in \"locked\" and must not change. You own function bodies and \
proof lines, and you may add lemma functions. You cannot use `assume`, add axioms, add imports \
or call functions that do not exist. A failed `prove` is reported with a counterexample. \
Answer with JSON only: {\"edits\": [{\"replace_lines\": [a, b], \"with\": [\"line\", ...]}], \
\"note\": \"...\"}. Line numbers refer to the module as sent; [a, b] is inclusive; [a, a-1] \
inserts before line a. Edits must not overlap.";

pub const RULES: &str = "R5 lookup: a cup is fed by a lane fact equal to its goal. R7 local.set: \
cup for a refined local; facts about the old value go stale. R10/R11 load/store: bounds cup; a \
store ends memory facts. R13 call: a cup per refined parameter; the result refinement enters the \
lane. R15 result: cup for the result refinement at function end. R16-R18 block/loop: fact clauses \
are cups at br and end (block) or at entry and back-edge (loop), and enter the lane inside. R19 \
br_if: the condition enters the taken edge, its negation the fall-through. R24/R25 div/rem: \
divisor nonzero; div_s not MIN/-1. R26 unreachable: cup False. R28 evaluation feeds cups on \
constants. R30 unfold: a predicate's body as a fact. R32 prove k: top k facts imply the next \
instruction's first unfed cup, or a failure with a countermodel. R33 lemma: a call to a lemma \
function; its fact parameters are cups. R34 assume: forbidden to you.";

/// The failing cups and line errors, as the request carries them (gradual mode, with lanes).
pub fn failing(lines: &[String]) -> (Vec<Value>, Vec<Value>) {
    let m = super::ast::Module::parse_lines(lines);
    let out = check_module(&m, true);
    let mut cups = vec![];
    let mut errs = vec![];
    for f in &out.funcs {
        for c in &f.cups {
            if matches!(c.verdict, Verdict::Proven)
                || (c.verdict == Verdict::Assumed
                    && c.assumptions.iter().all(|o| o.kind == "axiom"))
            {
                continue;
            }
            cups.push(json!({
                "line": c.line,
                "func": f.name,
                "goal": c.goal,
                "verdict": c.verdict.name(),
                "diag": c.diag,
                "lane": c.lane.iter().map(|(l, t)| json!({"line": l, "fact": t})).collect::<Vec<_>>(),
            }));
        }
        for (l, e) in &f.line_errors {
            errs.push(json!([l, e]));
        }
    }
    for (l, e) in &out.errors {
        errs.push(json!([l, e]));
    }
    (cups, errs)
}

/// One round's request (§7.3).
pub fn request(
    start: &SessionStart,
    lines: &[String],
    task: &str,
    round: u32,
    max_rounds: u32,
    last: Option<&Judgement>,
) -> Value {
    let module: Vec<String> = lines
        .iter()
        .enumerate()
        .map(|(i, l)| format!("{:>4}| {l}", i + 1))
        .collect();
    let (cups, errs) = failing(lines);
    let locked: Vec<Value> = locked_ranges(&start.owners(lines))
        .into_iter()
        .map(|(a, b)| json!([a, b]))
        .collect();
    let mut v = json!({
        "module": module.join("\n"),
        "locked": locked,
        "task": task,
        "cups": cups,
        "line_errors": errs,
        "rules": RULES,
        "round": round,
        "max_rounds": max_rounds,
    });
    if let Some(j) = last
        && !j.accepted
    {
        let rs: Vec<Value> = j
            .boundary
            .iter()
            .chain(&j.malformed)
            .chain(&j.strict)
            .map(|r| json!([r.line, r.msg]))
            .collect();
        v["last_round"] = json!({ "verdict": j.summary(), "reasons": rs });
    }
    v
}

/// The OpenRouter chat body for one round (with provider routing for throughput if asked).
pub fn chat_body(choice: &ModelChoice, req: &Value) -> Value {
    let mut b = json!({
        "model": choice.model,
        "temperature": 0,
        "max_tokens": MAX_TOKENS,
        "messages": [
            { "role": "system", "content": SYSTEM_PROMPT },
            { "role": "user", "content": req.to_string() },
        ],
    });
    if choice.fast {
        b["provider"] = json!({ "sort": "throughput" });
    }
    b
}

/// The assistant's text from an OpenRouter reply (or the API's error message).
pub fn reply_content(body: &str) -> Result<String, String> {
    let v: Value = serde_json::from_str(body).map_err(|e| format!("reply is not JSON: {e}"))?;
    if let Some(e) = v.get("error") {
        let msg = e.get("message").and_then(|m| m.as_str()).unwrap_or("error");
        return Err(format!("OpenRouter: {msg}"));
    }
    v["choices"][0]["message"]["content"]
        .as_str()
        .map(|s| s.to_string())
        .ok_or_else(|| "reply has no message content".into())
}

fn edits_of(v: &Value) -> Result<Vec<Edit>, String> {
    let arr = v["edits"].as_array().ok_or("no \"edits\" array")?;
    arr.iter()
        .map(|e| {
            let r = e["replace_lines"]
                .as_array()
                .ok_or("edit without replace_lines")?;
            let a = r
                .first()
                .and_then(|x| x.as_u64())
                .ok_or("bad replace_lines")? as u32;
            let b = r
                .get(1)
                .and_then(|x| x.as_u64())
                .ok_or("bad replace_lines")? as u32;
            let with = e["with"]
                .as_array()
                .ok_or("edit without with")?
                .iter()
                .map(|s| {
                    s.as_str()
                        .map(|s| s.to_string())
                        .ok_or("with: not a string")
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(Edit { a, b, with })
        })
        .collect()
}

/// The model's response: JSON (possibly fenced or with prose around it).
pub fn parse_response(text: &str) -> Result<(Vec<Edit>, String), String> {
    let (Some(a), Some(b)) = (text.find('{'), text.rfind('}')) else {
        return Err("the response holds no JSON object".into());
    };
    let v: Value = serde_json::from_str(&text[a..=b]).map_err(|e| format!("response JSON: {e}"))?;
    let note = v["note"].as_str().unwrap_or("").to_string();
    Ok((edits_of(&v)?, note))
}

/// What one round did.
#[derive(Clone, Debug)]
pub struct RoundOutcome {
    /// the edits are in the text (false: rolled back, or they could not be applied)
    pub applied: bool,
    pub judgement: Option<Judgement>,
    pub error: Option<String>,
    /// the text after the round
    pub lines: Vec<String>,
}

/// Apply a round's edits and judge them. A round that crosses the boundary (or does not parse)
/// is rolled back; one that is merely not strict-clean stays and runs in gradual mode.
pub fn play_round(start: &SessionStart, cur: &[String], edits: &[Edit]) -> RoundOutcome {
    let next = match apply_edits(cur, edits) {
        Ok(n) => n,
        Err(e) => {
            return RoundOutcome {
                applied: false,
                judgement: None,
                error: Some(e),
                lines: cur.to_vec(),
            };
        }
    };
    let j = start.judge(&next);
    let applied = !j.crossed();
    RoundOutcome {
        applied,
        lines: if applied { next } else { cur.to_vec() },
        judgement: Some(j),
        error: None,
    }
}

// ---------------- recorded sessions ----------------

#[derive(Clone, Debug)]
pub struct Turn {
    pub note: String,
    pub edits: Vec<Edit>,
    /// what the kernel said when the session was recorded: accepted | rejected | not-accepted
    pub expect: Option<String>,
}

#[derive(Clone, Debug)]
pub struct Script {
    pub title: String,
    pub example: String,
    pub task: String,
    pub start: Vec<String>,
    pub turns: Vec<Turn>,
}

pub fn parse_script(text: &str) -> Result<Script, String> {
    let v: Value = serde_json::from_str(text).map_err(|e| format!("session JSON: {e}"))?;
    let s = |k: &str| v[k].as_str().unwrap_or("").to_string();
    let start = v["start"]
        .as_array()
        .ok_or("session without start")?
        .iter()
        .map(|l| l.as_str().unwrap_or("").to_string())
        .collect();
    let turns = v["turns"]
        .as_array()
        .ok_or("session without turns")?
        .iter()
        .map(|t| {
            Ok(Turn {
                note: t["note"].as_str().unwrap_or("").to_string(),
                edits: edits_of(&t["response"])?,
                expect: t["expect"].as_str().map(|s| s.to_string()),
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(Script {
        title: s("title"),
        example: s("example"),
        task: s("task"),
        start,
        turns,
    })
}

/// The kind of verdict a round got, as recorded in a session's `expect`.
pub fn verdict_kind(o: &RoundOutcome) -> &'static str {
    match &o.judgement {
        None => "error",
        Some(j) if j.accepted => "accepted",
        Some(j) if j.crossed() => "rejected",
        Some(_) => "not-accepted",
    }
}

/// A recorded session in the format of public/examples/v2/sessions (any live session can be
/// saved and replayed).
pub fn script_json(s: &Script) -> Value {
    json!({
        "title": s.title,
        "example": s.example,
        "task": s.task,
        "start": s.start,
        "turns": s.turns.iter().map(|t| json!({
            "note": t.note,
            "expect": t.expect,
            "response": {
                "note": t.note,
                "edits": t.edits.iter().map(|e| json!({"replace_lines": [e.a, e.b], "with": e.with})).collect::<Vec<_>>(),
            },
        })).collect::<Vec<_>>(),
    })
}

/// A live session's state machine (the transport is the editor's fetch, or a mock in tests).
pub struct Live {
    pub start: SessionStart,
    pub lines: Vec<String>,
    pub task: String,
    pub round: u32,
    pub max_rounds: u32,
    pub last: Option<Judgement>,
    pub done: bool,
    pub turns: Vec<Turn>,
}

impl Live {
    pub fn new(lines: &[String], task: &str, max_rounds: u32) -> Live {
        Live {
            start: SessionStart::new(lines),
            lines: lines.to_vec(),
            task: task.to_string(),
            round: 0,
            max_rounds,
            last: None,
            done: false,
            turns: vec![],
        }
    }

    /// The next round's chat body, or None when the session is over.
    pub fn next_body(&mut self, choice: &ModelChoice) -> Option<Value> {
        if self.done || self.round >= self.max_rounds {
            self.done = true;
            return None;
        }
        self.round += 1;
        let req = request(
            &self.start,
            &self.lines,
            &self.task,
            self.round,
            self.max_rounds,
            self.last.as_ref(),
        );
        Some(chat_body(choice, &req))
    }

    /// Take the model's reply (the HTTP body) and play it as a round.
    pub fn on_reply(&mut self, body: &str) -> RoundOutcome {
        let parsed = reply_content(body).and_then(|c| parse_response(&c));
        let (edits, note) = match parsed {
            Ok(x) => x,
            Err(e) => {
                self.done = true;
                return RoundOutcome {
                    applied: false,
                    judgement: None,
                    error: Some(e),
                    lines: self.lines.clone(),
                };
            }
        };
        let o = play_round(&self.start, &self.lines, &edits);
        self.lines = o.lines.clone();
        self.turns.push(Turn {
            note,
            edits,
            expect: Some(verdict_kind(&o).into()),
        });
        if let Some(j) = &o.judgement {
            self.done = j.accepted;
            self.last = Some(j.clone());
        }
        o
    }
}
