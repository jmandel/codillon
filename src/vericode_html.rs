// The vericoding panel's markup: a narrow column of annotated text in Codillon's language
// (condensed sans labels, purple for proofs, darkred only for violations, dashed gray for what is
// merely unproven). Pure string building from the state; the editor installs it.

use super::vericode_ui::{SESSIONS, VcState, stored_key, stored_model};
use crate::proof_view::esc;
use crate::v2::adequacy::Fate;
use crate::v2::vericode::Owner;

fn act(a: &str, arg: &str, label: &str, class: &str) -> String {
    format!(
        "<button type=\"button\" class=\"vc-btn {class}\" data-act=\"{a}\" data-arg=\"{}\">{label}</button>",
        esc(arg)
    )
}

fn kind_class(kind: &str) -> &'static str {
    match kind {
        "accepted" => "vc-ok",
        "rejected" | "error" => "vc-bad",
        _ => "vc-open",
    }
}

pub fn panel(vc: &VcState, lines: &[String], strict: bool, disp: &dyn Fn(u32) -> u32) -> String {
    let rn = |t: &str| esc(&crate::proof_view::renumber(t, disp));
    let mut h = String::new();
    // ---- header: the mode and the boundary ----
    let owners = vc.start.owners(lines);
    let locked = owners.iter().filter(|o| **o == Owner::Student).count();
    let open = owners.iter().filter(|o| **o == Owner::Llm).count();
    h.push_str("<div class=\"vc-head\"><span class=\"vc-title\">vericoding</span>");
    h.push_str(&format!(
        "<span class=\"vc-seg\">{}{}</span>",
        act("strict", "0", "gradual", if strict { "" } else { "vc-on" }),
        act("strict", "1", "strict", if strict { "vc-on" } else { "" })
    ));
    h.push_str(&act("close", "", "×", "vc-x"));
    h.push_str("</div>");
    h.push_str(&format!(
        "<p class=\"vc-own\"><span class=\"vc-lockmark\"></span>{locked} spec lines locked (headers, predicates, harnesses, axioms) · \
<span class=\"vc-openmark\"></span>{open} lines for the implementation and its proofs. \
The kernel alone judges a submission: accepted only if every function it touched is VERIFIED (strict-clean).</p>"
    ));

    // ---- sessions ----
    h.push_str("<h3>session</h3>");
    match &vc.player {
        None if vc.live.is_none() => {
            h.push_str("<p class=\"vc-dim\">Replay a recorded LLM session through the real kernel (offline):</p><div class=\"vc-row\">");
            for (n, label) in SESSIONS {
                h.push_str(&act("load", n, label, "vc-link"));
            }
            h.push_str("</div>");
        }
        None => {
            let l = vc.live.as_ref().unwrap();
            h.push_str(&format!(
                "<p class=\"vc-dim\">live session · round {}/{}{}</p>",
                l.round,
                l.max_rounds,
                if vc.busy {
                    " · waiting for the model…"
                } else {
                    ""
                }
            ));
            if vc.busy {
                h.push_str(&act("stop", "", "stop after this round", "vc-link"));
            }
        }
        Some(p) => {
            h.push_str(&format!(
                "<p class=\"vc-task\"><b>{}</b><br>task: {}</p><div class=\"vc-row\">{}{}{}<span class=\"vc-dim\">turn {}/{}</span></div>",
                esc(&p.script.title),
                esc(&p.script.task),
                act("restart", "", "⏮ restart", ""),
                act("next", "", "▶ next turn", if p.next < p.script.turns.len() { "vc-primary" } else { "vc-off" }),
                act("all", "", "⏭ all", ""),
                p.next,
                p.script.turns.len()
            ));
        }
    }
    if let Some((kind, s)) = &vc.verdict {
        h.push_str(&format!(
            "<p class=\"vc-verdict {}\">{}</p>",
            kind_class(kind),
            rn(s)
        ));
    }
    if !vc.log.is_empty() {
        h.push_str("<ol class=\"vc-log\">");
        for (i, t) in vc.log.iter().enumerate().rev() {
            h.push_str(&format!(
                "<li><div class=\"vc-turn\"><span class=\"vc-n\">{}</span><span class=\"vc-who\">{}</span> {}</div>\
<div class=\"vc-edits\">{}</div><div class=\"vc-k {}\">kernel: {}{}</div>",
                i + 1,
                t.who,
                esc(&t.note),
                rn(&t.edits),
                kind_class(t.kind),
                if t.kind == "accepted" { "◆ " } else { "" },
                rn(&t.summary)
            ));
            if !t.reasons.is_empty() {
                h.push_str("<ul class=\"vc-reasons\">");
                for (l, m) in t.reasons.iter().take(5) {
                    h.push_str(&format!(
                        "<li><span class=\"vc-ln\">{}</span>{}</li>",
                        disp(*l),
                        rn(m)
                    ));
                }
                if t.reasons.len() > 5 {
                    h.push_str(&format!(
                        "<li class=\"vc-dim\">… {} more</li>",
                        t.reasons.len() - 5
                    ));
                }
                h.push_str("</ul>");
            }
            if !t.cups.is_empty() && t.kind != "rejected" {
                h.push_str(&format!(
                    "<details class=\"vc-cups\"{}><summary>failing cups sent back to the model</summary><ul>",
                    if i + 1 == vc.log.len() { " open" } else { "" }
                ));
                for (l, g, v, lane) in t.cups.iter().take(6) {
                    h.push_str(&format!(
                        "<li><span class=\"vc-ln\">{}</span>⟨{}⟩ <i>{}</i>{}</li>",
                        disp(*l),
                        esc(g),
                        esc(v),
                        if lane.is_empty() {
                            String::new()
                        } else {
                            format!(
                                "<div class=\"vc-lane\">lane: {}</div>",
                                esc(&lane.join(" · "))
                            )
                        }
                    ));
                }
                h.push_str("</ul></details>");
            }
            h.push_str("</li>");
        }
        h.push_str("</ol>");
    }

    // ---- adequacy ----
    let a = &vc.adequacy;
    h.push_str("<h3>adequacy <span class=\"vc-dim\">is the spec worth proving?</span></h3>");
    h.push_str("<ul class=\"vc-vac\">");
    for r in &a.vacuity {
        let (cls, text) = if r.vacuous {
            (
                "vc-bad",
                format!(
                    "VACUOUS: the kernel proves its precondition false; {}/{} inputs satisfy it. Every claim about it holds trivially.",
                    r.witnesses, r.tried
                ),
            )
        } else if r.witnesses == 0 {
            (
                "vc-warn",
                format!(
                    "probably vacuous: no input of {} satisfies its precondition",
                    r.tried
                ),
            )
        } else if r.unconstraining {
            (
                "vc-warn",
                "unconstraining: its result refinement holds for any value".to_string(),
            )
        } else if r.tried > 1 {
            (
                "",
                format!(
                    "precondition satisfiable ({}/{} inputs)",
                    r.witnesses, r.tried
                ),
            )
        } else {
            ("", "no precondition".to_string())
        };
        h.push_str(&format!(
            "<li class=\"{cls}\"><span class=\"vc-ln\">{}</span><b>{}</b>{} {}</li>",
            disp(r.header_line),
            esc(&r.func),
            if r.harness { " (harness)" } else { "" },
            esc(&text)
        ));
    }
    h.push_str(&format!(
        "</ul><p class=\"vc-dim\">vacuity by the kernel and {} evaluated inputs per function · {:.0} ms</p>",
        a.vacuity.iter().map(|r| r.tried).max().unwrap_or(0),
        a.vac_ms
    ));
    let done = a.fates.iter().filter(|f| f.is_some()).count();
    let killed = a
        .fates
        .iter()
        .filter(|f| matches!(f, Some(Fate::Killed(_))))
        .count();
    let surv: Vec<usize> = (0..a.fates.len())
        .filter(|i| a.fates[*i].as_ref().is_some_and(|f| f.survives()))
        .collect();
    let own = a
        .fates
        .iter()
        .filter(|f| matches!(f, Some(Fate::OwnOnly(_))))
        .count();
    let away = a
        .fates
        .iter()
        .filter(|f| matches!(f, Some(Fate::RunsAway(_))))
        .count();
    let proven = surv
        .iter()
        .filter(|i| matches!(a.fates[**i], Some(Fate::Survived { proven: true })))
        .count();
    if a.mutants.is_empty() {
        h.push_str("<p class=\"vc-dim\">no mutants: the implementation zone is empty</p>");
    } else {
        h.push_str(&format!(
            "<p class=\"vc-mut\">mutants {done}/{} · killed by the spec {killed} · <b>{} survive</b>{}{} · {:.0} ms{}</p>",
            a.mutants.len(),
            surv.len(),
            if proven > 0 || own > 0 {
                let mut v = vec![];
                if proven > 0 { v.push(format!("{proven} still proven")); }
                if own > 0 { v.push(format!("{own} caught only by the body's own invariants")); }
                format!(" ({})", v.join(", "))
            } else { String::new() },
            if away > 0 { format!(" · {away} run away") } else { String::new() },
            a.total_ms,
            if a.done { "" } else { " · running" }
        ));
        if a.done {
            let ops: Vec<String> = a
                .by_op
                .iter()
                .map(|(op, (n, k, ms))| {
                    format!("{op} {k}/{n} <span class=\"vc-dim\">{ms:.0} ms</span>")
                })
                .collect();
            h.push_str(&format!(
                "<p class=\"vc-ops\">killed by the spec, per operator: {}</p>",
                ops.join(" · ")
            ));
        }
        if !surv.is_empty() {
            h.push_str("<ul class=\"vc-surv\">");
            // the kernel still proves these: reported first (§7.2)
            let mut order = surv.clone();
            order.sort_by_key(|i| !matches!(a.fates[*i], Some(Fate::Survived { proven: true })));
            for i in order.iter().take(40) {
                let m = &a.mutants[*i];
                let still = matches!(a.fates[*i], Some(Fate::Survived { proven: true }));
                h.push_str(&format!(
                    "<li class=\"{}\" data-act=\"focus\" data-arg=\"{i}\"><span class=\"vc-ln\">{}</span>{} <code>{}</code> → <code>{}</code>{}</li>",
                    if vc.focus == Some(*i) { "vc-focus" } else { "" },
                    disp(m.line),
                    m.op,
                    esc(&m.from),
                    esc(&m.to),
                    if still {
                        " <span class=\"vc-still\">still proven</span>"
                    } else if matches!(a.fates[*i], Some(Fate::OwnOnly(_))) {
                        " <span class=\"vc-dim\">own invariant only</span>"
                    } else {
                        ""
                    }
                ));
            }
            if order.len() > 40 {
                h.push_str(&format!(
                    "<li class=\"vc-dim\">… {} more</li>",
                    order.len() - 40
                ));
            }
            h.push_str("</ul><p class=\"vc-dim\">A survivor is an equivalent mutant or a spec too weak to tell it apart.</p>");
        }
    }

    // ---- the optional live LLM ----
    h.push_str("<h3>LLM <span class=\"vc-dim\">optional</span></h3>");
    match stored_key() {
        None => h.push_str(&format!(
            "<p class=\"vc-dim\">No key: nothing is sent anywhere. To try a live session, paste your own OpenRouter key; it is kept in this browser's localStorage and sent only to openrouter.ai.</p>\
<div class=\"vc-form\"><input id=\"vc-key\" type=\"password\" placeholder=\"sk-or-…\" autocomplete=\"off\" spellcheck=\"false\">\
<input id=\"vc-model\" type=\"text\" value=\"{}\" spellcheck=\"false\">{}</div>",
            esc(&stored_model()),
            act("save-key", "", "save", "")
        )),
        Some(k) => {
            let tail: String = k.chars().rev().take(4).collect::<Vec<_>>().into_iter().rev().collect();
            h.push_str(&format!(
                "<p class=\"vc-dim\">key ••••{} (this browser only) {}</p><div class=\"vc-form\"><input id=\"vc-model\" type=\"text\" value=\"{}\" spellcheck=\"false\">{}</div><div class=\"vc-row\">{}</div>",
                esc(&tail),
                act("forget-key", "", "forget", "vc-link"),
                esc(&stored_model()),
                act("save-key", "", "set model", ""),
                act("ask", "", "Ask LLM to fill the body/proofs", if vc.busy { "vc-off" } else { "vc-primary" })
            ));
        }
    }
    if let Some(e) = &vc.llm_error {
        h.push_str(&format!("<p class=\"vc-verdict vc-bad\">{}</p>", esc(e)));
    }
    h
}
