//! Erasure of v2 text to plain WAT, line for line (design 16 §1.8).
//! A faithful port of `research/v2-examples/tools/erase.py`; the tests compare the two on every example.

use std::collections::HashSet;

const VALTYPES: [&str; 4] = ["i32", "i64", "f32", "f64"];
pub const PROOF_OPS: [&str; 4] = ["prove", "lemma", "unfold", "assume"];

fn split_comment_py(line: &str) -> (&str, &str) {
    match line.find(";;") {
        Some(i) => (&line[..i], &line[i..]),
        None => (line, ""),
    }
}

fn match_paren(s: &[char], i: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (j, c) in s.iter().enumerate().skip(i) {
        if *c == '(' {
            depth += 1;
        } else if *c == ')' {
            depth -= 1;
            if depth == 0 {
                return Some(j + 1);
            }
        }
    }
    None
}

/// Delete `(fact …)`, `(param $x (fact …))`, `(result (fact …))`; turn `(T | …)` into `T`.
pub fn erase_groups(code: &str) -> String {
    let cs: Vec<char> = code.chars().collect();
    erase_groups_chars(&cs)
}

fn erase_groups_chars(cs: &[char]) -> String {
    let mut out = String::new();
    let mut i = 0;
    while i < cs.len() {
        let c = cs[i];
        if c != '(' {
            out.push(c);
            i += 1;
            continue;
        }
        let Some(end) = match_paren(cs, i) else {
            out.push('(');
            out.push_str(&erase_groups_chars(&cs[i + 1..]));
            break;
        };
        let group: String = cs[i..end].iter().collect();
        let inner_full: String = cs[i + 1..end - 1].iter().collect();
        let inner = inner_full.trim();
        let toks: Vec<&str> = inner.split_whitespace().collect();
        if toks.first() == Some(&"fact") {
            i = end;
            continue;
        }
        if let Some(t0) = toks.first()
            && (*t0 == "param" || *t0 == "result")
        {
            let mut rest = inner[t0.len()..].trim().to_string();
            if rest.starts_with('$') {
                let parts: Vec<&str> = rest.splitn(2, char::is_whitespace).collect();
                rest = if parts.len() > 1 { parts[1].trim_start().to_string() } else { String::new() };
            }
            if rest.starts_with("(fact") {
                i = end;
                continue;
            }
        }
        if toks.len() >= 2 && VALTYPES.contains(&toks[0]) && toks[1].starts_with('|') {
            out.push_str(toks[0]);
            i = end;
            continue;
        }
        let _ = group;
        out.push('(');
        out.push_str(&erase_groups_chars(&cs[i + 1..end - 1]));
        out.push(')');
        i = end;
    }
    out
}

fn tidy(s: &str) -> String {
    let mut s = s.trim_end().to_string();
    while s.contains("  )") {
        s = s.replace("  )", " )");
    }
    s
}

fn with_comment(code: String, comment: &str) -> String {
    if comment.is_empty() { code } else { format!("{code} {comment}") }
}

/// Is this line a proof instruction by itself (no context needed)?
pub fn is_proof_op(stripped: &str) -> bool {
    stripped.split_whitespace().next().is_some_and(|t| PROOF_OPS.contains(&t))
}

/// Erase a whole v2 text, given as lines. The result has exactly as many lines.
pub fn erase_lines<S: AsRef<str>>(lines: &[S]) -> Vec<String> {
    let mut out = Vec::with_capacity(lines.len());
    let mut in_func = false;
    let mut lemma = false;
    let mut fact_locals: HashSet<String> = HashSet::new();
    for raw in lines {
        let line = raw.as_ref().trim_end_matches('\n');
        let (code, comment) = split_comment_py(line);
        let stripped = code.trim();
        let indent = &code[..code.len() - code.trim_start().len()];
        if stripped.starts_with("(func") {
            in_func = true;
            fact_locals.clear();
            lemma = code.contains("(export \"lemma:") || code.contains("(export \"axiom:");
            out.push(with_comment(tidy(&erase_groups(code)), comment));
            continue;
        }
        if in_func && stripped == ")" {
            in_func = false;
            lemma = false;
            out.push(line.to_string());
            continue;
        }
        if in_func && stripped.starts_with("(local") {
            let inner = stripped.trim_start_matches('(').trim_end_matches(')');
            let toks: Vec<&str> = inner.split_whitespace().collect();
            if toks.len() == 3 && toks[2] == "fact" {
                fact_locals.insert(toks[1].to_string());
                out.push(format!("{indent};;~ {}", line.trim()));
                continue;
            }
            out.push(with_comment(tidy(&erase_groups(code)), comment));
            continue;
        }
        if in_func && !stripped.is_empty() && !stripped.starts_with('(') {
            let toks: Vec<&str> = stripped.split_whitespace().collect();
            let is_proof = PROOF_OPS.contains(&toks[0])
                || (matches!(toks[0], "local.get" | "local.set" | "local.tee")
                    && toks.len() > 1
                    && fact_locals.contains(toks[1]));
            if lemma || is_proof {
                out.push(format!("{indent}nop ;;~ {}", line.trim()));
                continue;
            }
            out.push(with_comment(tidy(&erase_groups(code)), comment));
            continue;
        }
        if stripped.is_empty() {
            out.push(line.to_string());
            continue;
        }
        out.push(with_comment(tidy(&erase_groups(code)), comment));
    }
    out
}

/// Erase a whole text (lines separated by `\n`).
pub fn erase_text(text: &str) -> String {
    let mut lines: Vec<&str> = text.split('\n').collect();
    if lines.last() == Some(&"") {
        lines.pop();
    }
    let mut s = erase_lines(&lines).join("\n");
    s.push('\n');
    s
}
