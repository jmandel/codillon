//! Erasure of v2 text to plain WAT, line for line (design 16 §1.8).
//! Behaves like `research/v2-examples/tools/erase.py` (the tests compare the two on every example),
//! but reads lines with the parser's tokenizer ([`tokenize_spans`]), so strings, `;;` inside strings
//! and `(i32| $p)` are handled exactly as the parser handles them. Fact parameters are fact handles
//! (§1.5): `local.get/set/tee` of one erases to `nop`, like a fact local.

use super::sexpr::{S, Tok, read_line, split_comment, tokenize_spans};
use std::collections::HashSet;
use std::ops::Range;

const VALTYPES: [&str; 4] = ["i32", "i64", "f32", "f64"];
pub const PROOF_OPS: [&str; 4] = ["prove", "lemma", "unfold", "assume"];

type Toks = Vec<(Tok, Range<usize>)>;

fn atom(t: &Toks, i: usize, hi: usize) -> Option<&str> {
    match t.get(i) {
        Some((Tok::Atom(a), _)) if i < hi => Some(a),
        _ => None,
    }
}

/// Index of the token matching the `Open` at `i`, if it closes before `hi`.
fn matching(t: &Toks, i: usize, hi: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (j, (tok, _)) in t.iter().enumerate().take(hi).skip(i) {
        match tok {
            Tok::Open => depth += 1,
            Tok::Close => {
                depth -= 1;
                if depth == 0 {
                    return Some(j);
                }
            }
            _ => {}
        }
    }
    None
}

/// Is the group whose inner tokens are `lo..hi` erased entirely?
fn deleted_group(t: &Toks, lo: usize, hi: usize) -> bool {
    match atom(t, lo, hi) {
        Some("fact") => true,
        Some("param") | Some("result") => {
            let mut k = lo + 1;
            if atom(t, k, hi).is_some_and(|a| a.starts_with('$')) {
                k += 1;
            }
            k < hi && t[k].0 == Tok::Open && atom(t, k + 1, hi) == Some("fact")
        }
        _ => false,
    }
}

/// Erase tokens lo..hi of `code`, copying the text between tokens verbatim. Returns the text and
/// the source position reached.
fn erase_toks(
    code: &str,
    t: &Toks,
    lo: usize,
    hi: usize,
    mut pos: usize,
    out: &mut String,
) -> usize {
    let mut i = lo;
    while i < hi {
        let (tok, span) = &t[i];
        out.push_str(&code[pos..span.start]);
        if *tok != Tok::Open {
            out.push_str(&code[span.clone()]);
            pos = span.end;
            i += 1;
            continue;
        }
        let Some(j) = matching(t, i, hi) else {
            // unclosed group (a header whose `)` is on a later line): erase inside it, keep it open
            out.push('(');
            return erase_toks(code, t, i + 1, hi, span.end, out);
        };
        if deleted_group(t, i + 1, j) {
            pos = t[j].1.end;
            i = j + 1;
            continue;
        }
        if let Some(ty) = atom(t, i + 1, j)
            && VALTYPES.contains(&ty)
            && atom(t, i + 2, j) == Some("|")
        {
            out.push_str(ty);
            pos = t[j].1.end;
            i = j + 1;
            continue;
        }
        out.push('(');
        pos = erase_toks(code, t, i + 1, j, span.end, out);
        out.push_str(&code[pos..t[j].1.start]);
        out.push(')');
        pos = t[j].1.end;
        i = j + 1;
    }
    pos
}

/// Delete `(fact …)`, `(param $x (fact …))`, `(result (fact …))`; turn `(T | …)` into `T`.
pub fn erase_groups(code: &str) -> String {
    let Ok(t) = tokenize_spans(code) else {
        return code.to_string();
    };
    let mut out = String::new();
    let pos = erase_toks(code, &t, 0, t.len(), 0, &mut out);
    out.push_str(&code[pos..]);
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
    if comment.is_empty() {
        code
    } else {
        format!("{code} {comment}")
    }
}

/// Is this line a proof instruction by itself (no context needed)?
pub fn is_proof_op(stripped: &str) -> bool {
    stripped
        .split_whitespace()
        .next()
        .is_some_and(|t| PROOF_OPS.contains(&t))
}

/// Names of the fact parameters declared on a function header line.
pub fn fact_params(code: &str) -> Vec<String> {
    let Ok(r) = read_line(code) else {
        return vec![];
    };
    let items: Vec<&S> = r
        .open
        .iter()
        .flatten()
        .chain(r.items.iter().flat_map(|x| x.list().unwrap_or(&[])))
        .collect();
    items
        .into_iter()
        .filter(|x| x.head() == Some("param"))
        .filter_map(|x| {
            let l = x.list()?;
            let n = l.get(1)?.atom()?;
            (n.starts_with('$') && l.get(2)?.head() == Some("fact")).then(|| n.to_string())
        })
        .collect()
}

/// Erase a whole v2 text, given as lines. The result has exactly as many lines.
pub fn erase_lines<L: AsRef<str>>(lines: &[L]) -> Vec<String> {
    let mut out = Vec::with_capacity(lines.len());
    let mut in_func = false;
    let mut lemma = false;
    let mut fact_locals: HashSet<String> = HashSet::new();
    for raw in lines {
        let line = raw.as_ref().trim_end_matches('\n');
        let (code, comment) = split_comment(line);
        let stripped = code.trim();
        let indent = &code[..code.len() - code.trim_start().len()];
        if stripped.starts_with("(func") {
            in_func = true;
            fact_locals = fact_params(code).into_iter().collect();
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
            if let Ok(r) = read_line(code)
                && let [S::List(l)] = r.items.as_slice()
                && l.len() == 3
                && l[2].atom() == Some("fact")
                && let Some(n) = l[1].atom()
            {
                fact_locals.insert(n.to_string());
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

/// Context-free erasure of one line, as if it stood in an ordinary function body (comment
/// dropped). Lines whose erasure depends on context (lemma bodies, fact-handle get/set/tee) are
/// corrected by a whole-document pass ([`erase_lines`]).
pub fn erase_line(line: &str) -> String {
    let e = erase_lines(&["(func", line]);
    split_comment(&e[1]).0.trim_end().to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn fact_param_handles_erase_to_nop() {
        let src = "(func $f (param $x i32) (param $h (fact (i32.lt_u $x 8)))\n  local.get $h\n  prove 1\n  local.get $x\n  drop\n)";
        let e = erase_text(src);
        let l: Vec<&str> = e.lines().collect();
        assert_eq!(l[0], "(func $f (param $x i32)");
        assert_eq!(l[1], "  nop ;;~ local.get $h");
        assert_eq!(l[3], "  local.get $x");
    }
    #[test]
    fn shared_tokenizer_cases() {
        assert_eq!(erase_groups("(param $x (i32| $p))"), "(param $x i32)");
        assert_eq!(
            erase_groups("(func $f (export \"a;;(b\") (param $x (i32 | $p))"),
            "(func $f (export \"a;;(b\") (param $x i32)"
        );
        assert_eq!(split_comment("(export \"a;;b\") ;; c").1, ";; c");
    }
}
