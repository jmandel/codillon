//! Tokenizer and s-expression reader for one v2 line (design 16 §1.3).
//!
//! A line may be unbalanced: a function header opens `(func` and its `)` is on a later line.

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum S {
    Atom(String),
    Str(String),
    List(Vec<S>),
}

impl S {
    pub fn atom(&self) -> Option<&str> {
        match self {
            S::Atom(a) => Some(a),
            _ => None,
        }
    }
    pub fn list(&self) -> Option<&[S]> {
        match self {
            S::List(l) => Some(l),
            _ => None,
        }
    }
    /// The head atom of a list, e.g. `fact` for `(fact …)`.
    pub fn head(&self) -> Option<&str> {
        self.list().and_then(|l| l.first()).and_then(|h| h.atom())
    }
    pub fn render(&self) -> String {
        match self {
            S::Atom(a) => a.clone(),
            S::Str(s) => format!("\"{s}\""),
            S::List(l) => {
                let inner: Vec<String> = l.iter().map(|x| x.render()).collect();
                format!("({})", inner.join(" "))
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Open,
    Close,
    Atom(String),
    Str(String),
}

/// Split off a trailing `;;` comment (not inside a string).
pub fn split_comment(line: &str) -> (&str, &str) {
    let b = line.as_bytes();
    let mut in_str = false;
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'"' => in_str = !in_str,
            b'\\' if in_str => i += 1,
            b';' if !in_str && i + 1 < b.len() && b[i + 1] == b';' => return (&line[..i], &line[i..]),
            _ => {}
        }
        i += 1;
    }
    (line, "")
}

fn tokenize(code: &str) -> Result<Vec<Tok>, String> {
    let mut out = Vec::new();
    let cs: Vec<char> = code.chars().collect();
    let mut i = 0;
    while i < cs.len() {
        let c = cs[i];
        if c.is_whitespace() {
            i += 1;
        } else if c == '(' {
            // block comment `(; … ;)`
            if i + 1 < cs.len() && cs[i + 1] == ';' {
                let mut j = i + 2;
                while j + 1 < cs.len() && !(cs[j] == ';' && cs[j + 1] == ')') {
                    j += 1;
                }
                i = j + 2;
                continue;
            }
            out.push(Tok::Open);
            i += 1;
        } else if c == ')' {
            out.push(Tok::Close);
            i += 1;
        } else if c == '|' {
            out.push(Tok::Atom("|".into()));
            i += 1;
        } else if c == '"' {
            let mut s = String::new();
            let mut j = i + 1;
            while j < cs.len() && cs[j] != '"' {
                if cs[j] == '\\' && j + 1 < cs.len() {
                    s.push(cs[j]);
                    j += 1;
                }
                s.push(cs[j]);
                j += 1;
            }
            if j >= cs.len() {
                return Err("unterminated string".into());
            }
            out.push(Tok::Str(s));
            i = j + 1;
        } else {
            let mut j = i;
            while j < cs.len() && !cs[j].is_whitespace() && !matches!(cs[j], '(' | ')' | '"' | '|') {
                j += 1;
            }
            out.push(Tok::Atom(cs[i..j].iter().collect()));
            i = j;
        }
    }
    Ok(out)
}

/// Read a line into top-level items. `open` is the number of lists left unclosed at the end
/// (1 for a header line `(func …`); `extra_close` counts unmatched `)` (1 for a closing line).
pub struct LineItems {
    pub items: Vec<S>,
    pub open: Vec<Vec<S>>,
    pub extra_close: usize,
}

pub fn read_line(code: &str) -> Result<LineItems, String> {
    let toks = tokenize(code)?;
    let mut stack: Vec<Vec<S>> = Vec::new();
    let mut items = Vec::new();
    let mut extra_close = 0;
    for t in toks {
        match t {
            Tok::Open => stack.push(Vec::new()),
            Tok::Close => match stack.pop() {
                Some(l) => {
                    let s = S::List(l);
                    match stack.last_mut() {
                        Some(p) => p.push(s),
                        None => items.push(s),
                    }
                }
                None => extra_close += 1,
            },
            Tok::Atom(a) => match stack.last_mut() {
                Some(p) => p.push(S::Atom(a)),
                None => items.push(S::Atom(a)),
            },
            Tok::Str(a) => match stack.last_mut() {
                Some(p) => p.push(S::Str(a)),
                None => items.push(S::Str(a)),
            },
        }
    }
    Ok(LineItems { items, open: stack, extra_close })
}

/// Parse a WAT integer literal (decimal or hex, optional sign, `_` separators) to i128.
pub fn parse_int(s: &str) -> Option<i128> {
    let (neg, rest) = match s.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, s.strip_prefix('+').unwrap_or(s)),
    };
    let rest: String = rest.chars().filter(|c| *c != '_').collect();
    let v = if let Some(h) = rest.strip_prefix("0x") {
        i128::from_str_radix(h, 16).ok()?
    } else {
        if rest.is_empty() || !rest.chars().all(|c| c.is_ascii_digit()) {
            return None;
        }
        rest.parse::<i128>().ok()?
    };
    Some(if neg { -v } else { v })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn header_is_open() {
        let r = read_line("(func $f (param $x (i32 | $is_even)) (result i32)").unwrap();
        assert_eq!(r.open.len(), 1);
        assert_eq!(r.open[0].len(), 4);
        assert_eq!(r.open[0][2].render(), "(param $x (i32 | $is_even))");
    }
    #[test]
    fn comments_and_ints() {
        assert_eq!(split_comment("  nop ;; hi \"x\"").0, "  nop ");
        assert_eq!(parse_int("-0x10"), Some(-16));
        assert_eq!(parse_int("4294967295"), Some(4294967295));
        assert_eq!(parse_int("$x"), None);
    }
}
