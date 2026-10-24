// Deep links into the editor: parsing the URL fragment and encoding/decoding
// programs carried inline in it.
//
// Fragment syntax (all parameters optional, separated by `&`):
//   ex=<name>        load `examples/<name>.wat` (relative to the page)
//   src=<payload>    load the program carried inline: base64url (no padding) of the
//                    raw-DEFLATE compression of the UTF-8 program text
//   step=<n|last|fail>  position the step slider after the first run
//   embed=1          iframe mode (no page margins; height posted to the parent; no saving)

use anyhow::{Result, bail};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StepRequest {
    Number(usize),
    Last,
    Fail,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProgramSource {
    Example(String),
    Inline(String), // the encoded payload, as it appears in the URL
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct LinkParams {
    pub source: Option<ProgramSource>,
    pub step: Option<StepRequest>,
    pub embed: bool,
    pub fit: Option<bool>,       // fit=1: scale the editor to the frame width
    pub args: Option<Vec<i128>>, // arguments for $main (overrides its (@run …))
}

impl LinkParams {
    /// Parse a location hash (with or without the leading `#`).
    pub fn parse(hash: &str) -> Self {
        let mut ret = Self::default();
        let hash = hash.strip_prefix('#').unwrap_or(hash);
        for part in hash.split('&') {
            let (key, value) = match part.split_once('=') {
                Some((k, v)) => (k, v),
                None => (part, ""),
            };
            match key {
                "ex" if is_example_name(value) => {
                    ret.source = Some(ProgramSource::Example(value.to_string()))
                }
                "src" if !value.is_empty() => {
                    ret.source = Some(ProgramSource::Inline(value.to_string()))
                }
                "step" => {
                    ret.step = match value {
                        "last" => Some(StepRequest::Last),
                        "fail" => Some(StepRequest::Fail),
                        n => n.parse::<usize>().ok().map(StepRequest::Number),
                    }
                }
                "embed" => ret.embed = value == "1" || value.is_empty(),
                "fit" => ret.fit = Some(value == "1" || value.is_empty()),
                "args" => {
                    ret.args = value
                        .split(',')
                        .filter(|s| !s.is_empty())
                        .map(|s| s.trim().parse::<i128>())
                        .collect::<Result<Vec<_>, _>>()
                        .ok()
                }
                _ => {}
            }
        }
        ret
    }

    /// The localStorage key under which edits of a linked program are saved,
    /// so that a link never overwrites the user's own program.
    pub fn storage_key(&self, base: &str) -> Option<String> {
        match &self.source {
            None => None,
            Some(ProgramSource::Example(name)) => Some(format!("{base}:ex:{name}")),
            Some(ProgramSource::Inline(payload)) => {
                Some(format!("{base}:src:{:016x}", fnv1a64(payload.as_bytes())))
            }
        }
    }
}

// Example names are restricted so that a fragment can only fetch from `examples/`.
fn is_example_name(s: &str) -> bool {
    !s.is_empty()
        && s.len() <= 80
        && s.chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_' || c == '.')
        && !s.starts_with('.')
}

pub fn fnv1a64(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in bytes {
        h ^= *b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

const B64URL: &[u8; 64] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";

pub fn base64url_encode(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len().div_ceil(3) * 4);
    for chunk in bytes.chunks(3) {
        let b = [
            chunk[0],
            *chunk.get(1).unwrap_or(&0),
            *chunk.get(2).unwrap_or(&0),
        ];
        let n = ((b[0] as u32) << 16) | ((b[1] as u32) << 8) | b[2] as u32;
        let chars = chunk.len() + 1;
        for i in 0..chars {
            out.push(B64URL[((n >> (18 - 6 * i)) & 63) as usize] as char);
        }
    }
    out
}

pub fn base64url_decode(s: &str) -> Result<Vec<u8>> {
    let mut out = Vec::with_capacity(s.len() * 3 / 4);
    let mut acc: u32 = 0;
    let mut bits = 0;
    for c in s.trim_end_matches('=').bytes() {
        let v = match c {
            b'A'..=b'Z' => c - b'A',
            b'a'..=b'z' => c - b'a' + 26,
            b'0'..=b'9' => c - b'0' + 52,
            b'-' | b'+' => 62,
            b'_' | b'/' => 63,
            _ => bail!("invalid base64url character"),
        };
        acc = (acc << 6) | v as u32;
        bits += 6;
        if bits >= 8 {
            bits -= 8;
            out.push((acc >> bits) as u8);
            acc &= (1 << bits) - 1;
        }
    }
    Ok(out)
}

/// Encode program text for a `#src=` link.
pub fn encode_program(text: &str) -> String {
    base64url_encode(&miniz_oxide::deflate::compress_to_vec(text.as_bytes(), 9))
}

/// Decode the payload of a `#src=` link.
pub fn decode_program(payload: &str) -> Result<String> {
    let compressed = base64url_decode(payload)?;
    let bytes = miniz_oxide::inflate::decompress_to_vec_with_limit(&compressed, 1 << 22)
        .map_err(|e| anyhow::anyhow!("could not inflate program: {e:?}"))?;
    Ok(String::from_utf8(bytes)?)
}

/// The `&args=…` part of a fragment.
pub fn args_fragment(args: &Option<Vec<i128>>) -> String {
    match args {
        Some(a) => format!(
            "&args={}",
            a.iter()
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join(",")
        ),
        None => String::new(),
    }
}

/// Build the fragment for a shareable link to `text` at slider position `step`.
pub fn share_fragment(text: &str, step: Option<StepRequest>, embed: bool) -> String {
    let mut ret = format!("#src={}", encode_program(text));
    match step {
        Some(StepRequest::Number(n)) => ret.push_str(&format!("&step={n}")),
        Some(StepRequest::Last) => ret.push_str("&step=last"),
        Some(StepRequest::Fail) => ret.push_str("&step=fail"),
        None => {}
    }
    if embed {
        ret.push_str("&embed=1");
    }
    ret
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_fragments() {
        assert_eq!(LinkParams::parse(""), LinkParams::default());
        assert_eq!(LinkParams::parse("#"), LinkParams::default());
        let p = LinkParams::parse("#ex=isqrt-s3&step=fail&embed=1");
        assert_eq!(p.source, Some(ProgramSource::Example("isqrt-s3".into())));
        assert_eq!(p.step, Some(StepRequest::Fail));
        assert!(p.embed);
        let p = LinkParams::parse("#ex=isqrt&args=10,-3");
        assert_eq!(p.args, Some(vec![10, -3]));
        assert_eq!(args_fragment(&p.args), "&args=10,-3");
        assert_eq!(LinkParams::parse("#args=1,x").args, None);
        assert_eq!(LinkParams::parse("#embed=1&fit=1").fit, Some(true));
        let p = LinkParams::parse("step=12&ex=gcd");
        assert_eq!(p.step, Some(StepRequest::Number(12)));
        assert!(!p.embed);
        // no path traversal through example names
        assert_eq!(LinkParams::parse("#ex=../secret").source, None);
        assert_eq!(LinkParams::parse("#ex=a/b").source, None);
        assert_eq!(LinkParams::parse("#step=bogus").step, None);
    }

    #[test]
    fn base64url_roundtrip() {
        for len in 0..40 {
            let data: Vec<u8> = (0..len).map(|i| (i * 37 + 11) as u8).collect();
            let enc = base64url_encode(&data);
            assert!(!enc.contains('=') && !enc.contains('+') && !enc.contains('/'));
            assert_eq!(base64url_decode(&enc).unwrap(), data);
        }
        assert_eq!(base64url_encode(b"hello"), "aGVsbG8");
        assert!(base64url_decode("a*b").is_err());
    }

    #[test]
    fn program_roundtrip() {
        let prog = "(func $main\n  i32.const 10\n  call $isqrt\n  drop\n)\n;; ∀ unicode ⚖\n";
        let enc = encode_program(prog);
        assert_eq!(decode_program(&enc).unwrap(), prog);
        let frag = share_fragment(prog, Some(StepRequest::Number(7)), false);
        let p = LinkParams::parse(&frag);
        assert_eq!(p.step, Some(StepRequest::Number(7)));
        match p.source {
            Some(ProgramSource::Inline(payload)) => {
                assert_eq!(decode_program(&payload).unwrap(), prog)
            }
            _ => panic!("expected inline source"),
        }
    }

    #[test]
    fn storage_keys_differ_by_link() {
        let a = LinkParams::parse("#ex=gcd").storage_key("k").unwrap();
        let b = LinkParams::parse("#ex=isqrt").storage_key("k").unwrap();
        let c = LinkParams::parse("#src=abc").storage_key("k").unwrap();
        assert_ne!(a, b);
        assert!(c.starts_with("k:src:"));
        assert_eq!(LinkParams::parse("#step=3").storage_key("k"), None);
    }
}
