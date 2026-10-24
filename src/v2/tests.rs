//! Native tests for the v2 kernel: erasure against erase.py, parsing, and the expect.json oracle.

use super::ast::Module;
use super::erase::erase_text;

pub const EXAMPLES: [&str; 13] = [
    "parity",
    "parity-missing-proof",
    "parity-bug-gate",
    "isqrt",
    "isqrt-harness-bug",
    "isqrt-wrong-cup",
    "gcd",
    "gcd-bug-guard",
    "gcd-vacuous",
    "primality",
    "hashtable",
    "hashtable-stale",
    "hashtable-bug-tombstone",
];

pub fn testdata(name: &str, ext: &str) -> String {
    let p = format!("{}/src/v2/testdata/{name}.{ext}", env!("CARGO_MANIFEST_DIR"));
    std::fs::read_to_string(&p).unwrap_or_else(|e| panic!("{p}: {e}"))
}

#[test]
fn erasure_matches_erase_py() {
    for ex in EXAMPLES {
        let src = testdata(ex, "wat");
        let want = testdata(ex, "erased");
        let got = erase_text(&src);
        for (i, (g, w)) in got.lines().zip(want.lines()).enumerate() {
            assert_eq!(g, w, "{ex}: line {}", i + 1);
        }
        assert_eq!(got.lines().count(), want.lines().count(), "{ex}: line count");
        assert_eq!(got, want, "{ex}");
    }
}

#[test]
fn erased_examples_assemble() {
    for ex in EXAMPLES {
        let erased = erase_text(&testdata(ex, "wat"));
        let wat = format!("(module {erased})");
        wat::parse_str(&wat).unwrap_or_else(|e| panic!("{ex}: {e}"));
    }
}

#[test]
fn examples_parse_without_errors() {
    for ex in EXAMPLES {
        let m = Module::parse(&testdata(ex, "wat"));
        assert!(m.errors.is_empty(), "{ex}: {:?}", m.errors);
        assert!(m.funcs.iter().all(|f| f.end_line > 0), "{ex}");
    }
}
