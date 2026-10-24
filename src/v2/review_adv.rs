//! Reviewer's adversarial-program runner (snapshot clone only). For every REVIEW_ADV/*.wat, runs the kernel in
//! strict and gradual mode and writes REVIEW_ADV/../adv-results/<name>.txt listing every cup and line error.

use super::ast::Module;
use super::kernel::check_module;
use super::out::Feed;

#[test]
fn review_adv_programs() {
    let dir = match std::env::var("REVIEW_ADV") { Ok(d) => d, Err(_) => return };
    let outdir = format!("{dir}/../adv-results");
    let _ = std::fs::create_dir_all(&outdir);
    let mut names: Vec<_> = std::fs::read_dir(&dir).unwrap().filter_map(|e| e.ok()).map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "wat")).collect();
    names.sort();
    for p in names {
        let src = std::fs::read_to_string(&p).unwrap();
        let stem = p.file_stem().unwrap().to_string_lossy().to_string();
        let mut text = String::new();
        let m = Module::parse(&src);
        for (l, e) in &m.errors {
            text.push_str(&format!("PARSE ERROR line {l}: {e}\n"));
        }
        for gradual in [false, true] {
            text.push_str(&format!("== mode {}\n", if gradual { "gradual" } else { "strict" }));
            let t0 = std::time::Instant::now();
            let out = std::panic::catch_unwind(|| check_module(&m, gradual));
            let out = match out {
                Ok(o) => o,
                Err(_) => { text.push_str("PANIC in check_module\n"); continue; }
            };
            text.push_str(&format!("({} ms)\n", t0.elapsed().as_millis()));
            for (l, e) in &out.errors {
                text.push_str(&format!("MODULE ERROR line {l}: {e}\n"));
            }
            for f in &out.funcs {
                text.push_str(&format!("func {} lines {}-{} verified={} strict_clean={}\n", f.name, f.header_line, f.end_line, f.verified, f.strict_clean));
                for c in &f.cups {
                    let feed = match &c.feed {
                        Feed::Lookup { origin_line, .. } => format!("lookup@{origin_line}"),
                        Feed::Prove { prove_line, hyp_lines, .. } => format!("prove@{prove_line} hyps{hyp_lines:?}"),
                        Feed::Eval { steps } => format!("eval({steps})"),
                        Feed::DeadCode { ended_at } => format!("dead@{ended_at}"),
                        Feed::Unfed => "UNFED".into(),
                    };
                    text.push_str(&format!("  cup line {} op {:?} {:?} goal ⟨{}⟩ => {} by {} checks {:?} assumptions {:?} {}\n",
                        c.line, c.operand, c.kind.name(), c.goal, c.verdict.name(), feed, c.depends_on_checks,
                        c.assumptions.iter().map(|o| o.line).collect::<Vec<_>>(), c.diag.clone().unwrap_or_default()));
                }
                for (l, e) in &f.line_errors {
                    text.push_str(&format!("  line error {l}: {e}\n"));
                }
            }
        }
        std::fs::write(format!("{outdir}/{stem}.txt"), text).unwrap();
    }
}
