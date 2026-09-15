//! **The differential oracle: the Lean kernel against the Rust that shipped.**
//!
//! The plan says a checked parser is worth having "even with no FFI" because it
//! can be run against the Rust. This is that. It reads the JSONL that
//! `examples/oracle/` produces on a scratch checkout of the fork point `4748911`
//! (`main` was discarded; AGENTS §7.3) — one record per
//! candidate line, saying what `tm-core::grammar` makes of it — asks the kernel
//! the same questions through the FFI, and reports every disagreement.
//!
//! ```console
//! $ ORACLE=$(examples/oracle/build-oracle.sh)
//! $ "$ORACLE" gen 512 1 > /tmp/gen.jsonl
//! $ cargo run --example oracle-compare -- /tmp/gen.jsonl
//! ```
//!
//! ## What is comparable, and how the kernel is asked
//!
//! The kernel's whole surface is `String -> String` over a plan, so every
//! question has to be phrased as a request. Three are:
//!
//! * **is this an item line, and does it survive a read?** — one document, one
//!   line, no commands. `ok` with the same bytes back means the kernel kept it;
//!   an error means it refused the file.
//! * **what id does the kernel read off it?** — the *same line twice* in one
//!   document. An entity renders at most two lines and never two in one file, so
//!   the loader answers `dupId <id>` — and that names the id it parsed. A line
//!   that is not an item comes back as two prose lines instead, which is how
//!   "item" and "prose" are told apart from outside.
//! * **does an `est` edit produce the same line?** — `{"op":"est",...}` against
//!   the kernel, `ItemLine::set_token("est","45m")` against the Rust. This is
//!   the edit whose two implementations disagreed in shipped tm (`tm edit ^id
//!   est=` reported success and changed nothing), so it is the one worth
//!   diffing.
//!
//! Everything else the Rust records — `title`, `ci`, `shape`, `recur` — has no
//! observable counterpart at stage 1, because the kernel keeps every token
//! except the id and the estimate verbatim and does not interpret it. That is a
//! stated gap, not a silent one; see the report this prints.

#[path = "../tests/harness/mod.rs"]
mod harness;

use harness::*;
use std::collections::BTreeMap;
use std::io::Read;

/// The path both halves use; it must match `FILE` in `examples/oracle/`.
const FILE: &str = "week/2026-W37.md";

// ---------------------------------------------------------------------------
// Asking the kernel
// ---------------------------------------------------------------------------

fn doc(lines: &[&str]) -> Doc {
    Doc {
        path: FILE.to_string(),
        lines: lines.iter().map(|s| s.to_string()).collect(),
        region: None,
    }
}

#[derive(Debug)]
struct Kernel {
    /// the kernel treats the line as an item line (it has `- [x]`'s shape)
    item: bool,
    /// the id the kernel read, when it read exactly one
    id: Option<String>,
    /// the shape fault, when the line has an item's shape and does not parse
    shape_fault: Option<String>,
    /// a one-line document holding it loads
    accepts: bool,
    /// …and hands the bytes back unchanged
    roundtrip: bool,
    /// why not, when it does not load
    err: Option<String>,
}

fn ask_kernel(line: &str) -> Kernel {
    // probe 1: does one document holding just this line load, unchanged?
    let (accepts, roundtrip, err) = match ask(&[doc(&[line])]) {
        Reply::Err(e) => (false, false, Some(e)),
        Reply::Docs(back) => (true, back[0] == vec![line.to_string()], None),
    };

    // probe 2: the same line twice. An entity never renders two lines in one
    // file, so the loader has to say which id repeated — which is how the id it
    // parsed becomes observable from outside.
    let (item, id, shape_fault) = match ask(&[doc(&[line, line])]) {
        Reply::Docs(_) => (false, None, None), // two prose lines: not an item
        Reply::Err(e) => {
            let j = parse_json(&e).expect("the kernel's error is JSON");
            let id = ["dupId", "orphanDemotion", "splitLine", "notADemotion", "ambiguousDemotion"]
                .iter()
                .find_map(|k| j.get(k).and_then(J::str).map(str::to_string));
            let fault = j
                .get("badLine")
                .and_then(|b| b.get("why"))
                .and_then(J::str)
                .map(|w| w.trim_start_matches("Tm.PErr.").to_string());
            (true, id, fault)
        }
    };

    Kernel { item, id, shape_fault, accepts, roundtrip, err }
}

/// The line the kernel writes for `tm edit ^id est=45m`.
fn kernel_est_edit(line: &str, id: &str) -> Option<String> {
    let req = format!(
        "{{\"docs\":[{}],\"cmds\":[{{\"op\":\"est\",\"id\":{},\"min\":45}}]}}",
        doc(&[line]).encode(),
        escape(id)
    );
    let raw = tm_kernel_ffi::call(&req).ok()?;
    let j = parse_json(&raw).ok()?;
    let lines = j.get("ok")?.get("docs")?.arr()?.first()?.get("lines")?.arr()?;
    Some(lines.first()?.str()?.to_string())
}

// ---------------------------------------------------------------------------
// The Rust's answers, as the oracle binary printed them
// ---------------------------------------------------------------------------

struct Rust {
    text: String,
    item: bool,
    id: String,
    roundtrip: bool,
    out: String,
    problems: Vec<String>,
    est_edit: Option<String>,
}

fn read_records(src: &str) -> Vec<Rust> {
    src.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let j = parse_json(l).unwrap_or_else(|e| panic!("bad oracle record ({e}): {l}"));
            Rust {
                text: j.get("in").and_then(J::str).expect("`in`").to_string(),
                item: matches!(j.get("item"), Some(J::Bool(true))),
                id: j.get("id").and_then(J::str).unwrap_or("").to_string(),
                roundtrip: matches!(j.get("roundtrip"), Some(J::Bool(true))),
                out: j.get("out").and_then(J::str).unwrap_or("").to_string(),
                problems: j
                    .get("problems")
                    .and_then(J::arr)
                    .map(|a| a.iter().filter_map(J::str).map(str::to_string).collect())
                    .unwrap_or_default(),
                est_edit: j.get("est_edit").and_then(J::str).map(str::to_string),
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Comparing
// ---------------------------------------------------------------------------

#[derive(Default)]
struct Findings {
    /// category -> (count, up to three witnesses)
    by_kind: BTreeMap<String, (usize, Vec<String>)>,
}

impl Findings {
    fn note(&mut self, kind: &str, witness: String) {
        let e = self.by_kind.entry(kind.to_string()).or_insert((0, Vec::new()));
        e.0 += 1;
        if e.1.len() < 3 {
            e.1.push(witness);
        }
    }
}

/// **How many lines each comparison actually ran on.** A comparison that never
/// ran reports no disagreements, and that is not the same statement as "they
/// agree". The oracle prints these next to the findings so the difference is
/// visible.
#[derive(Default)]
struct Coverage {
    itemness: usize,
    byte_faithful_rust: usize,
    byte_faithful_kernel: usize,
    id: usize,
    acceptance: usize,
    est_edit: usize,
}

/// A category name, not a witness: the id or value that varies line by line is
/// replaced by `…` so 90 distinct messages do not become 90 categories. The
/// witnesses printed under each category keep the real text.
fn generalise(msg: &str) -> String {
    let mut out = String::new();
    let mut in_quotes = false;
    for c in msg.chars() {
        match c {
            '`' => {
                if !in_quotes {
                    out.push_str("`…`");
                }
                in_quotes = !in_quotes;
            }
            '"' => {
                // `: "7"` — the offending value at the end of a Rust message
                if !in_quotes {
                    out.push('…');
                }
                in_quotes = !in_quotes;
            }
            c if !in_quotes => out.push(c),
            _ => {}
        }
    }
    out
}

/// The kernel's diagnostic, as a name: `{"dupId":"a1"}` and `{"dupId":"b2"}`
/// are one finding, not two.
fn err_kind(err: &str) -> String {
    let Ok(j) = parse_json(err) else { return err.to_string() };
    let J::Obj(kv) = &j else { return err.to_string() };
    match kv.first() {
        Some((k, v)) if k == "badLine" => format!(
            "badLine/{}",
            v.get("why").and_then(J::str).unwrap_or("?").trim_start_matches("Tm.PErr.")
        ),
        Some((k, v)) if k == "itemCheck" => format!("itemCheck/{}", v.str().unwrap_or("?")),
        Some((k, _)) => k.clone(),
        None => err.to_string(),
    }
}

/// Why the kernel calls a line prose, when the Rust calls it an item. The
/// kernel's rule is `parseBody` (Line.lean): leading spaces, then exactly
/// `- [`, one state character, `]`.
fn why_prose(line: &str) -> &'static str {
    let s = line.trim_start_matches([' ', '\t']);
    let c: Vec<char> = s.chars().collect();
    if c.first() != Some(&'-') {
        return "does not start with `-`";
    }
    match c.get(1) {
        Some(' ') => {}
        Some(_) => return "no space after the bullet",
        None => return "nothing after the bullet",
    }
    match c.get(2) {
        Some('[') => {}
        // `- \t[x] …` and `-  [x] …`: the Rust skips a whitespace *run* here,
        // the kernel's `parseBody` matches the literal `- [`
        Some(w) if w.is_whitespace() => {
            return "more than one space, or a tab, between the bullet and `[`"
        }
        _ => return "no `[state]` box (a routines/optional/inbox line)",
    }
    if c.get(4) != Some(&']') {
        return "the `[` is not closed one character later";
    }
    "unclassified"
}

/// The corpus's item lines, as JSON strings, for piping into `tm-oracle parse`.
fn emit_corpus_lines() {
    for plan in plans() {
        for (rel, text) in markdown_files(&plan) {
            let _ = rel;
            for l in split_lines(&text) {
                if why_prose(&l) == "unclassified" {
                    println!("{}", escape(&l));
                }
            }
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.get(1).map(String::as_str) == Some("--emit-corpus-lines") {
        emit_corpus_lines();
        return;
    }
    let mut src = String::new();
    match args.get(1) {
        Some(p) if p != "-" => {
            src = std::fs::read_to_string(p).unwrap_or_else(|e| panic!("{p}: {e}"))
        }
        _ => {
            std::io::stdin().read_to_string(&mut src).unwrap();
        }
    }
    let records = read_records(&src);
    assert!(!records.is_empty(), "no records on stdin/argv[1]");

    let mut f = Findings::default();
    let mut cov = Coverage::default();
    let mut agree = 0usize;

    for r in &records {
        let k = ask_kernel(&r.text);
        let mut disagreed = false;

        // --- byte faithfulness, each side against itself -------------------
        // This is the one that would be a bug in either implementation, not a
        // difference of scope: a parser that keeps a line must hand it back.
        if r.item {
            cov.byte_faithful_rust += 1;
            if !r.roundtrip {
                f.note("RUST is not byte-faithful", format!("{:?} -> {:?}", r.text, r.out));
                disagreed = true;
            }
        }
        if k.accepts {
            cov.byte_faithful_kernel += 1;
            if !k.roundtrip {
                f.note("KERNEL is not byte-faithful", format!("{:?}", r.text));
                disagreed = true;
            }
        }

        // --- is it an item line? -------------------------------------------
        cov.itemness += 1;
        if r.item != k.item {
            let why = if k.item {
                "kernel: item, Rust: not an item line".to_string()
            } else {
                format!(
                    "Rust: item{}, kernel: prose ({})",
                    if r.id.is_empty() { " (no id)" } else { "" },
                    why_prose(&r.text)
                )
            };
            f.note(&format!("item-ness — {why}"), format!("{:?}", r.text));
            disagreed = true;
        }

        // --- the id ---------------------------------------------------------
        if r.item && k.item {
            cov.id += 1;
            match (r.id.as_str(), k.id.as_deref(), k.shape_fault.as_deref()) {
                ("", None, Some("noId")) => {}         // agree: no id
                ("", _, _) if k.id.is_some() => {
                    f.note(
                        "id — Rust reads none, kernel reads one",
                        format!("{:?} kernel id {:?}", r.text, k.id.as_deref().unwrap()),
                    );
                    disagreed = true;
                }
                (rid, Some(kid), _) if rid != kid => {
                    f.note(
                        "id — different id",
                        format!("{:?} rust {rid:?} kernel {kid:?}", r.text),
                    );
                    disagreed = true;
                }
                (rid, None, fault) if !rid.is_empty() => {
                    f.note(
                        &format!("id — Rust reads one, kernel refuses ({})", fault.unwrap_or("?")),
                        format!("{:?} rust id {rid:?}", r.text),
                    );
                    disagreed = true;
                }
                _ => {}
            }
        }

        // --- acceptance -----------------------------------------------------
        // `tm check`'s diagnostics on the Rust side, the loader's refusal on the
        // kernel's. They are the same question asked in two places.
        if r.item {
            cov.acceptance += 1;
        }
        if r.item && r.problems.is_empty() && !r.id.is_empty() && !k.accepts {
            f.note(
                &format!(
                    "acceptance — Rust is clean, kernel refuses: {}",
                    err_kind(&k.err.clone().unwrap_or_default())
                ),
                format!("{:?}   {}", r.text, k.err.clone().unwrap_or_default()),
            );
            disagreed = true;
        }
        if r.item && !r.problems.is_empty() && k.accepts {
            f.note(
                &format!(
                    "acceptance — Rust reports a problem, kernel accepts: {}",
                    generalise(&r.problems[0])
                ),
                format!("{:?}   {}", r.text, r.problems[0]),
            );
            disagreed = true;
        }

        // --- the `est` edit ---------------------------------------------------
        if let (Some(kid), true, Some(rust_edit)) = (k.id.as_deref(), k.accepts, r.est_edit.as_deref())
        {
            if !r.id.is_empty() && r.id == kid {
                cov.est_edit += 1;
                match kernel_est_edit(&r.text, kid) {
                    None => {
                        f.note("est edit — the kernel refused the edit", format!("{:?}", r.text));
                        disagreed = true;
                    }
                    Some(kernel_edit) if kernel_edit != rust_edit => {
                        f.note(
                            "est edit — different line",
                            format!("{:?}\n        rust   {rust_edit:?}\n        kernel {kernel_edit:?}", r.text),
                        );
                        disagreed = true;
                    }
                    Some(_) => {}
                }
            }
        }

        if !disagreed {
            agree += 1;
        }
    }

    // ---- report ---------------------------------------------------------
    println!("\n  differential oracle — Lean kernel vs the fork point 4748911's tm-core::grammar\n");
    println!("  {} lines compared, {agree} with nothing to report\n", records.len());
    if f.by_kind.is_empty() {
        println!("  no disagreements.");
    }
    for (kind, (n, witnesses)) in &f.by_kind {
        println!("  {n:>5}  {kind}");
        for w in witnesses {
            println!("         {w}");
        }
    }
    // A comparison that never ran has nothing to report, which is not the same
    // as agreement. These are the denominators.
    println!("\n  lines each comparison actually ran on:");
    println!("  {:>5}  is it an item line", cov.itemness);
    println!("  {:>5}  Rust hands the line back unchanged", cov.byte_faithful_rust);
    println!("  {:>5}  kernel hands the line back unchanged", cov.byte_faithful_kernel);
    println!("  {:>5}  the id (both call it an item)", cov.id);
    println!("  {:>5}  acceptance (Rust calls it an item)", cov.acceptance);
    println!("  {:>5}  the `est` edit (both read the same id, kernel loads it)", cov.est_edit);
    println!(
        "\n  not compared: title, ci, priority, parent, tags, shape, recurrence,\n  \
         budget, loc, buffer and flags — at stage 1 the kernel keeps every token\n  \
         but the id and the estimate verbatim and does not interpret it, so it\n  \
         has no answer to differ from.\n"
    );
}
