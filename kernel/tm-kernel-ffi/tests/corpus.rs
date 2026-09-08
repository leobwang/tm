//! **Stage 2's acceptance evidence: `render ∘ parse` byte-identical over the
//! full fixture corpus.**
//!
//! Every Markdown file in `kernel/corpus/` goes through the kernel's
//! `String -> String` boundary **with no commands at all** and the bytes that
//! come back are compared with the bytes that went in. There is nothing to
//! interpret in the result: either the file survived a read unchanged or it
//! did not.
//!
//! This is a stronger statement than round trip B, and a different one. B is a
//! theorem about `List (List Char)`; this is a measurement over the real files,
//! and it covers the two steps B cannot reach:
//!
//! 1. **the split at the very edge** (README gap 6) — bytes become a list of
//!    lines and a list of lines becomes bytes out here, in the harness, not in
//!    the kernel. `split_join_is_identity` pins that step on its own;
//! 2. **the JSON escaping on both sides of the FFI** — a quote, a backslash, a
//!    tab or an astral character has to survive the encoder here, the decoder
//!    in Lean, the encoder in Lean and the decoder here. `escaping_survives_
//!    the_boundary` pins that with characters the corpus does not contain.
//!
//! ## What the assertions are, and why they are shaped this way
//!
//! Two other agents are extending the grammar on their own branches while this
//! runs, so a hard "all 37 files must pass" would be a lie today and a
//! nuisance tomorrow. Instead:
//!
//! * **`no_file_is_silently_rewritten` is absolute.** A document the kernel
//!   *accepts* and hands back with different bytes is a data-loss bug, full
//!   stop. There is no baseline for it and there never should be.
//! * **`corpus_round_trip` is a ratchet.** `corpus/round-trip.expected` records
//!   which files round-trip today; a file recorded as passing that stops
//!   passing fails the build, and a file that starts passing does not. The
//!   number can only go up, and the report says what it is.
//!
//! Run `cargo test --test corpus -- --nocapture` for the file-by-file table,
//! including, for each file that does not load, the minimal set of lines that
//! reproduces the refusal.

#[path = "harness/mod.rs"]
mod harness;

use harness::*;
use std::collections::BTreeMap;
use std::path::Path;

// ---------------------------------------------------------------------------
// Outcomes
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq)]
enum Outcome {
    /// accepted, and every byte came back
    Ok,
    /// accepted, and the bytes changed — always a bug
    Differs { doc: String, line: usize, went_in: String, came_out: String },
    /// refused at load; the kernel named a diagnostic
    Reject(String),
}

impl Outcome {
    fn tag(&self) -> &'static str {
        match self {
            Outcome::Ok => "ok",
            Outcome::Differs { .. } => "differs",
            Outcome::Reject(_) => "reject",
        }
    }
    fn detail(&self) -> String {
        match self {
            Outcome::Ok => String::new(),
            Outcome::Differs { doc, line, .. } => format!("{doc} line {line}"),
            Outcome::Reject(e) => e.clone(),
        }
    }
}

/// Push a document set through the boundary and compare byte for byte.
fn round_trip(docs: &[Doc], originals: &[String]) -> Outcome {
    match ask(docs) {
        Reply::Err(e) => Outcome::Reject(e),
        Reply::Docs(back) => {
            assert_eq!(
                back.len(),
                docs.len(),
                "the kernel returned {} documents for {} requested",
                back.len(),
                docs.len()
            );
            for (k, lines) in back.iter().enumerate() {
                let out = join_lines(lines);
                if out != originals[k] {
                    let a: Vec<&str> = originals[k].split('\n').collect();
                    let b: Vec<&str> = out.split('\n').collect();
                    let n = a.len().min(b.len());
                    let doc = docs[k].path.clone();
                    for i in 0..n {
                        if a[i] != b[i] {
                            return Outcome::Differs {
                                doc,
                                line: i + 1,
                                went_in: a[i].to_string(),
                                came_out: b[i].to_string(),
                            };
                        }
                    }
                    return Outcome::Differs {
                        doc,
                        line: n + 1,
                        went_in: a.get(n).unwrap_or(&"<end of file>").to_string(),
                        came_out: b.get(n).unwrap_or(&"<end of file>").to_string(),
                    };
                }
            }
            Outcome::Ok
        }
    }
}

fn round_trip_file(rel: &str, text: &str) -> Outcome {
    let d = doc_of(rel, text);
    round_trip(&[d], std::slice::from_ref(&text.to_string()))
}

// ---------------------------------------------------------------------------
// Naming the line that did it
// ---------------------------------------------------------------------------

/// The kernel's own item-line shape (`parseBody`, Line.lean): optional
/// whitespace, then `- [` , one state character, `]`. Used only to decide
/// which lines the minimiser is allowed to remove — prose is context (a
/// heading decides a section, and §4.2's section discipline is checked against
/// it), so prose is always kept.
fn looks_like_item(l: &str) -> bool {
    let s = l.trim_start_matches([' ', '\t']);
    let c: Vec<char> = s.chars().take(5).collect();
    c.len() == 5 && c[0] == '-' && c[1] == ' ' && c[2] == '[' && c[4] == ']'
}

/// Why a file was refused, in the form that is actually useful to whoever has
/// to fix it.
struct Diagnosis {
    /// how many item lines the file has
    items: usize,
    /// every item line that is refused **on its own**, with all prose kept, and
    /// the diagnostic it produces. A file where this is the whole item list is
    /// one the grammar cannot read at all; a file where it is empty is refused
    /// by a *combination* of lines.
    singly: Vec<(usize, String, String)>,
    /// the smallest set of item lines that still reproduces the refusal — the
    /// pair, when the fault is a pair (a duplicate id, a cycle, a demotion)
    minimal: Vec<usize>,
    minimal_err: String,
}

fn diagnose(rel: &str, text: &str) -> Option<Diagnosis> {
    let all: Vec<String> = split_lines(text);
    let item_ix: Vec<usize> = (0..all.len()).filter(|&i| looks_like_item(&all[i])).collect();

    // prose is context: a heading decides a section, and §4.2's section
    // discipline is checked against it, so prose is never removed.
    let attempt = |keep: &[usize]| -> Option<String> {
        let lines: Vec<String> = (0..all.len())
            .filter(|i| !looks_like_item(&all[*i]) || keep.contains(i))
            .map(|i| all[i].clone())
            .collect();
        let d = Doc { path: rel.to_string(), lines, region: region_of(rel) };
        match ask(&[d]) {
            Reply::Err(e) => Some(e),
            Reply::Docs(_) => None,
        }
    };

    let whole = attempt(&item_ix)?;

    let singly: Vec<(usize, String, String)> = item_ix
        .iter()
        .filter_map(|&i| attempt(&[i]).map(|e| (i + 1, all[i].clone(), e)))
        .collect();

    // greedy delta-debug: drop an item line whenever the refusal survives
    let mut keep = item_ix.clone();
    let mut err = whole;
    let mut i = 0;
    while i < keep.len() {
        let mut trial = keep.clone();
        trial.remove(i);
        match attempt(&trial) {
            Some(e) => {
                keep = trial;
                err = e;
            }
            None => i += 1,
        }
    }
    Some(Diagnosis {
        items: item_ix.len(),
        singly,
        minimal: keep.iter().map(|i| i + 1).collect(),
        minimal_err: err,
    })
}

// ---------------------------------------------------------------------------
// The baseline
// ---------------------------------------------------------------------------

fn baseline_path() -> std::path::PathBuf {
    corpus_root().join("round-trip.expected")
}

/// `kind \t name \t tag \t detail`; `#` starts a comment.
fn read_baseline() -> BTreeMap<(String, String), (String, String)> {
    let text = std::fs::read_to_string(baseline_path())
        .unwrap_or_else(|e| panic!("{}: {e}", baseline_path().display()));
    let mut m = BTreeMap::new();
    for l in text.lines() {
        if l.trim().is_empty() || l.starts_with('#') {
            continue;
        }
        let f: Vec<&str> = l.split('\t').collect();
        assert!(f.len() >= 3, "malformed baseline row: {l:?}");
        m.insert(
            (f[0].to_string(), f[1].to_string()),
            (f[2].to_string(), f.get(3).unwrap_or(&"").to_string()),
        );
    }
    m
}

// ---------------------------------------------------------------------------
// Measuring
// ---------------------------------------------------------------------------

struct Row {
    kind: &'static str,
    name: String,
    outcome: Outcome,
}

fn measure() -> Vec<Row> {
    let mut rows = Vec::new();
    for plan in plans() {
        let plan_name = plan.file_name().unwrap().to_string_lossy().to_string();
        let files = markdown_files(&plan);
        assert!(!files.is_empty(), "{} holds no .md files", plan.display());

        for (rel, text) in &files {
            rows.push(Row {
                kind: "file",
                name: format!("{plan_name}/{rel}"),
                outcome: round_trip_file(rel, text),
            });
        }

        // the whole plan at once, which is how the host loads it: cross-file
        // duplicate ids and the two lines of a demotion are only visible here
        let docs: Vec<Doc> = files.iter().map(|(rel, text)| doc_of(rel, text)).collect();
        let originals: Vec<String> = files.iter().map(|(_, t)| t.clone()).collect();
        rows.push(Row { kind: "plan", name: plan_name, outcome: round_trip(&docs, &originals) });
    }
    rows
}

fn report(rows: &[Row]) {
    let base = read_baseline();
    println!("\n  kernel/corpus — render ∘ parse, no commands\n");
    for r in rows {
        let was = base.get(&(r.kind.to_string(), r.name.clone()));
        let note = match was {
            Some((tag, detail)) if *tag != r.outcome.tag() => {
                format!("   <- baseline said {tag} {detail}")
            }
            Some((_, detail)) if *detail != r.outcome.detail() => {
                format!("   <- baseline said {detail}")
            }
            None => "   <- not in baseline".to_string(),
            _ => String::new(),
        };
        println!(
            "  {:<7} {:<40} {:<8}{}{note}",
            r.kind,
            r.name,
            r.outcome.tag(),
            r.outcome.detail()
        );
        if let Outcome::Differs { doc, line, went_in, came_out } = &r.outcome {
            println!("          {doc} line {line} in  {went_in:?}");
            println!("          {doc} line {line} out {came_out:?}");
        }
    }

    // for every file that did not load, the minimal set of lines that does it
    let mut printed_header = false;
    for r in rows.iter().filter(|r| r.kind == "file" && matches!(r.outcome, Outcome::Reject(_))) {
        if !printed_header {
            println!("\n  why each file was refused (minimal failing lines, prose kept)\n");
            printed_header = true;
        }
        let (plan, rel) = r.name.split_once('/').unwrap();
        let path = corpus_root().join(plan).join(rel);
        let text = std::fs::read_to_string(&path).unwrap();
        match diagnose(rel, &text) {
            None => println!("  {} — not reproducible line by line", r.name),
            Some(d) => {
                println!("  {}", r.name);
                println!(
                    "      {} of {} item lines are refused on their own:",
                    d.singly.len(),
                    d.items
                );
                for (n, text, err) in &d.singly {
                    println!("        line {n:<3} {err}");
                    println!("                 {text}");
                }
                if d.singly.len() != d.items {
                    let all: Vec<String> = split_lines(&text);
                    println!("      smallest set that still fails: {}", d.minimal_err);
                    if d.minimal.is_empty() {
                        println!("        (none; the document itself is refused)");
                    }
                    for n in &d.minimal {
                        println!("        line {n:<3} {}", all[n - 1]);
                    }
                }
            }
        }
    }

    let files: Vec<&Row> = rows.iter().filter(|r| r.kind == "file").collect();
    let plans_: Vec<&Row> = rows.iter().filter(|r| r.kind == "plan").collect();
    let fok = files.iter().filter(|r| r.outcome == Outcome::Ok).count();
    let pok = plans_.iter().filter(|r| r.outcome == Outcome::Ok).count();
    println!(
        "\nCORPUS: {fok}/{} files and {pok}/{} whole plans round-trip byte-identically\n",
        files.len(),
        plans_.len()
    );
}

/// `TM_CORPUS_BLESS=1 cargo test --test corpus` rewrites the baseline from what
/// the kernel does today. The baseline is measured, never typed: a hand-edited
/// row is a claim nobody checked.
fn bless(rows: &[Row]) {
    let mut s = String::from(
        "# Measured, not written by hand: `TM_CORPUS_BLESS=1 cargo test --test corpus`.\n\
         #\n\
         # kind \\t name \\t outcome \\t detail\n\
         #\n\
         # `corpus_round_trip` asserts only that every row recorded `ok` is still\n\
         # `ok`.  A row that starts passing is reported, not failed: the grammar is\n\
         # being extended on other branches and this number may only rise.  The\n\
         # `detail` column is a note, not an assertion.\n\
         #\n\
         # `reject` is the kernel refusing to load the file at all.  It is never\n\
         # \"the file changed\": a document the kernel accepts and hands back with\n\
         # different bytes is `differs`, and `no_file_is_silently_rewritten` fails\n\
         # on it unconditionally, with no baseline.\n",
    );
    for r in rows {
        s.push_str(&format!(
            "{}\t{}\t{}\t{}\n",
            r.kind,
            r.name,
            r.outcome.tag(),
            r.outcome.detail()
        ));
    }
    std::fs::write(baseline_path(), s).unwrap();
    println!("wrote {}", baseline_path().display());
}

// ---------------------------------------------------------------------------
// The tests
// ---------------------------------------------------------------------------

/// **The absolute one.** A document the kernel accepts must come back byte for
/// byte. Accepting a file and rewriting it is the failure mode this whole
/// rebuild exists to make impossible (the first loader turned a `[-]` into a
/// `[ ]` on a plain read), so there is no baseline here and no file is exempt.
#[test]
fn no_file_is_silently_rewritten() {
    let rows = measure();
    let bad: Vec<&Row> = rows.iter().filter(|r| matches!(r.outcome, Outcome::Differs { .. })).collect();
    assert!(
        bad.is_empty(),
        "the kernel accepted and then rewrote {} document(s): {:?}",
        bad.len(),
        bad.iter()
            .map(|r| match &r.outcome {
                Outcome::Differs { doc, line, went_in, came_out } =>
                    format!("{} ({doc}) line {line}: {went_in:?} -> {came_out:?}", r.name),
                _ => unreachable!(),
            })
            .collect::<Vec<_>>()
    );
}

/// **The ratchet.** Every file the baseline records as round-tripping still
/// does. A file that newly round-trips is reported, not failed — the grammar is
/// being extended on other branches, and this number is only allowed to rise.
#[test]
fn corpus_round_trip() {
    let rows = measure();
    if std::env::var("TM_CORPUS_BLESS").as_deref() == Ok("1") {
        bless(&rows);
    }
    report(&rows);
    let base = read_baseline();

    let mut regressions = Vec::new();
    for ((kind, name), (tag, detail)) in &base {
        let Some(now) = rows.iter().find(|r| r.kind == kind && r.name == *name) else {
            panic!("baseline names `{kind} {name}`, which is not in the corpus any more");
        };
        if tag == "ok" && now.outcome != Outcome::Ok {
            regressions.push(format!(
                "{kind} {name}: round-tripped at baseline, now {} {}",
                now.outcome.tag(),
                now.outcome.detail()
            ));
        }
        let _ = detail;
    }
    assert!(regressions.is_empty(), "round-trip regressions:\n  {}", regressions.join("\n  "));

    let ok_now = rows.iter().filter(|r| r.outcome == Outcome::Ok).count();
    let ok_base = base.values().filter(|(t, _)| t == "ok").count();
    assert!(
        ok_now >= ok_base,
        "{ok_now} entries round-trip but the baseline records {ok_base}"
    );
}

/// **README gap 6, pinned.** The kernel's round trip is over `List (List
/// Char)`; the bytes are split on newlines and rejoined out here. That step is
/// the identity on every string, and here it is checked on the corpus itself
/// plus the four shapes that break naive splitters.
#[test]
fn split_join_is_identity() {
    let mut checked = 0usize;
    for plan in plans() {
        for (rel, text) in markdown_files(&plan) {
            assert_eq!(join_lines(&split_lines(&text)), text, "{rel}");
            // and the count is exactly newlines + 1, so no separator was
            // invented or dropped
            assert_eq!(split_lines(&text).len(), text.matches('\n').count() + 1, "{rel}");
            checked += 1;
        }
    }
    assert!(checked >= 30, "only {checked} corpus files were found");

    for s in ["", "\n", "\n\n", "a", "a\n", "a\nb", "\na", "a\n\nb\n", "\r\n\r\n"] {
        assert_eq!(join_lines(&split_lines(s)), s, "{s:?}");
    }
}

/// **The escaping, with characters the corpus does not contain.** The corpus is
/// plain UTF-8 with no quotes, backslashes, tabs or control characters, so it
/// cannot tell a correct JSON codec from one that is wrong on both sides. These
/// can. A CRLF file is here too: splitting on `\n` leaves the `\r` at the end of
/// the line, and it has to come back.
#[test]
fn escaping_survives_the_boundary() {
    let cases: &[(&str, &[&str])] = &[
        ("an empty document", &[]),
        ("one empty line", &[""]),
        ("only newlines", &["", "", ""]),
        ("a quote", &[r#"she said "hi" and left"#]),
        ("a backslash", &[r"C:\Users\a\b"]),
        ("a tab", &["a\tb"]),
        ("a CR (a CRLF file, split on LF)", &["# Notes\r", "- text\r", ""]),
        ("a control character", &["a\u{1}b"]),
        ("DEL", &["a\u{7f}b"]),
        ("an astral plane character", &["moon \u{1F319} done"]),
        ("a lone bullet", &["-"]),
        ("a bullet and a space", &["- "]),
        ("an item carrying a quote", &[r#"- [ ] 2 30m Say "hi" ^a1"#]),
        ("an item carrying a backslash", &[r"- [ ] 2 30m C:\x ^a1"]),
        ("an item carrying a tab", &["- [ ]\t2 30m Tabbed ^a1"]),
        ("an indented item", &["  - [ ] 2 30m Indented ^a1"]),
        ("an item with trailing spaces", &["- [ ] 2 30m Trail ^a1   "]),
    ];
    for (what, lines) in cases {
        let lines: Vec<String> = lines.iter().map(|s| s.to_string()).collect();
        let text = join_lines(&lines);
        let d = Doc { path: "backlog.md".into(), lines: lines.clone(), region: None };
        match ask(&[d]) {
            Reply::Err(e) => panic!("{what}: the kernel refused {lines:?} — {e}"),
            Reply::Docs(back) => {
                assert_eq!(back.len(), 1, "{what}");
                assert_eq!(back[0], lines, "{what}");
                assert_eq!(join_lines(&back[0]), text, "{what}");
            }
        }
    }
}

/// **The harness can see a rewrite.** `no_file_is_silently_rewritten` passes
/// today, and a comparison that cannot fail passes today too. So: hand
/// `round_trip` a document together with an "original" that differs from it by
/// one line, and check it says so, at that line, naming that document. Without
/// this the green tick above would be worth nothing.
#[test]
fn the_harness_can_see_a_rewrite() {
    let d = Doc {
        path: "backlog.md".into(),
        lines: vec!["# Untied".into(), "- [ ] 2 30m Claim ^a1".into(), "".into()],
        region: None,
    };
    // what the kernel will return is the document above; claim it went in with
    // a different second line
    let pretend_original = "# Untied\n- [x] 2 30m Claim ^a1\n".to_string();
    match round_trip(&[d], &[pretend_original]) {
        Outcome::Differs { doc, line, went_in, came_out } => {
            assert_eq!(doc, "backlog.md");
            assert_eq!(line, 2);
            assert_eq!(went_in, "- [x] 2 30m Claim ^a1");
            assert_eq!(came_out, "- [ ] 2 30m Claim ^a1");
        }
        other => panic!("the rewrite detector missed a changed line: {other:?}"),
    }

    // and a document whose line *count* changed, which is the other way bytes
    // can be lost
    let d = Doc { path: "backlog.md".into(), lines: vec!["a".into()], region: None };
    match round_trip(&[d], &["a\nb".to_string()]) {
        Outcome::Differs { line, came_out, .. } => {
            assert_eq!(line, 2);
            assert_eq!(came_out, "<end of file>");
        }
        other => panic!("the rewrite detector missed a dropped line: {other:?}"),
    }
}

/// The corpus is what it claims to be: the fixture trees copied off `main`,
/// still UTF-8, still there. A harness that measures an empty directory reports
/// a perfect score.
#[test]
fn the_corpus_is_present() {
    let root = corpus_root();
    assert!(root.is_dir(), "{} is missing", root.display());
    let plans = plans();
    assert_eq!(
        plans.len(),
        5,
        "expected the five fixture plans from main, found {:?}",
        plans.iter().map(|p| p.file_name().unwrap().to_string_lossy().to_string()).collect::<Vec<_>>()
    );
    let total: usize = plans.iter().map(|p| markdown_files(p).len()).sum();
    assert_eq!(total, 37, "expected 37 Markdown files in the corpus, found {total}");
    assert!(
        Path::new(&root.join("PROVENANCE.md")).is_file(),
        "kernel/corpus/PROVENANCE.md records where these files came from; it is missing"
    );
}
