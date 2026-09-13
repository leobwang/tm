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
//! ## Whole trees only (the owner's D6, 2026-09-13)
//!
//! Every request is a **whole plan tree**, which is how the host loads it. A
//! parent is read off its line since D6, and a link to an id the request does not
//! carry refuses the tree (`itemCheck: danglingParent`); a week file's `@O2` names
//! a month outcome, so a week file handed over alone no longer loads. The owner
//! accepted that the harness changes with it. So each plan is loaded **once**, and
//! a `file` row is **that file inside its plan's whole-tree load**: `ok` when the
//! plan loads and the file comes back byte for byte, `differs` when the plan loads
//! and the file's bytes changed, and `reject` — carrying the plan's refusal — when
//! the plan does not load. Until D6 a `file` row loaded the file on its own, so a
//! file of a refused plan could score `ok`; four of `plan-conflicts/`'s nine did,
//! and the score moved 33/37 → 29/37 with no file outside `plan-conflicts/` changing
//! (kernel/README.md, "Stage 4 final", step 3).
//!
//! Run `cargo test --test corpus -- --nocapture` for the file-by-file table,
//! including, for each plan that does not load, its refusals peeled one at a
//! time: the smallest set of item lines across the tree that still reproduces a
//! refusal, named, then removed, until the tree loads.

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

/// One document's bytes against what came back for it.
fn compare(doc: &str, original: &str, back: &[String]) -> Outcome {
    let out = join_lines(back);
    if out == original {
        return Outcome::Ok;
    }
    let a: Vec<&str> = original.split('\n').collect();
    let b: Vec<&str> = out.split('\n').collect();
    let n = a.len().min(b.len());
    for i in 0..n {
        if a[i] != b[i] {
            return Outcome::Differs {
                doc: doc.to_string(),
                line: i + 1,
                went_in: a[i].to_string(),
                came_out: b[i].to_string(),
            };
        }
    }
    Outcome::Differs {
        doc: doc.to_string(),
        line: n + 1,
        went_in: a.get(n).unwrap_or(&"<end of file>").to_string(),
        came_out: b.get(n).unwrap_or(&"<end of file>").to_string(),
    }
}

/// Push a document set through the boundary **once** and compare each document
/// byte for byte: one outcome per document, every one of them the plan's refusal
/// when the set does not load.
fn round_trip_each(docs: &[Doc], originals: &[String]) -> Vec<Outcome> {
    match ask(docs) {
        Reply::Err(e) => docs.iter().map(|_| Outcome::Reject(e.clone())).collect(),
        Reply::Docs(back) => {
            assert_eq!(
                back.len(),
                docs.len(),
                "the kernel returned {} documents for {} requested",
                back.len(),
                docs.len()
            );
            back.iter()
                .enumerate()
                .map(|(k, lines)| compare(&docs[k].path, &originals[k], lines))
                .collect()
        }
    }
}

/// The whole set's outcome: its refusal, or its first rewritten document, or `Ok`.
fn round_trip(docs: &[Doc], originals: &[String]) -> Outcome {
    let each = round_trip_each(docs, originals);
    each.iter()
        .find(|o| **o != Outcome::Ok)
        .cloned()
        .unwrap_or(Outcome::Ok)
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

/// One refusal of a refused plan: the item lines that reproduce it, as
/// (file, 1-based line, text), the kernel's name for it, the parents they need,
/// and the lines struck out with it because they name an id only it carried.
#[derive(Debug, Clone)]
struct Fault {
    lines: Vec<(String, usize, String)>,
    err: String,
    /// the parents those lines name, kept so the refusal is the file's and not one
    /// a missing parent manufactured
    context: Vec<(String, usize, String)>,
    struck_with_it: Vec<(String, usize, String)>,
}

/// The ids a line carries: its `^id` words.
fn ids_of(l: &str) -> Vec<String> {
    l.split_whitespace()
        .filter_map(|w| w.strip_prefix('^'))
        .filter(|w| !w.is_empty())
        .map(str::to_string)
        .collect()
}

/// The ids a line names: its `@parent` and its `after:^id` dependencies.
fn names_of(l: &str) -> Vec<String> {
    let mut v = Vec::new();
    for w in l.split_whitespace() {
        if let Some(p) = w.strip_prefix('@') {
            if !p.is_empty() {
                v.push(p.to_string());
            }
        }
        if let Some(d) = w.strip_prefix("after:") {
            v.extend(d.split(',').filter_map(|x| x.strip_prefix('^')).map(str::to_string));
        }
    }
    v
}

/// What a refusal *is*, for deciding whether a smaller tree still reproduces it:
/// the kernel's answer, except that a `badLine`'s line number is dropped — striking
/// an item line above it renumbers the line and does not change the refusal.
fn refusal_key(e: &str) -> String {
    match parse_json(e) {
        Ok(j) => match j.get("badLine") {
            Some(b) => format!(
                "badLine {} {}",
                b.get("path").and_then(J::str).unwrap_or_default(),
                b.get("why").and_then(J::str).unwrap_or_default()
            ),
            None => e.to_string(),
        },
        Err(_) => e.to_string(),
    }
}

/// **Why a whole plan was refused, one refusal at a time.** Only item lines are
/// ever removed — prose is context (a heading decides a section, and §4.2's
/// section discipline is checked against it) — and every request is the whole
/// tree (D6).
///
/// Repeatedly: take the refusal the tree gives now, and shrink the item lines still
/// standing until nothing more can be removed with **that** refusal surviving
/// (delta-debugging to a fixed point). A line is removed **together with every
/// kept line that names it**, transitively (`@parent`, `after:^id`): removing a
/// parent alone would manufacture a `danglingParent` the file does not have. What
/// is left is the refusal's lines and the parents they need. Strike out the lines
/// no other kept line names (the whole set, for a cycle, where every line is named)
/// — with every standing line that names an id only they carried, for the same
/// reason — and ask again, until the tree loads or a refusal survives with no item
/// line left.
fn peel_faults(files: &[(String, String)]) -> Vec<Fault> {
    let split: Vec<Vec<String>> = files.iter().map(|(_, t)| split_lines(t)).collect();
    let text = |q: (usize, usize)| split[q.0][q.1].as_str();
    // `q` and every line of `among` that names it, transitively
    let closure = |q: (usize, usize), among: &[(usize, usize)]| -> Vec<(usize, usize)> {
        let mut set = vec![q];
        loop {
            let ids: Vec<String> = set.iter().flat_map(|&x| ids_of(text(x))).collect();
            let more: Vec<(usize, usize)> = among
                .iter()
                .copied()
                .filter(|o| !set.contains(o) && names_of(text(*o)).iter().any(|n| ids.contains(n)))
                .collect();
            if more.is_empty() {
                return set;
            }
            set.extend(more);
        }
    };
    let named = |q: (usize, usize), among: &[(usize, usize)]| {
        ids_of(text(q))
            .iter()
            .any(|id| among.iter().any(|&o| o != q && names_of(text(o)).contains(id)))
    };
    let attempt = |keep: &[(usize, usize)]| -> Option<String> {
        let docs: Vec<Doc> = files
            .iter()
            .enumerate()
            .map(|(f, (rel, _))| Doc {
                path: rel.clone(),
                lines: (0..split[f].len())
                    .filter(|&i| !looks_like_item(&split[f][i]) || keep.contains(&(f, i)))
                    .map(|i| split[f][i].clone())
                    .collect(),
                region: region_of(rel),
            })
            .collect();
        match ask(&docs) {
            Reply::Err(e) => Some(e),
            Reply::Docs(_) => None,
        }
    };
    let cite = |qs: &[(usize, usize)]| -> Vec<(String, usize, String)> {
        qs.iter().map(|&(f, i)| (files[f].0.clone(), i + 1, split[f][i].clone())).collect()
    };

    let mut standing: Vec<(usize, usize)> = split
        .iter()
        .enumerate()
        .flat_map(|(f, ls)| (0..ls.len()).filter(|&i| looks_like_item(&ls[i])).map(move |i| (f, i)))
        .collect();
    let mut faults = Vec::new();
    while let Some(first) = attempt(&standing) {
        let key = refusal_key(&first);
        let mut keep = standing.clone();
        let mut err = first;
        loop {
            let mut changed = false;
            let mut i = 0;
            while i < keep.len() {
                let gone = closure(keep[i], &keep);
                let trial: Vec<(usize, usize)> = keep.iter().copied().filter(|q| !gone.contains(q)).collect();
                match attempt(&trial) {
                    Some(e) if refusal_key(&e) == key => {
                        keep = trial;
                        err = e;
                        changed = true;
                    }
                    _ => i += 1,
                }
            }
            if !changed {
                break;
            }
        }
        if keep.is_empty() {
            faults.push(Fault { lines: vec![], err, context: vec![], struck_with_it: vec![] });
            break;
        }
        let leaves: Vec<(usize, usize)> = keep.iter().copied().filter(|&q| !named(q, &keep)).collect();
        let mut struck = if leaves.is_empty() { keep.clone() } else { leaves.clone() };
        let own = struck.clone();
        loop {
            let rest: Vec<(usize, usize)> = standing.iter().copied().filter(|q| !struck.contains(q)).collect();
            let gone: Vec<String> = struck
                .iter()
                .flat_map(|&q| ids_of(text(q)))
                .filter(|id| !rest.iter().any(|&o| ids_of(text(o)).contains(id)))
                .collect();
            let more: Vec<(usize, usize)> = rest
                .into_iter()
                .filter(|&o| names_of(text(o)).iter().any(|n| gone.contains(n)))
                .collect();
            if more.is_empty() {
                break;
            }
            struck.extend(more);
        }
        standing.retain(|q| !struck.contains(q));
        let context: Vec<(usize, usize)> = keep.iter().copied().filter(|q| !own.contains(q)).collect();
        let also: Vec<(usize, usize)> = struck.iter().copied().filter(|q| !own.contains(q)).collect();
        faults.push(Fault { lines: cite(&own), err, context: cite(&context), struck_with_it: cite(&also) });
    }
    faults
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

        // the whole plan at once, which is how the host loads it and the only
        // request this harness makes (D6): a week line's `@O2` resolves against
        // the month file it came with, and cross-file duplicate ids and the two
        // lines of a demotion are only visible here
        let docs: Vec<Doc> = files.iter().map(|(rel, text)| doc_of(rel, text)).collect();
        let originals: Vec<String> = files.iter().map(|(_, t)| t.clone()).collect();
        let each = round_trip_each(&docs, &originals);
        let whole = each.iter().find(|o| **o != Outcome::Ok).cloned().unwrap_or(Outcome::Ok);
        for ((rel, _), outcome) in files.iter().zip(each) {
            rows.push(Row { kind: "file", name: format!("{plan_name}/{rel}"), outcome });
        }
        rows.push(Row { kind: "plan", name: plan_name, outcome: whole });
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

    // for every plan that did not load, its refusals peeled one at a time
    let mut printed_header = false;
    for r in rows.iter().filter(|r| r.kind == "plan" && matches!(r.outcome, Outcome::Reject(_))) {
        if !printed_header {
            println!("\n  why each plan was refused (its refusals one at a time: the fewest item lines across the tree that still fail, prose kept)\n");
            printed_header = true;
        }
        let files = markdown_files(&corpus_root().join(&r.name));
        let faults = peel_faults(&files);
        println!("  {} — {} refusal(s)", r.name, faults.len());
        for f in &faults {
            println!("      {}", f.err);
            if f.lines.is_empty() {
                println!("        (no item line; the documents themselves are refused)");
            }
            for (rel, n, text) in &f.lines {
                println!("        {rel}:{n:<3} {text}");
            }
            for (rel, n, text) in &f.context {
                println!("          (kept, a line above names it) {rel}:{n} {text}");
            }
            for (rel, n, text) in &f.struck_with_it {
                println!("          (struck with it, it names an id only the lines above carry) {rel}:{n} {text}");
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
         # Whole trees only (the owner's D6): each plan is loaded once, and a `file`\n\
         # row is that file inside its plan's whole-tree load -- `ok` when the plan\n\
         # loads and the file comes back byte for byte, `reject` with the plan's\n\
         # refusal when it does not.  A file is never loaded on its own.\n\
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

/// **Why a file is never loaded on its own any more** (the owner's D6). `plan-basic`'s
/// week file names the month's outcomes (`@O1`, `@O2`, `@O3`): handed over alone it
/// is refused `danglingParent`, inside its whole tree it round-trips. Before D6 the
/// parent was never read, and the file loaded both ways.
#[test]
fn a_week_file_names_its_parents_in_another_file() {
    let plan = corpus_root().join("plan-basic");
    let files = markdown_files(&plan);
    let (rel, text) = files
        .iter()
        .find(|(rel, _)| rel == "week/2026-W37.md")
        .expect("plan-basic/week/2026-W37.md is missing");
    assert!(text.contains("@O2 ^m2"), "the fixture no longer names a month outcome");
    match round_trip(&[doc_of(rel, text)], std::slice::from_ref(text)) {
        Outcome::Reject(e) => assert_eq!(e, r#"{"itemCheck":"danglingParent"}"#),
        other => panic!("a week file naming month outcomes loaded alone: {other:?}"),
    }
    let docs: Vec<Doc> = files.iter().map(|(r, t)| doc_of(r, t)).collect();
    let originals: Vec<String> = files.iter().map(|(_, t)| t.clone()).collect();
    assert_eq!(round_trip(&docs, &originals), Outcome::Ok);
}

/// **`plan-conflicts/`'s parent defects refuse the whole plan, each by its own
/// name** — which is what the fixture exists for (`PROVENANCE.md`: "a `@ghost`
/// parent", "a two-item `@parent` cycle"). Before D6 neither could fire: the
/// kernel never read a parent. Peeled from the whole tree, prose kept, the
/// `@ghost` line alone reproduces `danglingParent` and the ouroboros pair alone
/// reproduces `parentCycle`.
#[test]
fn the_conflicts_plan_refuses_its_parent_defects_by_name() {
    let files = markdown_files(&corpus_root().join("plan-conflicts"));
    let faults = peel_faults(&files);
    let has = |err: &str, want: &[&str]| {
        faults.iter().any(|f| {
            f.err == err
                && f.lines.len() == want.len()
                && f.lines.iter().zip(want).all(|((rel, _, text), w)| rel == "week/2026-W37.md" && text.contains(w))
        })
    };
    assert!(
        has(r#"{"itemCheck":"danglingParent"}"#, &["@ghost ^q1"]),
        "the @ghost parent is not refused by name on its own: {faults:#?}"
    );
    assert!(
        has(r#"{"itemCheck":"parentCycle"}"#, &["@y2 ^y1", "@y1 ^y2"]),
        "the @parent cycle is not refused by name on its own: {faults:#?}"
    );
}
