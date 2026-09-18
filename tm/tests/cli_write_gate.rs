//! **The one shared write gate** — the owner's **D35**, README **gap 584**.
//!
//! Every *kernel-backed* write has always been gated: `kernel_bridge::apply`
//! sends the whole tree, and a refusal writes nothing. The **host-only** write
//! paths — the ones gap 41 (`title=`, `p=`, `state=`, `--set`, `--unset ci`),
//! gap 5 (an id-less line) and §4.1's positional-slot surgery left behind —
//! never asked the kernel anything, so a user could keep editing a tree that
//! `tm plan`, `tm now` and `tm review` all refused. Driven on a tree with one
//! duplicated routine line: `tm edit ^d1 'title=…'` rewrote its file and
//! exited **0**, while `tm check` exited 2 on the same bytes.
//!
//! `kernel_bridge::gate` is now the one asker for all of them, over
//! `kernel_bridge::tree_refusal`, which `tm check` also reads. These tests are
//! about the three things that can go wrong with it:
//!
//! 1. it does not actually refuse (`every_write_verb_refuses_…`);
//! 2. it refuses without saying *what* or *where*
//!    (`a_refused_write_names_both_lines_…`);
//! 3. it is **missing** from a write path — which is exactly how gap 584
//!    happened, so `every_undo_recording_path_is_accounted_for` is a source
//!    guard rather than a behaviour test, and a new write verb fails it until
//!    its author says how that verb reaches the kernel.
//!
//! And two things that must **not** change: `tm undo` is deliberately ungated,
//! because it is the way *out* of a tree the kernel refuses, and `tm check`
//! stays D18/gap 145's one tolerant verb.

mod cli_common;

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use cli_common::Tm;

/// The duplicated routine line the kernel refuses the tree for: `routines.md`
/// gets a ninth line repeating `laundry`, so `laundry` is two store keys in
/// one file (D31's title keying) and the load is `dupId`, naming both.
const DOUBLED: &str = "- laundry    win:09:00-21:00 dur:30m every:week on-miss:persist\n";

/// Every file under the plan directory by relative path — the plan files,
/// `.tm/log.jsonl`, `.tm/state.json` and `.tm/undo.json` — **except**
/// `.tm/cache/`.
///
/// The cache is excluded because it is derived and rebuildable (the owner's
/// **D13**): `Ctx::load` resumes or writes the replay checkpoint before the
/// verb's body runs at all, so it moves under `tm check` too, and a verb that
/// refused has still not written anything a user typed or can lose.
///
/// Bytes, not text: the point of the assertion is that **nothing** moved, and
/// a comparison that went through `String` could not see a file the verb
/// rewrote with different bytes for the same characters.
fn snapshot(tm: &Tm) -> BTreeMap<String, Vec<u8>> {
    fn walk(root: &Path, dir: &Path, acc: &mut BTreeMap<String, Vec<u8>>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(root, &path, acc);
            } else if let Ok(bytes) = fs::read(&path) {
                let rel = path.strip_prefix(root).expect("under root").display().to_string();
                if rel.replace('\\', "/").starts_with(".tm/cache/") {
                    continue;
                }
                acc.insert(rel, bytes);
            }
        }
    }
    let mut acc = BTreeMap::new();
    walk(&tm.plan, &tm.plan, &mut acc);
    acc
}

/// A `plan-basic` tree with `setup` run on it *while it is still sound*, then
/// broken by the duplicated line. Returns the tree and its byte snapshot taken
/// **after** the break, so a later comparison is against the tree the verb was
/// handed.
fn broken_after(setup: &[&[&str]]) -> (Tm, BTreeMap<String, Vec<u8>>) {
    let tm = Tm::new();
    for args in setup {
        let out = tm.run(args);
        assert_eq!(out.code, 0, "setup {args:?} failed: {}{}", out.stdout, out.stderr);
    }
    let path = tm.plan.join("routines.md");
    let doubled = format!("{}{DOUBLED}", tm.read("routines.md"));
    fs::write(&path, &doubled).expect("write routines.md");
    let before = snapshot(&tm);
    (tm, before)
}

/// **Every write verb, with the setup its own preconditions need.**
///
/// Found by walking `cli::run`'s dispatch table from `main` down rather than
/// by listing the ones that came to mind — which is how gap 584 was missed in
/// the first place: gap 576 drove every verb that addresses an item *by
/// title*, and the defect was in the one that addresses it by `^id`.
///
/// `tm init` is not here (there is no tree yet), nor `tm check` (D18/gap 145's
/// tolerant verb — its own tests), nor `tm undo` (deliberately ungated, below),
/// nor the read verbs, which refuse already.
const WRITE_VERBS: &[(&[&[&str]], &[&str])] = &[
    (&[], &["wake", "07:15"]),
    (&[], &["arrive", "lounge"]),
    (&[], &["start", "^a1"]),
    (&[], &["done", "^a1"]),
    (&[&["start", "^a1"]], &["extend", "10m"]),
    (&[&["start", "^a1"]], &["stop"]),
    (&[], &["break"]),
    (&[&["start", "^a1"]], &["interrupt"]),
    (&[&["start", "^a1"], &["interrupt"]], &["resume"]),
    (&[&["start", "^a1"]], &["pause"]),
    (&[], &["energy", "3"]),
    (&[], &["idle", "w"]),
    (&[], &["add", "- [ ] 2 30m A new thing"]),
    (&[], &["edit", "^d2", "title=Renamed by the test"]),
    (&[], &["edit", "^d2", "ci=3"]),
    (&[], &["move", "^a1", "week"]),
    (&[], &["rank", "^a1", "1"]),
    (&[], &["demote", "^m4"]),
    (&[&["demote", "^m4"]], &["readopt", "^m4"]),
    (&[], &["drop", "^a1"]),
    (&[], &["event", "reply"]),
    (&[], &["skip", "lunch"]),
    (&[], &["routine", "done", "lunch"]),
    (&[], &["close", "day"]),
    (&[], &["sync-cal"]),
    (&[], &["review", "day", "--write"]),
    (&[], &["model", "--fit"]),
];

/// **No verb that writes reports success on a tree the kernel refuses, and
/// none of them writes a byte** (D35, gap 584).
///
/// The assertion is over the *whole* directory, `.tm/log.jsonl`,
/// `.tm/state.json` and `.tm/undo.json` included, because the defect this
/// replaces was not only about the plan files: gap 115's three verbs wrote
/// `state.json` and the log before the kernel ever saw the tree.
#[test]
fn every_write_verb_refuses_a_tree_the_kernel_cannot_load_and_writes_nothing() {
    for (setup, args) in WRITE_VERBS {
        let (tm, before) = broken_after(setup);
        let out = tm.run(args);
        assert_ne!(out.code, 0, "{args:?} exited 0 on a tree the kernel refuses: {}{}", out.stdout, out.stderr);
        // The refusal is the kernel's own, with D32's two positions on it —
        // one spelling of the sentence, whichever path the verb took.
        assert!(out.stderr.contains("dupId") || out.stderr.contains("routines.md:7"), "{args:?}: {}", out.stderr);
        let after = snapshot(&tm);
        assert_eq!(
            before.keys().collect::<Vec<_>>(),
            after.keys().collect::<Vec<_>>(),
            "{args:?} added or removed a file"
        );
        for (path, bytes) in &before {
            assert_eq!(
                bytes,
                after.get(path).expect("same key set"),
                "{args:?} wrote {path}"
            );
        }
    }
}

/// **The same verbs all still work on a sound tree** — the gate is a gate, not
/// a blanket refusal, and this is the half `tm check`'s own D32 wiring did not
/// need. Without it, a `gate` that returned an error unconditionally would pass
/// every assertion above.
#[test]
fn every_write_verb_still_works_on_a_tree_the_kernel_loads() {
    for (setup, args) in WRITE_VERBS {
        let tm = Tm::new();
        for s in *setup {
            let out = tm.run(s);
            assert_eq!(out.code, 0, "setup {s:?}: {}{}", out.stdout, out.stderr);
        }
        let out = tm.run(args);
        assert_eq!(out.code, 0, "{args:?} failed on a sound tree: {}{}", out.stdout, out.stderr);
    }
}

/// **A refused write names the file and the line, and says the write did not
/// happen** (D35's item 5, over D32's widened `dupId`).
///
/// Driven on a **swept** tree, so §6.3's automatic close has nothing to do and
/// its own refusal is not what is being read: the sentence under test is the
/// gate's.
#[test]
fn a_refused_write_names_both_lines_and_says_nothing_was_written() {
    let tm = Tm::new();
    // Two sound runs first: the second finds nothing left to close, so the
    // automatic close prints nothing and cannot be mistaken for the gate.
    tm.ok(&["plan"]);
    tm.ok(&["plan"]);
    let path = tm.plan.join("routines.md");
    let doubled = format!("{}{DOUBLED}", tm.read("routines.md"));
    fs::write(&path, &doubled).expect("write routines.md");

    let out = tm.run(&["edit", "^d2", "title=Renamed by the test"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(!out.stderr.contains("automatic close"), "the close spoke, not the gate: {}", out.stderr);
    // What is wrong, and where — both placements, in path-then-line order.
    assert!(out.stderr.contains("dupId"), "{}", out.stderr);
    assert!(out.stderr.contains("routines.md:7"), "{}", out.stderr);
    assert!(out.stderr.contains("routines.md:9"), "{}", out.stderr);
    // What it means for the command that was typed.
    assert!(out.stderr.contains("nothing was written"), "{}", out.stderr);
    assert!(out.stderr.contains("`tm edit`"), "{}", out.stderr);
    assert!(out.stderr.contains("tm undo"), "{}", out.stderr);

    // The same facts reach a script, keyed, not only the sentence.
    let json = tm.run(&["--json", "edit", "^d2", "title=Renamed by the test"]);
    let doc: serde_json::Value = serde_json::from_str(&json.stderr).expect("a json failure document");
    assert_eq!(doc["detail"]["refusal"], "dupId", "{doc}");
    assert_eq!(doc["detail"]["refusedWrite"], "edit", "{doc}");
    assert_eq!(doc["detail"]["a"]["path"], "routines.md", "{doc}");
    assert_eq!(doc["detail"]["a"]["line"], 7, "{doc}");
    assert_eq!(doc["detail"]["b"]["line"], 9, "{doc}");
}

/// **`tm undo` is deliberately NOT gated**, and this is the test that says so
/// out loud: it is the way *out* of a tree the kernel refuses, and a gate on it
/// would lock the user inside one.
///
/// The tree here is broken by a write `tm undo` itself cannot take back (the
/// duplicated line was never written by a verb), so what is checked is that
/// `undo` still reverses the **previous** command on such a tree.
#[test]
fn tm_undo_is_not_gated_so_a_refused_tree_can_still_be_backed_out_of() {
    let tm = Tm::new();
    tm.ok(&["edit", "^d2", "ci=3"]);
    let after_edit = tm.read("backlog.md");
    let path = tm.plan.join("routines.md");
    let doubled = format!("{}{DOUBLED}", tm.read("routines.md"));
    fs::write(&path, &doubled).expect("write routines.md");

    // Every writing verb refuses this tree now.
    assert_ne!(tm.run(&["edit", "^d2", "ci=4"]).code, 0);
    // `tm undo` does not.
    let out = tm.run(&["undo"]);
    assert_eq!(out.code, 0, "undo was refused on a broken tree: {}{}", out.stdout, out.stderr);
    assert_ne!(tm.read("backlog.md"), after_edit, "undo took nothing back");
    assert!(tm.line("backlog.md", "d2").contains(" 5 "), "the ci was not restored: {}", tm.line("backlog.md", "d2"));
}

// ---------------------------------------------------------------------------
// The source guard
// ---------------------------------------------------------------------------

/// How a write path reaches the kernel, as a string that must appear in the
/// body of the function that records the undo entry.
///
/// `apply` and `run_explained` are the kernel-backed writes: the kernel sees
/// the whole tree as part of doing the work, and a refusal writes nothing, so
/// a second load would be paid for nothing. `gate` is D35's, for the paths
/// that never reach the kernel at all.
const APPLY: &str = "kernel_bridge::apply(";
const GATE: &str = "kernel_bridge::gate(";
const CLOSE: &str = "closing::run_explained(";
const PREFLIGHT: &str = "preflight(&ctx,";

/// **Every function in the binary that records an undo entry, and how it asks
/// the kernel.** One row per function, not per call site: a function with two
/// branches carries the marker each branch uses.
///
/// This is the guard gap 584 needed and did not have. It is a *set* guard, in
/// the shape §12's one-reader grep uses: a new function that calls
/// `Recorder::start` is not in this table, so the test fails and its author has
/// to say how that verb reaches the kernel — rather than the question never
/// being asked, which is what happened to `tm edit`'s host-only branch.
///
/// **What it does not catch**, said plainly: a function that carries a marker
/// on one branch and writes on another. That is a judgment no grep makes, and
/// `every_write_verb_refuses_a_tree_the_kernel_cannot_load_and_writes_nothing`
/// above is what covers it — by driving the verbs.
const UNDO_RECORDERS: &[(&str, &str, &[&str])] = &[
    ("cli/day.rs", "wake", &[GATE]),
    ("cli/day.rs", "arrive", &[PREFLIGHT]),
    ("cli/day.rs", "start", &[GATE]),
    ("cli/day.rs", "done", &[GATE]),
    ("cli/day.rs", "extend", &[GATE]),
    ("cli/day.rs", "stop", &[GATE]),
    ("cli/day.rs", "take_break", &[GATE]),
    ("cli/day.rs", "interrupt", &[GATE]),
    ("cli/day.rs", "resume", &[PREFLIGHT]),
    ("cli/day.rs", "pause", &[GATE]),
    ("cli/day.rs", "energy", &[PREFLIGHT]),
    ("cli/day.rs", "idle", &[GATE]),
    ("cli/items.rs", "add_kernel", &[APPLY]),
    ("cli/items.rs", "add", &[GATE]),
    ("cli/items.rs", "edit", &[GATE]),
    ("cli/items.rs", "edit_kernel", &[APPLY]),
    ("cli/items.rs", "move_item", &[GATE, APPLY]),
    ("cli/items.rs", "rank", &[GATE, APPLY]),
    ("cli/items.rs", "demote", &[APPLY]),
    ("cli/items.rs", "readopt", &[GATE, APPLY]),
    ("cli/items.rs", "drop_item", &[GATE, APPLY]),
    ("cli/items.rs", "event", &[GATE]),
    ("cli/items.rs", "skip", &[GATE]),
    ("cli/items.rs", "routine", &[GATE]),
    ("cli/lifecycle.rs", "close", &[CLOSE]),
    ("cli/lifecycle.rs", "sync_cal", &[GATE]),
    ("cli/lifecycle.rs", "review", &[GATE]),
    ("cli/lifecycle.rs", "model", &[GATE]),
    ("tui/mod.rs", "mutate", &[GATE]),
    ("tui/mod.rs", "note", &[GATE]),
    ("tui/mod.rs", "set_location", &[GATE]),
];

/// The files the guard reads — every source file in the binary, so a write
/// path added in a new module is found too.
fn source_files() -> Vec<(String, String)> {
    fn walk(root: &Path, dir: &Path, acc: &mut Vec<(String, String)>) {
        for entry in fs::read_dir(dir).expect("read_dir").flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(root, &path, acc);
            } else if path.extension().is_some_and(|e| e == "rs") {
                let rel = path.strip_prefix(root).expect("under src").display().to_string();
                acc.push((rel, fs::read_to_string(&path).expect("read source")));
            }
        }
    }
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    let mut acc = Vec::new();
    walk(&src, &src, &mut acc);
    acc.sort();
    acc
}

/// Split one source file into `(function name, body)` at its column-0 `fn`
/// lines. Every `Recorder::start` call site in the binary is inside such a
/// function; the guard asserts that below, so a site that moved into an `impl`
/// block fails rather than disappearing.
fn top_level_fns(text: &str) -> Vec<(String, String)> {
    let starts: Vec<(usize, String)> = text
        .lines()
        .enumerate()
        .filter_map(|(i, l)| {
            let rest = l
                .strip_prefix("pub(crate) fn ")
                .or_else(|| l.strip_prefix("pub fn "))
                .or_else(|| l.strip_prefix("fn "))?;
            let name: String = rest.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
            Some((i, name))
        })
        .collect();
    let lines: Vec<&str> = text.lines().collect();
    starts
        .iter()
        .enumerate()
        .map(|(n, (i, name))| {
            let end = starts.get(n + 1).map_or(lines.len(), |(j, _)| *j);
            (name.clone(), lines[*i..end].join("\n"))
        })
        .collect()
}

#[test]
fn every_undo_recording_path_is_accounted_for() {
    let mut found: Vec<(String, String)> = Vec::new();
    for (rel, text) in source_files() {
        // Every call site is inside a column-0 function: if one is not, it
        // vanishes from `found` and the set comparison below says so.
        let sites = text.matches("Recorder::start(").count();
        let in_fns: usize = top_level_fns(&text)
            .iter()
            .map(|(_, body)| body.matches("Recorder::start(").count())
            .sum();
        assert_eq!(sites, in_fns, "{rel}: a `Recorder::start` call site is not in a column-0 fn");

        for (name, body) in top_level_fns(&text) {
            if !body.contains("Recorder::start(") {
                continue;
            }
            let rel = rel.replace('\\', "/");
            let Some((_, _, markers)) = UNDO_RECORDERS
                .iter()
                .find(|(f, n, _)| *f == rel && *n == name)
            else {
                panic!(
                    "{rel}::{name} records an undo entry and is not in `UNDO_RECORDERS` — \
                     say how it asks the kernel whether the tree still loads (D35, gap 584), \
                     then add its row"
                );
            };
            for marker in *markers {
                assert!(
                    body.contains(marker),
                    "{rel}::{name} is declared to reach the kernel through `{marker}` and does not"
                );
            }
            found.push((rel, name));
        }
    }
    let declared: Vec<(String, String)> = UNDO_RECORDERS
        .iter()
        .map(|(f, n, _)| ((*f).to_string(), (*n).to_string()))
        .collect();
    let mut found = found;
    found.sort();
    let mut declared = declared;
    declared.sort();
    assert_eq!(
        found, declared,
        "`UNDO_RECORDERS` and the sources disagree about which functions record an undo entry"
    );
}

/// **There is exactly one asker of "does the kernel load this tree"**
/// (AGENTS §5.3). `tree_refusal` is it; `tm check` and the write gate are its
/// two readers, and `Ctx::resolve_timeouts` is the third.
///
/// The question used to be asked two ways — `tm check` built its own request,
/// and `day::preflight` and `Ctx::resolve_timeouts` sent `apply(ctx, &[])`,
/// which is the same question through the machine that ends in a **write
/// step**. This fails if a fourth spelling appears.
#[test]
fn the_tree_load_question_has_one_asker() {
    let callers: Vec<String> = source_files()
        .into_iter()
        .filter(|(rel, text)| rel != "cli/kernel_bridge.rs" && text.contains("tree_refusal("))
        .map(|(rel, _)| rel)
        .collect();
    assert_eq!(
        callers,
        vec!["cli/ctx.rs".to_string(), "cli/lifecycle.rs".to_string()],
        "the readers of `tree_refusal` moved"
    );
    // And nothing outside the bridge builds the empty-command request by
    // hand. Code only: `lifecycle.rs`'s doc comment quotes the request's shape,
    // which is prose about the one asker and not a second one.
    for (rel, text) in source_files() {
        if rel == "cli/kernel_bridge.rs" {
            continue;
        }
        for line in text.lines().filter(|l| !l.trim_start().starts_with("//")) {
            assert!(
                !line.contains(r#""cmds": []"#) && !line.contains(r#""cmds":[]"#),
                "{rel} builds a load-the-tree request of its own: {line}"
            );
        }
    }
}
