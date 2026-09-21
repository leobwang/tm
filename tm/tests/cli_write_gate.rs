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
/// tolerant verb — its own tests, and `--fix-ids` has its own section below:
/// it asks the kernel about the tree its write **produces**, which is a
/// different question from the one `gate` asks), nor `tm undo` (deliberately
/// ungated, below), nor the read verbs, which refuse already.
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

// ---------------------------------------------------------------------------
// W-22 track A — README gap 1080: the reassurance is one rule, not a coin flip.
//
// D35's line was stamped by `kernel_bridge::gate` alone, and in `drop`, `move`,
// `readopt` and `demote` that call sits inside the **id-less** branch (D33:
// "the gate goes ahead of both, because this branch never reaches the kernel"),
// so an item that HAS an id went straight to `apply` and was refused with no
// stamp. Driven at one refusal on one tree: `rank`, `edit`, `skip`, `start`,
// `add` (inbox), `event`, `routine done`, `wake` and `break` printed the second
// line; `drop`, `demote`, `readopt`, `move`, `add --to` and `close day` printed
// only the kernel's sentence. `apply` now stamps too, and the rule it stamps by
// is the one definition of "does the kernel load this tree" — `tree_refusal`,
// asked only after a refusal — rather than a list of refusal names that would
// go stale the next time `Boundary.lean` gains an `LErr`.

/// The verb as D35's line spells it, from the argv the test sends. The first
/// word is enough to tell `tm drop` from `tm move`, and it is the word the
/// user typed; the rest (`close day`, `review --write`) is the verb's own
/// business and is read by the `--json` assertions below.
fn typed_verb(args: &[&str]) -> String {
    args[0].to_string()
}

/// **Every write verb says nothing was written, and says it in its own name**
/// (README gap 1080).
///
/// The enumeration is `WRITE_VERBS` — the same table gap 584's own test walks,
/// built by reading `cli::run`'s dispatch from `main` down — so a new write
/// verb is in this test the moment it is in that one. What the table cannot
/// see is a write path that never reaches the dispatch table at all; the
/// source guard `every_undo_recording_path_is_accounted_for` is the other half
/// of that, and neither can see a writer that records no undo entry and takes
/// no verb name (README gap 731's three).
///
/// Driven on a **swept** tree, like `a_refused_write_names_both_lines_…`: if
/// §6.3's automatic close speaks first, `CliError::report` suppresses the
/// repeat by design (gap 239) and this would be reading the close's sentence
/// instead of the verb's.
#[test]
fn every_write_verb_says_nothing_was_written_in_its_own_name() {
    for (setup, args) in WRITE_VERBS {
        let tm = Tm::new();
        tm.ok(&["plan"]);
        tm.ok(&["plan"]);
        for s in *setup {
            let out = tm.run(s);
            assert_eq!(out.code, 0, "setup {s:?}: {}{}", out.stdout, out.stderr);
        }
        let path = tm.plan.join("routines.md");
        let doubled = format!("{}{DOUBLED}", tm.read("routines.md"));
        fs::write(&path, &doubled).expect("write routines.md");

        let out = tm.run(args);
        assert_ne!(out.code, 0, "{args:?} exited 0: {}{}", out.stdout, out.stderr);
        assert!(
            !out.stderr.contains("automatic close"),
            "{args:?}: the close spoke, not the verb: {}",
            out.stderr
        );
        assert!(
            out.stderr.contains("nothing was written:"),
            "{args:?} refused without saying the write did not happen: {}",
            out.stderr
        );
        let verb = typed_verb(args);
        assert!(
            out.stderr.contains(&format!("`tm {verb}")),
            "{args:?}: the line does not name the verb that was typed: {}",
            out.stderr
        );
    }
}

/// **And it does NOT fire when the tree loads** (AGENTS §5.8: both directions).
///
/// `notDemoted` is a refusal about the *command* — the tree is sound, every
/// reading verb answers, and "every reading verb refuses this one too" would
/// be false. That is why the rule asks `tree_refusal` rather than stamping
/// every refusal `apply` returns.
#[test]
fn a_command_refusal_on_a_sound_tree_does_not_claim_the_tree_is_unloadable() {
    let tm = Tm::new();
    tm.ok(&["plan"]);
    tm.ok(&["plan"]);
    // `^m4` is live, not demoted: the kernel refuses the readopt by name.
    let out = tm.run(&["readopt", "^m4"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains("notDemoted"), "{}", out.stderr);
    assert!(
        !out.stderr.contains("nothing was written:"),
        "a command refusal claimed the tree cannot be loaded: {}",
        out.stderr
    );
    // And the tree really does still load, which is what makes the absence
    // right rather than merely quiet.
    tm.ok(&["check"]);

    let json = tm.run(&["--json", "readopt", "^m4"]);
    let doc: serde_json::Value =
        serde_json::from_str(&json.stderr).expect("a json failure document");
    assert_eq!(doc["detail"]["refusal"], "notDemoted", "{doc}");
    assert_eq!(doc["detail"]["refusedWrite"], serde_json::Value::Null, "{doc}");
}

/// **The kernel-backed half, keyed** — the same `--json` shape
/// `a_refused_write_names_both_lines_…` pins for a host-only path, for a verb
/// that reaches the kernel instead. `tm drop ^a1` takes `apply`, not `gate`.
#[test]
fn a_kernel_backed_write_stamps_refused_write_too() {
    let tm = Tm::new();
    tm.ok(&["plan"]);
    tm.ok(&["plan"]);
    let path = tm.plan.join("routines.md");
    let doubled = format!("{}{DOUBLED}", tm.read("routines.md"));
    fs::write(&path, &doubled).expect("write routines.md");

    let json = tm.run(&["--json", "drop", "^a1"]);
    let doc: serde_json::Value =
        serde_json::from_str(&json.stderr).expect("a json failure document");
    assert_eq!(doc["detail"]["refusal"], "dupId", "{doc}");
    assert_eq!(doc["detail"]["refusedWrite"], "drop", "{doc}");
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
/// `tm check --fix-ids` is the one write that cannot take `gate`: a tree
/// refused *for a missing `^id`* is the tree the flag exists to repair. It asks
/// the question D35 is actually about — does the tree this write **produces**
/// load? — against a `MemStore` mirror. Gap 675 landed that; D37 (gap 687) gave
/// the same path its `Recorder::start`, which is why this marker exists at all.
const FIX_IDS: &str = "kernel_bridge::fix_ids_refusal(";

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
    ("cli/lifecycle.rs", "check", &[FIX_IDS]),
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
    // And the body both of them share — `refusal_in`, which `fix_ids_refusal`
    // asks of a `MemStore` mirror (gap 675) — is the bridge's alone. A caller
    // outside it would be a second place deciding what "the tree" is.
    let inners: Vec<String> = source_files()
        .into_iter()
        .filter(|(rel, text)| rel != "cli/kernel_bridge.rs" && text.contains("refusal_in("))
        .map(|(rel, _)| rel)
        .collect();
    assert!(inners.is_empty(), "`refusal_in` is called outside the bridge: {inners:?}");
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

// ---------------------------------------------------------------------------
// `tm check --fix-ids` — the write the gate could not take (gap 675)
// ---------------------------------------------------------------------------

/// **`--fix-ids` writes, so it is a host-only write path** — and it went
/// ungated for four runs while the enumeration that was used to rule it out
/// keyed on `Recorder::start`, which `lifecycle::check` does not call.
///
/// Driven before the repair, on exactly this tree: it rewrote `backlog.md`,
/// printed the kernel's `dupId` beside the write, exited 2 on the errors, and
/// `tm undo` then said *"nothing to undo"*.
///
/// It cannot take `kernel_bridge::gate` — see the next test — so what is
/// asserted here is D35's actual sentence: **the tree the write produces must
/// load, or nothing is written.**
#[test]
fn fix_ids_writes_nothing_when_the_tree_it_would_write_is_still_refused() {
    let tm = Tm::new();
    // A refusal `--fix-ids` cannot repair: two `laundry` routine lines.
    let path = tm.plan.join("routines.md");
    let doubled = format!("{}{DOUBLED}", tm.read("routines.md"));
    fs::write(&path, &doubled).expect("write routines.md");
    // …and a line that really does need an id, so the flag has work to do.
    let backlog = tm.plan.join("backlog.md");
    let grown = format!("{}- [ ] 3 1b Thing with no id\n", tm.read("backlog.md"));
    fs::write(&backlog, &grown).expect("write backlog.md");
    let before = snapshot(&tm);

    let out = tm.run(&["check", "--fix-ids"]);
    assert_eq!(out.code, 2, "{}{}", out.stdout, out.stderr);

    // Nothing moved — the whole directory, bytes, `.tm/` included.
    let after = snapshot(&tm);
    assert_eq!(before.keys().collect::<Vec<_>>(), after.keys().collect::<Vec<_>>(), "--fix-ids added or removed a file");
    for (rel, bytes) in &before {
        assert_eq!(bytes, after.get(rel).expect("same key set"), "--fix-ids wrote {rel}");
    }
    assert!(!tm.read("backlog.md").contains("Thing with no id ^"), "an id was appended");

    // It says so, and it names the refusal that blocked it.
    assert!(out.stdout.contains("--fix-ids wrote nothing"), "{}", out.stdout);
    assert!(out.stdout.contains("dupId"), "{}", out.stdout);
    // **The blocking line is named.** The kernel stops at its first refusal, so
    // the tree on disk reports `badLine` on the id-less line — the very fault
    // the flag would have repaired — and without this the fault that actually
    // blocked the write would appear nowhere.
    assert!(out.stdout.contains("routines.md:7"), "{}", out.stdout);
    assert!(out.stdout.contains("routines.md:9"), "{}", out.stdout);

    // The same facts reach a script.
    let json = tm.run(&["--json", "check", "--fix-ids"]);
    let doc: serde_json::Value = serde_json::from_str(&json.stdout).expect("a json check document");
    assert_eq!(doc["fixed"].as_array().expect("fixed").len(), 0, "{doc}");
    assert!(doc["fix_refused"].as_str().expect("fix_refused").contains("dupId"), "{doc}");
}

/// **And the gate is not a blanket refusal**: a tree the kernel refuses *for a
/// missing `^id`* is precisely the tree `--fix-ids` exists to repair, so it must
/// still write there.
///
/// This is why `--fix-ids` cannot take `kernel_bridge::gate`, which asks about
/// the tree *before* the write: it would trap this user inside the refusal, the
/// same way a gate on `tm undo` would.
#[test]
fn fix_ids_is_still_the_way_out_of_a_tree_refused_for_a_missing_id() {
    let tm = Tm::new();
    let backlog = tm.plan.join("backlog.md");
    let grown = format!("{}- [ ] 3 1b Twin thing\n- [ ] 3 1b Twin thing\n", tm.read("backlog.md"));
    fs::write(&backlog, &grown).expect("write backlog.md");

    // The kernel refuses it now.
    let before = tm.run(&["check"]);
    assert_eq!(before.code, 2, "{}{}", before.stdout, before.stderr);
    assert!(before.stdout.contains("kernel-load"), "{}", before.stdout);

    // `--fix-ids` repairs it, and the tree loads afterwards.
    let out = tm.run(&["check", "--fix-ids"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stdout.contains("wrote nothing"), "{}", out.stdout);
    assert_eq!(out.stdout.matches(": assigned ^").count(), 2, "{}", out.stdout);
    let after = tm.run(&["check"]);
    assert_eq!(after.code, 0, "{}{}", after.stdout, after.stderr);
}

/// **D37, README gap 687: `--fix-ids` writes, so `tm undo` takes it back.**
///
/// `lifecycle::check` called no `Recorder::start` on any tree, ever, so an id
/// assignment could not be backed out by the verb the product tells users to
/// back out with. Driven before the repair, on the `--example` tree:
/// `tm check --fix-ids` printed `backlog.md:13: assigned ^n9gu`, exited **0**,
/// and `tm undo` answered *"nothing to undo"* with exit 1 — there was no
/// `.tm/undo.json` at all.
///
/// Three things, because an undo entry can be wrong in three ways: the bytes
/// have to come back, the **whole** tree has to come back (an entry that
/// restored the file and left `.tm/` behind would pass a one-file assertion),
/// and the stack has to be one entry deep afterwards rather than empty and
/// silently ignored.
#[test]
fn fix_ids_records_an_undo_entry_and_tm_undo_takes_the_ids_back() {
    let tm = Tm::new();
    let backlog = tm.plan.join("backlog.md");
    let grown = format!("{}- [ ] 3 1b Thing with no id\n", tm.read("backlog.md"));
    fs::write(&backlog, &grown).expect("write backlog.md");
    let before = snapshot(&tm);

    let out = tm.run(&["check", "--fix-ids"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(out.stdout.matches(": assigned ^").count(), 1, "{}", out.stdout);
    assert!(tm.read("backlog.md").contains("Thing with no id ^"), "no id was appended");

    // The entry exists, and it is this verb's.
    let stack: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(tm.plan.join(".tm/undo.json")).expect(
            "`--fix-ids` wrote no .tm/undo.json — D37, gap 687",
        ))
        .expect("an undo stack");
    let entries = stack["entries"].as_array().expect("entries");
    assert_eq!(entries.len(), 1, "{stack}");
    assert_eq!(entries[0]["verb"], "check", "{stack}");
    assert!(
        entries[0]["summary"].as_str().expect("summary").contains("--fix-ids"),
        "{stack}"
    );

    // `tm undo` takes it back, and says which verb it undid.
    let undo = tm.run(&["undo"]);
    assert_eq!(undo.code, 0, "{}{}", undo.stdout, undo.stderr);
    assert!(undo.stdout.starts_with("undid check (--fix-ids: 1 id assigned)"), "{}", undo.stdout);
    assert_eq!(tm.read("backlog.md"), grown, "the id was not taken off the line");

    // And the rest of the tree is where it was — **every plan file**, byte for
    // byte. The three files under `.tm/` are excluded by name and for a reason
    // each: `log.jsonl` is append-only and now carries the compensating event,
    // `undo.json` did not exist before and now holds the emptied stack, and
    // `state.json` is the runtime state the entry put back. Everything else
    // compares, so an entry that restored `backlog.md` and left another file
    // rewritten fails here.
    let after = snapshot(&tm);
    let housekeeping = |rel: &str| rel.replace('\\', "/").starts_with(".tm/");
    let plan_files: Vec<&String> = before.keys().filter(|r| !housekeeping(r)).collect();
    assert_eq!(plan_files.len(), 9, "{plan_files:?}");
    for rel in plan_files {
        assert_eq!(
            before.get(rel),
            after.get(rel),
            "undo left {rel} changed"
        );
    }
    // The fixture carries no `.tm/` at all, so the three that appeared are
    // exactly the three excluded above — and nothing else did.
    let new_keys: Vec<&String> = after.keys().filter(|r| !before.contains_key(*r)).collect();
    assert_eq!(
        new_keys,
        vec![".tm/log.jsonl", ".tm/state.json", ".tm/undo.json"],
        "a file nobody asked for"
    );
    // A verb that logged nothing still cancels itself by name (§10.1).
    let log = fs::read_to_string(tm.plan.join(".tm/log.jsonl")).expect("log");
    assert!(log.contains(r#""of":"verb:check""#), "{log}");

    // Nothing left to undo, and the stack is empty rather than absent.
    let again = tm.run(&["undo"]);
    assert_eq!(again.code, 1, "{}{}", again.stdout, again.stderr);
}

/// **A `--fix-ids` with no work records no entry**, so `tm undo` still reaches
/// the user's last real command instead of a no-op that shadows it. This is
/// `Recorder::finish`'s own rule — *"a command that changed nothing pushes
/// nothing"* — asserted here because D37 is the first time this verb can push.
#[test]
fn fix_ids_with_nothing_to_fix_records_nothing() {
    let tm = Tm::new();
    tm.ok(&["edit", "^d2", "ci=3"]);
    let out = tm.run(&["check", "--fix-ids"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert_eq!(out.stdout.matches(": assigned ^").count(), 0, "{}", out.stdout);

    let undo = tm.run(&["undo"]);
    assert_eq!(undo.code, 0, "{}{}", undo.stdout, undo.stderr);
    assert!(undo.stdout.starts_with("undid edit"), "{}", undo.stdout);
}

/// **`tm init --force` is exempt from the gate because it is PRESERVING, not
/// because "there is no tree yet"** (gap 680) — that reason was false, and a
/// reason that is false is the kind of thing the next enumeration inherits.
///
/// Driven: on a tree the kernel refuses, `tm init --force` exits 0 and creates a
/// horizon file. What makes that safe is that every file whose content is the
/// user's is `init::Mode::Preserve`, so **not one existing byte moves** and the
/// refusal is identical on both sides. The day `init` rewrites a plan file, it
/// owes the gate — and this test fails then.
#[test]
fn init_force_preserves_a_refused_tree() {
    let tm = Tm::new();
    let path = tm.plan.join("routines.md");
    let doubled = format!("{}{DOUBLED}", tm.read("routines.md"));
    fs::write(&path, &doubled).expect("write routines.md");
    let before = snapshot(&tm);
    let refused_before = tm.run(&["check"]);
    assert_eq!(refused_before.code, 2, "{}{}", refused_before.stdout, refused_before.stderr);

    let out = tm.run(&["init", "--force"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);

    // Every file that was there is byte-identical. New files may appear; a
    // changed one is the thing that would need the gate.
    let after = snapshot(&tm);
    for (rel, bytes) in &before {
        assert_eq!(
            Some(bytes),
            after.get(rel),
            "`tm init --force` rewrote {rel} on a tree the kernel refuses — it now owes the gate"
        );
    }
    // And the refusal is the same one, unchanged by the run.
    let refused_after = tm.run(&["check"]);
    assert_eq!(refused_after.stdout, refused_before.stdout, "`tm init --force` changed what the kernel says");
}
