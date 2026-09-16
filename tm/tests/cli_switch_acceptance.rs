//! **The switch's acceptance, landed before the switch** — design
//! `kernel/design/stage5/stage5-D9-D10-design.md` §14.6's **T9** and **T12**, under the owner's
//! **D19** (2026-09-16; AGENTS §4).
//!
//! S is one commit in which every verb begins reading the log through the kernel at once. D19
//! keeps that gate and makes it fit by landing everything separable **first**, green against the
//! **unswitched** binary. These are the instruments: eight of §14.6's ten T9 names (the other two
//! live in `cli_check_log.rs`, landed with D18 at `022317d`) and **T12**. They are S's acceptance,
//! so S cannot be claimed without them.
//!
//! **Every test here is written to hold on both sides of the switch**, which is the whole
//! mechanism. That means each one asserts the *observable invariant* the checkpoint exists to
//! preserve — the answers a verb gives — and never the mechanism's private shape. Today
//! `Ctx::replay_with` delegates to the Rust reader and the only thing under `.tm/cache/replay/` is
//! `tz.json` (`tz_table::wire_for`, D13); after S the same directory holds `ckpt.json` and the
//! sealed month files, and the *same assertions* then say the checkpoint was invalidated, deleted
//! or rebuilt correctly. A test that asserted "there is no checkpoint" would pass today and fail
//! at S, which is the opposite of what these are for.
//!
//! **Two of the ten cannot pass before the switch and are `#[ignore]`d rather than weakened**
//! (the brief's rule, and §5.12's): `an_unwritable_cache_rebuilds_in_memory_with_one_notice` needs
//! a notice no code emits yet — `kernel_log::unwritable_notice` has no caller in `tm/src` — and
//! `a_hand_undo_beyond_the_rebuild_bound_fails_by_name` needs `GenesisError::ReachTooFar`, which
//! has no call site until S (gap 120 part 3, D18 (iii)). Both carry their full post-switch body,
//! so S's acceptance is to **remove the attribute**, not to write the test.
//!
//! The W-6 ledger (`kernel/README.md`, "the W-6 audit repair") judged that seven of these "cannot
//! be written honestly before S" because `deleting_the_replay_cache_changes_nothing` "passes
//! vacuously today (nothing writes `.tm/cache/replay`)". Measured on this tree, the premise is
//! false: a capacity verb writes `.tm/cache/replay/tz.json` on its first run in a plan directory
//! (README, L8's behaviour row; `kernel_capacity.rs` calls `tz_table::wire_for(Some(&cache), ..)`),
//! so the deletion removes a real derived file and the rerun rebuilds it. D19 settles the rest.

mod cli_common;

#[path = "support/loggen.rs"]
#[allow(dead_code)]
mod loggen;

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use cli_common::Tm;

/// The instant most of these run at: three days after `energy-14d.jsonl`'s last line, so the log
/// carries days that are behind the ledger day — the ones a checkpoint seals after S.
const LATER: &str = "2026-09-10T09:00:00-05:00";
/// Inside the log's own last day: a command dated here is three days behind [`LATER`].
const INSIDE: &str = "2026-09-07T13:00:00-05:00";
/// `tm log`'s corpus bytes are taken at one pinned instant, because `--since` is relative to it.
const CORPUS_NOW: &str = "2026-09-15T09:00:00-05:00";
/// T12's instant: `model.json`'s `fitted` field is a date, so it is pinned rather than floating.
const FIT_NOW: &str = "2026-09-14T09:00:00-05:00";

/// The `--json` spellings compared whenever a test asks "did anything change?". Every one is a
/// read of the replay: the answer a verb gives is what a wrong checkpoint would move.
const JSON_SPELLINGS: &[&[&str]] = &[
    &["now"],
    &["plan"],
    &["log"],
    &["log", "--tail", "5"],
    &["log", "--since", "7d"],
    &["check"],
    &["review", "day"],
    &["review", "week"],
    &["review", "month"],
    &["model", "--show"],
    &["triage"],
];

/// What an undo must put back: the facts of the day the undone command touched — asked from a
/// **later** instant, so that after S they are read from a sealed day record through §11.1's
/// `Dates` scope rather than from the hot answer — beside today's own answers.
///
/// The three `tm log` views are deliberately absent. `tm log` prints the log's own lines, and an
/// undo **appends** its compensating event (§10.1) rather than editing one, so `tm log`'s answer
/// moves *correctly*. A test about facts surviving an append must not compare printed history with
/// itself; it compares the facts, and asserts the append separately.
const RESTORED_SPELLINGS: &[&[&str]] = &[
    &["now"],
    &["plan"],
    &["check"],
    &["triage"],
    &["model", "--show"],
    &["review", "day"],
    &["review", "day", "--date", "2026-09-07"],
    &["review", "week", "--date", "2026-W37"],
    &["review", "month", "--date", "2026-09"],
];

/// The one spelling in [`RESTORED_SPELLINGS`] that reads the day the undone command belongs to —
/// three days behind the instant it is asked from, and therefore behind the ledger day after S.
const THE_SEALED_DAY: &str = "review day --date 2026-09-07";

/// The answers with `replans` removed at every depth.
///
/// `tm review day`'s `replans` counts the day's `plan` events. A command that replans appends one,
/// and undoing that command appends its compensating event **and another plan** — the log is
/// append-only, so the count rises and stays risen. It is a count of history, exactly like
/// `tm log`'s lines, and it is the only such counter in these documents (measured: it is the single
/// key of the nine spellings that a `start` moves and an `undo` does not put back).
fn without_replans(answers: Vec<(String, String)>) -> Vec<(String, String)> {
    answers
        .into_iter()
        .map(|(name, body)| match serde_json::from_str::<serde_json::Value>(&body) {
            Ok(mut v) => {
                cli_common::scrub(&mut v, "replans", "[history]");
                let text = serde_json::to_string_pretty(&v).unwrap_or(body);
                (name, text)
            }
            Err(_) => (name, body),
        })
        .collect()
}

/// `kernel/corpus`, the copy of the fixture corpus that lives on this branch.
fn corpus() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../kernel/corpus")
}

/// `tm/tests/fixtures`, this file's own pinned bytes.
fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

/// Copy a directory tree (every fixture is read-only and stays that way).
fn copy_dir(from: &Path, to: &Path) {
    fs::create_dir_all(to).expect("create dir");
    for entry in fs::read_dir(from).expect("read fixture") {
        let entry = entry.expect("dir entry");
        let target = to.join(entry.file_name());
        if entry.file_type().expect("file type").is_dir() {
            copy_dir(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), &target).expect("copy file");
        }
    }
}

/// A temp plan directory holding a copy of `fixture`.
fn tree_of(fixture: &Path) -> Tm {
    let tmp = tempfile::TempDir::new().expect("temp dir");
    let plan = tmp.path().join("plan");
    copy_dir(fixture, &plan);
    Tm { tmp, plan }
}

/// One of the corpus's own plan trees, logs and all.
fn corpus_plan(name: &str) -> Tm {
    tree_of(&corpus().join(name))
}

/// `plan-basic` carrying one of the corpus's bare logs as its `.tm/log.jsonl`.
fn plan_with_log(log: &str) -> Tm {
    let tm = tree_of(&corpus().join("plan-basic"));
    fs::create_dir_all(tm.plan.join(".tm")).expect("mkdir .tm");
    fs::copy(corpus().join("logs").join(format!("{log}.jsonl")), tm.plan.join(".tm/log.jsonl"))
        .expect("copy the log");
    tm
}

/// The replay cache directory (D13), the one S fills with `ckpt.json` and the sealed months.
fn cache_dir(tm: &Tm) -> PathBuf {
    tm.plan.join(".tm/cache/replay")
}

/// Every file under `dir`, by relative path, with its bytes — for "nothing was persisted".
fn bytes_under(dir: &Path) -> BTreeMap<String, Vec<u8>> {
    let mut out = BTreeMap::new();
    fn walk(root: &Path, dir: &Path, out: &mut BTreeMap<String, Vec<u8>>) {
        let Ok(entries) = fs::read_dir(dir) else { return };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(root, &path, out);
            } else if let Ok(bytes) = fs::read(&path) {
                let rel = path.strip_prefix(root).unwrap_or(&path).display().to_string();
                out.insert(rel, bytes);
            }
        }
    }
    walk(dir, dir, &mut out);
    out
}

/// Run every spelling at `now` and keep its stdout, asserting each one succeeded. The answers are
/// what a stale, missing or wrongly-keyed checkpoint would move, so they are the comparand.
fn answers(tm: &Tm, now: &str, spellings: &[&[&str]]) -> Vec<(String, String)> {
    spellings
        .iter()
        .map(|args| {
            let mut all = vec!["--json"];
            all.extend_from_slice(args);
            let out = tm.run_at(now, &all);
            assert_eq!(
                out.code,
                0,
                "`tm --json {}` failed: {}{}",
                args.join(" "),
                out.stdout,
                out.stderr
            );
            (args.join(" "), out.stdout)
        })
        .collect()
}

/// Assert two answer sets are byte-identical, naming the first spelling that moved.
fn same(a: &[(String, String)], b: &[(String, String)], why: &str) {
    assert_eq!(a.len(), b.len(), "{why}: different numbers of answers");
    for ((name, left), (other, right)) in a.iter().zip(b) {
        assert_eq!(name, other, "{why}: the spellings are out of order");
        assert_eq!(left, right, "{why}: `tm --json {name}` moved");
    }
}

/// Which spellings differ between two answer sets — the *bite*: a test that asserts "the change
/// was honoured" is worth nothing unless the change was visible in the first place.
fn moved(a: &[(String, String)], b: &[(String, String)]) -> Vec<String> {
    a.iter()
        .zip(b)
        .filter(|((_, l), (_, r))| l != r)
        .map(|((n, _), _)| n.clone())
        .collect()
}

/// The log's physical lines.
fn log_lines(tm: &Tm) -> Vec<String> {
    fs::read_to_string(tm.plan.join(".tm/log.jsonl"))
        .unwrap_or_default()
        .lines()
        .map(str::to_string)
        .collect()
}

/// How many distinct local days the log's lines are dated in — a denominator for "across a seal".
fn dated_days(tm: &Tm) -> usize {
    log_lines(tm)
        .iter()
        .filter_map(|l| serde_json::from_str::<serde_json::Value>(l).ok())
        .filter_map(|v| v.get("t").and_then(|t| t.as_str()).map(|s| s[..10].to_string()))
        .collect::<std::collections::BTreeSet<_>>()
        .len()
}

// ---------------------------------------------------------------------------
// T9

/// **T9**: `tm undo` of a command dated behind the ledger day puts every fact back.
///
/// The log spans a fortnight and the undo is driven three days after the command it cancels, so
/// after S the command's own day is **below the checkpoint's ledger day** — sealed — and answering
/// this at all is design §7.4's "undo across a checkpoint" (`tagLast`, `settled`, the exact rebuild
/// point). Before S the same three days are just history. Either way the claim is the same one and
/// it is the one a user can check: the facts come back, and the log is not edited to do it —
/// the undo is **appended** (§10.1), so the prefix is byte-for-byte what it was.
#[test]
fn tm_undo_across_a_seal_restores_the_facts() {
    let tm = plan_with_log("energy-14d");
    let days = dated_days(&tm);
    assert!(days >= 14, "the log must span a fortnight to have anything behind the ledger: {days}");

    let before = without_replans(answers(&tm, LATER, RESTORED_SPELLINGS));
    let prefix = log_lines(&tm);

    let start = tm.run_at(INSIDE, &["--json", "start", "^t4", "--energy", "4"]);
    assert_eq!(start.code, 0, "{}{}", start.stdout, start.stderr);
    let after_start = without_replans(answers(&tm, LATER, RESTORED_SPELLINGS));
    let bite = moved(&before, &after_start);
    assert!(!bite.is_empty(), "the command changed no fact, so undoing it proves nothing");
    assert!(
        bite.iter().any(|s| s == THE_SEALED_DAY),
        "the command moved no fact about the older day, so nothing here crosses a seal: {bite:?}"
    );

    let undone = tm.run_at(LATER, &["--json", "undo"]);
    assert_eq!(undone.code, 0, "{}{}", undone.stdout, undone.stderr);
    assert_eq!(undone.json()["verb"], "start");

    // Append-only, read before anything else runs: the lines that were there are still there byte
    // for byte, and the undo *added* its compensating event (§10.1) rather than editing one. It is
    // not the last line — the undo replans, and that plan is appended after it — so the assertion
    // is over the lines the undo appended, not over the tail.
    let now_lines = log_lines(&tm);
    assert_eq!(&now_lines[..prefix.len()], &prefix[..], "the undo rewrote the log's prefix");
    let appended = &now_lines[prefix.len()..];
    assert!(
        appended.iter().any(|l| l.contains(r#""ev":"undo""#) && l.contains(r#""of":"start""#)),
        "no compensating `undo` of the `start` was appended: {appended:?}"
    );

    let after_undo = without_replans(answers(&tm, LATER, RESTORED_SPELLINGS));
    same(&before, &after_undo, "the undo did not restore the facts");

    eprintln!(
        "undo across a seal: {days} dated days, {} fact spellings compared, {} moved by the command \
         ({THE_SEALED_DAY} among them), {} log lines appended and 0 rewritten",
        RESTORED_SPELLINGS.len(),
        bite.len(),
        now_lines.len() - prefix.len()
    );
}

/// **T9**: the replay cache is derived, so deleting it changes no answer (D13; §14.6's own
/// "run verbs, `rm -r .tm/cache/replay`, rerun, compare every `--json`").
///
/// This is not vacuous today: a capacity verb writes `.tm/cache/replay/tz.json` on its first run in
/// a plan directory, so the deletion removes a real derived file and the rerun rebuilds it. After S
/// the same directory holds `ckpt.json` and the sealed month files, and the same assertion covers
/// them — which is exactly why it is spelled over the directory and not over one file's name.
#[test]
fn deleting_the_replay_cache_changes_nothing() {
    let tm = plan_with_log("energy-14d");

    // Warm it: the cache is written by a verb, not by loading a tree.
    tm.ok_at(LATER, &["now"]);
    let cached = bytes_under(&cache_dir(&tm));
    assert!(
        !cached.is_empty(),
        "nothing under {} — this test would be vacuous, which is worse than missing",
        cache_dir(&tm).display()
    );

    let before = answers(&tm, LATER, JSON_SPELLINGS);

    fs::remove_dir_all(cache_dir(&tm)).expect("delete the replay cache");
    assert!(!cache_dir(&tm).exists(), "the cache is still there");

    let after = answers(&tm, LATER, JSON_SPELLINGS);
    same(&before, &after, "deleting the replay cache moved an answer");

    let rebuilt = bytes_under(&cache_dir(&tm));
    assert!(!rebuilt.is_empty(), "the cache was deleted and never rebuilt");

    eprintln!(
        "cache deletion: {} cached files removed, {} rebuilt, {} `--json` spellings identical",
        cached.len(),
        rebuilt.len(),
        before.len()
    );
}

/// **T9**: a changed `tz` invalidates the checkpoint — the tree answers in the **new** zone.
///
/// The comparand is the same tree with the cache deleted: two trees identical in every byte except
/// the derived cache must answer identically, or the cache decided something. That is the exact
/// claim "invalidates the checkpoint" makes, and it is the claim whether the cache holds a zone
/// table (today) or a zone-keyed `ckpt.json` (after S, whose integrity check refuses a differing
/// zone key and goes to genesis, §9.8).
#[test]
fn a_changed_tz_invalidates_the_checkpoint() {
    let tm = plan_with_log("energy-14d");
    tm.ok_at(LATER, &["now"]);
    let under_chicago = answers(&tm, LATER, JSON_SPELLINGS);
    let zone_before = fs::read_to_string(cache_dir(&tm).join("tz.json")).unwrap_or_default();
    assert!(zone_before.contains("America/Chicago"), "the cache is not keyed by the old zone");

    let config = tm.plan.join("config.toml");
    let text = fs::read_to_string(&config).expect("read config.toml");
    assert!(text.contains(r#"tz = "America/Chicago""#), "the fixture's zone moved");
    fs::write(&config, text.replace(r#"tz = "America/Chicago""#, r#"tz = "Asia/Tokyo""#))
        .expect("write config.toml");

    // The comparand: the same tree, the same bytes, without the cache the old zone wrote.
    let fresh = tree_of(&tm.plan);
    fs::remove_dir_all(cache_dir(&fresh)).expect("delete the comparand's cache");

    let stale = answers(&tm, LATER, JSON_SPELLINGS);
    let rebuilt = answers(&fresh, LATER, JSON_SPELLINGS);

    let bite = moved(&under_chicago, &stale);
    assert!(!bite.is_empty(), "the zone change moved no answer, so nothing here is tested");
    same(&stale, &rebuilt, "the cache written under the old zone decided an answer");

    let zone_after = fs::read_to_string(cache_dir(&tm).join("tz.json")).unwrap_or_default();
    assert!(zone_after.contains("Asia/Tokyo"), "the cache still holds the old zone's table");

    eprintln!("changed tz: {} of {} answers moved: {bite:?}", bite.len(), under_chicago.len());
}

/// **T9**: a rewritten log **prefix** invalidates the checkpoint — the tree answers from the bytes
/// on disk now, not from what was replayed before.
///
/// A hand edit to an early line is precisely what §9.8's prefix digest exists to catch: after S a
/// differing length, a differing FNV-1a-64 or a prefix not ending in `\n` sends the call straight to
/// genesis. Before S there is nothing to invalidate, and the answer must still be the rewritten
/// log's. Same assertion, both sides.
#[test]
fn a_rewritten_log_prefix_invalidates_the_checkpoint() {
    let tm = plan_with_log("energy-14d");
    tm.ok_at(LATER, &["now"]);
    let before = answers(&tm, LATER, JSON_SPELLINGS);

    // The first `done` in the file: line 4 of a 155-line log, deep inside every chunk boundary and
    // every horizon, and a line whose minutes reach the reviews.
    let mut lines = log_lines(&tm);
    let at = lines
        .iter()
        .position(|l| l.contains(r#""ev":"done""#))
        .expect("the log has a `done`");
    assert!(at < 10, "the rewritten line must be in the prefix, not the tail: line {}", at + 1);
    let rewritten = lines[at].replace(r#""actual_min":86"#, r#""actual_min":7"#);
    assert_ne!(rewritten, lines[at], "the hand edit changed nothing in the line");
    lines[at] = rewritten;
    fs::write(tm.plan.join(".tm/log.jsonl"), format!("{}\n", lines.join("\n")))
        .expect("rewrite the log");

    let fresh = tree_of(&tm.plan);
    fs::remove_dir_all(cache_dir(&fresh)).expect("delete the comparand's cache");

    let stale = answers(&tm, LATER, JSON_SPELLINGS);
    let rebuilt = answers(&fresh, LATER, JSON_SPELLINGS);

    let bite = moved(&before, &stale);
    assert!(!bite.is_empty(), "the prefix rewrite moved no answer, so nothing here is tested");
    same(&stale, &rebuilt, "the cache built on the old prefix decided an answer");

    eprintln!(
        "rewritten prefix: line {} of {}, {} of {} answers moved: {bite:?}",
        at + 1,
        lines.len(),
        bite.len(),
        before.len()
    );
}

/// **T9**: a `now` **before** the ledger day is answered, and nothing about it is persisted.
///
/// Design §9.1 anchors one horizon to `now`, and §9.3's guards refuse a `now` below the ledger day
/// (`nowBelowLedger`); §9.7's genesis answers it **unpersisted** (`Outcome::GenesisUnpersisted`).
/// The user-visible half of that — the part that holds on both sides — is this: the early instant
/// gets its own honest answer, the tree on disk does not move, and the later instant answers
/// exactly what it answered before. A checkpoint written at an early `now` would break the third.
#[test]
fn a_now_before_the_ledger_is_answered_and_not_persisted() {
    const EARLY: &str = "2026-08-28T09:00:00-05:00";

    // Half one — **answered, and the checkpoint is not written for it.** §9.7 answers a `now` below
    // the ledger day from an *unpersisted* genesis (`Outcome::GenesisUnpersisted`), so the derived
    // cache the checkpoint lives in must come out byte-for-byte as it went in.
    let a = plan_with_log("energy-14d");
    a.ok_at(LATER, &["now"]);
    a.ok_at(LATER, &["plan"]);
    let cache_before = bytes_under(&cache_dir(&a));
    assert!(!cache_before.is_empty(), "nothing is cached, so \"not persisted\" would be vacuous");

    let early = a.run_at(EARLY, &["--json", "now"]);
    assert_eq!(early.code, 0, "the early `now` was not answered: {}{}", early.stdout, early.stderr);
    assert_eq!(
        early.json()["date"], "2026-08-28",
        "the early `now` answered some other day: {}",
        early.stdout
    );
    assert_eq!(
        bytes_under(&cache_dir(&a)),
        cache_before,
        "the early `now` wrote the replay cache"
    );

    // Half two — where "persisted" is fully observable, because the verb writes nothing of its own:
    // an early instant moves no byte of the tree, and the ledger day still answers what it did.
    //
    // `tm now` is **not** such a verb, deliberately and measurably: at an instant before the stored
    // runtime day it rolls `.tm/state.json` back (`Ctx::load`'s `roll_day`), clearing
    // `last_plan_hash`, so the next plan at the real day counts one more replan and
    // `tm review day`'s `replans` moves 1 → 2. That is the `--now` flag's own behaviour, it is
    // nothing the switch changes, and it is recorded as **gap 139** rather than asserted here as
    // correct.
    let b = plan_with_log("energy-14d");
    let late_before = answers(&b, LATER, JSON_SPELLINGS);
    let tree_before = bytes_under(&b.plan);
    for args in [["--json", "log"], ["--json", "check"]] {
        let out = b.run_at(EARLY, &args);
        assert_eq!(
            out.code,
            0,
            "`tm {}` at an early instant failed: {}{}",
            args.join(" "),
            out.stdout,
            out.stderr
        );
    }
    let tree_after = bytes_under(&b.plan);
    let changed: Vec<&String> = tree_after
        .iter()
        .filter(|(path, bytes)| tree_before.get(*path) != Some(bytes))
        .map(|(path, _)| path)
        .collect();
    assert!(changed.is_empty(), "an early read-only verb persisted something: {changed:?}");
    assert_eq!(tree_before.len(), tree_after.len(), "an early read-only verb added or removed a file");

    let late_after = answers(&b, LATER, JSON_SPELLINGS);
    same(&late_before, &late_after, "an early instant moved what the ledger day answers");

    eprintln!(
        "now before the ledger: {} cached files unchanged, {} tree files unchanged, \
         {} ledger-day answers unchanged",
        cache_before.len(),
        tree_after.len(),
        late_after.len()
    );
}

/// **T9**: an unwritable cache is not fatal — the checkpoint is kept in memory for that process and
/// exactly one notice says so (CRIT 26; `kernel_log::unwritable_notice`).
///
/// **Ignored until S, and not weakened to fit.** The notice exists (`kernel_log.rs`) but has no
/// emitter: nothing under `tm/src` calls it, because nothing under `tm/src` calls `kernel_log` at
/// all. Asserting "at most one notice" would pass today and assert nothing, so the body below is
/// the post-switch one and S's acceptance is to delete the `#[ignore]`. The half that *is* true
/// today is asserted by the sibling test `deleting_the_replay_cache_changes_nothing`: an
/// unwritable cache directory does not move an answer (driven by hand at this commit, 0 differences).
#[cfg(unix)]
#[test]
#[ignore = "the notice has no emitter until S: nothing in tm/src calls kernel_log::unwritable_notice"]
fn an_unwritable_cache_rebuilds_in_memory_with_one_notice() {
    use std::os::unix::fs::PermissionsExt;

    let tm = plan_with_log("energy-14d");
    tm.ok_at(LATER, &["now"]);
    let writable = answers(&tm, LATER, JSON_SPELLINGS);

    let dir = cache_dir(&tm);
    fs::remove_dir_all(&dir).expect("clear the cache");
    fs::create_dir_all(&dir).expect("recreate the cache directory");
    fs::set_permissions(&dir, fs::Permissions::from_mode(0o500)).expect("make it unwritable");

    let out = tm.run_at(LATER, &["--json", "now"]);

    // Restore before asserting: a failed assertion must not leave a directory the temp dir cannot
    // remove.
    fs::set_permissions(&dir, fs::Permissions::from_mode(0o700)).expect("restore the permissions");

    assert_eq!(out.code, 0, "an unwritable cache killed the verb: {}{}", out.stdout, out.stderr);
    assert_eq!(out.stdout, writable[0].1, "an unwritable cache moved the answer");

    let notices: Vec<&str> = out
        .stderr
        .lines()
        .filter(|l| l.contains(".tm/cache/replay") && l.contains("not writable"))
        .collect();
    assert_eq!(notices.len(), 1, "one notice per process, not {}: {:?}", notices.len(), out.stderr);
    assert!(
        notices[0].contains("rebuilds in memory"),
        "the notice does not say what it did instead: {}",
        notices[0]
    );
}

/// **T9**: a hand-written `undo` reaching further back than any rebuild can window fails **by
/// name**, and `tm check` is the one verb that still runs (OWNER Q9 (iii), D18, parity P31).
///
/// **Ignored until S, and not weakened to fit.** `GenesisError::ReachTooFar` is built and tested in
/// `kernel_log.rs`, but it has no call site in the binary: gap 120 part 3 has said so since W-6, and
/// nothing in `tm/src` calls `kernel_log`. Today the Rust reader replays the whole log and this
/// input simply works, so there is no failure to name. The body is the post-switch one; S's
/// acceptance is to delete the `#[ignore]`.
#[test]
#[ignore = "reachTooFar has no call site until S (gap 120 part 3, D18 (iii))"]
fn a_hand_undo_beyond_the_rebuild_bound_fails_by_name() {
    // A log longer than the resend cap (`kernel_log::RESEND_LINES` = 8,192 lines /
    // `RESEND_BYTES` = 1,536 KiB), so that a refusal needing a rebuild from the checkpoint's cut
    // cannot be answered within the memory gate (gap 102).
    let lines = loggen::log(loggen::Rate::Forty, 260);
    assert!(lines.len() > 8_192, "the generated log is inside the cap: {} lines", lines.len());

    // An `undo` matches the latest surviving event with its tag and id, so the target is an id
    // whose last `done` is in the first chunk and which is never done again.
    let done_at = |id: &str| {
        lines.iter().rposition(|l| l.contains(r#""ev":"done""#) && l.contains(&format!(r#""id":"{id}""#)))
    };
    let early: Vec<String> = lines[..1_000]
        .iter()
        .filter(|l| l.contains(r#""ev":"done""#))
        .filter_map(|l| serde_json::from_str::<serde_json::Value>(l).ok())
        .filter_map(|v| v.get("id").and_then(|i| i.as_str()).map(str::to_string))
        .collect();
    let target = early
        .iter()
        .find(|id| done_at(id).map_or(false, |at| at < 1_000))
        .expect("an id whose only `done` is in the first chunk");
    let reach = lines.len() - done_at(target).expect("the target's line");
    assert!(reach > 8_192, "the undo does not reach past the cap: {reach} lines");

    let tm = plan_with_log("energy-14d");
    let last_t = "2026-12-31T23:59:00-05:00";
    let text = format!(
        "{}\n{{\"t\":\"{last_t}\",\"ev\":\"undo\",\"of\":\"done\",\"id\":\"{target}\"}}\n",
        lines.join("\n")
    );
    fs::write(tm.plan.join(".tm/log.jsonl"), text).expect("write the log");

    // Every verb but `tm check` fails by name …
    for args in [vec!["now"], vec!["plan"], vec!["log"], vec!["review", "day"]] {
        let out = tm.run_at("2027-01-01T09:00:00-05:00", &args);
        assert_ne!(out.code, 0, "`tm {}` answered a log no rebuild can window", args.join(" "));
        assert!(
            out.stderr.contains("reachTooFar"),
            "`tm {}` did not name the fault: {}",
            args.join(" "),
            out.stderr
        );
    }

    // … and `tm check` is precisely the verb that keeps working, because it is how the line is
    // found (D18).
    let check = tm.run_at("2027-01-01T09:00:00-05:00", &["check"]);
    assert_eq!(check.code, 0, "`tm check` died on the log it exists to diagnose: {}", check.stderr);
    assert!(check.stdout.contains("reachTooFar"), "`tm check` did not name it: {}", check.stdout);
}

/// **T9**: `tm log`'s bytes on the corpus, human **and** `--json`, pinned.
///
/// This is the switch's sharpest instrument. At S, step 3 of §11.4 stops reading the selected
/// lines' bytes with `Ctx::entries_at` and asks the kernel's `render` op instead, and `tm log`'s
/// human line becomes the kernel's `display` plus the `k=v` pairs of the rendering (CRIT 20 deletes
/// `parse_timestamp`). Nothing in a diff says whether that moved a byte; this file does. The
/// expectation is **measured, not written by hand** — `TM_LOG_BLESS=1` rewrites it — and a case
/// that starts disagreeing is a failure, not a re-bless.
#[test]
fn tm_log_is_byte_identical_on_the_corpus() {
    let mut cases: Vec<(String, Tm, Vec<Vec<String>>)> = Vec::new();
    let spellings = |extra: &[&str]| {
        let mut all: Vec<Vec<String>> = vec![
            vec!["log".into()],
            vec!["log".into(), "--tail".into(), "5".into()],
            vec!["log".into(), "--since".into(), "14d".into()],
        ];
        if !extra.is_empty() {
            all.push(extra.iter().map(|s| s.to_string()).collect());
        }
        all
    };
    for plan in ["plan-home-day", "plan-travel-day"] {
        cases.push((plan.to_string(), corpus_plan(plan), spellings(&[])));
    }
    // `plan-recur` is the only corpus log carrying ids, so it is the only one `--item` can select.
    cases.push((
        "plan-recur".to_string(),
        corpus_plan("plan-recur"),
        spellings(&["log", "--item", "^m1"]),
    ));
    for log in ["energy-14d", "malformed", "review-14d", "three-days"] {
        cases.push((format!("logs/{log}"), plan_with_log(log), spellings(&[])));
    }

    let mut measured = String::new();
    let mut runs = 0;
    for (label, tm, spells) in &cases {
        for spell in spells {
            for json in [false, true] {
                let args: Vec<&str> = spell.iter().map(String::as_str).collect();
                let mut all = Vec::new();
                if json {
                    all.push("--json");
                }
                all.extend_from_slice(&args);
                let out = tm.run_at(CORPUS_NOW, &all);
                assert_eq!(
                    out.code, 0,
                    "`tm {}` on {label} failed: {}{}",
                    all.join(" "),
                    out.stdout,
                    out.stderr
                );
                assert!(out.stderr.is_empty(), "`tm {}` on {label} wrote to stderr: {}", all.join(" "), out.stderr);
                measured.push_str(&format!(
                    "=== {label} | tm {} | {}\n{}\n",
                    spell.join(" "),
                    if json { "json" } else { "human" },
                    out.stdout.trim_end_matches('\n')
                ));
                runs += 1;
            }
        }
    }

    let expected = fixtures().join("tm-log-corpus.expected");
    if std::env::var_os("TM_LOG_BLESS").is_some() {
        fs::write(&expected, &measured).expect("write the expectation");
        eprintln!("blessed {} cases into {}", runs, expected.display());
        return;
    }
    let want = fs::read_to_string(&expected).unwrap_or_else(|e| {
        panic!("{}: {e} — run with TM_LOG_BLESS=1 to write it", expected.display())
    });
    if want != measured {
        let first = want
            .lines()
            .zip(measured.lines())
            .position(|(a, b)| a != b)
            .unwrap_or(want.lines().count().min(measured.lines().count()));
        let case = measured
            .lines()
            .take(first + 1)
            .filter(|l| l.starts_with("=== "))
            .last()
            .unwrap_or("(before the first case)");
        panic!(
            "`tm log`'s bytes moved on the corpus, at line {} of the expectation, in case {case}:\n\
             expected: {:?}\n  actual: {:?}",
            first + 1,
            want.lines().nth(first),
            measured.lines().nth(first)
        );
    }
    eprintln!("tm log on the corpus: {} cases, {} bytes, byte-identical", runs, measured.len());
}

// ---------------------------------------------------------------------------
// T12

/// **T12**: `tm model --fit` on `energy-14d.jsonl` writes the fork point's own `model.json`, byte
/// for byte.
///
/// The fixture is not this branch's output re-blessed: it was produced by **building fork point
/// `4748911` and running its `tm`** (`kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh` extracts
/// the fork; `cargo build -p tm` in that scratch tree is its binary), on the same fixture tree at
/// the same pinned `--now`. Design §11.1's CRIT 4 is what this guards: at S the fit runs over the
/// **`All`**-scope `Replay`, so a scope that quietly narrowed the observations would refit on fewer
/// of them, and 61 observations would silently become 60.
#[test]
fn model_fit_is_the_fork_points_on_the_corpus() {
    let tm = plan_with_log("energy-14d");
    let out = tm.run_at(FIT_NOW, &["model", "--fit"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(
        out.stdout.contains("fitted from 61 observations"),
        "the fit saw a different number of observations: {}",
        out.stdout
    );

    let written = fs::read(tm.plan.join(".tm/model.json")).expect("read the written model");
    let fork = fs::read(fixtures().join("fork-4748911-energy-14d-model.json")).expect("read fixture");
    assert_eq!(
        String::from_utf8_lossy(&written),
        String::from_utf8_lossy(&fork),
        "`tm model --fit` no longer writes fork point 4748911's model.json"
    );
    assert_eq!(written.len(), 599, "the fork's model.json is 599 bytes");

    eprintln!("T12: {} bytes identical to fork 4748911's model.json", written.len());
}
