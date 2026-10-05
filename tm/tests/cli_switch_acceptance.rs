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

/// `.tm/state.json` (§10.2) — the other derived file, under the owner's **D42**.
fn state_path(tm: &Tm) -> PathBuf {
    tm.plan.join(".tm/state.json")
}

/// The checkpoint the replay cache holds (`kernel_log::CKPT_FILE`, §9.8's format 3), as JSON.
fn checkpoint(tm: &Tm) -> serde_json::Value {
    let path = cache_dir(tm).join("ckpt.json");
    let text = fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    serde_json::from_str(&text).unwrap_or_else(|e| panic!("{} is not JSON: {e}", path.display()))
}

/// One string field of a checkpoint.
fn ckpt_str(ckpt: &serde_json::Value, key: &str) -> String {
    ckpt[key].as_str().unwrap_or_else(|| panic!("the checkpoint has no string `{key}`: {ckpt}")).to_string()
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

/// **The `drift_min` of each `plan` event among `lines` logged on the local date `day`** (`YYYY-MM-DD`,
/// read off each line's own stamp, which carries its offset), in log order.
fn logged_drifts(lines: &[String], day: &str) -> Vec<u64> {
    lines
        .iter()
        .filter_map(|l| serde_json::from_str::<serde_json::Value>(l).ok())
        .filter(|v| v["ev"] == "plan" && v["t"].as_str().is_some_and(|t| t.starts_with(day)))
        .map(|v| v["drift_min"].as_u64().expect("a plan event carries drift_min"))
        .collect()
}

/// **The drift R3 logs in [`tm_undo_across_a_seal_restores_the_facts`], by value** (RULE M; README gap
/// 4877, the W-46 repair): the `drift_min` of each `plan` event appended on 2026-09-10 after the
/// `start` three days back, in log order, MEASURED on the switched binary. Fork 4748911 logged drift 0
/// on every one (it read the cache's `13:00` on the planned date, after `now`, so the old start moved
/// no row). Since R3 the kernel's day reserves that block from its LOGGED start (parity **P69**) in
/// overtime (parity **P46**), so the start moves the day's rows and the plans after it carry drift.
/// A drift the binary logs that is not exactly this list fails here: the moved value is named, never
/// accounted from whatever the run produced (which is what the W-45 and W-46 switches did, gap 4744).
const R3_DRIFTS_P69_P46: &[u64] = &[500, 500];

/// `answers` with `drift` minutes added to every review of the date `day` — the answer a review
/// of that day gives once the log holds that much more drift, every other byte as it was.
fn with_logged_drift(answers: Vec<(String, String)>, day: &str, drift: u64) -> Vec<(String, String)> {
    answers
        .into_iter()
        .map(|(name, body)| match serde_json::from_str::<serde_json::Value>(&body) {
            Ok(mut v) if v["review"]["date"] == day => {
                let was = v["review"]["drift_min"].as_u64().expect("a day review carries drift_min");
                v["review"]["drift_min"] = serde_json::json!(was + drift);
                (name, serde_json::to_string_pretty(&v).expect("JSON"))
            }
            _ => (name, body),
        })
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
    // **The drift the day's `plan` events logged since `before`, accounted from the log** (RULE M;
    // README gap 4744, the W-45 repair). `tm review day`'s `drift_min` sums the day's `plan` events'
    // `drift_min`, a count of history like `replans`: on fork 4748911's day every plan event here had
    // drift 0 (the fork read the cache's `13:00` on the planned date, after `now`, so the start three
    // days back moved no row), and since R3 the kernel's day reserves that block from its LOGGED
    // start (parity P69) in overtime (P46), so the start moves the day's rows and the plan events
    // logged after it carry drift. The moved value is not masked: `before` is advanced by exactly
    // the drift the log's appended `plan` events carry on the reviewed day — every one of them is
    // appended before `review day` runs (`plan` is the second spelling, and none after it writes
    // one) — and then the answers must be equal.
    let all = log_lines(&tm);
    let day = &LATER[..10];
    let drifts = logged_drifts(&all[prefix.len()..], day);
    eprintln!("R3 drifts logged on {day}: {drifts:?}");
    assert_eq!(drifts, R3_DRIFTS_P69_P46, "the drift R3 logs on {day} is the measured list, P69 and P46's");
    let drift: u64 = R3_DRIFTS_P69_P46.iter().sum();
    let before = with_logged_drift(before, day, drift);
    same(&before, &after_undo, "the undo did not restore the facts");

    eprintln!(
        "undo across a seal: {days} dated days, {} fact spellings compared, {} moved by the command \
         ({THE_SEALED_DAY} among them), {} log lines appended and 0 rewritten, {drift} minutes of \
         drift logged on {day} since and accounted",
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

/// **T9's symmetric half**: `.tm/state.json` is derived too, so deleting it changes no answer
/// (the owner's **D42**, README **gap 993**) — the same shape as
/// [`deleting_the_replay_cache_changes_nothing`] above, over the other derived file.
///
/// **What it is about, as the owner drove it.** With `^p1` running, `rm .tm/state.json` left
/// `tm plan` drawing `^p1` with `▶` — it reads the log — while `tm now` said *"nothing running"*,
/// `tm done` and `tm stop` said *"nothing is running"* and exited **1**, and `tm check` said
/// *"no problems"*. The log still held the `wake`, the `arrive` and the `start`. Two readers of
/// one day, disagreeing: AGENTS §5.3.
///
/// **Three assertions, and the second and third are why the first is not enough.**
///
/// 1. Every `--json` spelling is byte-identical across the deletion. That is the D13 sentence
///    said about this file.
/// 2. The rebuilt file itself is read, and it must name the same running block. The answers
///    alone would hold if `Ctx::reconcile_state` were deleted and `tm now` happened to be
///    answered from the plan — README gap 195's lesson, applied here: a test that stops at the
///    answers stays green while the mechanism it is named for is gone. Measured: with
///    `reconcile_state`'s body replaced by `Ok(())` this test fails at assertion 2 and at
///    assertion 3, and `moved()` reports `now` and `triage` as well.
/// 3. `tm done` **succeeds**, which is the half of gap 993 the user actually met. Exit 1 before,
///    exit 0 after, and it names the block the log knew about all along. It runs last, because
///    it is the one verb here that closes the thing being asserted.
///
/// **And the bite is asserted before anything else**: a state file with no running block in it
/// would make every line below vacuously true.
///
/// **What it does NOT warm, named here because the title does not say it** (W-21 repair step):
/// a RUNNING BREAK. Until the owner's D105 `tm break` set `active.paused` and appended nothing,
/// so in that state the deletion did move an answer — the pause — and the test that held that
/// state asserted exactly that move and no log line. Since D105 (parity P100) `tm break` logs a
/// `break_start` and the rebuild restores the break and its pause from it, so that state moves
/// nothing either: [`deleting_the_runtime_state_while_a_break_runs_changes_nothing`] is it.
#[test]
fn deleting_the_runtime_state_changes_nothing() {
    let tm = plan_with_log("energy-14d");

    // Warm it with the verbs that WRITE the runtime — a wake, an arrival and a running block —
    // and write them INSIDE the log's own last day, three days behind the instant everything is
    // asked from. That is deliberate: `roll_day` clears `arrival`, `window`, `budget` and
    // `last_plan_hash` at a day boundary and KEEPS `wake` and `loc`, so a rebuild from the log
    // has to carry those two across days too. Setting up at LATER would never exercise it.
    tm.ok_at(INSIDE, &["wake", "06:05"]);
    tm.ok_at(INSIDE, &["arrive", "lounge"]);
    tm.ok_at(INSIDE, &["start", "^p1"]);

    let before = answers(&tm, LATER, JSON_SPELLINGS);

    let before_bytes = fs::read_to_string(state_path(&tm)).expect("read .tm/state.json");
    let before_state: serde_json::Value =
        serde_json::from_str(&before_bytes).expect(".tm/state.json is not JSON");
    // The bite: without these three in the file, every line below is vacuously true.
    assert_eq!(
        before_state["active"]["id"], "p1",
        "nothing is running, so deleting the runtime state would prove nothing: {before_bytes}"
    );
    assert_eq!(before_state["wake"], "06:05", "the wake is not in the cache: {before_bytes}");
    assert_eq!(before_state["loc"], "lounge", "the location is not in the cache: {before_bytes}");

    fs::remove_file(state_path(&tm)).expect("delete the runtime state");
    assert!(!state_path(&tm).exists(), "the runtime state is still there");

    // **The rebuild is LOUD**, which is the half of gap 993 that mattered: a field the log cannot
    // carry must be named, not regenerated as `null` in silence.
    let first = tm.run_at(LATER, &["--json", "now"]);
    assert_eq!(first.code, 0, "the first verb after the deletion failed: {}{}", first.stdout, first.stderr);
    assert!(
        first.stderr.contains("rebuilt from .tm/log.jsonl"),
        "the rebuild said nothing: {:?}",
        first.stderr
    );
    assert!(
        first.stderr.contains("priorities_yesterday"),
        "the rebuild did not name what it could not restore: {:?}",
        first.stderr
    );

    let after = answers(&tm, LATER, JSON_SPELLINGS);
    eprintln!("PROBE bite = {:?}", moved(&before, &after));
    same(&before, &after, "deleting the runtime state moved an answer");

    // **This test bites on its own class**, measured rather than asserted: with
    // `Ctx::reconcile_state`'s body replaced by `Ok(())` and the two stderr assertions above
    // removed, `moved()` reports SEVEN of the eleven spellings — `now`, `plan`, `log`,
    // `log --tail 5`, `log --since 7d`, `review day`, `review week` — and `same()` fails on the
    // first. What it cannot see is in the test's own doc comment.
    //
    // The file itself is read as well as the answers, because README gap 195's lesson is that a
    // test which stops at the answers stays green while the mechanism it is named for is gone.
    // **Every §10.2 field comes back**, and the one that does not is written out here rather
    // than skipped.
    let after_bytes = fs::read_to_string(state_path(&tm)).expect("the runtime state was never rebuilt");
    let after_state: serde_json::Value =
        serde_json::from_str(&after_bytes).expect("the rebuilt .tm/state.json is not JSON");
    let mut expected = before_state.clone();
    // §7.4's hysteresis map is the one §10.2 field with no event behind it: no log line carries a
    // `p`. It comes back empty, the rebuild says so by name, and `tm plan` then ranks without
    // yesterday's damping — which on this tree moves no answer, and on another could.
    expected["priorities_yesterday"] = serde_json::json!({});
    assert_eq!(
        after_state, expected,
        "the rebuilt runtime state is not the deleted one minus the hysteresis map:\n{after_bytes}"
    );

    // The verb the defect was actually reported as: `tm done` exited **1** with "nothing is
    // running" while `tm plan` drew the same block with `▶`.
    let done = tm.run_at(LATER, &["--json", "done"]);
    assert_eq!(done.code, 0, "`tm done` still cannot see the running block: {}{}", done.stdout, done.stderr);
    assert_eq!(done.json()["id"], "p1", "`tm done` closed something else: {}", done.stdout);

    eprintln!(
        "runtime-state deletion: {} `--json` spellings identical, every §10.2 field but \
         `priorities_yesterday` came back out of {} log lines, `tm done` exit {}",
        before.len(),
        log_lines(&tm).len(),
        done.code
    );
}

/// **T9's FOURTH half, and the day the three above do not build: one with TWO arrivals**
/// — the owner's **D45**, README **gap 1202**.
///
/// **What it is about.** `.tm/state.json` holds whatever the LAST `tm arrive` wrote;
/// `Ctx::derived_state` used to read `DayReplay::arrival`, which is the day's **FIRST**
/// `Event::Arrive`. On a day with one arrival the two agree and
/// [`deleting_the_runtime_state_changes_nothing`] is green — which is exactly why nothing
/// caught it: its warm-up appends one arrival to a day whose own arrival has already rolled
/// away, and its answers are asked three days later, where `roll_day` has nulled the field on
/// both sides. **This test asks on the arrival's own day**, and the `energy-14d` fixture's last
/// day already carries `arrive lounge 07:10`, so one `tm arrive` at [`INSIDE`] makes two.
///
/// **The bite is asserted first, and it is the whole point**: the two arrivals must differ, or
/// every line below holds for the wrong reason. Measured before the repair: `arrival` came back
/// `07:10` where the cache said `13:00`, and `window` came back `["07:10","15:10"]` where the
/// cache said `["13:00","21:00"]` — a deletion moving a field is precisely what D42 was bought
/// to make impossible.
///
/// **And it is WIDER than gap 1202 reported.** That entry says *"Nothing in the shipped answers
/// moves on the fixture measured, which is why this is a gap and not a repair."* Measured here,
/// before the repair, with the field assertions relaxed to prints: `moved()` reports **five** of
/// the eleven spellings — `plan`, `log`, `log --tail 5`, `log --since 7d`, `review day`.
/// Fork 4748911's `Planner::window_and_budget` read `.tm/state.json`'s window when it had one and
/// fell back to the formula when it did not (so does the kernel's day since R3, gap 320's reading),
/// so a rebuilt window re-lays the afternoon, moves
/// the plan hash and appends a second `Event::Plan` — which is what the three `log` spellings and
/// the day review are seeing. The gap's own measurement was taken on a day whose arrival had
/// already rolled away; this one is taken on the arrival's own day.
///
/// **What it still does not cover.** `budget` does not move even before the repair, because
/// `capacity::budget_blocks` is a function of the config alone and every arrival of a day
/// therefore computes the same one; and `loc` does not move because `derived_state` already read
/// `loc_changes.last()`. So of §10.2's four arrival-shaped fields, **two** were first-arrival and
/// **two** were already last-arrival — one function disagreeing with itself, which is why the
/// assertion below names all four rather than the two that moved.
#[test]
fn deleting_the_runtime_state_keeps_the_last_arrival_of_the_day() {
    let tm = plan_with_log("energy-14d");

    // The fixture's own 2026-09-07 already holds `arrive lounge 07:10`; this is the second.
    tm.ok_at(INSIDE, &["arrive", "home"]);

    let arrivals: Vec<String> = log_lines(&tm)
        .iter()
        .filter(|l| l.contains(r#""ev":"arrive""#) && l.contains("2026-09-07T"))
        .cloned()
        .collect();
    assert_eq!(
        arrivals.len(),
        2,
        "the day does not have two arrivals, so this test would prove nothing:\n  {}",
        arrivals.join("\n  ")
    );

    let before_bytes = fs::read_to_string(state_path(&tm)).expect("read .tm/state.json");
    let before_state: serde_json::Value =
        serde_json::from_str(&before_bytes).expect(".tm/state.json is not JSON");
    // The bite: the cache must hold the SECOND arrival, and it must differ from the first.
    assert_eq!(before_state["arrival"], "13:00", "the cache is not the last arrival: {before_bytes}");
    assert!(
        arrivals[0].contains(r#""t":"2026-09-07T07:10:00-05:00""#),
        "the fixture's first arrival moved; this test's bite is gone:\n  {}",
        arrivals[0]
    );

    // **And the window must be a REAL window before the deletion**, or the
    // agreement below is vacuous. Built because a mutation found it: folding
    // `Ctx::arrival_window` to `((at, at), 0)` — the identity on its argument —
    // left this test GREEN, because the writer and the derivation both go
    // through that one function and a fold moves *both* sides equally.
    // `cli_day`'s `arrive_computes_window_and_budget_and_plans` fails on it, so
    // the definition is witnessed; this row was not the witness, and an
    // agreement assertion that cannot tell a window from a point is exactly
    // AGENTS §5.2's "a theorem can compile and mean nothing" in test form.
    let window = before_state["window"].as_array().expect("a window array");
    assert_ne!(window[0], window[1], "the cached window is a point: {before_bytes}");
    assert!(
        before_state["budget"].as_u64().is_some_and(|b| b > 0),
        "the cached budget is zero, so agreeing about it proves nothing: {before_bytes}"
    );

    let before = answers(&tm, INSIDE, JSON_SPELLINGS);

    fs::remove_file(state_path(&tm)).expect("delete the runtime state");
    let first = tm.run_at(INSIDE, &["--json", "now"]);
    assert_eq!(first.code, 0, "the first verb after the deletion failed: {}{}", first.stdout, first.stderr);

    let after_bytes = fs::read_to_string(state_path(&tm)).expect("the runtime state was never rebuilt");
    let after_state: serde_json::Value =
        serde_json::from_str(&after_bytes).expect("the rebuilt .tm/state.json is not JSON");

    // **D45: the derivation follows the verb.** Three fields, named one at a time so a failure
    // says which one, and then the whole record so a fourth cannot slip through.
    for key in ["arrival", "window", "budget", "loc"] {
        assert_eq!(
            after_state[key], before_state[key],
            "the rebuild disagrees with the cache about `{key}` on a day with two arrivals \
             (D45, README gap 1202):\n  cached  {}\n  rebuilt {}",
            before_state[key], after_state[key]
        );
    }
    let mut expected = before_state.clone();
    expected["priorities_yesterday"] = serde_json::json!({});
    assert_eq!(
        after_state, expected,
        "the rebuilt runtime state is not the deleted one minus the hysteresis map:\n{after_bytes}"
    );

    let after = answers(&tm, INSIDE, JSON_SPELLINGS);
    same(&before, &after, "deleting the runtime state after a second arrival moved an answer");

    eprintln!(
        "two arrivals: cached arrival {} window {}, rebuilt arrival {} window {}, {} spellings identical",
        before_state["arrival"], before_state["window"],
        after_state["arrival"], after_state["window"],
        before.len()
    );
}

/// **The shape the row above never drove: `tm arrive --at`** — README gaps **1305** and **1307**.
///
/// [`deleting_the_runtime_state_keeps_the_last_arrival_of_the_day`] makes its second arrival with
/// a bare `tm arrive`, so the event's `t` equals the arrival instant and the writer and the
/// derivation agreed **by accident**. The one shape where they diverge is the one D45's own
/// sentence describes, and it was untested: an auditor drove
/// `wake 06:00; arrive lounge --at 13:00; arrive home --at 07:00`, deleted the cache, and got
/// `arrival 14:12` and `window ["14:12","19:00"]` back — an instant carried by neither the cache
/// nor the log, and a REGRESSION on `3ec119b`, which read the logged payload.
///
/// **What was actually wrong, which is wider than the report.** `tm_core::log`'s own event
/// convention reads *"`wake.t` is the wake time; `arrive.t` the arrival; `start.t` the block
/// start"*. `tm wake` has always honoured it (`LogEntry::new(ctx.at(time), …)`); `tm arrive`
/// stamped `Ctx::now`, so `--at` survived only inside `window[0]` and every reader that took the
/// header for the arrival — `Ctx::last_arrival`, `DayReplay::arrival`,
/// DayReplay::wake_to_arrival_min — read the clock instead of the verb. The repair is in the
/// **writer**, so there is one fact and not two (AGENTS §5.3).
///
/// **The bite is asserted before the deletion**: the last arrival's logged `t` must BE 09:00, and
/// it must differ from the instant the command ran at, or every line below holds vacuously.
#[test]
fn a_retro_arrival_is_logged_at_its_own_time_and_survives_the_deletion() {
    let tm = plan_with_log("energy-14d");

    // The fixture's 2026-09-07 already holds `arrive lounge 07:10`; this is the second, and it is
    // dated four hours before the command that writes it.
    tm.ok_at(INSIDE, &["arrive", "home", "--at", "09:00"]);

    let arrivals: Vec<String> = log_lines(&tm)
        .iter()
        .filter(|l| l.contains(r#""ev":"arrive""#) && l.contains("2026-09-07T"))
        .cloned()
        .collect();
    assert_eq!(arrivals.len(), 2, "the day does not have two arrivals:\n  {}", arrivals.join("\n  "));
    // The bite, in the LOG: `arrive.t` is the arrival, not the clock.
    assert!(
        arrivals[1].contains(r#""t":"2026-09-07T09:00:00-05:00""#),
        "`arrive.t` is not the arrival, so `--at` survives only inside the payload:\n  {}",
        arrivals[1]
    );
    assert!(
        !arrivals[1].contains("T13:00:00"),
        "`arrive.t` is the instant the command ran at; this test's bite is gone:\n  {}",
        arrivals[1]
    );

    let before_bytes = fs::read_to_string(state_path(&tm)).expect("read .tm/state.json");
    let before_state: serde_json::Value = serde_json::from_str(&before_bytes).expect("JSON");
    assert_eq!(before_state["arrival"], "09:00", "the cache is not the retro arrival: {before_bytes}");
    let window = before_state["window"].as_array().expect("a window array");
    assert_eq!(window[0], "09:00", "the cached window does not start at the arrival: {before_bytes}");
    assert_ne!(window[0], window[1], "the cached window is a point: {before_bytes}");

    let before = answers(&tm, INSIDE, JSON_SPELLINGS);
    fs::remove_file(state_path(&tm)).expect("delete the runtime state");
    let first = tm.run_at(INSIDE, &["--json", "now"]);
    assert_eq!(first.code, 0, "the first verb after the deletion failed: {}{}", first.stdout, first.stderr);

    let after_bytes = fs::read_to_string(state_path(&tm)).expect("the runtime state was never rebuilt");
    let after_state: serde_json::Value = serde_json::from_str(&after_bytes).expect("JSON");
    for key in ["arrival", "window", "budget", "loc"] {
        assert_eq!(
            after_state[key], before_state[key],
            "the rebuild disagrees with the cache about `{key}` after a retro `--at` \
             (D45, README gap 1305):\n  cached  {}\n  rebuilt {}",
            before_state[key], after_state[key]
        );
    }
    let after = answers(&tm, INSIDE, JSON_SPELLINGS);
    same(&before, &after, "deleting the runtime state after a retro arrival moved an answer");

    // **And the day with two arrivals SAYS the window is recomputed** (gap 1306). The log's facts
    // carry only the first arrival's payload, so the rebuild computes the last one's from today's
    // walls; D42's rule is that such a field is named, never regenerated in silence.
    assert!(
        first.stderr.contains("RECOMPUTED rather than restored: `window` and `budget`"),
        "the rebuild recomputed the window on a two-arrival day and did not say so:\n{}",
        first.stderr
    );
}

/// **One arrival, and the tree moves under it** — README gap **1306**, the reuse critic's half.
///
/// W-23 made D42's rebuild recompute `window` and `budget` from `Ctx::arrival_window` **against
/// today's walls and config**, which is not the tree the arrival was logged against. Driven with
/// no `--at` anywhere: `arrive` at 09:00 logs `window ["09:00","17:00"]`, a calendar item is added
/// at 16:00, the cache is deleted, and the rebuild answers `["09:00","21:30"]` — hours of drift,
/// with the correct value sitting one line down in `.tm/log.jsonl`.
///
/// The repair reads the arrival record's own payload back whenever the log carries it, which on a
/// one-arrival day it always does. **The bite**: the added wall must actually move
/// `Ctx::arrival_window`, or this test is the row above with more files, so the recomputation is
/// asked for by name and asserted to differ from the logged answer.
#[test]
fn a_calendar_item_added_after_the_arrival_does_not_move_the_rebuilt_window() {
    let tm = corpus_plan("plan-basic");
    tm.ok_at(INSIDE, &["wake", "06:00"]);
    tm.ok_at(INSIDE, &["arrive", "lounge", "--at", "09:00"]);

    let before_bytes = fs::read_to_string(state_path(&tm)).expect("read .tm/state.json");
    let before_state: serde_json::Value = serde_json::from_str(&before_bytes).expect("JSON");
    let logged: Vec<String> = log_lines(&tm).iter().filter(|l| l.contains(r#""ev":"arrive""#)).cloned().collect();
    assert_eq!(logged.len(), 1, "the day must have exactly ONE arrival here:\n  {}", logged.join("\n  "));
    let before_window = before_state["window"].clone();

    // The wall that moves the formula: an evening Interval the arrival never saw.
    let cal = tm.plan.join("calendar/2026-W37.md");
    let mut text = fs::read_to_string(&cal).expect("read the calendar file");
    text.push_str("- [ ] 3 Late review          at:2026-09-07T16:00/19:30 loc:zoom ^g9\n");
    fs::write(&cal, &text).expect("write the calendar file");

    fs::remove_file(state_path(&tm)).expect("delete the runtime state");
    let first = tm.run_at(INSIDE, &["--json", "now"]);
    assert_eq!(first.code, 0, "the first verb after the deletion failed: {}{}", first.stdout, first.stderr);
    let after_state: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(state_path(&tm)).expect("rebuilt")).expect("JSON");

    for key in ["arrival", "window", "budget", "loc"] {
        assert_eq!(
            after_state[key], before_state[key],
            "a calendar item added after the arrival moved `{key}` on a rebuild \
             (D42/D45, README gap 1306):\n  cached  {}\n  rebuilt {}",
            before_state[key], after_state[key]
        );
    }

    // **The bite.** Ask the formula what it would have said with the new wall in the tree: if it
    // agrees with the logged window, this tree cannot tell a read from a recomputation.
    let planned = tm.run_at(INSIDE, &["--json", "plan"]);
    assert_eq!(planned.code, 0, "`tm --json plan` failed: {}{}", planned.stdout, planned.stderr);
    let with_wall = tm.run_at(INSIDE, &["arrive", "lounge", "--at", "09:00"]);
    assert_eq!(with_wall.code, 0, "the second arrive failed: {}{}", with_wall.stdout, with_wall.stderr);
    let recomputed: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(state_path(&tm)).expect("state")).expect("JSON");
    assert_ne!(
        recomputed["window"], before_window,
        "the added wall does not move `Ctx::arrival_window`, so this test would prove nothing: {}",
        recomputed["window"]
    );
}

/// **T9 with a break RUNNING: deleting `.tm/state.json` changes NOTHING** — the owner's **D105**
/// (README "Stage 6 — W-46 track K", gaps 1034, 1085 and 4740; parity **P100**), D42's
/// acceptance asserted for the one running state it could not answer for until now.
///
/// **What it was, and why it changed.** Until D105 `tm break` wrote `state.break_` and set
/// `active.paused` **without appending any event** — the `Event::Break` was written when the
/// break *ended*, stamped at its start — so a running break left no line in the log, and the
/// deletion brought the block back un-paused: this test asserted that move, bounded to exactly
/// one spelling and the pause (README gap 1085). Once R3's planner draws a running break (P45),
/// that same deletion moved `tm plan`, the three `tm log` views and `tm review day` and wrote a
/// `plan` event — a derived cache's deletion writing to its own authority, R3's second blocker
/// (gap 4740). D105 removes the second source of truth rather than restating the acceptance
/// around it: `tm break` logs a `break_start` when the break begins, the kernel's replay holds the
/// running break (`tm_core::log::Replay::open_break`), and the rebuild restores `break` and the
/// pause it sets from that line.
///
/// **What it asserts.** The bite first — a break RUNNING and a block PAUSED in the file, and the
/// `break_start` line in the log. Then, across the deletion: **no spelling of the eleven moves**;
/// the rebuilt file's running break, block and interruption are the deleted file's; the notice
/// says the break was RESTORED and nothing was GONE; and `.tm/log.jsonl` keeps its line count —
/// a derived cache's deletion costs no line of its authority.
#[test]
fn deleting_the_runtime_state_while_a_break_runs_changes_nothing() {
    let tm = plan_with_log("energy-14d");
    tm.ok_at(INSIDE, &["wake", "06:05"]);
    tm.ok_at(INSIDE, &["arrive", "lounge"]);
    tm.ok_at(INSIDE, &["start", "^p1"]);
    tm.ok_at(LATER, &["break", "20m", "--where", "walk"]);
    let started: Vec<String> = log_lines(&tm).into_iter().filter(|l| l.contains("\"ev\":\"break_start\"")).collect();
    assert_eq!(started.len(), 1, "`tm break` logged no `break_start` (D105): {started:?}");

    let before = answers(&tm, LATER, JSON_SPELLINGS);
    let before_lines = log_lines(&tm).len();
    let before_bytes = fs::read_to_string(state_path(&tm)).expect("read .tm/state.json");
    let before_state: serde_json::Value =
        serde_json::from_str(&before_bytes).expect(".tm/state.json is not JSON");
    // The bite: without a RUNNING break and a PAUSED block in the file, every line below is
    // vacuously true and this test is the one above with more words.
    assert_eq!(
        before_state["active"]["paused"], true,
        "nothing is paused, so this test would prove nothing: {before_bytes}"
    );
    assert!(
        !before_state["break"].is_null(),
        "no break is running, so this test would prove nothing: {before_bytes}"
    );

    fs::remove_file(state_path(&tm)).expect("delete the runtime state");

    let first = tm.run_at(LATER, &["--json", "now"]);
    assert_eq!(first.code, 0, "the first verb after the deletion failed: {}{}", first.stdout, first.stderr);
    assert!(
        first.stderr.contains("RESTORED from the log: `break`"),
        "the rebuild did not say the running break came back: {:?}",
        first.stderr
    );
    assert!(!first.stderr.contains("GONE"), "the rebuild said something was gone: {:?}", first.stderr);

    let after = answers(&tm, LATER, JSON_SPELLINGS);
    assert_eq!(
        moved(&before, &after),
        Vec::<String>::new(),
        "deleting the runtime state while a break runs moved an answer (D42, D105)"
    );
    // **The authority was not written to.** A derived cache's deletion may not cost a log line.
    assert_eq!(
        log_lines(&tm).len(),
        before_lines,
        "deleting the derived runtime state appended to .tm/log.jsonl"
    );

    let after_state: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(state_path(&tm)).expect("rebuilt state"))
            .expect("the rebuilt .tm/state.json is not JSON");
    for field in ["break", "active", "interrupt", "date", "wake", "loc"] {
        assert_eq!(
            after_state[field], before_state[field],
            "`{field}` did not come back out of the log:\nBEFORE {before_bytes}\nAFTER  {after_state}"
        );
    }

    eprintln!(
        "running-break deletion: 0 of {} `--json` spellings moved, {} log lines before and after",
        before.len(),
        before_lines
    );
}

/// **A running break with no block is RESTORED and named** — README gap **1191** (W-22: the
/// break was discarded with no `tm:` line at all, the inverse of D42's rule that a field which
/// cannot be derived fails LOUDLY), and since the owner's **D105** (parity P100) the stronger
/// claim: the break CAN be derived, so it comes back, and the notice says so by name.
///
/// The bite is the second assertion: without a running break and **no** active block in the
/// file, this is [`deleting_the_runtime_state_while_a_break_runs_changes_nothing`] again.
#[test]
fn a_break_running_with_no_block_is_restored_and_named() {
    let tm = plan_with_log("energy-14d");
    tm.ok_at(INSIDE, &["wake", "06:05"]);
    tm.ok_at(INSIDE, &["break", "20m", "--where", "walk"]);

    let before_bytes = fs::read_to_string(state_path(&tm)).expect("read .tm/state.json");
    let before_state: serde_json::Value =
        serde_json::from_str(&before_bytes).expect(".tm/state.json is not JSON");
    assert!(
        !before_state["break"].is_null(),
        "no break is running, so this test would prove nothing: {before_bytes}"
    );
    assert!(
        before_state["active"].is_null(),
        "a block is running, so this is the test above with fewer words: {before_bytes}"
    );

    let before_lines = log_lines(&tm).len();
    fs::remove_file(state_path(&tm)).expect("delete the runtime state");

    let first = tm.run_at(INSIDE, &["--json", "now"]);
    assert_eq!(first.code, 0, "the first verb after the deletion failed: {}{}", first.stdout, first.stderr);
    assert!(
        first.stderr.contains("RESTORED from the log: `break`"),
        "the running break was not named as restored (gap 1191, D105): {:?}",
        first.stderr
    );
    assert!(
        first.stderr.contains("rebuilt from .tm/log.jsonl"),
        "the rebuild itself was not announced: {:?}",
        first.stderr
    );

    // The break came back, and nothing was written to the authority to bring it.
    let after: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(state_path(&tm)).expect("rebuilt state"))
            .expect("the rebuilt .tm/state.json is not JSON");
    assert_eq!(after["break"], before_state["break"], "the running break did not come back out of the log");
    assert_eq!(
        log_lines(&tm).len(),
        before_lines,
        "deleting the derived runtime state appended to .tm/log.jsonl"
    );
}

/// **D42's notice names only what did not come back** — README gap **1192**, repaired at the
/// W-22 repair step.
///
/// The notice used to print a constant list of four fields as *"NOT restored"*. Driven by two
/// auditors: the rebuilt `.tm/state.json` is **byte-identical** to the deleted one on all four.
/// `active.paused` is the discriminating case — a block paused by `tm pause` comes back
/// **paused**, because `Event::Pause` is in the log — and the parenthetical *"a paused block
/// comes back RUNNING"* is true only of a pause a running `break` set, which is a different
/// thing. A loud notice that names what it did in fact restore trains the reader to ignore it,
/// which is what makes gap 1191's silence land.
///
/// So: the file comes back identical, and the notice says so rather than the opposite.
#[test]
fn the_rebuild_notice_names_only_what_did_not_come_back() {
    let tm = plan_with_log("energy-14d");
    // The arrival matters: the fixture's log carries an `Event::Arrive` for this day, so a
    // rebuild derives `arrival`, `window` and `budget` whether or not the host ever wrote
    // them. Without this line the rebuilt file is BETTER than the deleted one and the
    // byte-equality below fails for a reason that is not the defect.
    tm.ok_at(INSIDE, &["wake", "06:05"]);
    tm.ok_at(INSIDE, &["arrive", "lounge"]);
    tm.ok_at(INSIDE, &["start", "^p1"]);
    tm.ok_at(INSIDE, &["pause"]);

    let before_bytes = fs::read_to_string(state_path(&tm)).expect("read .tm/state.json");
    let before_state: serde_json::Value =
        serde_json::from_str(&before_bytes).expect(".tm/state.json is not JSON");
    // The bite: a block paused by `tm pause`, which is the case the old sentence was false about.
    assert_eq!(
        before_state["active"]["paused"], true,
        "nothing is paused, so this test would prove nothing: {before_bytes}"
    );
    assert!(
        before_state["break"].is_null(),
        "a break is running, so this is the break test and not this one: {before_bytes}"
    );

    fs::remove_file(state_path(&tm)).expect("delete the runtime state");
    let first = tm.run_at(INSIDE, &["--json", "now"]);
    assert_eq!(first.code, 0, "the first verb after the deletion failed: {}{}", first.stdout, first.stderr);

    let after_bytes = fs::read_to_string(state_path(&tm)).expect("rebuilt state");
    let after_state: serde_json::Value =
        serde_json::from_str(&after_bytes).expect("the rebuilt .tm/state.json is not JSON");
    // **The four fields the old sentence named, and they all came back.** Not whole-file
    // byte equality, and the reason is a finding of its own: on this fixture the deleted
    // cache holds the LAST `tm arrive` of the day and the rebuild derives the FIRST, so
    // `arrival`, `window` and `budget` differ for a reason that has nothing to do with the
    // notice (README gap 1202). By hand on a tree with no fixture log, `cmp` says the
    // rebuilt file is byte-identical — that drive is in the README block.
    for field in ["active", "priorities_yesterday", "closed"] {
        assert_eq!(
            after_state[field], before_state[field],
            "`{field}` did not come back, so the notice was right about it:\n\
             BEFORE {before_bytes}\nAFTER  {after_bytes}"
        );
    }
    assert!(
        !first.stderr.contains("were NOT restored"),
        "the notice still claims a list it did not check: {:?}",
        first.stderr
    );
    assert!(
        !first.stderr.contains("comes back RUNNING"),
        "the block came back PAUSED and the notice says it came back running: {:?}",
        first.stderr
    );
    assert!(
        first.stderr.contains("came back from the log's own"),
        "the notice does not say the pause was restored: {:?}",
        first.stderr
    );
    assert!(
        first.stderr.contains("RECOMPUTED"),
        "`active.est_min` came back from another source and the notice calls it lost: {:?}",
        first.stderr
    );
}

/// **T9**: a changed `tz` invalidates the checkpoint — the tree answers in the **new** zone.
///
/// The comparand is the same tree with the cache deleted: two trees identical in every byte except
/// the derived cache must answer identically, or the cache decided something. That is the exact
/// claim "invalidates the checkpoint" makes, and it is the claim whether the cache holds a zone
/// table (before S) or a zone-keyed `ckpt.json` (since S, whose integrity check refuses a differing
/// zone key and goes to genesis, §9.8).
///
/// **The answers alone did not make that claim, and now the checkpoint itself is read** (W-11 audit
/// repair, README gap 195). The two `--json` comparisons above are necessary and not sufficient: on
/// this fixture they both hold *even when the whole of `Snapshot::valid_for` is neutralised*
/// — measured — so a test that stopped there would stay green while the mechanism it is named for
/// was deleted (README gap 16, AGENTS §9.2). So the checkpoint on disk is read before and after:
/// it must be re-keyed to the new zone, in a **new generation naming the old one**, and its
/// manifest must name that new generation's records rather than the old zone's.
///
/// **What this still cannot separate, said plainly.** The host's `valid_for` is not the only zone
/// guard: the kernel's G0 refuses the same checkpoint (`ckpt.tzKey ≠ tz.key`), and the host's
/// fallback from that refusal is the same genesis, writing the same fresh generation. So no
/// CLI-visible fact distinguishes the two, and neutralising the host's branch alone leaves every
/// assertion here true. The guard that *is* separable is asserted where it can be —
/// `kernel_replay_parity.rs`'s `t5_a_changed_zone_key_is_refused_by_the_host_and_by_the_kernel_behind_it`,
/// which reads `rebuilt_because` (`another zone`, not `zone at line 0`) — and the host's own unit
/// test `a_snapshot_round_trips_its_text_with_the_checkpoint_verbatim` keeps `valid_for`'s four
/// refusals by name.
#[test]
fn a_changed_tz_invalidates_the_checkpoint() {
    let tm = plan_with_log("energy-14d");
    tm.ok_at(LATER, &["now"]);
    let under_chicago = answers(&tm, LATER, JSON_SPELLINGS);
    let zone_before = fs::read_to_string(cache_dir(&tm).join("tz.json")).unwrap_or_default();
    assert!(zone_before.contains("America/Chicago"), "the cache is not keyed by the old zone");

    // The checkpoint the old zone wrote, and something actually sealed under it: without a
    // checkpoint there is nothing here to invalidate, and the test would be about nothing.
    let ckpt_before = checkpoint(&tm);
    let gen_before = ckpt_str(&ckpt_before, "gen");
    let key_before = ckpt_str(&ckpt_before, "tzKey");
    assert!(key_before.starts_with("America/Chicago"), "the checkpoint is not keyed by the old zone: {key_before}");
    let months_before = ckpt_before["manifest"].as_object().expect("a manifest").len();
    assert!(months_before > 0, "the checkpoint seals no month, so there is no checkpoint to invalidate");

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

    // The checkpoint itself: re-keyed, a new generation, and the old zone's records unread.
    let ckpt_after = checkpoint(&tm);
    let key_after = ckpt_str(&ckpt_after, "tzKey");
    let gen_after = ckpt_str(&ckpt_after, "gen");
    assert!(key_after.starts_with("Asia/Tokyo"), "the checkpoint still carries the old zone's key: {key_after}");
    assert_ne!(gen_after, gen_before, "the old zone's generation was kept, so the checkpoint was not invalidated");
    assert_eq!(ckpt_str(&ckpt_after, "prevGen"), gen_before, "the new generation must name the old-zone one it replaced");
    let manifest = ckpt_after["manifest"].as_object().expect("a manifest");
    assert_eq!(manifest.len(), months_before, "the rebuild seals the same months");
    for (month, file) in manifest {
        let file = file.as_str().unwrap_or_else(|| panic!("{month} names no file: {file}"));
        assert!(file.contains(&gen_after), "{month} reads a record of another generation: {file}");
        assert!(!file.contains(&gen_before), "{month} still reads the old zone's sealed record: {file}");
    }

    eprintln!(
        "changed tz: {} of {} answers moved: {bite:?}; the checkpoint went {key_before} g{gen_before} → {key_after} g{gen_after} over {months_before} sealed months",
        bite.len(),
        under_chicago.len()
    );
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
/// **Un-ignored at S — the body is the one that was already written.** The notice exists (`kernel_log.rs`) but has no
/// emitter: nothing under `tm/src` calls it, because nothing under `tm/src` calls `kernel_log` at
/// all. Asserting "at most one notice" would pass today and assert nothing, so the body below is
/// the post-switch one and S's acceptance is to delete the `#[ignore]`. The half that *is* true
/// today is asserted by the sibling test `deleting_the_replay_cache_changes_nothing`: an
/// unwritable cache directory does not move an answer (driven by hand at this commit, 0 differences).
#[cfg(unix)]
#[test]
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
/// **Un-ignored at S — the body is the one that was already written.** `GenesisError::ReachTooFar` is built and tested in
/// `kernel_log.rs`, but it has no call site in the binary: gap 120 part 3 has said so since W-6, and
/// nothing in `tm/src` calls `kernel_log`. Today the Rust reader replays the whole log and this
/// input simply works, so there is no failure to name. The body is the post-switch one; S's
/// acceptance is to delete the `#[ignore]`.
#[test]
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
