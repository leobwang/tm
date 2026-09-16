//! **The door the switch opens** (stage 5 D9, step S's precondition; design
//! `kernel/design/stage5/stage5-D9-D10-design.md` §14.6 items 1-2, §11.1, §11.4).
//!
//! `Ctx::replay_with`'s body becomes `kernel_log::replay_scoped(scope)` at S. This file is what
//! says that body is the same reader: every function the switch will call is compared here with
//! the **in-tree Rust reader S deletes**, through the test chokepoint (`support/replay.rs`), while
//! that reader still exists to be compared against.
//!
//! It exists because the alternative is a fourth artifact built to a shape S replaces. The README
//! already names three (gaps 93, 130 and 132), and committing ~450 lines of uncalled, untested
//! host code would have been the fourth. Each test below is one of S's claims, measurable now:
//!
//! | test | S's claim |
//! |---|---|
//! | [`the_door_is_the_reader_it_replaces`] | §14.6 item 1: the `All` scope's `Replay` **is** `Ctx::replay_of`'s, field for field, over the corpus and a generated month |
//! | [`the_doors_narrow_scopes_carry_what_they_promise`] | §11.1: `Hot` carries the answer's own days; every day record it does carry is the whole reader's |
//! | [`the_door_names_every_unreadable_line_not_just_the_last_calls`] | D18 (i): `tm check` must name **every** refused line, and the answer's `warnings` array is per call |
//! | [`the_doors_render_is_the_lines_own_bytes`] | §11.4 steps 3-5: a selected line's payload is the kernel's rendering of that line |
//! | [`the_doors_tail_headers_are_the_recorders`] | §14.3 row R6: `tm undo`'s recorder reads the same headers from the same cut |
//! | [`the_doors_hot_scope_answers_every_all_time_question`] | gap 135: every §8.4 column-**A** fact is whole at `Hot`, the two done-date questions included |
//! | [`the_doors_total_is_the_logs_all_time_entry_count`] | gap 136: `tm log`'s `total` is `facts.entryCount`, not the row count of the scope |
//!
//! Nothing here is a twin of the shipped code: each test calls the function `Ctx` will call.

#[allow(dead_code)]
#[path = "../src/cli/tz_table.rs"]
mod tz_table;

#[allow(dead_code)]
#[path = "../src/cli/kernel_log.rs"]
mod kernel_log;

#[allow(dead_code)]
#[path = "support/replay.rs"]
mod replay;

#[allow(dead_code)]
#[path = "support/loggen.rs"]
mod loggen;

use std::collections::BTreeSet;
use std::path::Path;

use chrono::NaiveDate;
use chrono_tz::Tz;
use serde_json::Value;

const TZ: Tz = chrono_tz::America::Chicago;

/// The corpus logs T5 reads, by the same paths.
fn corpus_logs() -> Vec<(String, String)> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../kernel/corpus");
    [
        "logs/energy-14d.jsonl",
        "logs/malformed.jsonl",
        "logs/review-14d.jsonl",
        "logs/three-days.jsonl",
        "plan-home-day/.tm/log.jsonl",
        "plan-recur/.tm/log.jsonl",
        "plan-travel-day/.tm/log.jsonl",
    ]
    .iter()
    .map(|p| (p.to_string(), std::fs::read_to_string(root.join(p)).expect("corpus log")))
    .collect()
}

/// The day after the log's last dated line: a `now` at or past the ledger day, so the cache
/// persists its checkpoint rather than answering an unpersisted genesis (§9.7's G4).
fn day_after(text: &str) -> NaiveDate {
    let last = text
        .lines()
        .rev()
        .find_map(|l| {
            let v: Value = serde_json::from_str(l).ok()?;
            let t = v.get("t")?.as_str()?;
            chrono::DateTime::parse_from_rfc3339(t).ok()
        })
        .expect("a dated line");
    last.with_timezone(&TZ).date_naive() + chrono::Duration::days(1)
}

/// The zone table the host sends, cached under the plan root as the binary caches it (D13).
fn wire(root: &Path) -> Value {
    tz_table::wire_for(Some(&root.join(kernel_log::CACHE_DIR)), TZ)
}

/// One plan root holding `text`, and its bytes.
fn tree(text: &str) -> (tempfile::TempDir, Vec<u8>) {
    let dir = tempfile::tempdir().expect("a temp dir");
    std::fs::create_dir_all(dir.path().join(".tm")).expect("mkdir .tm");
    std::fs::write(dir.path().join(".tm/log.jsonl"), text).expect("write the log");
    let bytes = std::fs::read(dir.path().join(".tm/log.jsonl")).expect("read the log");
    (dir, bytes)
}

/// The door, at one scope, over a tree that already holds the log.
fn door(root: &Path, bytes: &[u8], today: NaiveDate, scope: kernel_log::Scope) -> kernel_log::Read {
    kernel_log::replay_scoped(root, bytes, TZ, &wire(root), today, scope, None)
        .unwrap_or_else(|e| panic!("the door answers: {e:?}"))
}

/// **§14.6 item 1**: the `All`-scope `Replay` is the one `Ctx::replay_of` derives, field for field
/// (the fork's own `PartialEq`, every field placed by its destructuring) and including the facts
/// D14 ports though nothing reads them.
///
/// The scopes are asked in turn on one root, so the second call reads the checkpoint the first
/// wrote: the merge is exercised against a real cache, not a single genesis.
#[test]
fn the_door_is_the_reader_it_replaces() {
    let mut logs = corpus_logs();
    logs.push(("generated 1mo (40 a day)".into(), loggen::text(&loggen::log(loggen::Rate::Forty, 30))));
    logs.push(("generated 1mo (61 a day)".into(), loggen::text(&loggen::log(loggen::Rate::SixtyOne, 30))));
    let (mut compared, mut days) = (0usize, 0usize);
    for (name, text) in &logs {
        let (dir, bytes) = tree(text);
        let today = day_after(text);
        let fork = replay::replay_of_text(text, TZ);
        // Twice: genesis, then from the checkpoint it wrote.
        for pass in ["genesis", "from the checkpoint"] {
            let read = door(dir.path(), &bytes, today, kernel_log::Scope::All);
            assert!(
                read.replay == fork,
                "{name} ({pass}): the door's Replay is not the reader's"
            );
            assert_eq!(read.replay.ported_facts(), fork.ported_facts(), "{name} ({pass}): the ported facts (D14)");
            assert_eq!(read.replay.line_count(), fork.line_count(), "{name} ({pass}): the line count");
            assert_eq!(read.replay.entry_count(), fork.entry_count(), "{name} ({pass}): the entry count");
            assert_eq!(read.replay.view(), fork.view(), "{name} ({pass}): the view rows");
            compared += 1;
        }
        days += fork.days.len();
    }
    eprintln!("the door: {} logs, {compared} scoped reads, {days} days compared, 0 differences", logs.len());
}

/// Which top-level fields of `a` differ from `b`'s: what a scope narrows away, by name.
///
/// A narrowing is not a disagreement — the caller asserts separately that every record a scope
/// *does* carry is the whole reader's — but which fields narrow is what a verb author needs to
/// know before choosing a scope, and §11.1's prose does not say.
fn narrowed_fields(a: &tm_core::log::Replay, b: &tm_core::log::Replay) -> Vec<&'static str> {
    let mut out = Vec::new();
    if a.days != b.days { out.push("days"); }
    if a.items != b.items { out.push("items"); }
    if a.instances != b.instances { out.push("instances"); }
    if a.energy != b.energy { out.push("energy"); }
    if a.durations != b.durations { out.push("durations"); }
    if a.interrupts != b.interrupts { out.push("interrupts"); }
    if a.named != b.named { out.push("named"); }
    if a.demotions != b.demotions { out.push("demotions"); }
    if a.closes != b.closes { out.push("closes"); }
    if a.dropped_items != b.dropped_items { out.push("dropped_items"); }
    if a.done_items != b.done_items { out.push("done_items"); }
    if a.last_done != b.last_done { out.push("last_done"); }
    if a.done_dates != b.done_dates { out.push("done_dates"); }
    if a.longest_leak != b.longest_leak { out.push("longest_leak"); }
    if a.open_block != b.open_block { out.push("open_block"); }
    if a.open_interrupt != b.open_interrupt { out.push("open_interrupt"); }
    if a.unknown != b.unknown { out.push("unknown"); }
    if a.warnings != b.warnings { out.push("warnings"); }
    if a.seams != b.seams { out.push("seams"); }
    if a.last_effective_t != b.last_effective_t { out.push("last_effective_t"); }
    // `Replay`'s `PartialEq` skips `rows` as line bookkeeping, so the narrowing
    // measured at W-7 never looked at it — and it *does* narrow, because every
    // row comes from a day record's headers. `tm check`'s far-future scan reads
    // `view()` (gap 132), which is why the omission mattered.
    if a.rows != b.rows { out.push("rows"); }
    if a.entry_count() != b.entry_count() { out.push("entry_count"); }
    if a.done_date_totals != b.done_date_totals { out.push("done_date_totals"); }
    out
}

/// **§11.1**: `Hot` merges the answer only. It is therefore a *narrowing*, never a disagreement —
/// every day record it carries is the whole reader's, and the all-time facts the checkpoint holds
/// (items, instances, named records, the open machine) are whole at every scope.
#[test]
fn the_doors_narrow_scopes_carry_what_they_promise() {
    let text = loggen::text(&loggen::log(loggen::Rate::Forty, 200));
    let (dir, bytes) = tree(&text);
    let today = day_after(&text);
    let fork = replay::replay_of_text(&text, TZ);

    let all = door(dir.path(), &bytes, today, kernel_log::Scope::All);
    assert!(all.replay == fork, "the `All` scope is the whole reader's");

    let hot = door(dir.path(), &bytes, today, kernel_log::Scope::Hot);
    assert!(
        hot.replay.days.len() < fork.days.len(),
        "a 200-day log must fold something, else this test proves nothing: {} of {} days",
        hot.replay.days.len(),
        fork.days.len()
    );
    for (date, day) in &hot.replay.days {
        assert_eq!(Some(day), fork.days.get(date), "the hot day {date} is not the reader's");
    }
    // **Which fields a scope narrows**, measured rather than assumed. §11.1 says `Hot` merges
    // "the answer only (A, W, O)" without saying which of `Replay`'s fields that leaves short,
    // and the answer turns out to be less obvious than the sentence: an item's *aggregate*
    // minutes ride the checkpoint, but its per-day breakdown and its done dates are the window
    // records', so `items` and `done_dates` narrow with the scope while `named` does not.
    let narrowed = narrowed_fields(&hot.replay, &fork);
    assert!(
        !narrowed.contains(&"named"),
        "`named` rides the checkpoint and must be whole at every scope; narrowed: {narrowed:?}"
    );
    assert_eq!(hot.replay.line_count(), fork.line_count(), "the line count is whole at `Hot`");
    eprintln!("the door's `Hot` narrowing: {narrowed:?}");

    // `Dates` reaches back to the days it names, and each is the reader's.
    let first = *fork.days.keys().next().expect("a day");
    let dates = door(
        dir.path(),
        &bytes,
        today,
        kernel_log::Scope::Dates { from: first, to: first + chrono::Duration::days(6) },
    );
    let reached: BTreeSet<NaiveDate> = dates.replay.days.keys().copied().collect();
    assert!(reached.contains(&first), "the `Dates` scope reaches its own first day");
    for d in &reached {
        assert_eq!(dates.replay.days.get(d), fork.days.get(d), "the dated day {d} is not the reader's");
    }
    eprintln!("the door's `Dates` narrowing: {:?}", narrowed_fields(&dates.replay, &fork));
    eprintln!(
        "the door's scopes: hot {} days, dates {} days, all {} days, reader {} days",
        hot.replay.days.len(),
        dates.replay.days.len(),
        all.replay.days.len(),
        fork.days.len()
    );
}

/// **D18 (i)**: `tm check` must name every line the reader refuses.
///
/// The answer's `warnings` array is **per call** (`Boundary.logBody` over `logVerdicts`): a hot
/// call carries its tail's only, and genesis returns only its last chunk's. So the sweep is its
/// own read-only pass over the whole file, and this test puts a bad line in the *first* chunk of a
/// log several chunks long — the line a per-call array would silently drop.
#[test]
fn the_door_names_every_unreadable_line_not_just_the_last_calls() {
    let mut lines = loggen::log(loggen::Rate::SixtyOne, 200);
    assert!(lines.len() > 2 * kernel_log::CHUNK_LINES, "the log must span chunks: {} lines", lines.len());
    // One in the first chunk, one in the middle, one in the last.
    let early = 10;
    let middle = kernel_log::CHUNK_LINES + 500;
    let late = lines.len() - 3;
    for i in [early, middle, late] {
        lines[i] = "not json at all".to_string();
    }
    let text = loggen::text(&lines);
    let (dir, bytes) = tree(&text);
    let now = day_after(&text).to_string();

    let swept = kernel_log::line_warnings(&bytes, &now, &wire(dir.path())).expect("the sweep answers");
    let got: Vec<u64> = swept.iter().map(|w| w.line as u64).collect();
    let want = replay::warning_lines_of_text(&text);
    assert_eq!(got, want, "the sweep's lines are the reader's");
    assert_eq!(
        got,
        vec![early as u64 + 1, middle as u64 + 1, late as u64 + 1],
        "every damaged line is named, whichever chunk it fell in"
    );
    for w in &swept {
        assert_eq!(w.text, "not json at all", "the warning quotes the line's own bytes");
        assert!(w.error.starts_with("not JSON"), "the warning names its cause: {}", w.error);
    }

    // A line that is not UTF-8 keeps the fork's phrase, which `tm check`'s own test asserts.
    let mut raw = text.into_bytes();
    raw.extend_from_slice(b"{\"t\":\"2026-09-07T08:30:00-05:00\",\"ev\":\"note\",\"text\":\"\xff\xfe\"}\n");
    let swept = kernel_log::line_warnings(&raw, &now, &wire(dir.path())).expect("the sweep answers");
    let last = swept.last().expect("a warning");
    assert_eq!(last.error, "invalid UTF-8", "D18 (i) keeps the phrase `tm check` is tested on");
    eprintln!(
        "the door's sweep: {} lines / {} bytes, {} warnings over {} chunks",
        lines.len() + 1,
        raw.len(),
        swept.len(),
        lines.len() / kernel_log::CHUNK_LINES + 1
    );
}

/// **§11.4 steps 3-5**: the payload `tm log` prints is the kernel's rendering of that line's own
/// bytes — for lines scattered across chunk boundaries, which is the case a single call cannot
/// serve.
#[test]
fn the_doors_render_is_the_lines_own_bytes() {
    let lines = loggen::log(loggen::Rate::SixtyOne, 120);
    let text = loggen::text(&lines);
    let (dir, bytes) = tree(&text);
    let now = day_after(&text).to_string();
    let n = lines.len() as u64;
    let wanted: Vec<u64> = vec![1, 2, kernel_log::CHUNK_LINES as u64, kernel_log::CHUNK_LINES as u64 + 1, n / 2, n - 1, n];

    let rendered = kernel_log::render_lines(&bytes, &now, &wire(dir.path()), &wanted).expect("the render answers");
    let fork: std::collections::BTreeMap<u64, tm_core::log::LogEntry> =
        replay::entries_of_text(&text).into_iter().collect();
    assert_eq!(rendered.len(), wanted.len(), "every wanted line comes back");
    for line in &wanted {
        let (value, display) = rendered.get(line).unwrap_or_else(|| panic!("line {line} was not rendered"));
        let entry = fork.get(line).unwrap_or_else(|| panic!("the reader has no line {line}"));
        assert_eq!(
            *value,
            serde_json::to_value(entry).expect("the reader's entry serialises"),
            "line {line}: the kernel's rendering is not the reader's entry"
        );
        assert_eq!(*display, entry.t.format("%Y-%m-%d %H:%M").to_string(), "line {line}: the display");
    }
    eprintln!("the door's render: {} lines asked of a {}-line log, across {} chunks", wanted.len(), n, n as usize / kernel_log::CHUNK_LINES + 1);
}

/// **§14.3 row R6**: `tm undo`'s recorder reads the headers a command appended. The door's tail
/// read gives the same `(line, tag, id)` as the whole replay's `headers_from`, at every cut — the
/// property `ctx.rs`'s own `the_recorders_tail_is_the_whole_replays` pins for the reader S deletes.
#[test]
fn the_doors_tail_headers_are_the_recorders() {
    let gen = loggen::text(&loggen::log(loggen::Rate::SixtyOne, 2));
    let mut lines: Vec<&str> = gen.lines().collect();
    lines.truncate(60);
    let good = lines.join("\n");
    let torn = &lines[3][..lines[3].len() / 2];
    let texts = [
        String::new(),
        "\n".to_string(),
        format!("{good}\n"),
        good.clone(),
        format!("{}\n\n{}\nnot json\n{}\r\n{}\n", lines[0], lines[1], lines[2], lines[4]),
        format!("{}\n{torn}", lines[0]),
        format!("{}\n{torn}{}\n{}\n", lines[0], lines[5], lines[6]),
    ];
    let mut cuts = 0;
    for (k, text) in texts.iter().enumerate() {
        let (dir, bytes) = tree(text);
        let now = if text.trim().is_empty() { "2026-09-15".to_string() } else { day_after(text).to_string() };
        let whole = replay::replay_of_text(text, TZ);
        for after in 0..=whole.line_count() + 2 {
            let got = kernel_log::headers_after(&bytes, &now, &wire(dir.path()), after).expect("a tail read");
            let want: Vec<(u64, String, Option<String>)> = whole
                .headers_from(after + 1)
                .iter()
                .map(|r| (r.line, r.tag.clone(), r.id.clone()))
                .collect();
            assert_eq!(got, want, "text {k}, after {after}");
            cuts += 1;
        }
    }
    eprintln!("the door's tail headers: {} texts, {cuts} cuts, 0 differences", texts.len());
}


/// **§9.6's pin — the one door function nothing called.** `max_line_of` reads `.tm/undo.json`
/// directly, because the seal policy needs a number and `UndoStack::load` wants the whole `Ctx`
/// this is called to build. It is exercised here because
/// [`every_door_function_the_switch_calls_is_exercised_here`] found it shipped into the binary
/// and called by nothing at all: not `tm/src` (nothing there reaches this module before S), not
/// a test, and not the module's own `#[cfg(test)]` block. The module-wide `#![allow(dead_code)]`
/// meant no warning could say so.
///
/// The three rules it has to keep: the **smallest** young `log_line` wins, an entry older than
/// 14 days does not pin the tail, and an entry written before R6 — with no `log_line` — is
/// ignored (CRIT 27).
#[test]
fn the_doors_undo_pin_is_the_smallest_young_log_line() {
    let now = chrono::DateTime::parse_from_rfc3339("2026-09-15T08:00:00-05:00").expect("a now");
    let entry = |t: &str, line: Option<u64>| match line {
        Some(l) => serde_json::json!({"t": t, "log_line": l}),
        None => serde_json::json!({"t": t}),
    };
    let stack = |entries: Vec<Value>| serde_json::json!({"entries": entries}).to_string();

    // The smallest of the young ones, not the last and not the first.
    let young = stack(vec![
        entry("2026-09-14T09:00:00-05:00", Some(400)),
        entry("2026-09-15T07:00:00-05:00", Some(120)),
        entry("2026-09-13T09:00:00-05:00", Some(310)),
    ]);
    assert_eq!(kernel_log::max_line_of(&young, now), Some(120));

    // Older than 14 days: a light user's stale stack does not pin the tail.
    let stale = stack(vec![
        entry("2026-08-01T09:00:00-05:00", Some(7)),
        entry("2026-09-14T09:00:00-05:00", Some(400)),
    ]);
    assert_eq!(kernel_log::max_line_of(&stale, now), Some(400));
    let all_stale = stack(vec![entry("2026-08-01T09:00:00-05:00", Some(7))]);
    assert_eq!(kernel_log::max_line_of(&all_stale, now), None);

    // Pre-R6 entries carry no `log_line` (CRIT 27), and neither does an empty
    // or an unreadable stack.
    let pre_r6 = stack(vec![entry("2026-09-14T09:00:00-05:00", None)]);
    assert_eq!(kernel_log::max_line_of(&pre_r6, now), None);
    assert_eq!(kernel_log::max_line_of(&stack(vec![]), now), None);
    assert_eq!(kernel_log::max_line_of("not json", now), None);
}

/// **§11.1's host-side merge, asserted directly.** `merge_records` is what the `All` scope uses
/// instead of `LogReq.merged`, whose request carries at most `MAX_SEALED_IN` = 62 records. Until
/// now it was only ever exercised *through* [`the_door_is_the_reader_it_replaces`], which cannot
/// separate a merge fault from a decode fault, and which on a small log merges nothing at all.
///
/// The two rules a reseal depends on: the answer's own record **wins** where both hold a day, and
/// the merged array comes out in day-key order whatever order the records arrive in.
#[test]
fn the_doors_merge_prefers_the_answer_and_keeps_day_order() {
    let facts = serde_json::json!({
        "days": [[12, "answer-12"], [10, "answer-10"]],
        "window": [[12, "w-answer-12"]],
    });
    let sealed = |pairs: Vec<(u64, &str)>| {
        pairs.into_iter().map(|(d, t)| (d, t.to_string())).collect::<std::collections::BTreeMap<u64, String>>()
    };
    let days = sealed(vec![(8, r#"[8,"sealed-8"]"#), (10, r#"[10,"sealed-10"]"#)]);
    let window = sealed(vec![(9, r#"[9,"w-sealed-9"]"#)]);

    let got = kernel_log::merge_records(&facts, &days, &window).expect("the merge");
    let keys: Vec<u64> = got["days"].as_array().expect("days").iter().map(|r| r[0].as_u64().expect("a day")).collect();
    assert_eq!(keys, vec![8, 10, 12], "day-key order, whatever order the records arrive in");
    assert_eq!(got["days"][1][1], "answer-10", "the answer's record wins where both hold the day");
    assert_eq!(got["days"][0][1], "sealed-8", "a day only the seal holds is carried");
    let wkeys: Vec<u64> = got["window"].as_array().expect("window").iter().map(|r| r[0].as_u64().expect("a day")).collect();
    assert_eq!(wkeys, vec![9, 12], "the window array merges by the same rule");

    // Nothing sealed is the identity, which is what `Hot` relies on.
    let empty = std::collections::BTreeMap::new();
    assert_eq!(kernel_log::merge_records(&facts, &empty, &empty).expect("the merge"), facts);
    // A record that is not JSON is named, not silently dropped.
    let bad = sealed(vec![(8, "not json")]);
    assert!(kernel_log::merge_records(&facts, &bad, &empty).is_err(), "a torn sealed record is a fault");
}

/// **The instrument the module-wide `#![allow(dead_code)]` takes away** (W-7 audit, defect 2).
///
/// `tm/src/cli/kernel_log.rs` carries `#![allow(dead_code)]` because before S nothing under
/// `tm/src` calls it: with the attribute removed, `cargo check -p tm --all-targets` warns on **92
/// items** — 79 that predate step S and 13 that are S's, of which 10 sit below the DOOR banner
/// and three above it (`Scope`, `Read`, `caches`). That is noise control, but it also means the
/// compiler cannot tell anyone that a function was shipped into the binary and called by nothing
/// — and `cargo test --workspace`'s "0 warnings" then carries no information about it.
///
/// This is the replacement: every `pub fn` below the DOOR banner in that file — the functions
/// `Ctx` calls at S — must be named as `kernel_log::<name>` somewhere in *this* file. A step that
/// adds a door function without a test fails here instead of passing quietly.
#[test]
fn every_door_function_the_switch_calls_is_exercised_here() {
    const MODULE: &str = include_str!("../src/cli/kernel_log.rs");
    const SELF: &str = include_str!("kernel_log_door.rs");
    const BANNER: &str = "// THE DOOR THE SWITCH OPENS";

    let below = MODULE.split_once(BANNER).unwrap_or_else(|| panic!("{BANNER} is gone from kernel_log.rs")).1;
    let names: Vec<&str> = below
        .lines()
        .filter_map(|l| l.strip_prefix("pub fn "))
        .filter_map(|l| l.split(['(', '<']).next())
        .collect();
    assert!(names.len() >= 6, "the door's functions: {names:?}");

    let missing: Vec<&&str> = names.iter().filter(|n| !SELF.contains(&format!("kernel_log::{n}"))).collect();
    assert!(
        missing.is_empty(),
        "shipped into the binary, called by no test: {missing:?} — every `pub fn` below the door \
         banner must be called by name here, because `dead_code` is allowed module-wide and \
         cannot say it for us"
    );
    eprintln!("the door's surface: {} functions, every one called here", names.len());
}

/// **Gap 135**: every *all-time* question a verb asks is answered whole at `Hot`.
///
/// `Ctx::load` defaults every verb not named in §11.1 to `Hot`, and `Hot` merges the answer
/// alone — so the sealed day records and the window's item-day minutes, done dates and
/// date-keyed instances are what it drops. Most reads are inside the window **by construction**:
/// the horizon `H = min(monthStart L, isoMonday L, L − 16)` sits at or before the start of the
/// current ISO week and of the current month, which is exactly the span
/// `priority::done_this_period` walks and the oldest date `auto_close` can reach.
///
/// **Two reads are not inside it.** `recur`'s `every:Nd` phase anchor is the *first* completion
/// date the log ever saw (`done_date_first`), and the ordinal recurrences' pending number counts
/// *every* distinct completion date (`done_date_count`). Both are §8.4 column-**A** facts, both
/// ride the kernel's own item record (`Seal.ItemAgg.doneFirst`/`doneCount`, "over **every** date,
/// a date below the horizon included") — and `decode_facts` used to drop those two wire fields and
/// rebuild the pair from the window's dates, which is a *suffix* at `Hot`. Every verb that ranks
/// candidates or builds instances (`tm plan`, `tm now`, `tm start`, `tm done`, `tm triage`, the
/// TUI) asks both questions at `Hot`.
///
/// The test is written to fail if it ever stops biting: it first requires the log to be long
/// enough that `Hot` really does narrow the day records *and* the raw done-date sets.
#[test]
fn the_doors_hot_scope_answers_every_all_time_question() {
    let text = loggen::text(&loggen::log(loggen::Rate::Forty, 200));
    let (dir, bytes) = tree(&text);
    let today = day_after(&text);
    let fork = replay::replay_of_text(&text, TZ);
    let hot = door(dir.path(), &bytes, today, kernel_log::Scope::Hot).replay;

    // Non-vacuity, both halves: `Hot` must really be a narrowing here, and it must really narrow
    // the *date sets* the two questions below used to be answered from.
    assert!(
        hot.days.len() < fork.days.len(),
        "a 200-day log must fold something: {} of {} days",
        hot.days.len(),
        fork.days.len()
    );
    let narrowed_sets: Vec<&String> = fork
        .done_dates
        .keys()
        .filter(|id| hot.done_dates.get(*id) != fork.done_dates.get(*id))
        .collect();
    assert!(
        !narrowed_sets.is_empty(),
        "no id's done-date set is narrowed at `Hot`, so this test cannot see the defect it exists for"
    );

    // The all-time questions, per id.
    let ids: BTreeSet<&String> = fork.items.keys().chain(fork.done_dates.keys()).collect();
    assert!(!ids.is_empty(), "the generated log has items");
    for id in &ids {
        let id = id.as_str();
        assert_eq!(hot.done_date_first(id), fork.done_date_first(id), "{id}: the first done date (the `every:Nd` phase anchor)");
        assert_eq!(hot.done_date_count(id), fork.done_date_count(id), "{id}: the count of distinct done dates");
        assert_eq!(hot.is_done(id), fork.is_done(id), "{id}: the done bit");
        assert_eq!(hot.last_done(id), fork.last_done(id), "{id}: the latest completion");
        assert_eq!(hot.block_minutes(id), fork.block_minutes(id), "{id}: the aggregate block minutes");
    }

    // The all-time questions about the log as a whole.
    assert_eq!(hot.entry_count(), fork.entry_count(), "the all-time entry count");
    assert_eq!(hot.line_count(), fork.line_count(), "the physical line count");
    assert_eq!(hot.done_minutes_map(), fork.done_minutes_map(), "the id-keyed minutes map");
    assert_eq!(
        hot.event_names().collect::<Vec<_>>(),
        fork.event_names().collect::<Vec<_>>(),
        "the `tm event` names"
    );
    assert_eq!(hot.done_items, fork.done_items, "the done ids");
    assert_eq!(hot.dropped_items, fork.dropped_items, "the dropped ids");
    assert_eq!(hot.open_block, fork.open_block, "the open block");
    assert_eq!(hot.open_interrupt, fork.open_interrupt, "the open interruption");
    assert_eq!(hot.longest_leak, fork.longest_leak, "the longest leak");
    assert_eq!(hot.last_effective_t, fork.last_effective_t, "the last effective `t`");

    eprintln!(
        "the door's `Hot` all-time facts: {} ids, {} of them with a narrowed done-date set, \
         {} days of {} carried; narrowed: {:?}",
        ids.len(),
        narrowed_sets.len(),
        hot.days.len(),
        fork.days.len(),
        narrowed_fields(&hot, &fork)
    );
}

/// **Gap 136**: `tm log`'s `total` is the log's **all-time** entry count (§11.4 step 5's
/// `facts.entryCount`), not the number of rows the scope it asked for happens to carry.
///
/// `Replay::entry_count()` was `rows.len()`, and the rows come from the day records: under a
/// narrowed scope they are that scope's. So `tm log --since 7d`, which asks `Dates`, would have
/// printed a `total` smaller than the log. The count rides the checkpoint, so the kernel can
/// answer it at any scope; the reader fills it from the entries it read, and the two agree on a
/// whole log.
#[test]
fn the_doors_total_is_the_logs_all_time_entry_count() {
    let text = loggen::text(&loggen::log(loggen::Rate::Forty, 200));
    let (dir, bytes) = tree(&text);
    let today = day_after(&text);
    let fork = replay::replay_of_text(&text, TZ);
    assert_eq!(fork.entry_count(), fork.view().len(), "on a whole log the reader's two counts agree");

    let first = *fork.days.keys().next().expect("a day");
    for (what, scope) in [
        ("hot", kernel_log::Scope::Hot),
        ("dates", kernel_log::Scope::Dates { from: first, to: first + chrono::Duration::days(6) }),
        ("all", kernel_log::Scope::All),
    ] {
        let r = door(dir.path(), &bytes, today, scope).replay;
        assert_eq!(r.entry_count(), fork.entry_count(), "{what}: the total is the log's, not the scope's");
    }

    // Non-vacuity: at `Hot` the rows really are fewer than the entries, so `rows.len()` would
    // have been a different — and wrong — number.
    let hot = door(dir.path(), &bytes, today, kernel_log::Scope::Hot).replay;
    assert!(
        hot.view().len() < fork.entry_count(),
        "`Hot` must carry fewer rows than the log has entries, else this test proves nothing: {} of {}",
        hot.view().len(),
        fork.entry_count()
    );
    eprintln!(
        "the door's `total`: {} entries all-time, {} rows carried at `Hot`",
        hot.entry_count(),
        hot.view().len()
    );
}
