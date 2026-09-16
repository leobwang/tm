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
