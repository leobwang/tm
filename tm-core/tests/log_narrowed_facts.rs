//! **The two narrowings the kernel's facts decoder needed** (stage 5 D9, step
//! X1, gap 128), each checked against the reader that stands today over the
//! four corpus logs and a generated month.
//!
//! Design §11.1's `kernel_log::decode_facts` builds a whole
//! [`tm_core::log::Replay`] from the kernel's facts **alone**. Two of `Replay`'s
//! fields were shaped so that it could not, and both were reshaped here:
//!
//! * **`events`** was `BTreeMap<String, Vec<NamedEvent>>`, an occurrence list
//!   per name. The kernel keeps the latest per `(name, id?)` (design §8.4:
//!   "latest instant per `(name, id?)`. Exact, because a `>= since` filter
//!   commutes with max"), which is what both readers in the binary ask for —
//!   `priority.rs`'s `event_names()` and `recur.rs`'s `latest_named()`, the pair
//!   step R3 narrowed them to. The field is now
//!   `named: BTreeMap<String, NamedRecord>`.
//! * **`ViewRow`** held a whole parsed `LogEntry`. The kernel supplies a
//!   header — `[line, tag, id, day, cancelled, display]` — and the line's own
//!   bytes come back from the `render` op (§11.4). `ViewRow` now holds exactly
//!   the header.
//!
//! This is the equivalence test design §14.3 requires of a reshape: the **old**
//! shape is recomputed from the log text here, and the new accessors are asked
//! every question the old ones answered. It prints its denominators, because a
//! comparison that never ran reports no disagreement (AGENTS §7.3).
//!
//! **It goes at the switch**, with the `Log::parse` it calls: after S a line's
//! payload comes from the kernel's `render`, and T5 — retargeted to the fork
//! point — is the comparison that survives.

#[path = "../../tm/tests/support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

#[path = "../../tm/tests/support/loggen.rs"]
#[allow(dead_code)]
mod loggen;

use std::collections::BTreeMap;

use chrono::{DateTime, Duration, FixedOffset};
use chrono_tz::Tz;
use tm_core::log::{undo_mask, Event, LogEntry};

const TZ: Tz = chrono_tz::America::Chicago;

/// A `DateTime` **with its written offset**, which `chrono`'s `PartialEq`
/// ignores: two spellings of one instant compare equal as `DateTime`s. The
/// reader keeps the spelling it read, and the file-order tie-break decides
/// *which* of two tied occurrences it keeps — so a comparison by `DateTime`
/// alone could not see the tie-break at all, and would be a check no input
/// could fail. This is the comparand instead (T5's `stamp_of` is the same idea).
fn stamped(t: DateTime<FixedOffset>) -> (DateTime<FixedOffset>, i32) {
    (t, t.offset().local_minus_utc())
}

/// **A log built to tie** — the input the corpus does not carry. Four pairs of
/// `tm event` lines share an instant and differ in their *written offset*, so
/// the two spellings are the same instant and not the same characters, and the
/// file-order tie-break (a later line wins) decides which survives. Two pairs
/// tie an unaddressed occurrence against an addressed one, which is the merge
/// `latest_named` does across the two keys; one is cancelled by an `undo`, so
/// the mask has to be applied before the tie is resolved.
const TIED: &str = concat!(
    r#"{"t":"2026-09-07T06:05:00-05:00","ev":"wake","slept_min":480}"#, "
",
    r#"{"t":"2026-09-07T17:00:00-05:00","ev":"event","name":"reply"}"#, "
",
    r#"{"t":"2026-09-07T22:00:00+00:00","ev":"event","name":"reply","id":"a4"}"#, "
",
    r#"{"t":"2026-09-07T17:00:00-05:00","ev":"event","name":"ping","id":"a4"}"#, "
",
    r#"{"t":"2026-09-07T22:00:00+00:00","ev":"event","name":"ping"}"#, "
",
    r#"{"t":"2026-09-08T06:10:00-05:00","ev":"wake","slept_min":470}"#, "
",
    r#"{"t":"2026-09-08T09:00:00-05:00","ev":"event","name":"reply","id":"b7"}"#, "
",
    r#"{"t":"2026-09-08T14:00:00+00:00","ev":"event","name":"reply","id":"b7"}"#, "
",
    r#"{"t":"2026-09-08T09:00:00-05:00","ev":"event","name":"gone","id":"c1"}"#, "
",
    r#"{"t":"2026-09-08T14:00:00+00:00","ev":"event","name":"gone","id":"c1"}"#, "
",
    r#"{"t":"2026-09-08T10:00:00-05:00","ev":"undo","of":"event","id":"c1"}"#, "
",
);

/// One surviving `tm event` occurrence, as the deleted `NamedEvent` list held
/// it: its physical line (file order), its instant and the id it was addressed
/// to.
type Occurrence = (u64, DateTime<FixedOffset>, Option<String>);

/// The logs every comparison below runs over: the four corpus logs and a
/// generated month, which is design §14.3's own equivalence-test input set.
fn inputs() -> Vec<(String, String)> {
    let root = format!("{}/../kernel/corpus/logs", env!("CARGO_MANIFEST_DIR"));
    let mut out: Vec<(String, String)> = ["energy-14d", "malformed", "review-14d", "three-days"]
        .iter()
        .map(|n| {
            let path = format!("{root}/{n}.jsonl");
            let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"));
            (n.to_string(), text)
        })
        .collect();
    out.push((
        "loggen 1mo (40 a day)".to_string(),
        loggen::text(&loggen::log(loggen::Rate::Forty, 30)),
    ));
    out.push(("tied `tm event` lines".to_string(), TIED.to_string()));
    out
}

/// **The old shape**: every surviving `tm event` occurrence, by name, in file
/// order — what `Replay.events` held and `events_named(name)` handed back.
fn occurrence_lists(text: &str) -> BTreeMap<String, Vec<Occurrence>> {
    let entries: Vec<(u64, LogEntry)> = chokepoint::entries_of_text(text);
    let only: Vec<LogEntry> = entries.iter().map(|(_, e)| e.clone()).collect();
    let mask = undo_mask(&only);
    let mut out: BTreeMap<String, Vec<Occurrence>> = BTreeMap::new();
    for (i, (line, e)) in entries.iter().enumerate() {
        if mask.cancelled[i] {
            continue;
        }
        if let Event::Named { name, id } = &e.ev {
            out.entry(name.clone())
                .or_default()
                .push((*line, e.t, id.clone()));
        }
    }
    out
}

/// **The old `Replay::latest_named`**, body for body, over an occurrence list:
/// keep the occurrences addressed to `id` or to nobody, then the maximum by
/// instant and the maximum by `(local date, instant)`, a tie going to the later
/// line because the walk was in file order.
fn fork_latest_named(
    occ: &[Occurrence],
    id: &str,
    tz: Tz,
) -> Option<(DateTime<FixedOffset>, DateTime<FixedOffset>)> {
    let mut out: Option<(DateTime<FixedOffset>, DateTime<FixedOffset>)> = None;
    for (_, t, who) in occ {
        if who.as_deref().is_some_and(|i| i != id) {
            continue;
        }
        let t = *t;
        out = Some(match out {
            None => (t, t),
            Some((mut latest, mut dated)) => {
                if t >= latest {
                    latest = t;
                }
                let key = |x: DateTime<FixedOffset>| (x.with_timezone(&tz).date_naive(), x);
                if key(t) >= key(dated) {
                    dated = t;
                }
                (latest, dated)
            }
        });
    }
    out
}

/// **The old `Replay::event_occurred`**, body for body.
fn fork_event_occurred(
    occ: &[Occurrence],
    since: Option<DateTime<FixedOffset>>,
    id: Option<&str>,
) -> bool {
    occ.iter().any(|(_, t, who)| {
        since.is_none_or(|s| *t >= s) && id.is_none_or(|i| who.as_deref() == Some(i))
    })
}

#[test]
fn the_narrowed_events_answer_every_question_the_occurrence_lists_did() {
    let (mut names, mut latest, mut occurred, mut logs_with_events) = (0usize, 0usize, 0usize, 0usize);
    for (label, text) in inputs() {
        let r = chokepoint::replay_of_text(&text, TZ);
        let lists = occurrence_lists(&text);
        logs_with_events += usize::from(!lists.is_empty());

        // `event_names()`: the names logged, and no others.
        let new: Vec<&str> = r.event_names().collect();
        let old: Vec<&str> = lists.keys().map(String::as_str).collect();
        assert_eq!(new, old, "{label}: the names `tm event` was logged with");
        names += old.len();

        for (name, occ) in &lists {
            // Every id the log addresses this name to, plus two it never does:
            // an id with no occurrence of its own (which must still see the
            // unaddressed ones) and the empty key.
            let mut ids: Vec<String> = occ.iter().filter_map(|(_, _, i)| i.clone()).collect();
            ids.sort();
            ids.dedup();
            ids.push("no-such-id".to_string());
            ids.push(String::new());

            for id in &ids {
                let want = fork_latest_named(occ, id, TZ);
                let got = r.latest_named(name, id, TZ);
                assert_eq!(
                    got.map(|l| (stamped(l.latest), stamped(l.latest_dated))),
                    want.map(|(l, d)| (stamped(l), stamped(d))),
                    "{label}: latest_named({name:?}, {id:?})"
                );
                // The query `recur::arrival_of` actually asks, at every
                // occurrence's own date and a day either side of it.
                for (_, t, _) in occ {
                    for shift in [-1i64, 0, 1] {
                        let since = (*t + Duration::days(shift)).with_timezone(&TZ).date_naive();
                        let want = want.and_then(|(l, d)| {
                            if l.with_timezone(&TZ).date_naive() >= since {
                                Some(l)
                            } else if d.with_timezone(&TZ).date_naive() >= since {
                                Some(d)
                            } else {
                                None
                            }
                        });
                        assert_eq!(
                            got.and_then(|l| l.on_or_after(Some(since), TZ)).map(stamped),
                            want.map(stamped),
                            "{label}: latest_named({name:?}, {id:?}).on_or_after({since})"
                        );
                        latest += 1;
                    }
                }
                latest += 1;
            }

            // `event_occurred`, at every occurrence's instant and a second
            // either side, addressed and unaddressed.
            let mut sinces: Vec<Option<DateTime<FixedOffset>>> = vec![None];
            for (_, t, _) in occ {
                for shift in [-1i64, 0, 1] {
                    sinces.push(Some(*t + Duration::seconds(shift)));
                }
            }
            for since in &sinces {
                for id in [None].into_iter().chain(ids.iter().map(|i| Some(i.as_str()))) {
                    assert_eq!(
                        r.event_occurred(name, *since, id),
                        fork_event_occurred(occ, *since, id),
                        "{label}: event_occurred({name:?}, {since:?}, {id:?})"
                    );
                    occurred += 1;
                }
            }
        }
    }
    assert!(logs_with_events >= 2, "the inputs carry `tm event` lines");
    assert!(names > 0 && latest > 0 && occurred > 0, "the comparisons ran");
    eprintln!(
        "narrowed events: {logs_with_events} logs with `tm event` lines, {names} names, \
         {latest} latest_named queries, {occurred} event_occurred queries; 0 disagreements"
    );
}

#[test]
fn the_view_rows_are_the_headers_of_the_entries_they_came_from() {
    let (mut rows, mut with_id) = (0usize, 0usize);
    for (label, text) in inputs() {
        let r = chokepoint::replay_of_text(&text, TZ);
        let entries = chokepoint::entries_of_text(&text);
        assert_eq!(
            r.view().len(),
            entries.len(),
            "{label}: one row an entry, malformed and blank lines excluded"
        );
        for (row, (line, e)) in r.view().iter().zip(&entries) {
            assert_eq!(row.line, *line, "{label}: the row's physical line");
            assert_eq!(row.tag, e.ev.name(), "{label}: line {line}'s tag");
            assert_eq!(
                row.id.as_deref(),
                e.ev.primary_id(),
                "{label}: line {line}'s primary id"
            );
            assert_eq!(stamped(row.t), stamped(e.t), "{label}: line {line}'s instant and offset");
            assert_eq!(
                row.display(),
                e.t.format("%Y-%m-%d %H:%M").to_string(),
                "{label}: line {line}'s display"
            );
            rows += 1;
            with_id += usize::from(row.id.is_some());
        }
    }
    assert!(rows > 0 && with_id > 0, "the comparison ran");
    eprintln!("view rows: {rows} headers compared ({with_id} carrying an id); 0 disagreements");
}
