//! **The writer's** serialization contract for `.tm/log.jsonl` (tm-spec-v1.md
//! §10.1): every event kind has the field names of the spec, in the spec's
//! order, and an unknown event survives a write losslessly.
//!
//! **Writer tests only, since S** (design §12). Every assertion that went
//! through `LogEntry::parse`, `Log::read` or `Log::append` went with the
//! reader those name, and each is still covered — by something that is not
//! a second reader of the same bytes:
//!
//! * per-line **parse acceptance** (a missing field, a mistyped field, a bad
//!   `ev`): `tm/tests/kernel_log_grammar.rs`'s T1, against fork point
//!   `4748911`'s frozen verdicts — a differential, where this was a
//!   self-check;
//! * **writer byte-identity** over real logs: T2, same file;
//! * a **malformed line is a warning, not an error**: `tm/tests/cli_check_log.rs`,
//!   end to end through `tm check` (the owner's D18 (i));
//! * **appending past a torn last line** (G9, parity P19):
//!   `tm-core/tests/store_state.rs`'s `append_text_repairs_a_torn_last_line_in_both_stores`
//!   and `tm/tests/cli_day.rs`'s `an_append_after_a_torn_line_starts_a_new_line`,
//!   both over `FsStore::append_text`, which **is** the writer `Ctx::append_entry`
//!   calls. `Log::append` never was.

use std::collections::BTreeSet;

use chrono::{DateTime, FixedOffset};
use serde_json::{Map, Value};
use tm_core::log::{Event, LogEntry, EVENT_NAMES};


fn at(s: &str) -> DateTime<FixedOffset> {
    DateTime::parse_from_rfc3339(s).unwrap()
}

/// Top-level keys of a JSON object **in the order they were written**:
/// `serde_json::Map` is a `BTreeMap` here, so parsing would sort them and
/// hide the field order the spec's examples fix.
fn keys(json: &str) -> Vec<String> {
    let b = json.as_bytes();
    let mut keys = Vec::new();
    let mut depth = 0usize;
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'{' | b'[' => depth += 1,
            b'}' | b']' => depth -= 1,
            b'"' => {
                let start = i + 1;
                let mut j = start;
                while j < b.len() && b[j] != b'"' {
                    j += if b[j] == b'\\' { 2 } else { 1 };
                }
                let mut k = j + 1;
                while k < b.len() && b[k].is_ascii_whitespace() {
                    k += 1;
                }
                if depth == 1 && k < b.len() && b[k] == b':' {
                    keys.push(json[start..j].to_string());
                }
                i = j;
            }
            _ => {}
        }
        i += 1;
    }
    keys
}



#[test]
fn every_event_kind_has_the_spec_field_names() {
    let t = at("2026-09-07T10:00:00-05:00");
    let s = |v: &str| v.to_string();
    let cases: Vec<(Event, &[&str])> = vec![
        (Event::Wake { slept_min: 490, onset_min: Some(25) }, &["t", "ev", "slept_min", "onset_min"]),
        (Event::Wake { slept_min: 490, onset_min: None }, &["t", "ev", "slept_min"]),
        (
            Event::Arrive { loc: s("lounge"), window: [s("07:00"), s("15:00")], budget: 6 },
            &["t", "ev", "loc", "window", "budget"],
        ),
        (
            Event::Start {
                id: s("t1"),
                pred: 5,
                rep: None,
                hsw: 0.95,
                slept_min: 490,
                loc: s("lounge"),
                blocks_done: 0,
                since_break_min: 0,
            },
            &["t", "ev", "id", "pred", "hsw", "slept_min", "loc", "blocks_done", "since_break_min"],
        ),
        (
            Event::Done {
                id: s("t1"),
                est_min: 60,
                actual_min: 67,
                went: None,
                tags: vec![],
                ci: 5,
                partial: true,
            },
            &["t", "ev", "id", "est_min", "actual_min", "tags", "ci", "partial"],
        ),
        (Event::Extend { id: s("t3"), by_min: 60 }, &["t", "ev", "id", "by_min"]),
        (Event::Stop { id: s("t3"), remaining_min: 30 }, &["t", "ev", "id", "remaining_min"]),
        (
            Event::Break { planned_min: 20, actual_min: None, r#where: None },
            &["t", "ev", "planned_min"],
        ),
        (
            Event::Energy { pred: 5, rep: 4, hsw: 3.45, loc: s("lounge") },
            &["t", "ev", "pred", "rep", "hsw", "loc"],
        ),
        (Event::Interrupt { id: None }, &["t", "ev"]),
        (Event::Resume { lost_min: 55, dropped: vec![] }, &["t", "ev", "lost_min", "dropped"]),
        (Event::Pause { id: s("t3") }, &["t", "ev", "id"]),
        (Event::Unpause { id: s("t3") }, &["t", "ev", "id"]),
        (Event::Idle { attributed: s("leak"), min: 14 }, &["t", "ev", "attributed", "min"]),
        (
            Event::Routine { item: s("lunch"), inst: s("2026-09-07"), status: s("skipped"), actual_min: None },
            &["t", "ev", "item", "inst", "status"],
        ),
        (Event::Skip { item: s("lunch"), inst: s("2026-09-07") }, &["t", "ev", "item", "inst"]),
        (
            Event::Plan { hash: s("a91f"), replans_today: 4, drift_min: 75 },
            &["t", "ev", "hash", "replans_today", "drift_min"],
        ),
        (Event::Named { name: s("reply"), id: None }, &["t", "ev", "name"]),
        (
            Event::Demote { id: s("m2"), from: s("2026-W37"), to: s("2026-09"), est_min: 180 },
            &["t", "ev", "id", "from", "to", "est_min"],
        ),
        (Event::Readopt { id: s("m2") }, &["t", "ev", "id"]),
        (
            Event::Move { id: s("a1"), from: s("backlog"), to: s("week/2026-W37") },
            &["t", "ev", "id", "from", "to"],
        ),
        (Event::Drop { id: s("a5") }, &["t", "ev", "id"]),
        (
            Event::Edit { id: s("t8"), field: s("est"), from: s("2b"), to: s("1b") },
            &["t", "ev", "id", "field", "from", "to"],
        ),
        (Event::Note { text: s("hi") }, &["t", "ev", "text"]),
        (Event::Loc { loc: s("home") }, &["t", "ev", "loc"]),
        (Event::Close { period: s("day"), key: s("2026-09-07") }, &["t", "ev", "period", "key"]),
        (Event::Undo { of: s("done"), id: None }, &["t", "ev", "of"]),
        // The owner's D105 (parity P100): the line `tm break` writes when a break begins.
        (
            Event::BreakStart { planned_min: 20, r#where: Some(s("walk")) },
            &["t", "ev", "planned_min", "where"],
        ),
    ];
    let mut seen = BTreeSet::new();
    for (ev, want) in cases {
        let entry = LogEntry::new(t, ev.clone());
        let json = entry.to_json().unwrap();
        assert_eq!(keys(&json), want, "{json}");
        let v: Value = serde_json::from_str(&json).unwrap();
        assert_eq!(v["ev"], Value::from(ev.name()), "{json}");
        assert!(EVENT_NAMES.contains(&ev.name()), "{}", ev.name());
        seen.insert(ev.name().to_string());
    }
    let all: BTreeSet<String> = EVENT_NAMES.iter().map(|n| n.to_string()).collect();
    assert_eq!(seen, all, "every known event kind is covered");
    // 26 until the owner's D105 added `break_start` (parity P100).
    assert_eq!(EVENT_NAMES.len(), 27);
}


/// What "losslessly" means for [`Event::Unknown`], stated where a change
/// would break it: every key and value survives, but `rest` is a
/// `serde_json::Map` (a `BTreeMap` here), so a line written with **unsorted**
/// keys comes back sorted — value-identical, not byte-identical. Every other
/// unknown-event assertion in this suite (and the fixture) happens to use
/// keys that are already sorted, so nothing else pins this down.
#[test]
fn unknown_events_keep_every_key_but_canonicalise_their_order() {
    // Put in deliberately unsorted, so the sorting below is the writer's doing
    // and not the input's.
    let mut rest = Map::new();
    rest.insert("note".into(), Value::from("meh"));
    rest.insert("level".into(), Value::from(3));
    rest.insert("anger".into(), Value::Null);
    let e = LogEntry::new(at("2026-09-08T13:00:00-05:00"), Event::Unknown { ev: "mood".into(), rest });
    assert_eq!(
        e.to_json().unwrap(),
        r#"{"t":"2026-09-08T13:00:00-05:00","ev":"mood","anger":null,"level":3,"note":"meh"}"#
    );
    assert_eq!(e.ev.name(), "mood");
    assert!(!EVENT_NAMES.contains(&e.ev.name()), "`mood` must not be a known kind");

    // An `id` inside an unknown event's payload is still its primary id — what
    // `undo{id}` matches against — and it is written in sorted position too.
    let mut rest = Map::new();
    rest.insert("z".into(), Value::from(1));
    rest.insert("id".into(), Value::from("k7"));
    let built = LogEntry::new(at("2026-09-08T13:00:00-05:00"), Event::Unknown { ev: "zorg".into(), rest });
    assert_eq!(
        built.to_json().unwrap(),
        r#"{"t":"2026-09-08T13:00:00-05:00","ev":"zorg","id":"k7","z":1}"#
    );
    assert_eq!(built.ev.primary_id(), Some("k7"));
}


