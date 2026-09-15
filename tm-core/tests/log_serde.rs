//! Serialization contract for `.tm/log.jsonl` (tm-spec-v1.md §10.1): every
//! example line's key set round-trips, every other event kind has the field
//! names of the spec, unknown events survive losslessly, malformed lines are
//! tolerated. (The fixture log's byte-identical write-back and its snapshot test the
//! reader too, so step R12 moved them beside it, into `log.rs`'s `reader_tests`.)

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use chrono::{DateTime, FixedOffset};
use serde_json::{Map, Value};
use tm_core::log::{Event, Log, LogEntry, EVENT_NAMES};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/logs").join(name)
}

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

/// The §10.1 examples with their `…` timestamps expanded.
const SPEC_LINES: &[&str] = &[
    r#"{"t":"2026-09-07T06:05:00-05:00","ev":"wake","slept_min":490}"#,
    r#"{"t":"2026-09-07T07:00:00-05:00","ev":"arrive","loc":"lounge","window":["07:00","15:00"],"budget":6}"#,
    r#"{"t":"2026-09-07T07:02:00-05:00","ev":"start","id":"t1","pred":5,"rep":5,"hsw":0.95,"slept_min":490,"loc":"lounge","blocks_done":0,"since_break_min":0}"#,
    r#"{"t":"2026-09-07T08:09:00-05:00","ev":"done","id":"t1","est_min":60,"actual_min":67,"went":1,"tags":["lean"],"ci":5}"#,
    r#"{"t":"2026-09-07T09:08:00-05:00","ev":"break","planned_min":20,"actual_min":24,"where":"walk"}"#,
    r#"{"t":"2026-09-07T09:32:00-05:00","ev":"energy","pred":5,"rep":4,"hsw":3.45,"loc":"lounge"}"#,
    r#"{"t":"2026-09-07T12:10:00-05:00","ev":"interrupt","id":"t4"}"#,
    r#"{"t":"2026-09-07T13:05:00-05:00","ev":"resume","lost_min":55,"dropped":["t5"]}"#,
    r#"{"t":"2026-09-07T15:40:00-05:00","ev":"idle","attributed":"leak","min":14}"#,
    r#"{"t":"2026-09-07T16:10:00-05:00","ev":"routine","item":"package","inst":"2026-09-07","status":"done","actual_min":18}"#,
    r#"{"t":"2026-09-07T21:30:00-05:00","ev":"plan","hash":"a91f…","replans_today":4,"drift_min":75}"#,
    r#"{"t":"2026-09-07T21:31:00-05:00","ev":"event","name":"reply","id":"a4"}"#,
    r#"{"t":"2026-09-07T21:32:00-05:00","ev":"demote","id":"m2","from":"2026-W37","to":"2026-09","est_min":180}"#,
    r#"{"t":"2026-09-07T21:33:00-05:00","ev":"undo","of":"done","id":"t4"}"#,
];

#[test]
fn spec_examples_round_trip_byte_identically() {
    for line in SPEC_LINES {
        let e = LogEntry::parse(line).unwrap_or_else(|err| panic!("{line}: {err}"));
        assert!(!matches!(e.ev, Event::Unknown { .. }), "{line} parsed as Unknown");
        let back = e.to_json().unwrap();
        // Same keys in the same order, same values (the timestamp included).
        assert_eq!(back, *line);
        assert_eq!(
            serde_json::from_str::<Value>(&back).unwrap(),
            serde_json::from_str::<Value>(line).unwrap()
        );
        assert_eq!(LogEntry::parse(&back).unwrap(), e);
    }
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
    ];
    let mut seen = BTreeSet::new();
    for (ev, want) in cases {
        let entry = LogEntry::new(t, ev.clone());
        let json = entry.to_json().unwrap();
        assert_eq!(keys(&json), want, "{json}");
        let v: Value = serde_json::from_str(&json).unwrap();
        assert_eq!(v["ev"], Value::from(ev.name()), "{json}");
        assert!(EVENT_NAMES.contains(&ev.name()), "{}", ev.name());
        assert_eq!(LogEntry::parse(&json).unwrap(), entry, "{json}");
        seen.insert(ev.name().to_string());
    }
    let all: BTreeSet<String> = EVENT_NAMES.iter().map(|n| n.to_string()).collect();
    assert_eq!(seen, all, "every known event kind is covered");
    assert_eq!(EVENT_NAMES.len(), 26);
}

#[test]
fn unknown_events_round_trip_and_known_bad_payloads_do_not() {
    let line = r#"{"t":"2026-09-08T13:00:00-05:00","ev":"mood","level":3,"nested":{"a":[1,2]},"note":"meh"}"#;
    let e = LogEntry::parse(line).unwrap();
    let Event::Unknown { ev, rest } = &e.ev else {
        panic!("{:?}", e.ev);
    };
    assert_eq!(ev, "mood");
    assert_eq!(rest.len(), 3);
    assert_eq!(rest["level"], Value::from(3));
    assert_eq!(e.ev.name(), "mood");
    assert_eq!(e.ev.primary_id(), None);
    assert!(!e.ev.is_state_change());
    assert_eq!(e.to_json().unwrap(), line, "already in canonical key order");

    // Built by hand, keys come out sorted after `ev`.
    let mut rest = Map::new();
    rest.insert("z".into(), Value::from(1));
    rest.insert("id".into(), Value::from("k7"));
    let built = LogEntry::new(at("2026-09-08T13:00:00-05:00"), Event::Unknown { ev: "zorg".into(), rest });
    assert_eq!(
        built.to_json().unwrap(),
        r#"{"t":"2026-09-08T13:00:00-05:00","ev":"zorg","id":"k7","z":1}"#
    );
    assert_eq!(built.ev.primary_id(), Some("k7"));

    // A known name with a bad payload names the event and the field.
    let err = LogEntry::parse(r#"{"t":"2026-09-08T13:00:00-05:00","ev":"wake"}"#).unwrap_err();
    assert!(err.to_string().contains("\"wake\""), "{err}");
    assert!(err.to_string().contains("slept_min"), "{err}");
    let err = LogEntry::parse(r#"{"t":"2026-09-08T13:00:00-05:00","ev":"done","id":"t1","est_min":"x","actual_min":1,"ci":5}"#)
        .unwrap_err();
    assert!(err.to_string().contains("\"done\""), "{err}");
    assert!(err.to_string().contains("est_min"), "{err}");
    // A raw-identifier field is named without its `r#` prefix.
    let err = LogEntry::parse(r#"{"t":"2026-09-08T13:00:00-05:00","ev":"break","planned_min":20,"where":5}"#)
        .unwrap_err();
    assert!(err.to_string().contains("\"break\": where:"), "{err}");
    // `ev` itself is required and must be a string.
    assert!(LogEntry::parse(r#"{"t":"2026-09-08T13:00:00-05:00","text":"x"}"#)
        .unwrap_err()
        .to_string()
        .contains("ev"));
    assert!(LogEntry::parse(r#"{"t":"2026-09-08T13:00:00-05:00","ev":7}"#)
        .unwrap_err()
        .to_string()
        .contains("string"));
    // Event alone (without the `t` wrapper) parses too.
    let ev: Event = serde_json::from_str(r#"{"ev":"note","text":"x"}"#).unwrap();
    assert_eq!(ev, Event::Note { text: "x".into() });
}

/// What "losslessly" means for [`Event::Unknown`], stated where a change
/// would break it: every key and value survives, but `rest` is a
/// `serde_json::Map` (a `BTreeMap` here), so a line written with **unsorted**
/// keys comes back sorted — value-identical, not byte-identical. Every other
/// unknown-event assertion in this suite (and the fixture) happens to use
/// keys that are already sorted, so nothing else pins this down.
#[test]
fn unknown_events_keep_every_key_but_canonicalise_their_order() {
    let line = r#"{"t":"2026-09-08T13:00:00-05:00","ev":"mood","note":"meh","level":3,"anger":null}"#;
    let e = LogEntry::parse(line).unwrap();
    let back = e.to_json().unwrap();
    assert_ne!(back, line, "the keys were not written in sorted order");
    assert_eq!(
        back,
        r#"{"t":"2026-09-08T13:00:00-05:00","ev":"mood","anger":null,"level":3,"note":"meh"}"#
    );
    // Nothing is lost: same value, and a second round trip is a fixed point.
    assert_eq!(
        serde_json::from_str::<Value>(&back).unwrap(),
        serde_json::from_str::<Value>(line).unwrap()
    );
    assert_eq!(LogEntry::parse(&back).unwrap(), e);
    assert_eq!(LogEntry::parse(&back).unwrap().to_json().unwrap(), back);

    // The documented flip side: an unknown *extra* key on a **known** event is
    // dropped on re-serialization. Nothing rewrites `.tm/log.jsonl` (§10.1 is
    // append-only), so this only affects `to_jsonl`.
    let e = LogEntry::parse(r#"{"t":"2026-09-08T13:00:00-05:00","ev":"note","text":"hi","extra":1}"#)
        .unwrap();
    assert_eq!(e.ev, Event::Note { text: "hi".into() });
    assert_eq!(
        e.to_json().unwrap(),
        r#"{"t":"2026-09-08T13:00:00-05:00","ev":"note","text":"hi"}"#
    );
}

#[test]
fn malformed_lines_are_warnings_not_errors() {
    let log = Log::read(fixture("malformed.jsonl")).unwrap();
    assert_eq!(log.entries.len(), 3, "{:?}", log.entries);
    assert_eq!(log.entries[0].ev, Event::Wake { slept_min: 490, onset_min: None });
    assert_eq!(log.entries[1].ev.name(), "mood");
    assert_eq!(log.entries[2].ev, Event::Note { text: "last good line".into() });
    let lines: Vec<usize> = log.warnings.iter().map(|w| w.line).collect();
    assert_eq!(lines, vec![2, 3, 4, 5, 6, 7, 10]);
    let msg = |line: usize| {
        log.warnings
            .iter()
            .find(|w| w.line == line)
            .map(|w| w.error.clone())
            .unwrap()
    };
    assert!(msg(3).contains("slept_min"), "{}", msg(3));
    assert!(msg(4).contains("`t`"), "{}", msg(4));
    assert!(msg(5).contains("est_min"), "{}", msg(5));
    assert!(msg(6).contains("timestamp"), "{}", msg(6));
    assert!(msg(10).contains("string"), "{}", msg(10));
    assert_eq!(log.warnings[0].text, "this is not json");
    assert_eq!(log.warnings[0].to_string(), format!("line 2: {} ({:?})", msg(2), "this is not json"));
    // Missing file → empty log, no error.
    let missing = Log::read(fixture("does-not-exist.jsonl")).unwrap();
    assert!(missing.is_empty() && missing.warnings.is_empty());
}

#[test]
fn append_creates_the_directory_and_one_object_per_line() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join(".tm").join("log.jsonl");
    let e1 = LogEntry::new(at("2026-09-07T06:05:00-05:00"), Event::Wake { slept_min: 490, onset_min: None });
    let e2 = LogEntry::new(at("2026-09-07T07:00:00-05:00"), Event::Note { text: "multi\nline \"quoted\"".into() });
    Log::append(&path, &e1).unwrap();
    assert!(path.exists());
    Log::append(&path, &e2).unwrap();
    let text = std::fs::read_to_string(&path).unwrap();
    assert_eq!(text.lines().count(), 2);
    assert!(text.ends_with('\n'));
    let log = Log::read(&path).unwrap();
    assert_eq!(log.entries, vec![e1.clone(), e2.clone()]);
    assert!(log.warnings.is_empty());
    Log::append_all(&path, &[e1.clone(), e2.clone()]).unwrap();
    assert_eq!(Log::read(&path).unwrap().len(), 4);
    // A directory in the way is a write error.
    let bad = dir.path().join("dir-not-file");
    std::fs::create_dir_all(&bad).unwrap();
    assert!(Log::append(&bad, &e1).is_err());
}
