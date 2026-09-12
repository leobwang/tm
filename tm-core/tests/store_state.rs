//! `.tm/state.json` (§10.2) and the generic `.tm/*.json` helpers: the
//! snippet in the spec parses field for field, round trips through a store,
//! and a missing file loads as the default.

use std::collections::BTreeMap;

use chrono::{NaiveDate, NaiveTime};
use serde_json::json;
use tempfile::TempDir;
use tm_core::model::{Id, IsoWeek, YearMonth};
use tm_core::store::{ActiveBlock, Closed, FsStore, MemStore, RuntimeState, Store, StoreExt, STATE_PATH};

/// §10.2 verbatim (the `…` of the hash kept, the line breaks are JSON
/// whitespace).
const SPEC_STATE: &str = r#"{"date":"2026-09-07","wake":"06:05","arrival":"07:00","loc":"lounge","window":["07:00","16:00"],"budget":6,
 "active":{"id":"t3","started":"09:32","est_min":192,"paused":false},
 "break":null,"interrupt":null,
 "last_plan_hash":"a91f…","priorities_yesterday":{"d1":1,"m2":3},
 "closed":{"day":"2026-09-06","week":"2026-W36","month":"2026-08"}}"#;

fn hm(h: u32, m: u32) -> NaiveTime {
    NaiveTime::from_hms_opt(h, m, 0).unwrap()
}

fn spec_state() -> RuntimeState {
    RuntimeState {
        date: Some(NaiveDate::from_ymd_opt(2026, 9, 7).unwrap()),
        wake: Some(hm(6, 5)),
        arrival: Some(hm(7, 0)),
        loc: Some("lounge".to_string()),
        window: Some((hm(7, 0), hm(16, 0))),
        budget: Some(6),
        active: Some(ActiveBlock {
            id: Id::new("t3"),
            started: hm(9, 32),
            est_min: 192,
            paused: false,
        }),
        break_: None,
        interrupt: None,
        last_plan_hash: Some("a91f…".to_string()),
        priorities_yesterday: BTreeMap::from([(Id::new("d1"), 1), (Id::new("m2"), 3)]),
        closed: Closed {
            day: Some(NaiveDate::from_ymd_opt(2026, 9, 6).unwrap()),
            week: Some(IsoWeek::new(2026, 36)),
            month: Some(YearMonth::new(2026, 8)),
        },
    }
}

#[test]
fn the_spec_snippet_parses_field_for_field() {
    let parsed: RuntimeState = serde_json::from_str(SPEC_STATE).unwrap();
    assert_eq!(parsed, spec_state());
    // …and writing it back produces the same JSON document.
    let written: serde_json::Value = serde_json::from_str(&serde_json::to_string(&parsed).unwrap()).unwrap();
    assert_eq!(written, serde_json::from_str::<serde_json::Value>(SPEC_STATE).unwrap());
}

#[test]
fn state_json_snapshot() {
    insta::assert_json_snapshot!("state_of_the_spec", spec_state());
    insta::assert_json_snapshot!("state_default", RuntimeState::default());
}

#[test]
fn state_round_trips_through_both_stores() {
    let state = spec_state();

    let mem = MemStore::new();
    assert_eq!(mem.load_state().unwrap(), RuntimeState::default(), "missing file → default");
    mem.save_state(&state).unwrap();
    assert_eq!(mem.load_state().unwrap(), state);
    let text = mem.text(STATE_PATH).unwrap();
    assert!(text.ends_with("}\n"), "pretty JSON with a final newline: {text:?}");
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&text).unwrap(),
        serde_json::from_str::<serde_json::Value>(SPEC_STATE).unwrap()
    );

    let dir = TempDir::new().unwrap();
    let fs_store = FsStore::new(dir.path().join("plan"));
    assert_eq!(fs_store.load_state().unwrap(), RuntimeState::default());
    fs_store.save_state(&state).unwrap();
    assert!(dir.path().join("plan/.tm/state.json").is_file(), ".tm/ is created");
    assert_eq!(fs_store.load_state().unwrap(), state);
    assert_eq!(std::fs::read_to_string(dir.path().join("plan/.tm/state.json")).unwrap(), text);

    // A partial file loads: every field has a default.
    mem.insert(STATE_PATH, r#"{"loc":"home","budget":4}"#);
    let partial = mem.load_state().unwrap();
    assert_eq!(partial.loc.as_deref(), Some("home"));
    assert_eq!(partial.budget, Some(4));
    assert_eq!(partial.date, None);
    assert!(partial.priorities_yesterday.is_empty());
    assert_eq!(partial.closed, Closed::default());

    // A malformed file is an error, not a silent default.
    mem.insert(STATE_PATH, "{ not json");
    assert!(mem.load_state().is_err());
}

#[test]
fn json_helpers_serve_model_json() {
    let mem = MemStore::new();
    assert_eq!(mem.read_json::<serde_json::Value>(".tm/model.json").unwrap(), None);
    let model = json!({
        "energy": { "lounge": [4, 5, 5, 5, 5, 4, 4, 4, 3, 3, 2, 2] },
        "sleep_debt_shift": 0.8,
        "duration": { "lean": 1.6, "_default": 1.3 },
        "fitted": "2026-09-14",
        "n_obs": 61
    });
    mem.write_json(".tm/model.json", &model).unwrap();
    assert_eq!(
        mem.read_json::<serde_json::Value>(".tm/model.json").unwrap(),
        Some(model)
    );
    // `.tm/` is not part of the plan tree.
    assert!(mem.list_files().unwrap().is_empty());

    // The helpers are available through a trait object too.
    let erased: &dyn Store = &mem;
    assert_eq!(erased.read_json::<serde_json::Value>("nope.json").unwrap(), None);
}

#[test]
fn append_text_extends_the_log_in_place() {
    let dir = TempDir::new().unwrap();
    let root = dir.path().join("plan");
    let events = [
        "{\"t\":\"2026-09-07T06:05:00-05:00\",\"ev\":\"wake\",\"slept_min\":490}\n",
        "{\"t\":\"2026-09-07T07:02:00-05:00\",\"ev\":\"start\",\"id\":\"t1\"}\n",
    ];
    for store in [
        Box::new(FsStore::new(&root)) as Box<dyn Store>,
        Box::new(MemStore::new()) as Box<dyn Store>,
    ] {
        for line in events {
            store.append_text(".tm/log.jsonl", line).unwrap();
        }
        assert_eq!(store.read_text(".tm/log.jsonl").unwrap(), events.concat());
        // The log is not a plan file.
        assert!(!store.list_files().unwrap().iter().any(|f| f.contains("log")));
    }
    assert_eq!(
        std::fs::read_to_string(root.join(".tm/log.jsonl")).unwrap(),
        events.concat()
    );
}
