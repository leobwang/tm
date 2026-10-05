//! Fixture tests: every `plan-basic` file round-trips byte-identically, and
//! the parsed items of the key files are snapshotted (insta yaml) so
//! downstream modules can see the shapes.

use std::path::{Path, PathBuf};

use tm_core::config::Config;
use tm_core::grammar::{parse_file, serialize_file, ParsedFile};
use tm_core::model::{Horizon, Id, Item, Scope, Shape, State};

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/plan-basic")
}

const FILES: &[&str] = &[
    "month/2026-09.md",
    "week/2026-W37.md",
    "backlog.md",
    "routines.md",
    "optional.md",
    "calendar/2026-W37.md",
    "day/2026-09-07.md",
    "inbox.md",
];

fn load(rel: &str) -> (String, ParsedFile) {
    let cfg = Config::load(fixture_dir().join("config.toml")).unwrap();
    let text = std::fs::read_to_string(fixture_dir().join(rel)).unwrap();
    let parsed = parse_file(rel, &text, &cfg);
    (text, parsed)
}

#[test]
fn fixture_config_is_the_spec_default() {
    let cfg = Config::load(fixture_dir().join("config.toml")).unwrap();
    assert_eq!(cfg, Config::default());
    let text = std::fs::read_to_string(fixture_dir().join("config.toml")).unwrap();
    assert_eq!(text, Config::default_toml());
}

#[test]
fn every_fixture_round_trips_byte_identically() {
    for rel in FILES {
        let (text, parsed) = load(rel);
        assert_eq!(serialize_file(&parsed), text, "{rel}");
        assert!(
            parsed.all_problems().is_empty(),
            "{rel}: {:?}",
            parsed.all_problems()
        );
        for item in parsed.items() {
            assert_eq!(item.line_text(), parsed.lines[item.src.line - 1].text(), "{rel}");
        }
    }
}

/// §17 M1's DoD is "parse→serialize is byte-identical for **every**
/// fixture", not just `plan-basic`: §17.1 lists five trees, and the one whose
/// lines are most likely to lose bytes on a rewrite is `plan-conflicts`,
/// whose whole point is malformed values (`due:tomorrow`, `!9`, `ci:7`, `^%`,
/// a leading `7 2b` that stays in the title).
#[test]
fn every_file_of_every_fixture_round_trips_byte_identically() {
    let mut checked = 0usize;
    for dir in fixture_dirs() {
        let cfg = Config::load(dir.join("config.toml")).unwrap_or_default();
        for path in markdown_files(&dir) {
            let rel = path
                .strip_prefix(&dir)
                .expect("under the fixture")
                .to_string_lossy()
                .replace('\\', "/");
            let text = std::fs::read_to_string(&path).expect("readable");
            let parsed = parse_file(&rel, &text, &cfg);
            assert_eq!(
                serialize_file(&parsed),
                text,
                "{}/{rel} did not round-trip",
                dir.file_name().unwrap_or_default().to_string_lossy()
            );
            for item in parsed.items() {
                assert_eq!(
                    item.line_text(),
                    parsed.lines[item.src.line - 1].text(),
                    "{}/{rel}",
                    dir.file_name().unwrap_or_default().to_string_lossy()
                );
            }
            checked += 1;
        }
    }
    assert!(checked >= 30, "only {checked} files were round-tripped");
}

/// §17.1's fixture trees.
fn fixture_dirs() -> Vec<PathBuf> {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures");
    let mut out: Vec<PathBuf> = std::fs::read_dir(&root)
        .expect("fixtures/ readable")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.is_dir() && p.join("config.toml").is_file())
        .collect();
    out.sort();
    assert!(out.len() >= 5, "§17.1 lists five fixture trees: {out:?}");
    out
}

/// Every `.md` under `dir`, outside `.tm/`, sorted.
fn markdown_files(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(entries) = std::fs::read_dir(&d) else {
            continue;
        };
        for entry in entries.filter_map(Result::ok) {
            let path = entry.path();
            let name = entry.file_name().to_string_lossy().to_string();
            if path.is_dir() {
                if !name.starts_with('.') {
                    stack.push(path);
                }
            } else if path.extension().is_some_and(|e| e == "md") {
                out.push(path);
            }
        }
    }
    out.sort();
    out
}

#[test]
fn every_fixture_item_has_a_unique_id_except_open_files() {
    // `tm close week` *copies* a line into `month/…#Demoted` keeping its id
    // (§6.3), so the spec fixture has `^m2` in both files by design.
    let mut seen = std::collections::HashSet::new();
    for rel in FILES {
        let (_, parsed) = load(rel);
        for item in parsed.items() {
            if matches!(parsed.horizon, Horizon::Routine | Horizon::Optional | Horizon::Inbox) {
                assert!(!item.has_id(), "{rel}: {}", item.title);
                continue;
            }
            assert!(item.has_id(), "{rel}: {}", item.title);
            if item.src.section.as_deref() == Some("Demoted") {
                continue;
            }
            assert!(seen.insert(item.id.clone()), "duplicate id {}", item.id);
        }
    }
}

#[test]
fn month_file() {
    let (_, f) = load("month/2026-09.md");
    assert_eq!(f.front("month"), Some("2026-09"));
    let items: Vec<&Item> = f.items().collect();
    assert_eq!(items.len(), 4);
    assert_eq!(items[0].priority, Some(1));
    assert_eq!(items[0].title, "Lean: through ch.8 of the tutorial");
    assert_eq!(items[0].src.section.as_deref(), Some("Outcomes"));
    assert_eq!(items[3].state, State::Demoted);
    assert_eq!(items[3].src.section.as_deref(), Some("Demoted"));
    assert_eq!(items[3].stamps.demoted_value(), "W37");
}

#[test]
fn week_file_snapshot() {
    let (_, f) = load("week/2026-W37.md");
    assert_eq!(f.front("budget"), Some("25"));
    assert_eq!(f.front("planned"), Some("20"));
    let items: Vec<&Item> = f.items().collect();
    assert_eq!(items.len(), 11);
    assert_eq!(f.find(&Id::new("t3")).unwrap().state, State::Active);
    assert!(matches!(f.find(&Id::new("x1")).unwrap().shape, Shape::Interval { .. }));
    assert_eq!(f.find(&Id::new("x2")).unwrap().shape, Shape::None);
    insta::assert_yaml_snapshot!("week_2026-W37_items", items);
}

#[test]
fn backlog_file_snapshot() {
    let (_, f) = load("backlog.md");
    let items: Vec<&Item> = f.items().collect();
    assert_eq!(items.len(), 7);
    assert_eq!(items[4].series, Some(("cell-bio".to_string(), 0)));
    assert_eq!(items[6].series, Some(("cell-bio".to_string(), 2)));
    assert_eq!(items[4].state, State::Done);
    insta::assert_yaml_snapshot!("backlog_items", items);
}

#[test]
fn routines_file_snapshot() {
    let (_, f) = load("routines.md");
    let items: Vec<&Item> = f.items().collect();
    assert_eq!(items.len(), 8);
    for it in &items {
        assert_eq!(it.scope, Scope::Open);
        assert!(matches!(it.shape, Shape::Window { .. }), "{}", it.title);
        assert!(!it.has_id());
    }
    assert_eq!(items[0].ci, 0);
    assert!(items[0].ci_explicit);
    assert_eq!(items[1].ci, 1);
    assert!(!items[1].ci_explicit);
    insta::assert_yaml_snapshot!("routines_items", items);
}

#[test]
fn optional_file() {
    let (_, f) = load("optional.md");
    let items: Vec<&Item> = f.items().collect();
    assert_eq!(items.len(), 2);
    assert_eq!(items[0].ci, 0);
    assert_eq!(items[0].scope, Scope::Open);
    assert_eq!(items[0].dur.unwrap().minutes, 60);
    assert_eq!(items[1].budget.cap.unwrap().to_string(), "4h/w");
}

#[test]
fn calendar_file_snapshot() {
    let (_, f) = load("calendar/2026-W37.md");
    let items: Vec<&Item> = f.items().collect();
    assert_eq!(items.len(), 4);
    // fork `Item::is_travel_day`'s reading of the flag (R3 deleted that method, README gap 4752)
    assert!(items[2].has_flag("travel-day"));
    assert_eq!(items[2].buffer.unwrap().minutes, 120);
    assert!(items[3].is_manual());
    insta::assert_yaml_snapshot!("calendar_2026-W37_items", items);
}

#[test]
fn day_file_structure() {
    let (_, f) = load("day/2026-09-07.md");
    assert_eq!(f.front("wake"), Some("06:05"));
    assert_eq!(f.front("slept"), Some("8h10m"));
    assert_eq!(f.front("window"), Some("07:00..16:00"));
    let g = f.generated("plan").unwrap();
    assert_eq!(g.info, "10:42");
    assert_eq!(g.start_line, 10);
    assert_eq!(g.end_line, Some(25));
    let items: Vec<&Item> = f.items().collect();
    assert_eq!(items.len(), 1, "only the pinned item is an item line");
    assert_eq!(items[0].id, Id::new("p1"));
    assert_eq!(items[0].src.section.as_deref(), Some("Pinned"));
    assert_eq!(items[0].src.line, 28);
    assert!(f.in_generated(15));
    assert!(!f.in_generated(28));
}

#[test]
fn inbox_file() {
    let (_, f) = load("inbox.md");
    let items: Vec<&Item> = f.items().collect();
    assert_eq!(items.len(), 4);
    assert_eq!(items[0].title, "pset2 fri 6b ci4 max 2b/d");
    assert!(items.iter().all(|i| i.problems.is_empty()));
}

#[test]
fn edit_in_file_changes_only_that_line() {
    let (text, mut f) = load("week/2026-W37.md");
    let it = f
        .items_mut()
        .find(|i| i.id == Id::new("t3"))
        .unwrap();
    it.src.tokens.set_token("est", "0b");
    let out = serialize_file(&f);
    let diff: Vec<(&str, &str)> = text
        .lines()
        .zip(out.lines())
        .filter(|(a, b)| a != b)
        .collect();
    assert_eq!(
        diff,
        vec![(
            "- [>] 4 2b Exercises 5.3–5.5            @m1 est:1b ^t3",
            "- [>] 4 2b Exercises 5.3–5.5            @m1 est:0b ^t3"
        )]
    );
}
