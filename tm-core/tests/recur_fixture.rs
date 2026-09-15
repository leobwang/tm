//! `recur.rs` against the `plan-recur` fixture (§17.1): every kind of
//! recurrence, expanded over 2026-09-01..2026-09-21 with the fixture's two
//! weeks of log history replayed.

#[path = "../../tm/tests/support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

use std::path::{Path, PathBuf};

use chrono::{NaiveDate, NaiveDateTime};
use serde::Serialize;
use tm_core::config::Config;
use tm_core::grammar::{parse_file, ParsedFile};
use tm_core::log::Replay;
use tm_core::model::{Instance, IsoWeek, Recur};
use tm_core::recur::{self, InstanceInfo};
use tm_core::tree::Tree;

/// Build order: month, week, backlog, routines, optional (store.rs's order).
const FILES: &[&str] = &[
    "month/2026-09.md",
    "week/2026-W37.md",
    "backlog.md",
    "routines.md",
    "optional.md",
];

const TODAY: &str = "2026-09-07";
const NOW: &str = "2026-09-07T10:42";
const RANGE: (&str, &str) = ("2026-09-01", "2026-09-21");

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/plan-recur")
}

fn load() -> (Tree, Config, Replay) {
    let cfg = Config::load(fixture_dir().join("config.toml")).unwrap();
    let parsed: Vec<ParsedFile> = FILES
        .iter()
        .map(|rel| {
            let text = std::fs::read_to_string(fixture_dir().join(rel)).unwrap();
            parse_file(rel, &text, &cfg)
        })
        .collect();
    for f in &parsed {
        assert!(
            f.all_problems().is_empty(),
            "{} has parse problems: {:?}",
            f.path,
            f.all_problems()
        );
    }
    let log_text = std::fs::read_to_string(fixture_dir().join(".tm/log.jsonl")).unwrap();
    let log_warnings = chokepoint::warning_lines_of_text(&log_text);
    assert!(log_warnings.is_empty(), "log warnings: {:?}", log_warnings);
    let replay = chokepoint::replay_of_text(&log_text, cfg.tz);
    assert!(
        replay.warnings.is_empty(),
        "replay warnings: {:?}",
        replay.warnings
    );
    let tree = Tree::build(&parsed, &cfg);
    assert!(
        tree.problems().is_empty(),
        "fixture tree problems: {:?}",
        tree.problems()
    );
    (tree, cfg, replay)
}

fn date(s: &str) -> NaiveDate {
    tm_core::model::parse_date(s).unwrap()
}

fn dt(s: &str) -> NaiveDateTime {
    tm_core::model::parse_datetime(s).unwrap()
}

fn fmt_dt(t: NaiveDateTime) -> String {
    t.format("%Y-%m-%dT%H:%M").to_string()
}

#[derive(Serialize)]
struct Row {
    inst: String,
    status: String,
    due: Option<String>,
    window: Option<String>,
    #[serde(skip_serializing_if = "str::is_empty")]
    flags: String,
}

#[derive(Serialize)]
struct ItemRows {
    item: String,
    recur: String,
    on_miss: String,
    instances: Vec<Row>,
}

fn flags(info: &InstanceInfo) -> String {
    let mut v: Vec<String> = Vec::new();
    if info.mandatory {
        v.push("mandatory".into());
    }
    if info.last_chance {
        v.push("last-chance".into());
    }
    if info.overdue {
        v.push("overdue".into());
    }
    if let Some(d) = info.carried_from {
        v.push(format!("carried-from {d}"));
    }
    if info.deferred_from_yesterday {
        v.push("deferred".into());
    }
    if info.not_yet {
        v.push("not-yet".into());
    }
    v.join(" · ")
}

fn row(inst: &Instance, info: &InstanceInfo) -> Row {
    Row {
        inst: inst.key.to_string(),
        status: format!("{:?}", inst.status),
        due: inst.due.map(fmt_dt),
        window: inst
            .window
            .map(|(a, b)| format!("{}..{}", fmt_dt(a), fmt_dt(b))),
        flags: flags(info),
    }
}

fn recur_label(r: &Recur) -> String {
    r.token().unwrap_or_else(|| "-".to_string())
}

#[test]
fn instances_over_three_weeks() {
    let (tree, cfg, replay) = load();
    let (today, now) = (date(TODAY), dt(NOW));
    let range = (date(RANGE.0), date(RANGE.1));
    let rows: Vec<ItemRows> = tree
        .iter()
        .map(|item| {
            let instances = recur::instances_with_info(item, range, today, now, &replay, &cfg);
            ItemRows {
                item: Tree::key_of(item).to_string(),
                recur: recur_label(&item.recur),
                on_miss: item.on_miss.as_str().to_string(),
                instances: instances.iter().map(|(i, info)| row(i, info)).collect(),
            }
        })
        .filter(|r| !r.instances.is_empty())
        .collect();
    insta::assert_yaml_snapshot!("instances_2026-09-01_to_09-21", rows);
}

#[test]
fn today_instances_for_the_planner() {
    let (tree, cfg, replay) = load();
    let (today, now) = (date(TODAY), dt(NOW));
    let items: Vec<_> = tree.iter().collect();
    let rows: Vec<ItemRows> = recur::today_instances(items, today, now, &replay, &cfg)
        .iter()
        .map(|(i, info)| ItemRows {
            item: i.item.to_string(),
            recur: recur_label(&tree.get(&i.item).map(|it| it.recur.clone()).unwrap()),
            on_miss: tree
                .get(&i.item)
                .map(|it| it.on_miss.as_str().to_string())
                .unwrap(),
            instances: vec![row(i, info)],
        })
        .collect();
    insta::assert_yaml_snapshot!("today_instances_2026-09-07", rows);
}

#[test]
fn week_instances_cover_the_whole_week() {
    let (tree, cfg, replay) = load();
    let (today, now) = (date(TODAY), dt(NOW));
    let week = IsoWeek::parse("2026-W37").unwrap();
    let items: Vec<_> = tree.iter().collect();
    let grid = recur::week_instances(items, week, today, now, &replay, &cfg);
    // No instance starts after the week (a still-pending overdue instance,
    // like the vitamins that were due on 09-05, is carried in on purpose).
    let (_, to) = week.range();
    for (i, _) in &grid {
        let start = i.window.map(|w| w.0.date()).or(i.due.map(|d| d.date()));
        assert!(
            start.is_none_or(|s| s <= to),
            "{:?} {:?} starts after {to}",
            i.item,
            i.key
        );
    }
    // One daily routine per day of the week, and the weekly laundry once.
    let lunch = grid
        .iter()
        .filter(|(i, _)| i.item.as_str() == "lunch")
        .count();
    assert_eq!(lunch, 7);
    let laundry: Vec<String> = grid
        .iter()
        .filter(|(i, _)| i.item.as_str() == "laundry")
        .map(|(i, _)| i.key.to_string())
        .collect();
    // §12.3 splits the screen: the grid is *this week's* windows, and overdue
    // persist items are a separate list beside it. So last week's laundry
    // window (still Pending, carried) keeps its own date and is not a W37
    // column — `today_instances` is what surfaces it, and does.
    assert_eq!(laundry, vec!["2026-09-07"]);
    let items: Vec<_> = tree.iter().collect();
    let carried: Vec<String> = recur::today_instances(items, today, now, &replay, &cfg)
        .iter()
        .filter(|(i, _)| i.item.as_str() == "laundry")
        .map(|(i, info)| format!("{} overdue={}", i.key, info.overdue))
        .collect();
    // …and surfaces it *alone*, keyed on this week's occurrence and carrying
    // last week's overdue badge: §5.3's persisted miss and the occurrence
    // that came round while it stayed open are one obligation, so there is
    // one row and doing it once discharges the whole carry.
    assert_eq!(carried, vec!["2026-09-07 overdue=true".to_string()]);
}
