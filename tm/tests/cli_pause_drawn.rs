//! **A typed `tm pause` is NOT lost time** — the owner's D68 (stage 6 W-38
//! track T, parity P59, README gap 3344).
//!
//! `plan-basic`, `^t4` started at 07:00, a typed `tm pause` 07:30–07:40 and an
//! interruption 09:40–09:55. Until D68 `tm plan` drew both as lost time —
//! `lost 10m … paused` and `lost 15m … interruption` — while `tm review day`
//! counted `lost 15m`: one span, two readings (AGENTS §5.3). The spec's "lost"
//! is interruption time (§9's Interruption row logs `lost=` on `resume`), so
//! the review's reading stands and the DRAWING moves: the pause is drawn
//! `paused 10m`, in the pause style, with `--json` kind `pause`.
//!
//! Every test reads the bytes a user reads: `tm --json plan`, the day file,
//! its SVG, `tm review day` and `tm review week --json`. The last one compares
//! the kernel's cells with the host's for the same row, through the FFI.

mod cli_common;
mod tui_common;

#[allow(dead_code)]
#[path = "support/rowwire.rs"]
mod rowwire;

use std::fs;

use chrono::Duration;
use cli_common::Tm;
use serde_json::{json, Value};

use tm_core::dayplan::{DayPlan, SegKind, PAUSED_NOTE};
use tm_core::model::Id;

/// The day file the plan lands in.
const DAY: &str = "day/2026-09-07.md";

/// The day's SVG (§12.1's day bar).
const SVG: &str = "day/2026-09-07.svg";

/// `^t4` from 07:00, paused 07:30–07:40, interrupted 09:40–09:55.
fn paused_then_interrupted() -> Tm {
    let tm = Tm::new();
    tm.ok_at("2026-09-07T06:05:00-05:00", &["wake", "06:05", "--slept", "8h"]);
    tm.ok_at("2026-09-07T07:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm.ok_at("2026-09-07T07:30:00-05:00", &["pause"]);
    tm.ok_at("2026-09-07T07:40:00-05:00", &["pause"]);
    tm.ok_at("2026-09-07T09:40:00-05:00", &["interrupt"]);
    tm.ok_at("2026-09-07T09:55:00-05:00", &["resume"]);
    tm
}

/// `(kind, start, end, text)` of every segment of `tm --json plan` at `at`
/// that starts before 10:00 — the day's past half and the open row.
fn past(tm: &Tm, at: &str) -> Vec<(String, String, String, String)> {
    let plan = tm.json_at(at, &["plan"]);
    plan["segments"]
        .as_array()
        .cloned()
        .unwrap_or_default()
        .iter()
        .map(|s| {
            let st = |k: &str| s[k].as_str().unwrap_or_default().to_string();
            (st("kind"), st("start"), st("end"), st("text"))
        })
        .filter(|s| s.1.as_str() < "10:00")
        .collect()
}

/// `HH:MM` as minutes of the day.
fn min(hhmm: &str) -> u32 {
    let (h, m) = hhmm.split_once(':').unwrap_or(("0", "0"));
    h.parse::<u32>().unwrap_or(0) * 60 + m.parse::<u32>().unwrap_or(0)
}

/// **The drive, pinned.** The pause is drawn `paused 10m` with nothing in the
/// note column and `--json` kind `pause`; the interruption is drawn as before,
/// `lost 15m … interruption`, kind `lost`.
#[test]
fn a_typed_pause_is_drawn_as_a_pause_and_an_interruption_as_lost() {
    let tm = paused_then_interrupted();
    let segs = past(&tm, "2026-09-07T10:00:00-05:00");
    let pause: Vec<_> = segs.iter().filter(|s| s.1 == "07:30").collect();
    assert_eq!(pause.len(), 1, "{segs:?}");
    let (kind, _, end, text) = pause[0];
    assert_eq!((kind.as_str(), end.as_str()), ("pause", "07:40"), "{segs:?}");
    assert!(text.contains("paused 10m"), "the pause is drawn as a pause: {text:?}");
    assert!(!text.contains("lost"), "and never as lost time: {text:?}");
    assert!(text.trim_end().ends_with("@m2"), "the word is said once, in the title: {text:?}");
    let lost: Vec<_> = segs.iter().filter(|s| s.1 == "09:40").collect();
    assert_eq!(lost.len(), 1, "{segs:?}");
    assert_eq!((lost[0].0.as_str(), lost[0].2.as_str()), ("lost", "09:55"), "{segs:?}");
    assert!(lost[0].3.contains("lost 15m") && lost[0].3.contains("interruption"), "{:?}", lost[0].3);
    assert!(
        !segs.iter().any(|s| s.0 == "lost" && s.3.contains("paused")),
        "no row the plan draws as lost is a pause: {segs:?}"
    );
}

/// **`.tm/last_plan.json` reads the span as `tm --json plan` does** (README gap
/// 3433's stored half, the W-38 repair): the typed pause is stored `pause`, the
/// interruption `lost` — the stored plan recorded both as `lost` with nothing
/// to tell them apart.
#[test]
fn the_stored_plan_calls_a_typed_pause_a_pause() {
    let tm = paused_then_interrupted();
    let segs = past(&tm, "2026-09-07T10:00:00-05:00");
    let stored: Value = serde_json::from_str(
        &std::fs::read_to_string(tm.plan.join(".tm/last_plan.json")).expect("the stored plan"),
    )
    .expect("json");
    let kinds: Vec<(String, String)> = stored["segments"]
        .as_array()
        .cloned()
        .unwrap_or_default()
        .iter()
        .filter(|s| s["start"].as_str().is_some_and(|t| t < "10:00"))
        .map(|s| (s["kind"].as_str().unwrap_or_default().to_string(), s["start"].as_str().unwrap_or_default().to_string()))
        .collect();
    let json: Vec<(String, String)> = segs.iter().map(|s| (s.0.clone(), s.1.clone())).collect();
    assert_eq!(kinds, json, "the stored plan and --json read each span alike");
    assert!(kinds.contains(&("pause".to_string(), "07:30".to_string())), "{kinds:?}");
    assert!(kinds.contains(&("lost".to_string(), "09:40".to_string())), "{kinds:?}");
}

/// **One reading of the day's lost time** — D68's point. The minutes `tm plan`
/// draws as lost are the minutes `tm review day` counts lost, and the pause's
/// ten are in neither.
#[test]
fn the_minutes_the_plan_draws_lost_are_the_minutes_the_review_counts() {
    let tm = paused_then_interrupted();
    let segs = past(&tm, "2026-09-07T10:00:00-05:00");
    let drawn: u32 = segs.iter().filter(|s| s.0 == "lost").map(|s| min(&s.2) - min(&s.1)).sum();
    let paused: u32 = segs.iter().filter(|s| s.0 == "pause").map(|s| min(&s.2) - min(&s.1)).sum();
    let review = tm.json_at("2026-09-07T10:01:00-05:00", &["review", "day"]);
    assert_eq!(review["review"]["lost_min"], 15, "{review}");
    assert_eq!(drawn, 15, "{segs:?}");
    assert_eq!(paused, 10, "{segs:?}");
    let text = tm.run_at("2026-09-07T10:02:00-05:00", &["review", "day"]);
    assert!(text.stdout.contains("lost 15m"), "{}", text.stdout);
}

/// **The day file and its SVG draw the pause, too.** The file's `tm:plan`
/// section holds the `paused 10m` row and no `lost 10m`; the SVG fills the
/// pause with the pause style's colour, not Lost's hatching, and keeps the
/// hatching for the interruption.
#[test]
fn the_day_file_and_its_svg_draw_the_pause() {
    let tm = paused_then_interrupted();
    tm.ok_at("2026-09-07T10:00:00-05:00", &["plan"]);
    let day = tm.read(DAY);
    let row = day.lines().find(|l| l.starts_with("07:30")).unwrap_or_else(|| panic!("{day}"));
    assert!(row.contains("paused 10m") && !row.contains("lost"), "{row:?}");
    assert!(day.lines().any(|l| l.starts_with("09:40") && l.contains("lost 15m")), "{day}");
    let svg = tm.read(SVG);
    let rects: Vec<&str> = svg.split("<rect").filter(|r| r.contains("<title>Claude Code drafts tests · ")).collect();
    let fill_of = |dur: &str| -> String {
        let r = rects
            .iter()
            .find(|r| r.contains(&format!("drafts tests · {dur} ·")))
            .unwrap_or_else(|| panic!("no {dur} rect: {rects:?}"));
        let at = r.find("fill=\"").expect("a fill") + 6;
        r[at..at + r[at..].find('"').expect("a closing quote")].to_string()
    };
    let (r, g, b) = tm_core::emit::CellStyle::Pause.colour();
    assert_ne!(
        tm_core::emit::CellStyle::Pause.colour(),
        tm_core::emit::CellStyle::Lost.colour(),
        "a pause is not drawn in lost time's colour"
    );
    assert_eq!(fill_of("10m"), format!("#{r:02x}{g:02x}{b:02x}"), "the pause's own colour");
    assert_eq!(fill_of("15m"), "url(#tm-lost)", "the interruption keeps Lost's hatching");
}

/// **The week grid keeps a typed pause a pause** — never a leak — and the
/// interruption an interruption (D69's call on gap 3244 reads D68 into the
/// week review: the grid was already right about the typed pause, and this
/// pins it).
#[test]
fn the_week_grid_counts_a_typed_pause_as_a_pause() {
    let tm = paused_then_interrupted();
    let week = tm.json_at("2026-09-07T10:03:00-05:00", &["review", "week"]);
    let day = week["review"]["heat"]
        .as_array()
        .and_then(|d| d.iter().find(|x| x["date"] == "2026-09-07"))
        .unwrap_or_else(|| panic!("{week}"));
    let style = |i: usize, s: tm_core::review::Style| -> u64 {
        day["hours"][i][s.index()].as_u64().unwrap_or_default()
    };
    use tm_core::review::Style;
    assert_eq!(style(7, Style::Pause), 10, "{day}");
    assert_eq!(style(7, Style::Leak) + style(7, Style::Idle), 0, "{day}");
    assert_eq!(style(9, Style::Interrupt), 15, "{day}");
}

/// **The kernel draws the row the host draws**, through the FFI: a Lost row
/// carrying `^t4` and the `paused` note is `paused 50m` with an empty note on
/// both sides (`Emit.titleCell`/`Emit.noteCell` against `emit::row_cells`),
/// and the same row with the `interruption` note is `lost 50m … interruption`
/// on both. The note the kernel reads is the NAME the kernel's planner writes
/// (`Note.paused`), so the host's prose note is set beside it by hand.
#[test]
fn the_kernel_and_the_host_draw_a_paused_row_alike() {
    let cfg = tui_common::config();
    let tree = tui_common::tree(&cfg);
    let base = tui_common::day_plan(&cfg);
    let proto = base
        .segments
        .iter()
        .find(|s| matches!(s.kind, SegKind::Block))
        .expect("a block")
        .clone();
    let mut plan = DayPlan::empty(base.date, base.window, base.budget_blocks);
    plan.priorities = base.priorities.clone();
    let notes = [(PAUSED_NOTE, "paused"), ("interruption", "interruption")];
    for (text, _) in notes {
        let mut seg = proto.clone();
        seg.kind = SegKind::Lost;
        seg.item = Some(Id::new("t4"));
        seg.instance = None;
        seg.flags.note = Some(text.to_string());
        seg.flags.done = false;
        seg.flags.current = false;
        seg.flags.hot = false;
        seg.flags.underused = false;
        seg.flags.planned_min = None;
        seg.flags.multiplier = None;
        seg.end = seg.start + Duration::minutes(50);
        plan.segments.push(seg);
    }
    let fork = rowwire::fork_cells(&plan, &tree, &cfg);
    let mut req = rowwire::request(docs(), &plan, &cfg);
    // The rows wire sends a paused row's note NAME itself and no other note (W-38 land step,
    // README gap 3436) -- what the generated cell arm in `planner_invariants.rs` relies on.
    assert_eq!(req["plan"]["segments"][0]["note"], json!({"name": "paused"}));
    assert_eq!(req["plan"]["segments"][1]["note"], Value::Null);
    for (i, (_, name)) in notes.iter().enumerate() {
        req["plan"]["segments"][i]["note"] = json!({"name": name});
    }
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    let rows = resp["ok"]["plan"]["rows"].as_array().unwrap_or_else(|| panic!("no rows: {raw}"));
    assert_eq!(rows.len(), 2, "{raw}");
    for (i, f) in fork.iter().enumerate() {
        let k = |c: &str| rows[i][c].as_str().unwrap_or_default().to_string();
        assert_eq!((k("title"), k("note")), (f.title.clone(), f.note.clone()), "row {i}: {raw}");
    }
    assert_eq!((fork[0].title.as_str(), fork[0].note.as_str()), ("paused 50m", ""));
    assert_eq!((fork[1].title.as_str(), fork[1].note.as_str()), ("lost 50m", "interruption"));
}

/// **The day bar draws the pause as a pause** — the surface `tm tui` and
/// `day/<date>.svg` share (`emit::daybar_cells`): a paused row's cell is the
/// pause style, which the TUI draws with the light dash and not Lost's
/// diagonal, and which is not hatched; a Lost row with any other note keeps
/// Lost's. (An agent cannot drive the TUI — it refuses a terminal that is not
/// a tty, AGENTS §5.13 — so this is its drawing, asserted on the function the
/// TUI calls.)
#[test]
fn the_day_bar_draws_a_pause_as_a_pause() {
    use tm_core::emit::{self, CellStyle};
    let cfg = tui_common::config();
    let tree = tui_common::tree(&cfg);
    let base = tui_common::day_plan(&cfg);
    let proto = base
        .segments
        .iter()
        .find(|s| matches!(s.kind, SegKind::Block))
        .expect("a block")
        .clone();
    let mut plan = DayPlan::empty(base.date, base.window, base.budget_blocks);
    for text in [PAUSED_NOTE, "interruption"] {
        let mut seg = proto.clone();
        seg.kind = SegKind::Lost;
        seg.item = Some(Id::new("t4"));
        seg.flags.note = Some(text.to_string());
        plan.segments.push(seg);
    }
    let wake = base.segments.first().map_or(proto.start, |s| s.start) - Duration::hours(2);
    let bar = emit::daybar_cells(&plan, None, &tree, &cfg, 96, wake, proto.end + Duration::hours(1));
    assert_eq!(bar.segments[0].style, CellStyle::Pause, "{:?}", bar.segments[0]);
    assert_eq!(bar.segments[1].style, CellStyle::Lost, "{:?}", bar.segments[1]);
    assert!(!CellStyle::Pause.is_hatched() && CellStyle::Lost.is_hatched());
    assert_eq!(tui_common::theme::cell_glyph(&bar.segments[0]), '╌');
    assert_eq!(tui_common::theme::cell_glyph(&bar.segments[1]), '╱');
}

/// The fixture tree as the kernel's request carries it — `kernel_row_cells`'
/// own list of documents.
fn docs() -> Vec<Value> {
    let dir = tui_common::fixture_dir();
    let files = [
        "month/2026-09.md",
        "week/2026-W37.md",
        "backlog.md",
        "routines.md",
        "optional.md",
        "calendar/2026-W37.md",
        "day/2026-09-07.md",
        "inbox.md",
    ];
    files
        .iter()
        .filter_map(|rel| {
            fs::read_to_string(dir.join(rel))
                .ok()
                .map(|t| json!({"path": rel, "lines": t.lines().collect::<Vec<_>>()}))
        })
        .collect()
}
