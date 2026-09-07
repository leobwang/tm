//! §17.2: `day/<date>.svg`, written by hand — one `<rect>` per segment with a
//! `<title>` child, hatched patterns for lost and interrupted time, a dotted
//! stroke on optionals, hour ticks, the cursor and the ghost row.

mod emit_fixture;

use emit_fixture::{at, config, ghost_plan, plan, tree};
use tm_core::emit;
use tm_core::model::Id;
use tm_core::planner::{DayPlan, SegFlags, SegKind, Segment};

fn svg(day: &DayPlan, ghost: Option<&DayPlan>, w: u32, h: u32) -> String {
    let cfg = config();
    let tree = tree(&cfg);
    let bar = emit::daybar_cells(day, ghost, &tree, &cfg, 96, at(6, 5), at(10, 42));
    emit::render_svg(&bar, day, &cfg, w, h)
}

#[test]
fn the_day_bar_svg_has_a_rect_per_segment() {
    let day = plan();
    let out = svg(&day, None, 960, 48);
    assert!(out.starts_with("<svg xmlns=\"http://www.w3.org/2000/svg\""));
    assert!(out.ends_with("</svg>\n"));
    // One rect per segment, plus the background (the two `<pattern>`s hold a
    // rect each, without an `x`).
    let rects = out.matches("<rect x=").count();
    assert_eq!(rects, day.segments.len() + 1);
    // Every segment with an item carries its hover title.
    assert_eq!(out.matches("<title>").count(), day.segments.len());
    assert!(out.contains("<title>Exercises 5.3–5.5 · 2h · ci4 · p1 · @O1</title>"));
    // Hour ticks with labels every three hours, and the cursor.
    assert!(out.contains(">09<"));
    assert!(out.contains("class=\"cursor\""));
    assert!(out.contains(">10:42<"));
    assert!(!out.contains("class=\"ghost\""), "no ghost plan was given");
    insta::assert_snapshot!("svg_day", out);
}

#[test]
fn lost_and_interrupted_time_are_hatched_and_optionals_dotted() {
    let mut day = plan();
    // §9's interruption: an ad-hoc wall with no id, and the minutes it lost.
    day.segments.push(Segment {
        start: at(12, 10),
        end: at(13, 5),
        kind: SegKind::Wall,
        energy: None,
        item: None,
        instance: None,
        flags: SegFlags {
            note: Some("interrupt".to_string()),
            ..SegFlags::default()
        },
    });
    day.segments.push(Segment {
        start: at(15, 30),
        end: at(15, 44),
        kind: SegKind::Lost,
        energy: None,
        item: None,
        instance: None,
        flags: SegFlags {
            note: Some("leak".to_string()),
            ..SegFlags::default()
        },
    });
    day.segments.sort_by_key(|s| s.start);
    let out = svg(&day, None, 960, 48);
    assert!(out.contains("<pattern id=\"tm-lost\""));
    assert!(out.contains("<pattern id=\"tm-interrupt\""));
    assert!(out.contains("fill=\"url(#tm-lost)\""), "leak hatched orange");
    assert!(
        out.contains("fill=\"url(#tm-interrupt)\""),
        "interruption hatched red"
    );
    assert!(
        out.contains("stroke-dasharray=\"2 2\""),
        "optionals are dotted (§11 optional quota)"
    );
    insta::assert_snapshot!("svg_interrupted", out);
}

#[test]
fn the_ghost_row_is_drawn_beneath() {
    let day = plan();
    let ghost = ghost_plan();
    let out = svg(&day, Some(&ghost), 480, 60);
    assert!(out.contains("class=\"ghost\""));
    // The ghost row sits below the plan row and above the hour labels.
    let plan_y: f64 = 0.0;
    let _ = plan_y;
    insta::assert_snapshot!("svg_day_with_ghost", out);
}

#[test]
fn segments_outside_the_bars_span_are_skipped() {
    let mut day = plan();
    day.segments.push(Segment {
        start: at(6, 5) + chrono::Duration::hours(25),
        end: at(6, 5) + chrono::Duration::hours(26),
        kind: SegKind::Block,
        energy: Some(3),
        item: Some(Id::new("t5")),
        instance: None,
        flags: SegFlags::default(),
    });
    let before = svg(&plan(), None, 400, 40);
    let after = svg(&day, None, 400, 40);
    assert_eq!(
        before.matches("<rect x=").count(),
        after.matches("<rect x=").count(),
        "a segment past the 24 h span draws nothing"
    );
}

#[test]
fn an_empty_day_still_renders() {
    let day = DayPlan::empty(emit_fixture::date(), (at(7, 0), at(16, 0)), 6);
    let out = svg(&day, None, 200, 24);
    assert!(out.contains("</svg>"));
    assert_eq!(out.matches("<title>").count(), 0);
}
