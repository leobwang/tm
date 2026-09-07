//! §17.2: `day/<date>.svg`, written by hand — one `<rect>` per segment with a
//! `<title>` child, hatched patterns for lost and interrupted time, a dotted
//! stroke on optionals, hour ticks, the cursor and the ghost row.

mod emit_fixture;

use emit_fixture::{at, config, ghost_plan, plan, tree};
use tm_core::emit;
use tm_core::model::Id;
use tm_core::planner::{DayPlan, SegFlags, SegKind, Segment};

fn svg(day: &DayPlan, ghost: Option<&DayPlan>, w: u32, h: u32) -> String {
    svg_cols(day, ghost, w, h, 96)
}

fn svg_cols(day: &DayPlan, ghost: Option<&DayPlan>, w: u32, h: u32, cols: usize) -> String {
    let cfg = config();
    let tree = tree(&cfg);
    let bar = emit::daybar_cells(day, ghost, &tree, &cfg, cols, at(6, 5), at(10, 42));
    emit::render_svg(&bar, day, &cfg, w, h)
}

/// `(y, height)` of every `<rect>` inside the `<g class="…">` group named.
fn group_rects(svg: &str, class: &str) -> Vec<(f64, f64)> {
    let open = format!("<g class=\"{class}\">");
    let from = svg.find(&open).map(|i| i + open.len()).unwrap_or(0);
    let body = &svg[from..];
    let body = &body[..body.find("</g>").unwrap_or(body.len())];
    body.split("<rect ")
        .skip(1)
        .map(|r| {
            let attr = |name: &str| -> f64 {
                let key = format!("{name}=\"");
                let i = r.find(&key).expect("attribute") + key.len();
                r[i..][..r[i..].find('"').expect("close quote")]
                    .parse()
                    .expect("number")
            };
            (attr("y"), attr("height"))
        })
        .collect()
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

    // The ghost row sits strictly below the plan row and strictly above the
    // hour labels. (Regression: this was `let plan_y = 0.0; let _ = plan_y;`,
    // which asserted nothing — moving `ghost_y` to 0.0, painting the ghost
    // over the plan, left the test passing.)
    let plan_rects = group_rects(&out, "plan");
    let ghost_rects = group_rects(&out, "ghost");
    assert!(!plan_rects.is_empty() && !ghost_rects.is_empty());
    let plan_bottom = plan_rects
        .iter()
        .map(|(y, h)| y + h)
        .fold(f64::MIN, f64::max);
    let ghost_top = ghost_rects.iter().map(|(y, _)| *y).fold(f64::MAX, f64::min);
    let ghost_bottom = ghost_rects
        .iter()
        .map(|(y, h)| y + h)
        .fold(f64::MIN, f64::max);
    assert!(
        plan_rects.iter().all(|(y, _)| *y == 0.0),
        "the plan row starts at the top"
    );
    assert!(
        ghost_top >= plan_bottom,
        "ghost row at {ghost_top} overlaps the plan row ending at {plan_bottom}"
    );
    // The hour labels are the only `<text>` in the tick group; the ghost must
    // end above their baseline.
    let label_y: f64 = out
        .split("<text ")
        .skip(1)
        .filter(|t| t.starts_with("x=") && t.contains("text-anchor"))
        .map(|t| {
            let i = t.find("y=\"").expect("y") + 3;
            t[i..][..t[i..].find('"').expect("quote")]
                .parse()
                .expect("number")
        })
        .fold(f64::MAX, f64::min);
    assert!(
        ghost_bottom <= label_y,
        "ghost row ends at {ghost_bottom}, below the hour labels at {label_y}"
    );
    insta::assert_snapshot!("svg_day_with_ghost", out);
}

#[test]
fn every_segment_keeps_its_title_and_its_hue() {
    // Regression: the rect's fill and `<title>` were looked up in
    // `bar.cells` by segment index, so a segment that won no *column* — one
    // overlapped by a finished segment, or one shorter than a cell — was drawn
    // as a flat grey rect with no hover text.
    //
    // (a) The log-vs-plan overlap the module documents: a finished block and a
    // planned one over the same minutes, left of the cursor.
    let mut day = plan();
    let mut planned = day.segments[0].clone();
    planned.flags.done = false;
    planned.item = Some(Id::new("t5"));
    planned.energy = Some(3);
    day.segments.insert(1, planned);
    let out = svg(&day, None, 960, 48);
    assert_eq!(out.matches("<title>").count(), day.segments.len());
    assert!(
        !out.contains("fill=\"#888888\""),
        "no segment falls back to grey:\n{out}"
    );
    assert!(out.contains("<title>Review the drafts · 1h7m · ci3 · p3 · @O2</title>"));

    // (b) A segment too short to dominate any cell.
    let mut day = plan();
    day.segments.push(Segment {
        start: at(10, 0),
        end: at(10, 4),
        kind: SegKind::Block,
        energy: Some(3),
        item: Some(Id::new("t5")),
        instance: None,
        flags: SegFlags::default(),
    });
    day.segments.sort_by_key(|s| s.start);
    let out = svg(&day, None, 960, 48);
    assert_eq!(out.matches("<title>").count(), day.segments.len());
    assert!(!out.contains("fill=\"#888888\""));

    // (c) A bar narrower than the plan has segments — §12.1 sets `cols =
    // width`, and the TUI stacks its panes below 110 columns.
    for cols in [12usize, 24, 48, 96, 200] {
        let day = plan();
        let out = svg_cols(&day, None, 960, 48, cols);
        assert_eq!(
            out.matches("<title>").count(),
            day.segments.len(),
            "cols = {cols}"
        );
    }
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

#[test]
fn the_other_two_fixture_days_render() {
    // M4's definition of done: a day-section and an SVG snapshot for an early
    // start (the §4.3 day above), a late start with a wall, and a home day.
    let late = emit_fixture::late_start_plan();
    let out = svg(&late, None, 960, 48);
    assert_eq!(out.matches("<title>").count(), late.segments.len());
    assert!(out.contains("<title>Dentist · 1h20m · ci2</title>"), "the wall");
    assert!(out.contains("fill=\"url(#tm-lost)\""), "the 10m leak");
    insta::assert_snapshot!("svg_late_start", out);

    let home = emit_fixture::home_day_plan();
    let out = svg(&home, None, 960, 48);
    assert_eq!(out.matches("<title>").count(), home.segments.len());
    // A batch hovers as the whole batch, with the `ci` and `p` of the key it
    // was assigned at (§7.5, its first member).
    assert!(out.contains(
        "<title>batch: Insurance claim for the bike · Call the bank about the card (2) \
         · 50m · ci2 · p3</title>"
    ));
    assert!(out.contains("<title>sleep · 8h30m · ci0</title>"));
    insta::assert_snapshot!("svg_home_day", out);
}
