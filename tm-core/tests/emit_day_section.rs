//! §4.3: the generated `<!-- tm:plan … -->` section of the day file.
//!
//! The plan is the §4.3 example, hand-built in `emit_fixture` (the planner is
//! still a stub). The snapshot is the whole block; four rows are additionally
//! asserted byte for byte against the spec's own text.
//!
//! The spec's example is hand-aligned and cannot be reproduced by any single
//! rule — it starts the title at column 14 on rows with a mark (`✓ Read ch.6
//! §1–2`, `⏰`, `🌙`) and at column 15 on rows without one, and it slides the
//! estimate into the empty `@parent` column on the three rows that have no
//! parent. This renderer keeps every column at a fixed offset, so:
//!
//! * rows whose mark is blank, or whose `ci` column holds a narrow glyph
//!   (`·`, `○`, `───`), start the title one column earlier than the example;
//! * `⏰ Meeting w/ host  1h`, `⚠ Pick up package  20m` and `○ Severance S3E4
//!   1h` keep their estimate in the estimate column (48) instead of sliding it
//!   to 43;
//! * the `09:00` break's `(24m)` sits in the actual column (52), where the
//!   example puts it at 48.
//!
//! Everything else — the mark set, the `4↓p3` cell, `2b×1.6`, the note column
//! at 55, `@parent` at 43, the estimate at 48 and the `───  window ends 16:00`
//! divider — is the example's.

mod emit_fixture;

use emit_fixture::{at, config, date, plan, tree};
use tm_core::emit::{self, Layout};

/// The *character* column a substring starts at (`str::find` counts bytes, and
/// these rows are full of `§`, `–` and `✓`).
fn col(line: &str, needle: &str) -> Option<usize> {
    line.find(needle).map(|b| line[..b].chars().count())
}

/// The four §4.3 rows a fixed-column renderer reproduces exactly.
const SPEC_ROWS: &[(usize, &str)] = &[
    (
        0,
        "07:00  5 p1 ✓ Read ch.6 §1–2               @m3  1b  (67m)",
    ),
    (
        1,
        "08:00  5 p1 ✓ Read ch.6 §3                 @m3  1b  (58m)",
    ),
    (3, "09:20  4 p1 ▶ Exercises 5.3–5.5            @m1  2b×1.6"),
    (13, "21:30  🌙      wind-down · bed 22:00"),
];

#[test]
fn day_section_matches_the_spec_example() {
    let cfg = config();
    let tree = tree(&cfg);
    let day = plan();
    let (info, body) = emit::render_plan_section(&day, &tree, &cfg, at(10, 42));

    // The `<!-- tm:plan start 10:42 -->` stamp.
    assert_eq!(info, "10:42");

    let lines: Vec<&str> = body.lines().collect();
    assert_eq!(lines.len(), 14, "13 segments plus the window divider");
    for (i, expected) in SPEC_ROWS {
        assert_eq!(&lines[*i], expected, "row {i} differs from tm-spec-v1 §4.3");
    }

    // The columns the spec fixes: @parent at 43, est at 48, note at 55.
    assert_eq!(col(lines[0], "@m3"), Some(43));
    assert_eq!(col(lines[0], "1b"), Some(48));
    assert_eq!(col(lines[0], "(67m)"), Some(52));
    assert_eq!(col(lines[5], "↓ slot 4, item 3"), Some(55));
    assert_eq!(col(lines[0], "Read"), Some(14), "the title column");

    insta::assert_snapshot!("day_section", body);
}

#[test]
fn marks_and_glyphs_are_the_spec_set() {
    let cfg = config();
    let tree = tree(&cfg);
    let day = plan();
    let (_, body) = emit::render_plan_section(&day, &tree, &cfg, at(10, 42));
    let lines: Vec<&str> = body.lines().collect();

    assert!(lines[0].contains('✓'), "done");
    assert!(lines[3].contains('▶'), "current");
    assert!(lines[5].contains("4↓p3"), "under-used slot next to the ci");
    assert!(lines[10].contains('⚠'), "HOT (p0)");
    assert!(lines[6].contains('⏰'), "interval");
    assert!(lines[12].contains('○'), "optional");
    assert!(lines[4].starts_with("11:20  ·"), "routine");
    assert!(lines[13].contains('🌙'), "wind-down");
    assert_eq!(lines[9], "15:10  ───    window ends 16:00");
}

#[test]
fn the_divider_lands_where_the_budget_runs_out() {
    let cfg = config();
    let tree = tree(&cfg);
    let mut day = plan();
    // A budget nothing exhausts pushes the divider to the window end, in front
    // of the first segment planned past it (dinner at 17:30).
    day.budget_blocks = 12;
    let (_, body) = emit::render_plan_section(&day, &tree, &cfg, at(10, 42));
    let lines: Vec<&str> = body.lines().collect();
    let divider = lines
        .iter()
        .position(|l| l.contains("window ends"))
        .expect("divider");
    assert_eq!(lines[divider], "16:00  ───    window ends 16:00");
    assert!(lines[divider + 1].starts_with("17:30"));

    // A day that stops inside the window gets no divider at all.
    let mut short = plan();
    short.segments.retain(|s| s.start < at(15, 0));
    short.budget_blocks = 12;
    let (_, body) = emit::render_plan_section(&short, &tree, &cfg, at(10, 42));
    assert!(!body.contains("window ends"));
}

#[test]
fn titles_are_truncated_to_the_layout_width() {
    let cfg = config();
    let tree = tree(&cfg);
    let day = plan();
    let (_, body) =
        emit::render_plan_section_with(&day, &tree, &cfg, at(10, 42), &Layout::new(12));
    let lines: Vec<&str> = body.lines().collect();
    assert_eq!(
        lines[5], "11:50  4↓p3   Claude Code…  @m2  1b     ↓ slot 4, item 3",
        "the title is cut with … and every later column moves left with it"
    );
    insta::assert_snapshot!("day_section_narrow", body);
}

#[test]
fn a_log_faithful_day_keeps_the_actuals_and_the_real_starts() {
    let cfg = config();
    let tree = tree(&cfg);
    let day = emit_fixture::log_faithful_plan();
    let (_, body) = emit::render_plan_section(&day, &tree, &cfg, at(10, 42));
    let lines: Vec<&str> = body.lines().collect();
    // `plan-basic`'s log: 07:02 start ^t1 · 08:09 done 67m · 09:08 break 24m ·
    // 09:32 start ^t3.
    assert!(lines[0].starts_with("07:02"));
    assert!(lines[0].ends_with("(67m)"));
    assert!(lines[2].starts_with("09:08"));
    assert!(lines[3].starts_with("09:32"));
    insta::assert_snapshot!("day_section_log_faithful", body);
}

#[test]
fn a_batch_is_one_row_naming_its_items() {
    use tm_core::model::Id;
    use tm_core::planner::{SegFlags, SegKind, Segment};

    let cfg = config();
    let tree = tree(&cfg);
    let mut day = plan();
    day.segments.push(Segment {
        start: at(16, 0),
        end: at(17, 0),
        kind: SegKind::Batch(vec![Id::new("a3"), Id::new("a1"), Id::new("p1")]),
        energy: Some(2),
        item: None,
        instance: None,
        flags: SegFlags {
            planned_min: Some(60),
            ..SegFlags::default()
        },
    });
    day.segments.sort_by_key(|s| s.start);
    let (_, body) = emit::render_plan_section(&day, &tree, &cfg, at(10, 42));
    let row = body
        .lines()
        .find(|l| l.starts_with("16:00"))
        .expect("the batch row");
    // §7.5's `batch: package · insurance · bank (3)`, with the items' own
    // titles.
    // `p` is the first member's — the key the batch was assigned at (§7.5).
    assert_eq!(row, "16:00  2 p0   batch: Pick up package · I…       1b");
    let wide = emit::render_plan_section_with(&day, &tree, &cfg, at(10, 42), &Layout::new(90)).1;
    let row = wide
        .lines()
        .find(|l| l.starts_with("16:00"))
        .expect("the batch row");
    assert!(row.contains(
        "batch: Pick up package · Insurance claim for the bike · \
         Call the bank about the card (3)"
    ));
    insta::assert_snapshot!("day_section_batch", body);
}

#[test]
fn the_day_file_links_its_svg() {
    assert_eq!(emit::svg_link(date()), "![day](2026-09-07.svg)");
    assert_eq!(emit::svg_file_name(date()), "2026-09-07.svg");
}
