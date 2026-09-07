//! §4.3: the generated `<!-- tm:plan … -->` section of the day file.
//!
//! The plan is the §4.3 example, hand-built in `emit_fixture` (the planner is
//! still a stub). The snapshot is the whole block; four rows are additionally
//! asserted byte for byte against the spec's own text.
//!
//! The spec's example is hand-aligned and cannot be reproduced by any single
//! rule — it starts the title at column 14 on rows with a mark (`✓ Read ch.6
//! §1–2`) and at column 15 on rows without one, and it slides the estimate
//! into the empty `@parent` column on the three rows that have no parent. This
//! renderer keeps every column at a fixed offset, counted in *terminal*
//! columns, so:
//!
//! * rows whose mark is blank start the title one column earlier than the
//!   example — including the `⏰` and `🌙` rows, whose glyph is two columns
//!   wide, so the example's `⏰` + six spaces is 15 display columns just like
//!   its `·` + seven spaces;
//! * `⏰ Meeting w/ host  1h`, `⚠ Pick up package  20m` and `○ Severance S3E4
//!   1h` keep their estimate in the estimate column (48) instead of sliding it
//!   to 43;
//! * the `09:00` break's `(24m)` sits in the actual column (52), where the
//!   example puts it at 48.
//!
//! `M4`'s definition of done asks for three fixture days; the §4.3 day is the
//! early start, and `emit_fixture::late_start_plan` / `home_day_plan` are the
//! other two.
//!
//! Everything else — the mark set, the `4↓p3` cell, `2b×1.6`, the note column
//! at 55, `@parent` at 43, the estimate at 48 and the `───  window ends 16:00`
//! divider — is the example's.

mod emit_fixture;

use emit_fixture::{at, config, date, plan, tree};
use tm_core::emit::{self, Layout};

/// The *terminal* column a substring starts at (`str::find` counts bytes,
/// these rows are full of `§`, `–` and `✓`, and `⏰`/`🌙` are two columns wide).
fn col(line: &str, needle: &str) -> Option<usize> {
    line.find(needle)
        .map(|b| tm_core::emit::display_width(&line[..b]))
}

/// The three §4.3 rows a fixed-column renderer reproduces exactly.
///
/// The `⏰`/`🌙` rows cannot join them: the example pads those glyphs as if
/// they were one column wide, which puts their titles at display column 15 —
/// the same place its unmarked `·` rows put theirs, and one column right of
/// its own marked rows. A single fixed grid has to pick one, and it picks 14.
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

    // Every row starts its title at the same *display* column, wide glyphs
    // included (`⏰` and `🌙` are two terminal columns, not one).
    assert_eq!(col(lines[6], "Meeting"), Some(14), "the ⏰ row");
    assert_eq!(col(lines[13], "wind-down"), Some(14), "the 🌙 row");
    assert_eq!(col(lines[12], "Severance"), Some(14), "the ○ row");
    assert_eq!(col(lines[4], "lunch"), Some(14), "the · row");

    insta::assert_snapshot!("day_section", body);
}

#[test]
fn wide_glyphs_do_not_widen_their_row() {
    // Regression: `pad`/`truncate` counted characters, so `⏰` (U+23F0) and
    // `🌙` (U+1F319) — both East-Asian Wide — pushed everything after them one
    // terminal column right, and the fixed grid the module promises went
    // ragged on exactly those two rows.
    assert_eq!(emit::display_width("⏰"), 2, "U+23F0 is two columns");
    assert_eq!(emit::display_width("🌙"), 2, "U+1F319 is two columns");
    assert_eq!(emit::display_width("·"), 1);
    assert_eq!(emit::display_width("読書"), 4, "and so is a CJK title");
    // A spread across the width table, so a mis-sorted range (the lookup
    // binary-searches) shows up here rather than as a ragged row.
    for c in "⌚⏳ㄱ㐀一가豈！⭐🀄🈁🚀🪐𠀀".chars() {
        assert_eq!(emit::char_width(c), 2, "{c:?} (U+{:04X}) is wide", c as u32);
    }
    // East-Asian *Ambiguous* code points (`★`, `✓`, `▶`, …) are one column in
    // a Latin terminal, which is where these files are read.
    for c in "·✓▶⚠○↓─…§–×★abc0 ".chars() {
        assert_eq!(emit::char_width(c), 1, "{c:?} (U+{:04X}) is narrow", c as u32);
    }
    assert_eq!(emit::char_width('\u{fe0f}'), 0, "a variation selector");
    assert_eq!(emit::char_width('\u{0301}'), 0, "a combining acute");

    let cfg = config();
    let tree = tree(&cfg);
    let day = plan();
    let (_, body) = emit::render_plan_section(&day, &tree, &cfg, at(10, 42));
    // Every row's title — the first non-blank run after the mark column —
    // starts at display column 14, whatever glyph the `ci` column holds.
    for line in body.lines().filter(|l| !l.contains("window ends")) {
        let title_at = line
            .char_indices()
            .find(|(b, c)| !c.is_whitespace() && emit::display_width(&line[..*b]) >= 13)
            .map(|(b, _)| emit::display_width(&line[..b]));
        assert_eq!(title_at, Some(14), "title column of {line:?}");
    }
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
    // titles. `p` is the first member's — the key the batch was assigned at.
    // Regression: plain truncation cut the row down to
    // `batch: Pick up package · I…`, losing every member after the first and
    // the `(3)`; the frame is kept and the *members* are shortened instead.
    assert_eq!(row, "16:00  2 p0   batch: Pic… · In… · Ca… (3)       1b");
    assert!(row.contains("(3)"), "the count always survives");
    // A width that fits more shows more of each member, never a longer row.
    for w in 12..90 {
        let out = emit::render_plan_section_with(&day, &tree, &cfg, at(10, 42), &Layout::new(w)).1;
        let row = out
            .lines()
            .find(|l| l.starts_with("16:00"))
            .expect("the batch row");
        let title = &row[row.find("batch:").expect("batch:")..];
        let title = title.split("  ").next().expect("the title cell");
        assert!(
            emit::display_width(title) <= w,
            "batch title {title:?} overflows the {w}-column title cell"
        );
        assert!(title.starts_with("batch: "), "the frame survives: {title:?}");
    }
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
fn the_notes_are_derived_when_the_planner_writes_none() {
    // Regression: emit printed `flags.note` verbatim and derived nothing, so a
    // planner that sets only `flags.underused` / `flags.hot` produced a `↓` or
    // `⚠` row with an empty note column. The plan carries what both notes need
    // (`diagnostics.underused` is the exact `(t4, 4, 3)` triple; the tree
    // carries `^a3`'s window).
    let cfg = config();
    let tree = tree(&cfg);
    let mut day = plan();
    for seg in &mut day.segments {
        seg.flags.note = None;
    }
    let (_, body) = emit::render_plan_section(&day, &tree, &cfg, at(10, 42));
    let lines: Vec<&str> = body.lines().collect();
    assert!(lines[5].ends_with("↓ slot 4, item 3"), "{}", lines[5]);
    assert!(lines[10].ends_with("due today"), "{}", lines[10]);
    assert_eq!(body, emit::render_plan_section(&plan(), &tree, &cfg, at(10, 42)).1);

    // Without a diagnostics entry the note falls back to the segment's own
    // slot energy and the item's `ci`.
    day.diagnostics.underused.clear();
    let (_, body) = emit::render_plan_section(&day, &tree, &cfg, at(10, 42));
    assert!(
        body.lines().nth(5).expect("row").ends_with("↓ slot 4, item 3"),
        "slot energy 4, `^t4` is ci 3"
    );

    // A written note always wins.
    let mut day = plan();
    day.segments[5].flags.note = Some("mine".to_string());
    let (_, body) = emit::render_plan_section(&day, &tree, &cfg, at(10, 42));
    assert!(body.lines().nth(5).expect("row").ends_with("mine"));

    // A deadline that is not today reads as the day it falls on.
    let mut day = plan();
    day.date = date().pred_opt().expect("2026-09-06");
    day.segments[9].flags.note = None; // `^a3`, the `⚠` row

    let (_, body) = emit::render_plan_section(&day, &tree, &cfg, at(10, 42));
    assert!(
        body.lines().nth(10).expect("row").ends_with("due tomorrow"),
        "^a3's window closes 2026-09-07"
    );
}

#[test]
fn a_late_start_with_a_wall_renders() {
    // M4's second fixture day: the window opens at 10:30, after the dentist,
    // and the 3-block budget runs out at 16:30 — mid-window, not at its edge.
    let cfg = config();
    let tree = tree(&cfg);
    let day = emit_fixture::late_start_plan();
    let (info, body) = emit::render_plan_section(&day, &tree, &cfg, at(10, 42));
    assert_eq!(info, "10:42");
    let lines: Vec<&str> = body.lines().collect();
    assert!(lines[0].starts_with("09:00  ⏰"), "the wall comes first");
    assert!(lines[1].starts_with("10:20  ·"), "then the leak");
    assert!(lines[2].starts_with("10:30"), "and only then the window");
    let divider = lines
        .iter()
        .position(|l| l.contains("window ends"))
        .expect("divider");
    assert_eq!(lines[divider], "16:30  ───    window ends 18:30");
    assert!(lines[divider + 1].starts_with("16:30"), "^a3 follows it");
    // Both marks derive their note.
    assert!(lines[7].ends_with("↓ slot 5, item 3"), "{}", lines[7]);
    assert!(lines[divider + 1].ends_with("due today"));
    insta::assert_snapshot!("day_section_late_start", body);
}

#[test]
fn a_home_day_renders() {
    // M4's third fixture day: `home_max_ci = 3` caps every slot, so the `ci`
    // column reads 3 even for `^t1` (ci 5). It also carries the batch row and
    // the sleep routine.
    let cfg = config();
    let tree = tree(&cfg);
    let day = emit_fixture::home_day_plan();
    let (_, body) = emit::render_plan_section(&day, &tree, &cfg, at(10, 42));
    let lines: Vec<&str> = body.lines().collect();
    assert!(lines[0].starts_with("08:00  3 p3"), "{}", lines[0]);
    assert!(
        lines.iter().all(|l| !l.contains(" 5 p") && !l.contains(" 4 p")),
        "no slot above the home cap of 3"
    );
    let batch = lines.iter().find(|l| l.starts_with("12:00")).expect("batch");
    assert!(batch.contains("batch:") && batch.contains("(2)"), "{batch}");
    // Regression: a `Sleep` segment used to render as `routine 8h30m`.
    let sleep = lines.last().expect("the sleep row");
    assert!(sleep.starts_with("22:00  ·"), "{sleep}");
    assert!(sleep.contains("sleep 8h30m"), "{sleep}");
    insta::assert_snapshot!("day_section_home_day", body);
}

#[test]
fn a_sleep_segment_with_no_item_still_says_sleep() {
    // Regression: `SegKind::Routine | SegKind::Sleep` shared one `routine`
    // fallback, so the timeline said `routine 1h` where the day bar's tooltip
    // said `sleep · 1h`.
    use tm_core::planner::{DayPlan, SegFlags, SegKind, Segment};

    let cfg = config();
    let tree = tree(&cfg);
    let mut day = DayPlan::empty(date(), (at(7, 0), at(16, 0)), 6);
    day.segments = vec![Segment {
        start: at(22, 0),
        end: at(23, 0),
        kind: SegKind::Sleep,
        energy: None,
        item: None,
        instance: None,
        flags: SegFlags::default(),
    }];
    let (_, body) = emit::render_plan_section(&day, &tree, &cfg, at(10, 42));
    assert_eq!(body.lines().last(), Some("22:00  ·      sleep 1h"));
    let bar = emit::daybar_cells(&day, None, &tree, &cfg, 96, at(6, 5), at(22, 30));
    assert_eq!(bar.cells[bar.cursor_col].tooltip, "sleep · 1h");
}

#[test]
fn the_day_file_links_its_svg() {
    assert_eq!(emit::svg_link(date()), "![day](2026-09-07.svg)");
    assert_eq!(emit::svg_file_name(date()), "2026-09-07.svg");
}
