//! §12.1: the day-bar geometry the terminal widget and the SVG share.
//!
//! One row of `cols` cells over 24 h from wake to wake, the cursor at `now`,
//! the arrival plan as a ghost row, and the colour rules (project hue by
//! FNV-1a of the root id, brightness = `ci`).

mod emit_fixture;

use chrono::Duration;
use chrono_tz::Tz;
use emit_fixture::{at, config, ghost_plan, plan, tree, TZ};
use tm_core::capacity::local_dt;
use tm_core::emit::{self, Cell, CellStyle, DayBar};
use tm_core::model::Id;
use tm_core::planner::DayPlan;

/// One character per cell: the brightness digit for work, a letter otherwise.
fn ascii(cells: &[Cell]) -> String {
    cells
        .iter()
        .map(|c| match c.style {
            CellStyle::Work => char::from_digit(u32::from(c.brightness), 10).unwrap_or('?'),
            CellStyle::Routine => 'r',
            CellStyle::Break => 'b',
            CellStyle::Lost => 'L',
            CellStyle::Interrupt => 'I',
            CellStyle::Optional => 'o',
            CellStyle::Wall => 'w',
            CellStyle::Rest => '.',
            CellStyle::Sleep => 'z',
            CellStyle::Empty => ' ',
        })
        .collect()
}

fn bar_at_10_42(ghost: Option<&DayPlan>) -> (DayBar, DayPlan) {
    let cfg = config();
    let tree = tree(&cfg);
    let day = plan();
    let bar = emit::daybar_cells(&day, ghost, &tree, &cfg, 96, at(6, 5), at(10, 42));
    (bar, day)
}

#[test]
fn ninety_six_columns_are_fifteen_minute_cells() {
    let (bar, _) = bar_at_10_42(None);
    assert_eq!(bar.cols, 96);
    assert_eq!(bar.span_min, 24 * 60);
    assert!((bar.cell_minutes() - 15.0).abs() < f64::EPSILON);
    assert_eq!(bar.cells.len(), 96);
    // Column 0 starts at wake; the last one ends 24 h later.
    assert_eq!(bar.start_of(0), at(6, 5));
    assert_eq!(bar.start_of(95), at(6, 5) + Duration::minutes(1425));
}

#[test]
fn the_cursor_sits_in_the_cell_that_holds_now() {
    let (bar, _) = bar_at_10_42(None);
    // 10:42 − 06:05 = 277 min = cell 18 (10:35–10:50).
    assert_eq!(bar.cursor_col, 18);
    assert_eq!(bar.col_of(at(10, 42)), Some(18));
    assert_eq!(bar.start_of(18), at(10, 35));
    // Before wake and past the 24 h span there is no column.
    assert_eq!(bar.col_of(at(6, 0)), None);
    assert_eq!(bar.col_of(at(6, 5) + Duration::hours(24)), None);
    // The cursor's own cell is the current block.
    let cell = &bar.cells[18];
    assert_eq!(cell.style, CellStyle::Work);
    assert!(cell.tooltip.starts_with("Exercises 5.3–5.5 · 2h · ci4 · p1 · @O1"));
}

#[test]
fn cells_follow_the_segments() {
    let (bar, day) = bar_at_10_42(None);
    insta::assert_snapshot!("daybar_96", ascii(&bar.cells));

    // Wake to the first block is empty; the first block is `ci` 5 work.
    assert_eq!(bar.cells[0].style, CellStyle::Empty);
    assert_eq!(bar.cells[0].segment, None);
    let first = bar.col_of(at(7, 30)).expect("07:30");
    assert_eq!(bar.cells[first].style, CellStyle::Work);
    assert_eq!(bar.cells[first].brightness, 5);
    assert_eq!(bar.cells[first].segment, Some(0));
    // The wall, the optional and the wind-down keep their own styles.
    assert_eq!(
        bar.cells[bar.col_of(at(13, 0)).expect("13:00")].style,
        CellStyle::Wall
    );
    assert_eq!(
        bar.cells[bar.col_of(at(18, 30)).expect("18:30")].style,
        CellStyle::Optional
    );
    assert_eq!(
        bar.cells[bar.col_of(at(21, 45)).expect("21:45")].style,
        CellStyle::Sleep
    );
    // Every cell that has a segment points at a real one.
    for cell in &bar.cells {
        if let Some(i) = cell.segment {
            assert!(i < day.segments.len());
        }
    }
}

#[test]
fn the_ghost_row_is_empty_without_a_ghost_plan() {
    let (bar, _) = bar_at_10_42(None);
    assert!(bar.ghost.is_empty());

    let ghost = ghost_plan();
    let (with, _) = bar_at_10_42(Some(&ghost));
    assert_eq!(with.ghost.len(), 96);
    assert_eq!(with.cells, bar.cells, "the plan row is unaffected");
    // The arrival plan had `^t5` at 13:50, where the day now has a break.
    assert_eq!(
        with.ghost[with.col_of(at(14, 0)).expect("14:00")].style,
        CellStyle::Work
    );
    assert_eq!(
        with.cells[with.col_of(at(14, 0)).expect("14:00")].style,
        CellStyle::Break
    );
    insta::assert_snapshot!("daybar_96_ghost", ascii(&with.ghost));
}

#[test]
fn the_left_half_is_the_log_and_the_right_half_the_plan() {
    // A finished block and a planned one over the same minutes: left of the
    // cursor the finished one wins, right of it the planned one does.
    let cfg = config();
    let tree = tree(&cfg);
    let mut day = plan();
    let mut planned = day.segments[0].clone();
    planned.flags.done = false;
    planned.item = Some(Id::new("t5"));
    planned.energy = Some(3);
    day.segments.insert(1, planned);
    let bar = emit::daybar_cells(&day, None, &tree, &cfg, 96, at(6, 5), at(10, 42));
    let col = bar.col_of(at(7, 30)).expect("07:30");
    assert_eq!(bar.cells[col].segment, Some(0), "the logged block");
    assert_eq!(bar.cells[col].brightness, 5);

    // The same pair in the afternoon (right of the cursor) picks the plan.
    let mut day = plan();
    let mut logged = day.segments[8].clone();
    logged.flags.done = true;
    day.segments.insert(8, logged);
    let bar = emit::daybar_cells(&day, None, &tree, &cfg, 96, at(6, 5), at(10, 42));
    let col = bar.col_of(at(14, 30)).expect("14:30");
    assert_eq!(bar.cells[col].segment, Some(9), "the planned block");
}

#[test]
fn hues_come_from_the_root_id_and_brightness_from_ci() {
    let cfg = config();
    let (bar, _) = bar_at_10_42(None);
    let t1 = &bar.cells[bar.col_of(at(7, 30)).expect("07:30")];
    let t3 = &bar.cells[bar.col_of(at(10, 0)).expect("10:00")];
    // `^t1` and `^t3` hang off different month outcomes (O1 vs O1 through m1
    // and m3): both roots are `O1`, so both cells share the hue.
    assert_eq!(t1.hue, Some(emit::hue_index(&Id::new("O1"), 12)));
    assert_eq!(t1.hue, t3.hue);
    assert_eq!(t1.brightness, 5);
    assert_eq!(t3.brightness, 4);

    // Brightness scales the palette colour: 5 is the colour itself, 0 black.
    let full = emit::palette_rgb(&cfg, t1.hue.expect("hue"));
    assert_eq!(t1.rgb(&cfg), full);
    let mut dark = t1.clone();
    dark.brightness = 0;
    assert_eq!(dark.rgb(&cfg), (0, 0, 0));
    let mut half = t1.clone();
    half.brightness = 3;
    let (r, g, b) = half.rgb(&cfg);
    assert_eq!(
        (r, g, b),
        (
            (f64::from(full.0) * 0.6).round() as u8,
            (f64::from(full.1) * 0.6).round() as u8,
            (f64::from(full.2) * 0.6).round() as u8
        )
    );

    // Non-work styles have fixed colours (§12.1: routines grey, breaks light
    // grey, walls dark).
    let wall = &bar.cells[bar.col_of(at(13, 0)).expect("13:00")];
    assert_eq!(wall.rgb(&cfg), CellStyle::Wall.colour());
}

#[test]
fn hue_index_is_stable_fnv1a_over_the_palette() {
    // The same id always lands on the same colour, ids spread over 12.
    let ids = ["O1", "O2", "O3", "m1", "t3", "a3", "g1"];
    let hues: Vec<usize> = ids
        .iter()
        .map(|s| emit::hue_index(&Id::new(*s), 12))
        .collect();
    assert!(hues.iter().all(|h| *h < 12));
    assert_eq!(hues, ids.iter().map(|s| emit::hue_index(&Id::new(*s), 12)).collect::<Vec<_>>());
    insta::assert_snapshot!(
        "daybar_hues",
        ids.iter()
            .zip(&hues)
            .map(|(i, h)| format!("{i} -> {h}"))
            .collect::<Vec<_>>()
            .join("\n")
    );
    // An empty palette never panics.
    assert_eq!(emit::hue_index(&Id::new("O1"), 0), 0);
}

#[test]
fn col_of_inverts_start_of_for_every_width() {
    // Regression: `start_of` rounded its boundary to whole seconds (as
    // `cells_of` does) while `col_of` divided the unrounded minutes, so on any
    // width that does not divide 1440 the two disagreed — at `cols = 110`, the
    // config's `min_width`, on half of the columns. The TUI maps a hover `x`
    // to a column with `col_of` and paints it from `start_of`, so those
    // columns reported the neighbour's tooltip.
    let cfg = config();
    let tree = tree(&cfg);
    let day = plan();
    for cols in [1usize, 7, 13, 48, 90, 96, 110, 120, 137, 200, 1440] {
        let bar = emit::daybar_cells(&day, None, &tree, &cfg, cols, at(6, 5), at(10, 42));
        for c in 0..cols {
            let start = bar.start_of(c);
            assert_eq!(bar.col_of(start), Some(c), "cols {cols}, col {c} start");
            // The last instant of the cell belongs to it too.
            let last = bar.start_of(c + 1) - Duration::seconds(1);
            if last >= start {
                assert_eq!(bar.col_of(last), Some(c), "cols {cols}, col {c} end");
            }
        }
        // The cursor is the column `now` falls in, by the same rule.
        assert_eq!(bar.col_of(at(10, 42)), Some(bar.cursor_col), "cols {cols}");
        // Column boundaries march forwards and cover the whole 24 h.
        assert_eq!(bar.start_of(0), at(6, 5));
        assert_eq!((bar.start_of(cols) - at(6, 5)).num_minutes(), 1440);
    }
}

#[test]
fn every_segment_has_a_cell_of_its_own() {
    // §17.2's SVG draws one rect per segment from `bar.segments`, which every
    // segment has even when it wins no column.
    let cfg = config();
    let tree = tree(&cfg);
    let day = plan();
    let bar = emit::daybar_cells(&day, None, &tree, &cfg, 12, at(6, 5), at(10, 42));
    assert_eq!(bar.segments.len(), day.segments.len());
    for (i, cell) in bar.segments.iter().enumerate() {
        assert_eq!(cell.segment, Some(i));
        assert!(!cell.tooltip.is_empty(), "segment {i} has no tooltip");
    }
    // A cell that won a column carries exactly what that segment's own cell
    // does, so the SVG and the terminal never disagree.
    for cell in &bar.cells {
        if let Some(i) = cell.segment {
            assert_eq!(cell, &bar.segments[i]);
        }
    }
}

#[test]
fn the_bar_spans_twenty_four_real_hours_across_a_dst_change() {
    // 2026-11-01 is the fall-back day in America/Chicago: 25 wall-clock hours.
    let cfg = config();
    let tree = tree(&cfg);
    let wake = local_dt(
        TZ,
        chrono::NaiveDate::from_ymd_opt(2026, 10, 31).expect("date"),
        chrono::NaiveTime::from_hms_opt(23, 0, 0).expect("time"),
    );
    let day = DayPlan::empty(
        chrono::NaiveDate::from_ymd_opt(2026, 11, 1).expect("date"),
        (wake, wake + Duration::hours(8)),
        6,
    );
    let bar = emit::daybar_cells(&day, None, &tree, &cfg, 96, wake, wake + Duration::hours(5));
    assert_eq!((bar.start_of(95) - wake).num_minutes(), 1425);
    // 23:45 minus one wall-clock hour, because the day gained one.
    assert_eq!(bar.start_of(95).format("%H:%M").to_string(), "21:45");
    assert_eq!(bar.cursor_col, 20);
    assert_eq!(Tz::America__Chicago, TZ);
}
