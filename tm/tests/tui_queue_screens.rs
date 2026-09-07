//! §17 M6/M7: `TestBackend` snapshots of Screens 2, 3 and 5 at 120 and 90
//! columns, drawn from a hand-built `App` state over the `plan-basic` fixture
//! (Monday 2026-09-07 10:42).
//!
//! 120 columns is §12's "layout ≥ 110 columns as drawn"; 90 is below
//! `tui.min_width`, where the panes stack.

mod tui_queue_common;

use tui_queue_common::{draw, inbox, necessities, queue, world};

// ---------------------------------------------------------------------------
// Screen 2 — Queue (§12.2)
// ---------------------------------------------------------------------------

#[test]
fn queue_120() {
    let w = world();
    let state = queue::QueueState::new();
    let out = draw(120, 20, |f, a| queue::render(&state, &w.view(), f, a));
    insta::assert_snapshot!("queue_120", out);
}

#[test]
fn queue_90() {
    let w = world();
    let state = queue::QueueState::new();
    let out = draw(90, 24, |f, a| queue::render(&state, &w.view(), f, a));
    insta::assert_snapshot!("queue_90", out);
}

#[test]
fn queue_120_drilled_into_m2() {
    let w = world();
    let view = w.view();
    let mut state = queue::QueueState::new();
    // Move to ^m2 (the second week line) and drill: §12.2's `Tasks @m2`.
    state.week_sel = 1;
    let action = queue::on_key(&mut state, &view, tui_queue_common::special(
        crossterm::event::KeyCode::Enter,
    ));
    assert_eq!(action, queue::Action::Redraw);
    assert_eq!(state.pane, queue::Pane::Tasks);
    let out = draw(120, 20, |f, a| queue::render(&state, &view, f, a));
    insta::assert_snapshot!("queue_120_tasks_m2", out);
}

#[test]
fn queue_row_columns() {
    let w = world();
    let view = w.view();
    let rows = queue::week_rows(&view);
    let table: Vec<String> = rows
        .iter()
        .map(|r| {
            format!(
                "{:<3} p{} ci{} {:<4} {:<28} {:<4} {:<10} {:<8} {:<10} {}",
                r.id.as_str(),
                r.p.map(|p| p.to_string()).unwrap_or("-".into()),
                r.ci,
                r.est,
                r.title,
                r.parent,
                r.due,
                r.u,
                r.fits,
                if r.done { "done" } else { &r.bar }
            )
        })
        .collect();
    insta::assert_snapshot!("queue_week_rows", table.join("\n"));

    let months: Vec<String> = queue::month_rows(&view)
        .iter()
        .map(|r| {
            format!(
                "{:<3} {:<3} {:<45} {:<4} {}{}",
                r.id.as_str(),
                r.priority.map(|k| format!("!{k}")).unwrap_or("-".into()),
                r.title,
                r.bar,
                if r.demoted { "demoted " } else { "" },
                r.stamps
            )
        })
        .collect();
    insta::assert_snapshot!("queue_month_rows", months.join("\n"));

    let m2 = tm_core::model::Id::new("m2");
    let tasks = queue::task_rows(&view, Some(&m2));
    let task_table: Vec<String> = tasks
        .iter()
        .map(|r| {
            format!(
                "{:<3} p{} ci{} {:<4} {:<30} {}",
                r.id.as_str(),
                r.p.map(|p| p.to_string()).unwrap_or("-".into()),
                r.ci,
                r.est,
                r.title,
                r.blocked.clone().unwrap_or_default()
            )
        })
        .collect();
    insta::assert_snapshot!("queue_task_rows_m2", task_table.join("\n"));
    insta::assert_snapshot!("queue_fits_footer_m2", queue::fits_footer(&view, &tasks));
}

#[test]
fn queue_progress_bars_and_done_marks() {
    // §12.2's `▓▓▓░░░` and `✓` need a log and a finished line, which the
    // fixture (deliberately) has neither of: work the fixture into a temp copy.
    let tmp = tempfile::TempDir::new().expect("temp dir");
    let root = tmp.path().join("plan");
    copy_dir(
        std::path::Path::new(&tui_queue_common::fixture("plan-basic")),
        &root,
    );
    let week = root.join("week/2026-W37.md");
    let text = std::fs::read_to_string(&week)
        .expect("week")
        .replace("- [ ] 5 3b Read ch.6 ", "- [x] 5 3b Read ch.6 ");
    std::fs::write(&week, text).expect("write");

    let log = [
        // ^t3 is a child of ^m1 (6b): three of its six blocks are done.
        tui_queue_common::done("t3", 4, 180, "2026-09-06T10:00:00-05:00"),
        // ^t4 is a child of ^m2 (6b): one block.
        tui_queue_common::done("t4", 3, 60, "2026-09-07T09:00:00-05:00"),
    ];
    let w = tui_queue_common::world_with_log(&root.to_string_lossy(), &log);
    let view = w.view();
    let rows: Vec<String> = queue::week_rows(&view)
        .iter()
        .map(|r| {
            format!(
                "{:<3} {:<28} {}",
                r.id.as_str(),
                r.title,
                if r.done { "✓".to_string() } else { r.bar.clone() }
            )
        })
        .collect();
    insta::assert_snapshot!("queue_week_progress", rows.join("\n"));

    let state = queue::QueueState::new();
    let out = draw(120, 16, |f, a| queue::render(&state, &view, f, a));
    insta::assert_snapshot!("queue_120_progress", out);
}

#[test]
fn hysteresis_is_marked_and_explained() {
    // §7.4: `p` may improve by at most one bin a day. Yesterday ^d1 sat at 7;
    // today's EDF pass wants 4, so it is held at 6 and the row says so.
    let mut yesterday = std::collections::BTreeMap::new();
    yesterday.insert(tm_core::model::Id::new("d1"), 7u8);
    let w = tui_queue_common::world_with_yesterday(
        &tui_queue_common::fixture("plan-basic"),
        &yesterday,
    );
    let view = w.view();
    let rows = queue::week_rows(&view);
    let d1 = rows.iter().find(|r| r.id.as_str() == "d1").expect("d1");
    assert!(d1.hysteresis, "d1 should be held by hysteresis");
    assert_eq!(d1.p, Some(6));

    let state = queue::QueueState::new();
    let out = draw(120, 16, |f, a| queue::render(&state, &view, f, a));
    assert!(
        out.contains("p6*"),
        "the held row is marked with `*`:\n{out}"
    );
    assert!(
        out.contains("held by hysteresis"),
        "the pane footnote explains the mark:\n{out}"
    );
    insta::assert_snapshot!("queue_120_hysteresis", out);
}

/// Copy a directory tree (the fixtures are read-only).
fn copy_dir(from: &std::path::Path, to: &std::path::Path) {
    std::fs::create_dir_all(to).expect("create dir");
    for entry in std::fs::read_dir(from).expect("read fixture") {
        let entry = entry.expect("dir entry");
        let target = to.join(entry.file_name());
        if entry.file_type().expect("file type").is_dir() {
            copy_dir(&entry.path(), &target);
        } else {
            std::fs::copy(entry.path(), &target).expect("copy file");
        }
    }
}

// ---------------------------------------------------------------------------
// Screen 3 — Necessities (§12.3)
// ---------------------------------------------------------------------------

#[test]
fn necessities_120() {
    let w = world();
    let state = necessities::NecessitiesState::new();
    let out = draw(120, 24, |f, a| {
        necessities::render(&state, &w.view(), f, a)
    });
    insta::assert_snapshot!("necessities_120", out);
}

#[test]
fn necessities_90() {
    let w = world();
    let state = necessities::NecessitiesState::new();
    let out = draw(90, 28, |f, a| {
        necessities::render(&state, &w.view(), f, a)
    });
    insta::assert_snapshot!("necessities_90", out);
}

#[test]
fn necessities_rows_and_grid() {
    let w = world();
    let view = w.view();
    let rows: Vec<String> = necessities::rows(&view)
        .iter()
        .map(|r| {
            format!(
                "{:<11} {:<3} {:<38} p{} need {:<6} cap {:<6} {:<8} {}",
                format!("{:?}", r.section),
                r.id.as_str(),
                r.title,
                r.p.map(|p| p.to_string()).unwrap_or("-".into()),
                r.need,
                r.capacity,
                r.u,
                r.detail
            )
        })
        .collect();
    insta::assert_snapshot!("necessities_rows", rows.join("\n"));

    let g = necessities::grid(&view);
    let mut lines = vec![format!(
        "     {}",
        g.days
            .iter()
            .map(|d| d.format("%a").to_string())
            .collect::<Vec<_>>()
            .join(" ")
    )];
    for (i, row) in g.cells.iter().enumerate() {
        lines.push(format!(
            "{:02}   {}",
            necessities::FIRST_HOUR + i as u32,
            row.iter()
                .map(|c| match c {
                    necessities::Cell::Free => ".",
                    necessities::Cell::Window => "w",
                    necessities::Cell::Wall => "W",
                    necessities::Cell::Conflict => "X",
                })
                .collect::<Vec<_>>()
                .join("   ")
        ));
    }
    insta::assert_snapshot!("necessities_grid", lines.join("\n"));
}

#[test]
fn necessities_impossible_first() {
    // `plan-conflicts` carries `^i1`: 40b due tomorrow (§17.1's "impossible
    // deadline"), which §7.3 must report with its shortfall.
    let w = tui_queue_common::world_from(&tui_queue_common::fixture("plan-conflicts"));
    let view = w.view();
    let rows = necessities::rows(&view);
    assert_eq!(
        rows[0].section,
        necessities::Section::Impossible,
        "IMPOSSIBLE comes first (§12.3)"
    );
    assert_eq!(rows[0].id.as_str(), "i1");
    assert!(rows[0].detail.starts_with("needs "), "{}", rows[0].detail);

    let table: Vec<String> = rows
        .iter()
        .filter(|r| r.section != necessities::Section::Necessary)
        .map(|r| {
            format!(
                "{:<11} {:<3} {:<40} need {:<7} cap {:<7} {:<8} {}",
                format!("{:?}", r.section),
                r.id.as_str(),
                r.title,
                r.need,
                r.capacity,
                r.u,
                r.detail
            )
        })
        .collect();
    insta::assert_snapshot!("necessities_conflicts_rows", table.join("\n"));

    let state = necessities::NecessitiesState::new();
    let out = draw(120, 24, |f, a| necessities::render(&state, &view, f, a));
    insta::assert_snapshot!("necessities_120_conflicts", out);
}

#[test]
fn waiting_monitor_shows_days_and_timeout() {
    // §11's Waiting monitor: "items in `[?]` with days waiting and timeout",
    // on the Necessities screen. ^a4 is `on-event:reply/7d waiting:2026-09-05`
    // and today is 2026-09-07.
    let w = world();
    let view = w.view();
    let row = necessities::rows(&view)
        .into_iter()
        .find(|r| r.section == necessities::Section::Waiting)
        .expect("a waiting row");
    assert_eq!(row.id.as_str(), "a4");
    assert_eq!(row.detail, "2d / 7d");
    assert_eq!(row.event.as_deref(), Some("reply"));

    // Once `tm event reply` is logged the row says so, and `t` is what wrote
    // it (§5.1: the wait ends, the line goes back to `[ ]`).
    let log = [tui_queue_common::named_event(
        "reply",
        Some("a4"),
        "2026-09-07T08:00:00-05:00",
    )];
    let w2 = tui_queue_common::world_with_log(&tui_queue_common::fixture("plan-basic"), &log);
    let view2 = w2.view();
    let row2 = necessities::rows(&view2)
        .into_iter()
        .find(|r| r.section == necessities::Section::Waiting)
        .expect("a waiting row");
    assert_eq!(row2.detail, "2d / 7d · arrived");
}

#[test]
fn conflicting_walls_are_red() {
    // `plan-conflicts` exists for exactly this (§17.1: "overlapping walls").
    let w = tui_queue_common::world_from(&tui_queue_common::fixture("plan-conflicts"));
    let view = w.view();
    let g = necessities::grid(&view);
    assert!(
        !g.conflicts.is_empty(),
        "plan-conflicts should have overlapping walls"
    );
    assert!(
        g.cells
            .iter()
            .any(|row| row.iter().any(|c| *c == necessities::Cell::Conflict)),
        "the overlap should paint a Conflict cell"
    );
    assert_eq!(
        necessities::Cell::Conflict.style().fg,
        Some(ratatui::style::Color::Red)
    );
}

// ---------------------------------------------------------------------------
// Screen 5 — Inbox and capture (§12.5)
// ---------------------------------------------------------------------------

#[test]
fn inbox_120() {
    let w = world();
    let mut state = inbox::CaptureState::new();
    state.editing = true;
    state.buffer = "pset2 fri 6b ci4 max 2b/d".to_string();
    let out = draw(120, 16, |f, a| inbox::render(&state, &w.view(), f, a));
    insta::assert_snapshot!("inbox_120", out);
}

#[test]
fn inbox_90() {
    let w = world();
    let state = inbox::CaptureState::new();
    let out = draw(90, 16, |f, a| inbox::render(&state, &w.view(), f, a));
    insta::assert_snapshot!("inbox_90", out);
}

#[test]
fn inbox_list_previews() {
    let w = world();
    let view = w.view();
    let lines: Vec<String> = inbox::inbox_lines(&view)
        .iter()
        .map(|l| {
            format!(
                "{:>3}  {:<45} {}",
                l.line,
                l.raw,
                l.problem.clone().unwrap_or_else(|| l.parsed.clone())
            )
        })
        .collect();
    insta::assert_snapshot!("inbox_lines", lines.join("\n"));
}
