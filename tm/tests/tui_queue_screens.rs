//! §17 M6/M7: `TestBackend` snapshots of Screens 2, 3 and 5 at 120 and 90
//! columns, drawn from a hand-built `App` state over the `plan-basic` fixture
//! (Monday 2026-09-07 10:42).
//!
//! 120 columns is §12's "layout ≥ 110 columns as drawn"; 90 is below
//! `tui.min_width`, where the panes stack.

mod cli_common;
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

    // §12.2: the Tasks pane lists the children of the *selection*. With no
    // selection there is nothing to list, the footer says `0b of 0b`, and the
    // pane title drops the `@<id>`.
    assert!(queue::task_rows(&view, None).is_empty());
    assert_eq!(queue::fits_footer(&view, &[]), "fits this week: 0b of 0b");
    let mut state = queue::QueueState::new();
    state.pane = queue::Pane::Tasks;
    state.anchor = queue::Pane::Week;
    state.week_sel = usize::MAX;
    assert_eq!(state.parent(&view), None);
    assert_eq!(state.selection(&view), None);
    assert_eq!(
        queue::on_key(&mut state, &view, tui_queue_common::key('J')),
        queue::Action::Note("nothing selected".to_string())
    );
    let out = draw(120, 10, |f, a| queue::render(&state, &view, f, a));
    assert!(out.contains(" Tasks "), "{out}");
    assert!(out.contains("fits this week: 0b of 0b"), "{out}");
}

/// §7.2: `allocation(item, period)` is `min(need, capacity)` from the EDF pass,
/// shown as "fits 6b of 6b". On `plan-basic` everything fits, so every column
/// reads `n/n` and an implementation that printed `remaining/remaining` would
/// look right. `plan-conflicts` has the case that tells them apart: `^i1` is
/// 40b due tomorrow, and only 6b of it fits before the deadline.
#[test]
fn the_fits_column_reports_the_allocation_not_the_remainder() {
    let w = tui_queue_common::world_from(&tui_queue_common::fixture("plan-conflicts"));
    let view = w.view();
    let rows = queue::week_rows(&view);

    let i1 = rows.iter().find(|r| r.id.as_str() == "i1").expect("i1");
    assert_eq!(i1.fits, "fits 6/40", "u={}", i1.u);
    assert_eq!(i1.u, "u=8.67", "40b × 1.3 over the 6b before tomorrow");

    // The `of` half is the §6.4 remainder, whatever the allocation was.
    assert_eq!(
        tm_core::priority::fmt_blocks(
            view.tree.remaining(&tm_core::model::Id::new("i1")).expect("remaining"),
            view.block_min()
        ),
        "40b"
    );

    // And a row whose need does fit still reads `n/n`.
    let x2 = rows.iter().find(|r| r.id.as_str() == "x2").expect("x2");
    assert_eq!(x2.fits, "fits 8/8");

    // The Tasks footer runs the same reservation over the rest of the week, so
    // O2's pile of children cannot all fit into it either.
    let o2 = tm_core::model::Id::new("O2");
    let tasks = queue::task_rows(&view, Some(&o2));
    let footer = queue::fits_footer(&view, &tasks);
    let (fits, total) = footer
        .trim_start_matches("fits this week: ")
        .split_once(" of ")
        .expect("`fits this week: A of B`");
    assert_ne!(
        fits, total,
        "O2's children must not all fit in one week: {footer}"
    );
    insta::assert_snapshot!("queue_fits_footer_o2_conflicts", footer);
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
    assert_eq!(
        (g.first_hour, g.last_hour),
        (necessities::FIRST_HOUR, necessities::LAST_HOUR),
        "plan-basic has no wall outside the default band"
    );
    for (i, row) in g.cells.iter().enumerate() {
        lines.push(format!(
            "{:02}   {}",
            g.first_hour + i as u32,
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

/// **The owner's D67 on the Necessities screen** (README gap 3522, the W-38
/// repair): an `IMPOSSIBLE` line whose item the day names in
/// `diagnostics.unplaced` ends with the same ` · not placed: <reason>` tail
/// `tm plan`'s banner and the Today pane print (`emit::unplaced_note_in`, one
/// definition), and an item the day does not name keeps its line unchanged.
#[test]
fn necessities_names_why_an_impossible_item_has_no_row() {
    use tm_core::dayplan::NoPlace;
    let w = tui_queue_common::world_from(&tui_queue_common::fixture("plan-conflicts"));
    let plain = necessities::rows(&w.view());
    let unplaced = [(tm_core::model::Id::new("i1"), NoPlace::NoRunLeft)];
    let named = necessities::rows(&w.view().with_unplaced(&unplaced));
    let i1 = |rows: &[necessities::Row]| {
        rows.iter()
            .find(|r| r.section == necessities::Section::Impossible && r.id.as_str() == "i1")
            .map(|r| r.detail.clone())
            .expect("i1 is IMPOSSIBLE")
    };
    assert_eq!(
        i1(&named),
        format!("{}{}", i1(&plain), tm_core::emit::unplaced_note_in(&unplaced, &tm_core::model::Id::new("i1"))),
        "the tail is the banner's"
    );
    assert!(i1(&named).ends_with(" · not placed: no run left"), "{}", i1(&named));
    assert!(!i1(&plain).contains("not placed"), "{}", i1(&plain));
    let others = |rows: &[necessities::Row]| rows.iter().filter(|r| r.id.as_str() != "i1").map(|r| r.detail.clone()).collect::<Vec<_>>();
    assert_eq!(others(&named), others(&plain), "an item the day does not name keeps its line");
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

/// §12.3's four groups are disjoint. An overdue `on-miss:persist` item used to
/// be listed twice — once in the dated list with a shortfall measured against a
/// deadline in the past, and again under "Necessary today".
#[test]
fn an_overdue_item_is_listed_once_and_never_as_impossible() {
    let tmp = tempfile::TempDir::new().expect("temp dir");
    let root = tmp.path().join("plan");
    copy_dir(
        std::path::Path::new(&tui_queue_common::fixture("plan-basic")),
        &root,
    );
    // ^d1's deadline moves three days into the past (§5.3: a Point defaults to
    // on_miss = persist, so it stays `[ ]` and goes overdue). A dated `[?]`
    // line goes in too: §5.1 gives it the Waiting list and nothing else.
    let week = root.join("week/2026-W37.md");
    let mut text = std::fs::read_to_string(&week)
        .expect("week")
        .replace("due:2026-09-11T23:59", "due:2026-09-04T23:59");
    text.push_str(
        "- [?] 3 1b Chase the reimbursement due:2026-09-10T23:59 waiting:2026-09-05 ^w9\n",
    );
    std::fs::write(&week, text).expect("write");

    let w = tui_queue_common::world_from(&root.to_string_lossy());
    let view = w.view();
    let rows = necessities::rows(&view);
    let d1: Vec<&necessities::Row> = rows.iter().filter(|r| r.id.as_str() == "d1").collect();
    assert_eq!(
        d1.len(),
        1,
        "d1 must appear once, got {:?}",
        rows.iter()
            .map(|r| (r.section, r.id.to_string(), r.detail.clone()))
            .collect::<Vec<_>>()
    );
    assert_eq!(d1[0].section, necessities::Section::Necessary);
    assert_eq!(d1[0].detail, "overdue since Sep 4");
    assert!(
        !rows
            .iter()
            .any(|r| r.section == necessities::Section::Impossible),
        "a past-due deadline is overdue, not IMPOSSIBLE (§7.3, priority.rs)"
    );
    // No row may name a capacity "available by" a date that has gone.
    assert!(
        !rows.iter().any(|r| r.detail.contains("available by Sep 4")),
        "a shortfall against a past deadline is not actionable"
    );

    // The dated `[?]` line is in the Waiting list and nowhere else (§5.1).
    let w9: Vec<&necessities::Row> = rows.iter().filter(|r| r.id.as_str() == "w9").collect();
    assert_eq!(w9.len(), 1, "{w9:?}");
    assert_eq!(w9[0].section, necessities::Section::Waiting);

    // Every id/instance pair is unique — the cursor and the pane scroll count
    // these rows.
    let mut keys: Vec<(String, Option<tm_core::model::InstanceKey>)> =
        rows.iter().map(|r| (r.id.to_string(), r.instance)).collect();
    let before = keys.len();
    keys.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| format!("{:?}", a.1).cmp(&format!("{:?}", b.1))));
    keys.dedup();
    assert_eq!(keys.len(), before, "duplicate rows: {keys:?}");
}

/// §12.3's red is `check.rs`'s `wall-conflict`: two walls that *overlap*, not
/// two that land in the same hour cell.
#[test]
fn walls_sharing_an_hour_without_overlapping_are_not_red() {
    let view = grid_world(&[
        "- [ ] 5 20m Standup at:2026-09-08T10:00/10:20 ^k1",
        "- [ ] 5 20m Sync at:2026-09-08T10:40/11:00 ^k2",
    ]);
    let view = view.view();
    let g = necessities::grid(&view);
    assert!(g.conflicts.is_empty(), "{:?}", g.conflicts);
    let tue = (10 - g.first_hour) as usize;
    assert_eq!(g.cells[tue][1], necessities::Cell::Wall);
    assert!(
        !g.cells
            .iter()
            .any(|row| row.iter().any(|c| *c == necessities::Cell::Conflict)),
        "no pair overlaps, so nothing is red"
    );

    // Overlap them and the shared span — and only it — turns red.
    let world = grid_world(&[
        "- [ ] 5 1h Standup at:2026-09-08T10:00/11:00 ^k1",
        "- [ ] 5 1h Sync at:2026-09-08T10:30/12:00 ^k2",
    ]);
    let view = world.view();
    let g = necessities::grid(&view);
    assert_eq!(g.conflicts.len(), 1);
    assert_eq!(g.cells[(10 - g.first_hour) as usize][1], necessities::Cell::Conflict);
    assert_eq!(g.cells[(11 - g.first_hour) as usize][1], necessities::Cell::Wall);
}

/// §12.3 is the screen that exists to show walls, so a wall at night is drawn:
/// the 06–24 band (which keeps the `sleep` window from filling the grid) grows
/// to hold it.
#[test]
fn a_night_wall_widens_the_grid_instead_of_vanishing() {
    let world = grid_world(&["- [ ] 5 2h Redeye at:2026-09-08T03:00/05:00 ^n1"]);
    let view = world.view();
    let g = necessities::grid(&view);
    assert_eq!(g.first_hour, 3);
    assert_eq!(g.last_hour, necessities::LAST_HOUR);
    assert_eq!(g.cells[0][1], necessities::Cell::Wall, "Tue 03:00");
    assert_eq!(g.cells[1][1], necessities::Cell::Wall, "Tue 04:00");
    assert_eq!(g.cells[2][1], necessities::Cell::Free, "the wall ends 05:00");
    // The night rows the wall opened stay clear of the `sleep` window.
    assert!(
        g.cells[0].iter().all(|c| *c != necessities::Cell::Window),
        "a routine window must not follow the grid into the night"
    );

    // An overnight wall shows both halves.
    let world = grid_world(&["- [ ] 5 8h Sleeper at:2026-09-09T22:00/2026-09-10T06:00 ^n2"]);
    let view = world.view();
    let g = necessities::grid(&view);
    assert_eq!(g.first_hour, 0);
    for h in 22..24 {
        assert_eq!(g.cells[(h - g.first_hour) as usize][2], necessities::Cell::Wall, "Wed {h}:00");
    }
    for h in 0..6 {
        assert_eq!(g.cells[(h - g.first_hour) as usize][3], necessities::Cell::Wall, "Thu {h}:00");
    }
}

/// A `plan-basic` copy with extra week lines, for the grid tests.
fn grid_world(extra: &[&str]) -> tui_queue_common::World {
    let tmp = tempfile::TempDir::new().expect("temp dir");
    let root = tmp.path().join("plan");
    copy_dir(
        std::path::Path::new(&tui_queue_common::fixture("plan-basic")),
        &root,
    );
    let week = root.join("week/2026-W37.md");
    let mut text = std::fs::read_to_string(&week).expect("week");
    for line in extra {
        text.push_str(line);
        text.push('\n');
    }
    std::fs::write(&week, text).expect("write");
    let world = tui_queue_common::world_from(&root.to_string_lossy());
    // The `World` outlives the TempDir, which is fine: everything is parsed.
    drop(tmp);
    world
}

/// §12: "below 110 columns, panes stack". Neither stacked half may drop a line
/// in silence — the old fixed 9-row split cut the grid at 11:00, hiding all
/// three of `plan-basic`'s meetings with nothing on screen to say so.
#[test]
fn the_stacked_panes_never_drop_a_line_in_silence() {
    let w = world();
    let view = w.view();
    let state = necessities::NecessitiesState::new();
    let g = necessities::grid(&view);

    // Tall enough for both halves: every hour and every row is drawn.
    let out = draw(90, 45, |f, a| necessities::render(&state, &view, f, a));
    for hour in g.first_hour..g.last_hour {
        assert!(
            out.lines().any(|l| l.starts_with(&format!("│{hour:02} "))),
            "hour {hour:02} is missing from the 90-column grid:\n{out}"
        );
    }
    for r in necessities::rows(&view) {
        assert!(out.contains(r.id.as_str()), "{} is missing:\n{out}", r.id);
    }
    assert!(!out.contains("more hours"), "nothing was dropped:\n{out}");
    assert!(!out.contains("more ↓"), "nothing was dropped:\n{out}");

    // Not tall enough: both halves say how much they could not draw.
    let out = draw(90, 18, |f, a| necessities::render(&state, &view, f, a));
    assert!(out.contains("more hours to 24:00"), "{out}");
    assert!(out.contains("more ↓"), "{out}");
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
                "{:>3}  {:<45} {:<28} {}",
                l.line,
                l.raw,
                l.target.to_string(),
                l.problem.clone().unwrap_or_else(|| l.parsed.clone())
            )
        })
        .collect();
    insta::assert_snapshot!("inbox_lines", lines.join("\n"));
}

/// §12.5's `t` gets a line *out* of the inbox. It used to default an undated,
/// unparented line back to `inbox.md`, so `t` then `Enter` was a drop and a
/// re-add of the same text into the same file — and it handed the shell a
/// stale `from_inbox` line number to delete afterwards.
#[test]
fn triage_never_targets_the_inbox_it_came_from() {
    let w = world();
    let view = w.view();
    let lines = inbox::inbox_lines(&view);
    assert!(
        lines.iter().all(|l| l.target.file != "inbox.md"),
        "{:?}",
        lines
            .iter()
            .map(|l| (l.line, l.target.to_string()))
            .collect::<Vec<_>>()
    );

    // Line 2 has no date and no `@parent`: §2's home for that is `backlog.md`.
    let mut state = inbox::CaptureState::new();
    state.sel = 1;
    inbox::on_key(&mut state, &view, tui_queue_common::key('t'));
    assert_eq!(state.buffer, "ask Kun about the dinner place");
    assert_eq!(state.triaging, Some(2));
    assert_eq!(
        inbox::on_key(
            &mut state,
            &view,
            tui_queue_common::special(crossterm::event::KeyCode::Enter)
        ),
        queue::Action::Mutate(queue::Mutation::Capture {
            text: "- [ ] ask Kun about the dinner place".to_string(),
            file: "backlog.md".to_string(),
            section: None,
            from_inbox: Some(2),
        })
    );

    // Tab back onto `inbox.md` anyway and the drop is withheld: `from_inbox`
    // is a line number taken before the add, and an add to the same file would
    // shift it.
    let mut state = inbox::CaptureState::new();
    state.sel = 1;
    inbox::on_key(&mut state, &view, tui_queue_common::key('t'));
    state.target = Some(4);
    assert_eq!(state.capture(&view).target.file, "inbox.md");
    assert_eq!(
        inbox::on_key(
            &mut state,
            &view,
            tui_queue_common::special(crossterm::event::KeyCode::Enter)
        ),
        queue::Action::Mutate(queue::Mutation::Capture {
            text: "- ask Kun about the dinner place".to_string(),
            file: "inbox.md".to_string(),
            section: None,
            from_inbox: None,
        })
    );
}

/// §13's `tm triage` and this screen both preview `inbox.md`. They must not
/// drift: same lines, same numbers, same raw text, and the same §4.1 line
/// wherever the natural-language layer of §12.5 recognises nothing. Where it
/// does fire — the spec's own `pset2 fri 6b ci4 max 2b/d` — the screen shows
/// the richer line, which is the point of the capture box.
#[test]
fn the_inbox_list_agrees_with_tm_triage() {
    let tm = cli_common::Tm::new();
    let w = tui_queue_common::world_from(&tm.plan.to_string_lossy());
    let view = w.view();
    let ours = inbox::inbox_lines(&view);
    let theirs = tm.json(&["triage"]);
    let theirs = theirs["lines"].as_array().expect("lines");

    assert_eq!(ours.len(), theirs.len(), "{ours:?} vs {theirs:?}");
    let mut differ = Vec::new();
    for (a, b) in ours.iter().zip(theirs) {
        assert_eq!(a.line as u64, b["line"].as_u64().expect("line"));
        // `tm triage` echoes the file's line; the screen strips the bullet,
        // because `t` puts these words in the capture box for editing.
        let raw = b["raw"].as_str().expect("raw");
        assert_eq!(a.raw.as_str(), raw.strip_prefix("- ").unwrap_or(raw));
        assert_eq!(a.problem, None, "line {} should parse", a.line);
        assert_eq!(b["problem"].as_str(), None);
        let cli = b["parsed"].as_str().expect("parsed");
        if a.parsed != cli {
            differ.push(format!("{:>3}  screen {}\n     tm triage {cli}", a.line, a.parsed));
        }
    }
    // Exactly one line differs, and it is the one §12.5's example is about.
    insta::assert_snapshot!("inbox_vs_tm_triage", differ.join("\n"));
}
