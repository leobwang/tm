//! **The kernel's cells against the shipped bytes** (README gaps **1105** and
//! **1318**, stage 6 W-24).
//!
//! `Emit.lean` landed at W-22 and had **no caller**. Its nineteen theorems said
//! the cells were consistent with themselves; the claim that they were the
//! *fork's* cells rested on a human having read `tm-core/src/emit.rs` beside
//! `Emit.lean`. Gap 1105 is exactly that sentence — *"the cells are proved
//! consistent with themselves and checked against the fork by reading"* — and
//! this file is the machine that stops it being true.
//!
//! # What it does
//!
//! One fixture day (`tui_common`'s hand-built §4.3 timeline over the
//! `plan-basic` tree), rendered twice:
//!
//! * **Rust**: [`emit::row_cells`] over the `Tree` the fork's parser built, then
//!   [`emit::render_row`] — the bytes the day file gets, which is
//!   [`emit::plan_rows`] itself.
//! * **Lean**: the same segments over the wire's new `plan` section, answered by
//!   `EmitWire.rowsJson` → `Emit.rowOf`, against the kernel's **own** parse of
//!   the same markdown, then fed to the same [`emit::render_row`].
//!
//! The two cell lists are compared cell by cell, and the padded rows byte for
//! byte. The Rust never tells the kernel a title, a `ci`, an estimate or a
//! parent: those four cells are the two parsers' independent answers about one
//! file, which is the comparison gap 1105 asks for and the one a reader cannot
//! do.
//!
//! # What it cannot see, and the one row it is allowed to differ on
//!
//! * **The `⚠` note is `Emit.noteCell`'s declared hole** (README gap **1102**):
//!   `note_cell`'s hot branch needs the fork's `effective_due`, of which this
//!   kernel has no view, so the kernel answers `[]` where the fork says `due
//!   today`. [`EXPECTED_NOTE_HOLES`] names the rows this is allowed on **by
//!   their text**, the count is asserted, and every other cell of those rows is
//!   still compared exactly — so the hole cannot widen quietly and a row that
//!   stops differing fails this test.
//! * **A note the fork's planner wrote as prose cannot cross.** `SegFlags::note`
//!   is a `String` and `Planner.Note` is eleven names with their arguments
//!   (D30 Q6: the kernel holds the name, `Emit.noteText` holds the words), so a
//!   host whose planner produced text has nothing to send. This test therefore
//!   sends `note: null` and the kernel **derives** the note column; that is why
//!   the `↓` row below is a real comparison and the `⚠` row is not.
//!   [`the_kernel_writes_the_forks_note_sentences`] covers the eleven names the
//!   other way, and says what *it* cannot see.
//! * It is a **library-level** comparison of one day: no binary is driven, so
//!   nothing here sees the CLI, the store or the day file's framing. That is
//!   `one_renderer.rs`'s job and it still does it.
//! * The fixture day has four of the ten kinds, so
//!   [`the_kernel_and_the_fork_agree_on_a_batch_row`] and
//!   [`the_kernel_and_the_fork_agree_on_every_kind_of_row`] build the rest.
//!   `Ghost` is the eleventh kind and is the kernel's alone — the fork carries
//!   the ghost row as a `SegFlags` bit — so no fork cell exists to compare it
//!   against and it is **not covered** (README gap 1322).

mod tui_common;

#[allow(dead_code)]
#[path = "../src/cli/tz_table.rs"]
mod tz_table;

use std::collections::HashMap;
use std::fs;

use chrono::{Datelike, Timelike};
use serde_json::{json, Value};

use tm_core::config::Config;
use tm_core::emit::{self, Layout, RowCells};
use tm_core::model::Id;
use tm_core::planner::{self, DayPlan, SegKind, Segment};
use tm_core::tree::Tree;

/// **Every cell the kernel is allowed to disagree with the fork about on this
/// day, with the gap that records why** — `(row title, cell, fork, kernel, gap)`.
///
/// Two, both declared in `Emit.lean`'s own header before this file existed:
///
/// * **gap 1102** — `note_cell`'s `⚠` branch needs the fork's `effective_due`,
///   of which this kernel has no view, so the kernel answers nothing where the
///   fork says `due today`.
/// * **gap 1101** — the fork's `est_cell` reads `est_original` first and this
///   kernel has **one** estimate view, `Core.est`, which is `est:` then the
///   leading estimate. The fixture's `- [>] 4 2b Exercises 5.3–5.5 @m1 est:1b
///   ^t3` carries both, so the two readers pick different numbers. Inventing a
///   second view of the field to agree would be AGENTS §5.3's own defect.
///
/// Every entry must fire **exactly once**: a hole that closes fails this test
/// as loudly as a hole that widens, so neither can happen quietly.
const DECLARED_HOLES: &[(&str, &str, &str, &str, u32)] = &[
    ("Pick up package", "note", "due today", "", 1102),
    ("Exercises 5.3–5.5", "est", "2b×1.6", "1b×1.6", 1101),
];

/// Seconds from `0001-01-01T00:00:00Z` to the Unix epoch: the kernel counts
/// instants from the former and `chrono` from the latter.
///
/// The **third** copy of this number in the tree — `tm/src/cli/kernel_log.rs`'s
/// `EPOCH_FROM_CE` is the binary's and `tm/tests/kernel_replay_parity.rs` has
/// the other test-side one; a test crate cannot `use tm::…` (binary crate), so
/// the constant is retyped rather than shared (README gap **1323**). A wrong
/// value here is not a silent one: every `time` cell below would be off by the
/// whole difference and [`the_kernel_and_the_fork_write_the_same_cells`] fails
/// naming both clocks — which is how this was found on the first run.
const EPOCH_FROM_CE: i64 = 62_135_596_800;

/// A `chrono` instant as the kernel's absolute second.
fn kernel_sec(t: chrono::DateTime<chrono_tz::Tz>) -> i64 {
    t.timestamp() + EPOCH_FROM_CE
}

// ---------------------------------------------------------------------------
// The request
// ---------------------------------------------------------------------------

/// The fixture's documents, as the wire carries them.
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

/// An exact decimal as the wire's `{num, den}` pair.
///
/// The fork's multiplier is an `f64` and this kernel has no float (AGENTS §4),
/// so the test does the conversion the host will do at R3: six places, which is
/// `energy::fmt_multiplier`'s two with room to spare, over `10^6` — inside
/// `CapWire.maxPairDen`. An `f64` that is not a six-place decimal would be
/// rounded here, and the fixture's 1.6 is not one of those.
fn decimal_pair(x: f64) -> Value {
    let scaled = (x * 1_000_000.0).round() as u64;
    json!({"num": scaled, "den": 1_000_000u64})
}

/// One segment, as the `plan` section carries it.
///
/// `instance` is not sent: no cell reads it (`Emit.rowOf` takes a `Seg` and
/// never looks at `inst`). `flags.ghost` is not sent either — the kernel makes
/// the ghost row a *kind* and the fork makes it a flag, and the fixture has no
/// ghost row.
fn seg_json(seg: &Segment) -> Value {
    let mut o = json!({
        "start": kernel_sec(seg.start),
        "stop": kernel_sec(seg.end),
        "kind": planner::kind_label(&seg.kind),
        "energy": seg.energy,
        "item": seg.item.as_ref().map(|i| i.to_string()),
        "planned": seg.flags.planned_min,
        "flags": {
            "done": seg.flags.done,
            "current": seg.flags.current,
            "underused": seg.flags.underused,
            "hot": seg.flags.hot,
            "mandatory": seg.flags.mandatory,
            "deferred": seg.flags.deferred,
            "open": seg.flags.open,
        },
        // **Deliberately null**: see the module header. The fork's planner wrote
        // this column as prose and the kernel's `Note` is a name, so there is
        // nothing to send and the kernel derives what it can.
        "note": Value::Null,
    });
    if let SegKind::Batch(ids) = &seg.kind {
        o["batch"] = json!(ids.iter().map(|i| i.to_string()).collect::<Vec<_>>());
    }
    if let Some(m) = seg.flags.multiplier {
        o["mult"] = decimal_pair(m);
    }
    o
}

/// The whole request: the documents, the zone, the clock, and the `plan`
/// section's rows.
fn request(plan: &DayPlan, cfg: &Config) -> Value {
    let prios: Vec<Value> = plan
        .priorities
        .iter()
        .map(|(id, p)| json!({"id": id.to_string(), "p": p.p}))
        .collect();
    json!({
        "docs": docs(),
        "now": plan.date.to_string(),
        "blockMin": cfg.block_min(),
        "tz": tz_table::wire_for(None, cfg.tz),
        "plan": {
            "bed": format!("{:02}:{:02}", cfg.day.bed.hour(), cfg.day.bed.minute()),
            "priorities": prios,
            "segments": plan.segments.iter().map(seg_json).collect::<Vec<_>>(),
        }
    })
}

/// The kernel's rows for a day, as [`RowCells`].
fn kernel_cells(plan: &DayPlan, cfg: &Config) -> Vec<RowCells> {
    let req = request(plan, cfg);
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("the response is json");
    let rows = resp["ok"]["plan"]["rows"]
        .as_array()
        .unwrap_or_else(|| panic!("no plan.rows in the response:\n{raw}"));
    rows.iter()
        .map(|r| {
            let s = |k: &str| r[k].as_str().unwrap_or_else(|| panic!("{k} in {r}")).to_string();
            RowCells {
                time: s("time"),
                ci: s("ci"),
                p: s("p"),
                mark: s("mark"),
                title: s("title"),
                parent: s("parent"),
                est: s("est"),
                actual: s("actual"),
                note: s("note"),
                batch_names: r["batchNames"].as_array().and_then(|xs| {
                    if xs.is_empty() {
                        None
                    } else {
                        Some(xs.iter().map(|x| x.as_str().unwrap_or_default().to_string()).collect())
                    }
                }),
            }
        })
        .collect()
}

/// The fork's cells for the same day.
fn fork_cells(plan: &DayPlan, tree: &Tree, cfg: &Config) -> Vec<RowCells> {
    let prios: HashMap<&Id, u8> = plan.priorities.iter().map(|(id, p)| (id, p.p)).collect();
    plan.segments
        .iter()
        .map(|seg| emit::row_cells(seg, plan, tree, cfg, &prios))
        .collect()
}

/// `(cell name, fork, kernel)` for every cell of a row that differs.
///
/// The nine cells **and** `batchNames`, which is not a cell but is carried
/// beside them and would otherwise be compared only by the batch test.
fn differences(a: &RowCells, b: &RowCells) -> Vec<(&'static str, String, String)> {
    const NAMES: [&str; 9] = [
        "time", "ci", "p", "mark", "title", "parent", "est", "actual", "note",
    ];
    let mut out: Vec<(&'static str, String, String)> = NAMES
        .iter()
        .zip(a.cells().iter().zip(b.cells()))
        .filter(|(_, (x, y))| *x != y)
        .map(|(n, (x, y))| (*n, (*x).to_string(), y.to_string()))
        .collect();
    if a.batch_names != b.batch_names {
        out.push((
            "batchNames",
            format!("{:?}", a.batch_names),
            format!("{:?}", b.batch_names),
        ));
    }
    out
}

// ---------------------------------------------------------------------------
// The comparisons
// ---------------------------------------------------------------------------

/// **Every cell of every row, both ways, on one day.**
///
/// The kernel is not told a single one of the four cells it has to read the
/// plan for — `title`, `ci` (through the item), `est` and `parent` — so an
/// agreement here is two parsers agreeing about one tree, not a copy of an
/// answer.
#[test]
fn the_kernel_and_the_fork_write_the_same_cells() {
    let cfg = tui_common::config();
    let tree = tui_common::tree(&cfg);
    let plan = tui_common::day_plan(&cfg);

    let fork = fork_cells(&plan, &tree, &cfg);
    let lean = kernel_cells(&plan, &cfg);
    assert_eq!(
        lean.len(),
        fork.len(),
        "the kernel answered {} rows for {} segments (`Emit.rowsOf_length`'s wire half)",
        lean.len(),
        fork.len()
    );
    assert!(fork.len() > 10, "a day worth comparing: {}", fork.len());

    let mut fired = vec![0usize; DECLARED_HOLES.len()];
    for (i, (f, k)) in fork.iter().zip(&lean).enumerate() {
        for (cell, a, b) in differences(f, k) {
            let hit = DECLARED_HOLES.iter().position(|(title, c, fk, kn, _)| {
                *title == f.title && *c == cell && *fk == a && *kn == b
            });
            match hit {
                Some(n) => fired[n] += 1,
                None => panic!(
                    "row {i} (`{}`) differs in `{cell}` and no README gap declares it:\n  \
                     fork: {a:?}\n  kernel: {b:?}\n  {f:#?}\n  {k:#?}",
                    f.title
                ),
            }
        }
    }
    for (n, (title, cell, _, _, gap)) in DECLARED_HOLES.iter().enumerate() {
        assert_eq!(
            fired[n], 1,
            "README gap {gap} is one cell of this day (`{title}`'s `{cell}`) and it fired \
             {} times. If the gap CLOSED, delete its row from DECLARED_HOLES.",
            fired[n]
        );
    }
}

/// **And the bytes.** The kernel's cells, padded by the one padder, are the day
/// file's lines.
///
/// This is the sentence gap 1105 says has never been checked: *"no byte
/// comparison between the two has ever been run"*. The two [`DECLARED_HOLES`]
/// cells are substituted before padding and **nothing else is**, so on every
/// other row every byte the file gets came out of the kernel.
#[test]
fn the_kernels_cells_padded_are_the_day_files_bytes() {
    let cfg = tui_common::config();
    let tree = tui_common::tree(&cfg);
    let plan = tui_common::day_plan(&cfg);
    let layout = Layout::default();

    let shipped = emit::plan_rows(&plan, &tree, &cfg, &layout);
    let fork = fork_cells(&plan, &tree, &cfg);
    let lean = kernel_cells(&plan, &cfg);
    assert_eq!(shipped.len(), lean.len());

    let mut patched = 0usize;
    let mut untouched = 0usize;
    for (i, ((want, cells), f)) in shipped.iter().zip(&lean).zip(&fork).enumerate() {
        let mut cells = cells.clone();
        let mut here = 0usize;
        for (title, cell, fk, _, _) in DECLARED_HOLES {
            if *title != f.title {
                continue;
            }
            match *cell {
                "note" => cells.note = (*fk).to_string(),
                "est" => cells.est = (*fk).to_string(),
                other => panic!("DECLARED_HOLES names a cell this test cannot patch: {other}"),
            }
            here += 1;
        }
        if here == 0 {
            untouched += 1;
        } else {
            patched += here;
        }
        assert_eq!(
            &emit::render_row(&cells, &layout),
            want,
            "row {i}'s bytes are not the day file's"
        );
    }
    assert_eq!(patched, DECLARED_HOLES.len(), "the declared holes, and no others");
    assert!(
        untouched >= shipped.len() - DECLARED_HOLES.len(),
        "more rows were patched than there are declared holes"
    );

    // And the padder really is doing work: at least one row was padded wider
    // than its cells, so `render_row` is not an identity this test could not
    // tell from one.
    assert!(
        shipped.iter().any(|r| r.contains("   ")),
        "no row has a padded column; the comparison would not see a padder"
    );
}

/// **A batch row**, which the fixture day has none of: `Emit.batchTitle` is
/// §7.5's frame over `Emit.batchNames`, and `emit::fit_batch` is the frame over
/// `emit::batch_names`, and the wire carries the members so the fitter can
/// reach them.
#[test]
fn the_kernel_and_the_fork_agree_on_a_batch_row() {
    let cfg = tui_common::config();
    let tree = tui_common::tree(&cfg);
    let base = tui_common::day_plan(&cfg);

    // Three real ids of the fixture tree, gathered into one block.
    let members: Vec<Id> = ["t4", "t5", "a3"].iter().map(|s| Id::new(*s)).collect();
    let mut seg = base
        .segments
        .iter()
        .find(|s| matches!(s.kind, SegKind::Block))
        .expect("a block to turn into a batch")
        .clone();
    seg.kind = SegKind::Batch(members.clone());
    seg.item = None;
    seg.flags.note = None;
    let mut plan = DayPlan::empty(base.date, base.window, base.budget_blocks);
    plan.priorities = base.priorities.clone();
    plan.segments = vec![seg];

    let fork = fork_cells(&plan, &tree, &cfg);
    let lean = kernel_cells(&plan, &cfg);
    assert_eq!(lean.len(), 1);
    assert_eq!(differences(&fork[0], &lean[0]), vec![], "the batch row's cells");
    assert_eq!(
        lean[0].batch_names,
        fork[0].batch_names,
        "the members the fitter needs"
    );
    // The title really is the batch frame, so this test is not comparing two
    // empty strings.
    assert!(
        lean[0].title.starts_with("batch: ") && lean[0].title.ends_with("(3)"),
        "{:?}",
        lean[0].title
    );
    // And the fitted bytes agree at a width that forces `fit_batch` to cut.
    for w in [emit::DEFAULT_TITLE_W, 24, 18] {
        let layout = Layout::new(w);
        assert_eq!(
            emit::render_row(&lean[0], &layout),
            emit::render_row(&fork[0], &layout),
            "the batch row at title width {w}"
        );
    }
}

/// **One row of every kind the fork can produce**, because the fixture day has
/// four of ten.
///
/// `Rest`, `Lost`, `Sleep` and `WindDown` are the kinds whose *title* carries a
/// duration (`rest 20m`, `lost 20m`, `sleep 8h`, `wind-down · bed 22:00`), and
/// the fixture never places one; without this, `Emit.titleCell`'s four
/// corresponding branches are unwitnessed by any machine and a change to them
/// leaves every other test in this repository green.
///
/// Each kind is placed twice — once with an item of the fixture tree and once
/// without — because `title_cell`'s fallback (`—`, `routine`, `sleep`) only
/// fires on the second.
#[test]
fn the_kernel_and_the_fork_agree_on_every_kind_of_row() {
    let cfg = tui_common::config();
    let tree = tui_common::tree(&cfg);
    let base = tui_common::day_plan(&cfg);
    let proto = base
        .segments
        .iter()
        .find(|s| matches!(s.kind, SegKind::Block))
        .expect("a block")
        .clone();

    let kinds = [
        SegKind::Block,
        SegKind::Batch(vec![Id::new("t4"), Id::new("t5")]),
        SegKind::Break,
        SegKind::Routine,
        SegKind::Wall,
        SegKind::Rest,
        SegKind::Optional,
        SegKind::WindDown,
        SegKind::Sleep,
        SegKind::Lost,
    ];
    let mut segments = Vec::new();
    for kind in &kinds {
        for item in [Some(Id::new("t4")), None] {
            let mut seg = proto.clone();
            seg.kind = kind.clone();
            seg.item = item;
            seg.instance = None;
            seg.flags.note = None;
            seg.flags.done = false;
            seg.flags.current = false;
            seg.flags.hot = false;
            seg.flags.underused = false;
            segments.push(seg);
        }
    }
    let mut plan = DayPlan::empty(base.date, base.window, base.budget_blocks);
    plan.priorities = base.priorities.clone();
    plan.segments = segments;

    let fork = fork_cells(&plan, &tree, &cfg);
    let lean = kernel_cells(&plan, &cfg);
    assert_eq!(lean.len(), kinds.len() * 2);
    for (i, (f, k)) in fork.iter().zip(&lean).enumerate() {
        let kind = planner::kind_label(&plan.segments[i].kind);
        assert_eq!(
            differences(f, k),
            vec![],
            "a `{kind}` row with item {:?}",
            plan.segments[i].item
        );
    }
    // The four duration-carrying titles really were exercised, so an agreement
    // on ten empty strings would not pass.
    for want in ["rest ", "lost ", "sleep ", "wind-down · bed "] {
        assert!(
            lean.iter().any(|c| c.title.starts_with(want)),
            "no row's title starts `{want}`: {:#?}",
            lean.iter().map(|c| c.title.clone()).collect::<Vec<_>>()
        );
    }
}

/// **The eleven `Note` names, rendered by the kernel.**
///
/// The other direction of the module header's second bullet: here the *kernel*
/// is given the name and the *fork's* row is given the sentence, so the
/// comparison is `Emit.noteText` against the text `tm-core/src/planner.rs`
/// writes at each `notes.push` / `note: Some(…)` site.
///
/// **What this cannot see**, and it is the weaker of the two comparisons: the
/// right-hand sides below are **transcribed** from the fork's `format!` strings
/// rather than produced by running its planner into each of the eleven
/// conditions. A transcription error would agree with itself. What it does
/// catch is the kernel's renderer drifting from the sentence recorded here, and
/// it covers all eleven constructors, which no fixture day does.
#[test]
fn the_kernel_writes_the_forks_note_sentences() {
    let cfg = tui_common::config();
    let base = tui_common::day_plan(&cfg);
    let day = base.date;

    // (the wire's note, the sentence `tm-core/src/planner.rs` writes)
    let cases: Vec<(Value, String)> = vec![
        (
            json!({"name": "travelDay"}),
            "travel day: no blocks planned (`travel-day` wall today)".to_string(),
        ),
        (json!({"name": "travelDayWall"}), "travel day".to_string()),
        (json!({"name": "paused"}), "paused".to_string()),
        (json!({"name": "interruption"}), "interruption".to_string()),
        (
            json!({"name": "budgetSpent", "blocksDone": 6}),
            "budget spent: 6 blocks done, the rest of the day is rest".to_string(),
        ),
        (
            json!({"name": "runningLeft", "leftMin": 23}),
            "running · 23m left".to_string(),
        ),
        (
            json!({"name": "breakWhere", "text": "walk"}),
            "walk".to_string(),
        ),
        (
            json!({"name": "idleAttributed", "text": "idle → ^t3"}),
            "idle → ^t3".to_string(),
        ),
        (
            json!({"name": "plannedOf", "planned": 300, "total": 360}),
            "planned 5b of 6b (83%)".to_string(),
        ),
        (
            json!({"name": "bufferBefore", "id": "g1"}),
            format!("buffer before {}", tui_common::tree(&cfg).get(&Id::new("g1")).map(|i| i.title.clone()).expect("g1")),
        ),
        (
            json!({"name": "noPosition", "id": "t9", "durMin": 45, "lo": 0, "hi": 0}),
            String::new(), // filled in below: the two clocks are the window's
        ),
    ];

    let mut plan = DayPlan::empty(day, base.window, base.budget_blocks);
    let proto = base
        .segments
        .iter()
        .find(|s| matches!(s.kind, SegKind::Block))
        .expect("a block")
        .clone();
    plan.segments = vec![proto; cases.len()];

    let mut req = request(&plan, &cfg);
    // `noPosition`'s two instants are the plan window's, so the expected text
    // can be built from the same two clocks the kernel renders.
    let lo = kernel_sec(base.window.0);
    let hi = kernel_sec(base.window.1);
    let no_position = format!(
        "t9: no free 45m position in {}–{}; not planned today",
        planner::fmt_clock(base.window.0),
        planner::fmt_clock(base.window.1)
    );
    for (i, (note, _)) in cases.iter().enumerate() {
        let mut note = note.clone();
        if note["name"] == json!("noPosition") {
            note["lo"] = json!(lo);
            note["hi"] = json!(hi);
        }
        req["plan"]["segments"][i]["note"] = note;
    }

    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    let rows = resp["ok"]["plan"]["rows"]
        .as_array()
        .unwrap_or_else(|| panic!("no plan.rows:\n{raw}"));
    assert_eq!(rows.len(), cases.len());
    for (i, (note, want)) in cases.iter().enumerate() {
        let want = if want.is_empty() { &no_position } else { want };
        assert_eq!(
            rows[i]["note"].as_str().expect("note"),
            want,
            "the sentence for {note}"
        );
    }
}

/// **The wire refuses what R10 says it refuses**, through the kernel, by name.
///
/// A decoder whose rejection theorems are all proved and whose refusals never
/// reach the wire is half a guard; these are the same refusals seen from the
/// host's side.
#[test]
fn the_wire_refuses_a_bad_row_by_name() {
    let cfg = tui_common::config();
    let plan = tui_common::day_plan(&cfg);
    let base = request(&plan, &cfg);

    let cases: Vec<(&str, Value, &str)> = vec![
        ("an unknown kind", json!("nosuchkind"), "badSegment 0 kind"),
        ("an inverted segment", Value::Null, "segmentRefused 0 inverted"),
    ];
    for (what, kind, want) in cases {
        let mut req = base.clone();
        if kind.is_null() {
            let stop = req["plan"]["segments"][0]["stop"].clone();
            req["plan"]["segments"][0]["start"] = json!(stop.as_i64().expect("stop") + 60);
        } else {
            req["plan"]["segments"][0]["kind"] = kind;
        }
        let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
        let resp: Value = serde_json::from_str(&raw).expect("json");
        assert_eq!(
            resp["err"]["plan"].as_str(),
            Some(want),
            "{what}: {raw}"
        );
    }

    // An energy past five, a priority past seven and a batch past the cap.
    let mut req = base.clone();
    req["plan"]["segments"][0]["energy"] = json!(6);
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    assert_eq!(resp["err"]["plan"].as_str(), Some("badSegment 0 energy"), "{raw}");

    let mut req = base.clone();
    req["plan"]["priorities"][0]["p"] = json!(8);
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    assert_eq!(resp["err"]["plan"].as_str(), Some("badPriority 0"), "{raw}");

    let mut req = base.clone();
    req["plan"]["segments"][0]["kind"] = json!("batch");
    req["plan"]["segments"][0]["batch"] =
        json!((0..17).map(|k| k.to_string()).collect::<Vec<_>>());
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    assert_eq!(resp["err"]["plan"].as_str(), Some("badSegment 0 batch"), "{raw}");

    // And the unmodified request is accepted, so the refusals above are not
    // this request being refused for some other reason.
    let raw = tm_kernel_ffi::call(&base.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    assert!(resp["ok"]["plan"]["rows"].is_array(), "{raw}");
}

/// **A `plan` section on a request that also edits the documents is refused by
/// name.**
///
/// The rows are rendered against the plan as `runLoad` read it and the
/// documents come back as the commands left them, so answering both would put
/// two states in one response. That is gap 109's stance on
/// `capacityWithCommands`, one section along, and it is a refusal rather than a
/// gap because a wrong answer here would be silent.
#[test]
fn a_plan_section_with_commands_is_refused() {
    let cfg = tui_common::config();
    let plan = tui_common::day_plan(&cfg);
    let mut req = request(&plan, &cfg);
    req["cmds"] = json!([{"op": "drop", "id": "t4"}]);

    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    assert_eq!(resp["err"]["plan"].as_str(), Some("rowsWithCommands"), "{raw}");

    // The same command WITHOUT a `plan` section still applies, so the refusal
    // is the pairing and not the command.
    req.as_object_mut().expect("an object").remove("plan");
    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    assert!(resp["ok"]["docs"].is_array(), "{raw}");
}

/// **A request with no `plan` section answers exactly as it did before**, which
/// is the Lean theorem `EmitWire.runRows_without_a_plan_section_is_runCap` seen
/// from the host: the FFI entry moved and nothing else did.
#[test]
fn a_request_without_a_plan_section_is_unchanged() {
    let cfg = tui_common::config();
    let plan = tui_common::day_plan(&cfg);
    let mut req = request(&plan, &cfg);
    req.as_object_mut().expect("an object").remove("plan");

    let raw = tm_kernel_ffi::call(&req.to_string()).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    assert!(resp["ok"]["docs"].is_array(), "{raw}");
    assert!(resp["ok"]["report"].is_object(), "{raw}");
    assert!(resp["ok"].get("plan").is_none(), "a plan key with no plan section: {raw}");
}

/// The fixture day this file compares actually exercises the cells it claims
/// to — otherwise an agreement on nine empty strings would pass every
/// assertion above.
#[test]
fn the_fixture_day_fills_every_column() {
    let cfg = tui_common::config();
    let tree = tui_common::tree(&cfg);
    let plan = tui_common::day_plan(&cfg);
    let fork = fork_cells(&plan, &tree, &cfg);
    const NAMES: [&str; 9] = [
        "time", "ci", "p", "mark", "title", "parent", "est", "actual", "note",
    ];
    for (i, name) in NAMES.iter().enumerate() {
        let filled = fork
            .iter()
            .filter(|c| !c.cells()[i].trim().is_empty())
            .count();
        assert!(filled > 0, "no row of the fixture day has a `{name}` cell");
    }
    // And the day covers more than one kind.
    let kinds: std::collections::BTreeSet<&str> = plan
        .segments
        .iter()
        .map(|s| planner::kind_label(&s.kind))
        .collect();
    assert!(kinds.len() >= 5, "one kind of row is not a day: {kinds:?}");
    assert_eq!(plan.date.year(), 2026, "the fixture moved");
}
