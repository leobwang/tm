//! Harness for the M7 TUI tests (tm-spec-v1.md §17: "`ratatui` `TestBackend`
//! snapshots of each pane at 120 and 90 columns").
//!
//! The three screen modules live in the `tm` **binary** crate, which an
//! integration test cannot `use`, so they are included here by path. Each
//! module is self-contained (it depends only on `tm-core`, `ratatui` and
//! `crossterm`), which is also what makes the shell agent's merge a matter of
//! three `mod` lines in `tui/mod.rs`.
//!
//! [`world`] builds the same hand-made `App` state for every test: the
//! `plan-basic` fixture at Monday 2026-09-07 10:42 with an empty log and the
//! synthetic capacity `priority_plan_basic.rs` uses (half a day today, a whole
//! one after), so the `u` and `fits` columns pin §7's arithmetic and not
//! `capacity::lookahead`'s.
//!
//! **§7's arithmetic is fork 4748911's, by value** (stage 6 W-46 track C; README gap
//! 4752, the class): the grants the screens render are fork `priority::compute`'s over the
//! world's candidates and that capacity, read from this test binary's frozen file
//! (`forkcap::FROZEN`, `../support/forkcap.rs`) and asked of `tm-oracle capacity` under
//! `TM_ORACLE`.  Until W-46 they were tm-core's in-tree copy of it, which R3 leaves with no
//! shipped caller and deletes — the screens are the binary's and keep their tests; where
//! their input comes from is the harness's.

#![allow(dead_code)]

/// The test chokepoint (step R12): every replay here is read through it.
#[path = "../support/replay.rs"]
pub mod chokepoint;

#[allow(dead_code, unused_imports)]
#[path = "../../src/tui/queue.rs"]
pub mod queue;

#[allow(dead_code, unused_imports)]
#[path = "../../src/tui/necessities.rs"]
pub mod necessities;

#[allow(dead_code, unused_imports)]
#[path = "../../src/tui/inbox.rs"]
pub mod inbox;

use std::collections::BTreeMap;

use chrono::{DateTime, Duration, NaiveDate, NaiveTime};
use chrono_tz::Tz;
use crossterm::event::{KeyCode, KeyEvent, KeyModifiers};
use ratatui::backend::TestBackend;
use ratatui::buffer::Buffer;
use ratatui::layout::Rect;
use ratatui::{Frame, Terminal};

use tm_core::capacity::{local_dt, DayCapacity, UnitCapacity, CAP_DEN};
use tm_core::energy::Model;
use tm_core::log::{Event, LogEntry, Replay};
use tm_core::priority::{self, Candidate, Prio};

/// Fork 4748911's answers, by value (W-46 track C): this binary's `forkcap::FROZEN` file, one per
/// binary that includes this harness (`tui_queue_capture`, `tui_queue_keys`, `tui_queue_reorder`,
/// `tui_queue_screens`), each re-blessed by its own run of the module's bless.
#[allow(dead_code)]
#[path = "../support/forkcap.rs"]
pub mod forkcap;
use tm_core::store::{MemStore, PlanFiles, Store};
use tm_core::tree::Tree;

use queue::View;

/// The fixture's timezone (§16).
pub const TZ: Tz = Tz::America__Chicago;

/// Path of a fixture directory under `tm-core/tests/fixtures`.
pub fn fixture(name: &str) -> String {
    format!(
        "{}/../tm-core/tests/fixtures/{name}",
        env!("CARGO_MANIFEST_DIR")
    )
}

/// `YYYY-MM-DD`.
pub fn date(s: &str) -> NaiveDate {
    NaiveDate::parse_from_str(s, "%Y-%m-%d").expect("date")
}

/// Everything a [`View`] borrows, owned.
pub struct World {
    /// The parsed plan (carries the config).
    pub files: PlanFiles,
    /// The tree built from it.
    pub tree: Tree,
    /// An empty replay (the fixture has no `.tm/log.jsonl`).
    pub replay: Replay,
    /// Today's candidates.
    pub candidates: Vec<Candidate>,
    /// Their priorities.
    pub prios: Vec<Prio>,
    /// The synthetic lookahead, in the exact units the screens read (stage 5
    /// D10 L8; whole minutes here, so every floor is the minute it was).
    pub caps: Vec<UnitCapacity>,
    /// 2026-09-07.
    pub today: NaiveDate,
    /// 2026-09-07 10:42 America/Chicago.
    pub now: DateTime<Tz>,
}

impl World {
    /// The read-only view the screens render.
    pub fn view(&self) -> View<'_> {
        View::new(
            &self.tree,
            &self.files,
            &self.files.config,
            &self.replay,
            &self.candidates,
            &self.prios,
            &self.caps,
            self.today,
            self.now,
        )
    }
}

/// Today keeps half a day, every later day a whole one.
fn caps(days: u32, from: NaiveDate) -> Vec<DayCapacity> {
    (0..days as i64)
        .map(|i| DayCapacity {
            date: from + Duration::days(i),
            minutes_at_level: if i == 0 { [0, 0, 30, 30, 60, 60] } else { [0, 0, 60, 60, 120, 120] },
        })
        .collect()
}

/// The `plan-basic` world at Monday 2026-09-07 10:42.
pub fn world() -> World {
    world_from(&fixture("plan-basic"))
}

/// The same, from any plan directory.
pub fn world_from(dir: &str) -> World {
    world_with_log(dir, &[])
}

/// The same, with a hand-made log (§10.1) behind it — what fills the §6.4
/// progress bars.
pub fn world_with_log(dir: &str, entries: &[LogEntry]) -> World {
    world_with(dir, entries, &BTreeMap::new())
}

/// The same, with yesterday's stored priorities — what §7.4's hysteresis
/// compares against.
pub fn world_with_yesterday(dir: &str, yesterday: &BTreeMap<tm_core::model::Id, u8>) -> World {
    world_with(dir, &[], yesterday)
}

/// The general constructor.
pub fn world_with(
    dir: &str,
    entries: &[LogEntry],
    yesterday: &BTreeMap<tm_core::model::Id, u8>,
) -> World {
    let store = MemStore::from_dir(dir).expect("fixture readable");
    let files = store.read_tree().expect("tree parses");
    let tree = Tree::build(&files.files, &files.config);
    let replay = chokepoint::replay_of_entries(entries, files.config.tz);
    let today = date("2026-09-07");
    let now = local_dt(
        files.config.tz,
        today,
        NaiveTime::from_hms_opt(10, 42, 0).expect("time"),
    );
    let candidates = priority::collect_candidates(
        &tree,
        &replay,
        &files.config,
        &Model::default(),
        today,
        now,
    );
    let caps = caps(priority::lookahead_days(&candidates, today), today);
    let (prios, _) = forkcap::rank(forkcap::store(), &candidates, &caps, yesterday, &files.config, today);
    // A whole-minute day in units: each level's minutes × `CAP_DEN`, the definition of a unit.
    let caps = caps.iter().map(|d| UnitCapacity { date: d.date, units: d.minutes_at_level.map(|m| u128::from(m) * CAP_DEN) }).collect();
    World {
        files,
        tree,
        replay,
        candidates,
        prios,
        caps,
        today,
        now,
    }
}

/// One `done` event on 2026-09-07 (§10.1), for the progress bars.
pub fn done(id: &str, ci: u8, minutes: u32, at: &str) -> LogEntry {
    LogEntry::new(
        chrono::DateTime::parse_from_rfc3339(at).expect("timestamp"),
        Event::Done {
            id: id.to_string(),
            est_min: minutes,
            actual_min: minutes,
            went: Some(1),
            tags: Vec::new(),
            ci,
            partial: false,
        },
    )
}

/// One `event` (§10.1) — what `tm event <name>` appends and what §5.1's
/// waiting monitor watches for.
pub fn named_event(name: &str, id: Option<&str>, at: &str) -> LogEntry {
    LogEntry::new(
        chrono::DateTime::parse_from_rfc3339(at).expect("timestamp"),
        Event::Named {
            name: name.to_string(),
            id: id.map(str::to_string),
        },
    )
}

/// One key press without modifiers.
pub fn key(c: char) -> KeyEvent {
    let mods = if c.is_ascii_uppercase() {
        KeyModifiers::SHIFT
    } else {
        KeyModifiers::NONE
    };
    KeyEvent::new(KeyCode::Char(c), mods)
}

/// One special key.
pub fn special(code: KeyCode) -> KeyEvent {
    KeyEvent::new(code, KeyModifiers::NONE)
}

/// Draw one screen into a `TestBackend` and return the buffer as text.
pub fn draw(width: u16, height: u16, f: impl FnOnce(&mut Frame, Rect)) -> String {
    let mut term = Terminal::new(TestBackend::new(width, height)).expect("terminal");
    term.draw(|frame| {
        let area = frame.area();
        f(frame, area);
    })
    .expect("draw");
    buffer_text(term.backend().buffer())
}

/// The buffer as one string per row, trailing blanks trimmed.
pub fn buffer_text(buf: &Buffer) -> String {
    let w = buf.area.width as usize;
    buf.content
        .chunks(w)
        .map(|row| {
            let line: String = row.iter().map(|c| c.symbol()).collect();
            line.trim_end().to_string()
        })
        .collect::<Vec<_>>()
        .join("\n")
}
