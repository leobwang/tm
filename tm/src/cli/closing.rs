//! §6.3's close, kernel-backed (stage 4 step 6).
//!
//! # API overview
//!
//! * [`run`] — one close request through [`kernel_bridge::apply`]. The
//!   explicit `tm close <day|week|month>` (with the month's `--drop` list)
//!   and the automatic close both come here, so there is one request shape,
//!   one report, and one set of log events written from it.
//! * [`auto_close`] — §6.3's "runs automatically on the first command after
//!   the period ends": when `state.closed` is behind the last ended period of
//!   any grain, **one** `autoClose` call at now closes every ended region of
//!   every grain, whatever its age — no catch-up loop and no window. The
//!   fork-point `AUTO_CLOSE_CATCHUP = 16` day-by-day iteration is gone (the
//!   owner's D1 package; `autoClose_catches_up_in_one_step`, L19b). It also
//!   runs, once, when `state.closed.swept` is unset although the stamps are
//!   current — a tree the fork-point binary last wrote, whose catch-up
//!   stamped periods closed that it never ran and left their lines stranded
//!   (see [`due`]).
//! * [`last_day`] / [`last_week`] / [`last_month`] / [`last_ended_key`] — the
//!   last period of each grain that has ended at `today`. That is
//!   `state.closed`'s stamp (§10.2's `closed` map stays Rust's) and the key
//!   `tm close` prints; it is the boundary of the kernel's `Closed`
//!   (`Grain.lean`: a region is closed once `now`'s index has passed it),
//!   cross-checked against the kernel itself in this module's tests; and
//!   [`running_key`], the one period of a grain no close can take yet.
//! * [`ReportOut`] — what a close did, as `tm close --json` prints it: the
//!   kernel's per-item list (the owner's D3) with document indices read back
//!   to paths, and [`ReportOut::summary`], the human line's counts, **read
//!   off the same list** — the host recomputes nothing about the close.
//!
//! What the kernel's close does not do, and this host therefore no longer
//! does either (each recorded by name in kernel/README.md's stage-4 step-6
//! block, next to the rule it replaces): the day file's `review pending`
//! placeholder (F3, stage 6); a closed week's `closed:` front matter; `est:`
//! = remaining and the day's logged minutes (gap 54); and reopening a week
//! file's `[>]` at a day close (the day row takes lines from day files only).
//! Overdue dated items **do** go into `backlog.md#Overdue` again since the
//! owner's D7 (stage 4 final, kernel/README.md gap 55): the kernel's week close
//! moves a past-due `persist` line there (`moveOverdue`), and a not-yet-due one
//! is demoted keeping its `due:` (D8). Children **are** folded into their
//! parent again since goal B3's repair (stage 4 final step 4): an unfinished
//! child of a line the week close files from the same file is dropped, `[~]` in
//! place (`dropIntoParent`, logged as nothing — the fork point deleted the line
//! and logged nothing), and its own remaining floors the parent's record by
//! §6.4's `max` (`copyFolding`, `copyMergingFolding`).

use chrono::NaiveDate;
use serde::Serialize;

use tm_core::log::Event;
use tm_core::model::{Horizon, Id, IsoWeek, YearMonth};
use tm_core::store::Closed;

use super::ctx::Ctx;
use super::kernel_bridge::{self, CloseDid, Cmd, Grain};
use super::out::{CliError, KernelIssue};

/// The last day that has ended at `today`: yesterday.
pub fn last_day(today: NaiveDate) -> NaiveDate {
    today.pred_opt().unwrap_or(today)
}

/// The last ISO week that has ended at `today`: the one before today's.
pub fn last_week(today: NaiveDate) -> IsoWeek {
    IsoWeek::from_date(today).prev()
}

/// The last calendar month that has ended at `today`: the one before today's.
pub fn last_month(today: NaiveDate) -> YearMonth {
    YearMonth::from_date(today).prev()
}

/// The key of the last period of `grain` that has ended at `today`
/// (`2026-09-06`, `2026-W36`, `2026-08`).
pub fn last_ended_key(grain: Grain, today: NaiveDate) -> String {
    match grain {
        Grain::Day => last_day(today).format("%Y-%m-%d").to_string(),
        Grain::Week => last_week(today).to_string(),
        Grain::Month => last_month(today).to_string(),
    }
}

/// The key of the period of `grain` containing `today` — the one no close
/// can take yet.
pub fn running_key(grain: Grain, today: NaiveDate) -> String {
    match grain {
        Grain::Day => today.format("%Y-%m-%d").to_string(),
        Grain::Week => IsoWeek::from_date(today).to_string(),
        Grain::Month => YearMonth::from_date(today).to_string(),
    }
}

/// Whether `state.closed` is behind the last ended period of any grain —
/// the gate §6.3's "recorded in `state.json`" puts in front of the automatic
/// close, so a command that follows a caught-up one does not call the kernel.
pub fn behind(closed: &Closed, today: NaiveDate) -> bool {
    closed.day.is_none_or(|d| d < last_day(today))
        || closed.week.is_none_or(|w| w < last_week(today))
        || closed.month.is_none_or(|m| m < last_month(today))
}

/// Whether the automatic close must call the kernel: `state.closed` is
/// [`behind`], **or** no kernel `autoClose` has swept the tree since its
/// stamps were last written by a binary that did not know `swept` — the
/// fork-point binary, whose sixteen-period catch-up stamped older periods
/// closed without running them (kernel/README.md stage 4 step 6's table,
/// row 2). Current stamps alone say which periods have ended, not that
/// nothing live is left in them; a successful sweep is what says that
/// (`autoClose_catches_up_in_one_step`), so it is what sets `swept`.
pub fn due(closed: &Closed, today: NaiveDate) -> bool {
    !closed.swept || behind(closed, today)
}

/// Move `state.closed`'s stamp for `grain` up to the last ended period —
/// never back. Returns whether it moved.
fn advance(closed: &mut Closed, grain: Grain, today: NaiveDate) -> bool {
    match grain {
        Grain::Day => {
            let d = last_day(today);
            let moved = closed.day.is_none_or(|c| c < d);
            if moved {
                closed.day = Some(d);
            }
            moved
        }
        Grain::Week => {
            let w = last_week(today);
            let moved = closed.week.is_none_or(|c| c < w);
            if moved {
                closed.week = Some(w);
            }
            moved
        }
        Grain::Month => {
            let m = last_month(today);
            let moved = closed.month.is_none_or(|c| c < m);
            if moved {
                closed.month = Some(m);
            }
            moved
        }
    }
}

/// `--date` on `tm close`: the kernel closes every ended region of the
/// grain, so the flag no longer picks a period — it is kept for the
/// spellings scripts hold, and it must name a period that has ended. A
/// period still running is refused before anything is read: the kernel
/// cannot close it (`closeTo_target_is_open`), and saying `closed` over it
/// would be the silent wrong answer.
pub fn check_date(grain: Grain, date: &str, today: NaiveDate) -> Result<(), CliError> {
    let ended = match grain {
        Grain::Day => tm_core::model::parse_date(date)? <= last_day(today),
        Grain::Week => IsoWeek::parse(date)? <= last_week(today),
        Grain::Month => YearMonth::parse(date)? <= last_month(today),
    };
    if ended {
        Ok(())
    } else {
        Err(CliError::msg(format!(
            "periodNotEnded — `tm close {g} --date {date}`: that {g} has not ended at {today}; \
             a close takes only periods that have ended (the kernel's `Closed`, the owner's D1), \
             and the last {g} that has is {last}",
            g = grain.name(),
            today = today.format("%Y-%m-%d"),
            last = last_ended_key(grain, today),
        )))
    }
}

/// Minutes as the kernel emitted them: an integer pair, never divided here.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct MinOut {
    /// Numerator.
    pub num: u64,
    /// Denominator, positive.
    pub den: u64,
}

/// One line a close acted on — one entry of the kernel's report (D3).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ClosedLine {
    /// The item's id, bare.
    pub id: String,
    /// The grain of the close that took it: `day`, `week` or `month`.
    pub grain: &'static str,
    /// What happened to it, by the kernel's constructor name: `move`,
    /// `moveReopening`, `copy` (a `[-]` left behind and a stamped record
    /// filed forward), `copyMerging` (the same, rewriting the item's standing
    /// `# Demoted` record — kernel/README.md gap 53), `carry` (a wall still
    /// ahead, moved unstamped), `moveOverdue` (past due with `persist`, moved
    /// unstamped to `backlog.md # Overdue` — the owner's D7), `dropIntoParent`
    /// (an unfinished child of a line the week close files: `[~]` in place,
    /// its remaining folded into that line's record), `copyFolding` and
    /// `copyMergingFolding` (the two copies, with that fold's floor on the
    /// record's estimate — goal B3's repair).
    pub did: &'static str,
    /// The file it was taken from.
    pub from: String,
    /// The file it went to.
    pub to: String,
    /// The stamp it gained (`D07`, `W37`), if any.
    pub stamp: Option<String>,
    /// Its estimate in minutes afterwards, as `{num, den}`; `null` when the
    /// line carries no estimate.
    pub min: Option<MinOut>,
}

/// What a close did (`tm close --json`'s `report`).
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
pub struct ReportOut {
    /// The kernel's per-item list, in its fold order.
    pub closes: Vec<ClosedLine>,
    /// The ids `tm close month --drop` dropped (the host's `drop` commands,
    /// which the kernel ran ahead of the close in the same request).
    pub dropped: Vec<String>,
}

/// The human line's counts, each read off the report.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Summary {
    /// Lines that left their file for another: `move`, `moveReopening`,
    /// `carry`, `moveOverdue` — not the copies (`copy`, `copyMerging` and their
    /// `…Folding` forms), which leave a `[-]` behind, and not a child the week
    /// close dropped, which stays where it is.
    pub moved: usize,
    /// Lines that gained a stamp.
    pub demoted: usize,
    /// Walls carried into the live week.
    pub carried: usize,
    /// Lines the request left `[~]`: the `--drop` ids, and the unfinished
    /// children the week close dropped into their parent (`dropIntoParent`,
    /// goal B3's repair). Before kernel/README.md "Stage 4 final, repair"
    /// (defect 4) only the `--drop` ids were counted, so the example week's
    /// close printed `0 dropped` over four tasks it had just made `[~]`.
    pub dropped: usize,
}

impl ReportOut {
    /// The counts of the human line.
    pub fn summary(&self) -> Summary {
        Summary {
            moved: self
                .closes
                .iter()
                .filter(|c| {
                    ![
                        CloseDid::Copy,
                        CloseDid::CopyMerging,
                        CloseDid::CopyFolding,
                        CloseDid::CopyMergingFolding,
                        CloseDid::DropIntoParent,
                    ]
                    .iter()
                    .any(|d| c.did == d.name())
                })
                .count(),
            demoted: self.closes.iter().filter(|c| c.stamp.is_some()).count(),
            carried: self.closes.iter().filter(|c| c.did == CloseDid::Carry.name()).count(),
            dropped: self.dropped.len()
                + self
                    .closes
                    .iter()
                    .filter(|c| c.did == CloseDid::DropIntoParent.name())
                    .count(),
        }
    }

    /// `closed week 2026-W37 · 1 moved · 5 demoted · 1 carried · 4 dropped`.
    pub fn line(&self, period: &str, key: &str) -> String {
        let s = self.summary();
        format!(
            "closed {period} {key} · {} moved · {} demoted · {} carried · {} dropped",
            s.moved, s.demoted, s.carried, s.dropped
        )
    }
}

/// Which close a request carries.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Which {
    /// `tm close <grain>`: that grain's close.
    One(Grain),
    /// The automatic close: every grain once, day then week then month.
    All,
}

/// The period key of a plan path (`day/2026-09-07.md` → `2026-09-07`), the
/// form §10.1's `demote` event carries; any other path as itself.
fn period_key(path: &str) -> String {
    match Horizon::from_path(path) {
        Some(Horizon::Day(d)) => d.format("%Y-%m-%d").to_string(),
        Some(Horizon::Week(w)) => w.to_string(),
        Some(Horizon::Month(m)) => m.to_string(),
        _ => path.to_string(),
    }
}

/// Run one close through the kernel: the `--drop` list first (a dropped
/// line is settled, and no close row takes a settled line), then the close,
/// in **one** request. On success, log what the report names — a `demote`
/// for every stamped entry and a `move` for every entry that left its file,
/// in the kernel's order; a child the week close dropped into its parent
/// (`dropIntoParent`) moved nowhere and logs nothing, as fork-point
/// `close_week` logged nothing for its `dropped_children` — plus a `drop` per
/// `--drop` id and a `close` per grain, advance `state.closed`, and return the
/// report. On a refusal nothing has been written, logged or stamped.
pub fn run(ctx: &mut Ctx, which: Which, drops: &[Id]) -> Result<ReportOut, CliError> {
    let mut cmds: Vec<Cmd> = drops
        .iter()
        .map(|id| Cmd::Drop { id: id.to_string() })
        .collect();
    cmds.push(match which {
        Which::One(grain) => Cmd::Close { grain },
        Which::All => Cmd::AutoClose,
    });
    let applied = kernel_bridge::apply(ctx, &cmds)?;

    let mut report = ReportOut {
        closes: Vec::new(),
        dropped: drops.iter().map(|d| d.to_string()).collect(),
    };
    for id in drops {
        ctx.append_event(Event::Drop { id: id.to_string() })?;
    }
    for e in &applied.closes {
        let (from, to) = (applied.path_of(e.from).to_string(), applied.path_of(e.to).to_string());
        let min = e.minutes.map(|m| MinOut { num: m.num(), den: m.den() });
        if e.did == CloseDid::DropIntoParent {
            // stays in its file, `[~]`; its minutes are in its parent's record
        } else if e.stamp.is_some() {
            ctx.append_event(Event::Demote {
                id: e.id.clone(),
                from: period_key(&from),
                to: period_key(&to),
                est_min: e.minutes.map_or(0, |m| m.whole()),
            })?;
        } else {
            ctx.append_event(Event::Move {
                id: e.id.clone(),
                from: from.clone(),
                to: to.clone(),
            })?;
        }
        report.closes.push(ClosedLine {
            id: e.id.clone(),
            grain: e.grain.name(),
            did: e.did.name(),
            from,
            to,
            stamp: e.stamp.map(|s| s.to_string()),
            min,
        });
    }

    let today = ctx.today;
    let grains = match which {
        Which::One(g) => vec![g],
        Which::All => vec![Grain::Day, Grain::Week, Grain::Month],
    };
    for g in grains {
        // The explicit close always records itself (it is what `tm undo`
        // reopens); the automatic one records a grain only when the report
        // names a line that grain's close took — §10.1 logs what happened,
        // and a close of nothing happened to nothing. A sweep of an
        // upgraded tree can take lines without moving a stamp (see [`due`]),
        // and it happened too, so the stamp's movement does not decide.
        advance(&mut ctx.state.closed, g, today);
        let took = report.closes.iter().any(|c| c.grain == g.name());
        if which != Which::All || took {
            ctx.append_event(Event::Close {
                period: g.name().to_string(),
                key: last_ended_key(g, today),
            })?;
        }
    }
    if which == Which::All {
        // Every ended region of every grain has been closed by the kernel:
        // the stamps are now trustworthy as "nothing live left behind".
        ctx.state.closed.swept = true;
    }
    ctx.save_state()?;
    if applied.docs.iter().any(|d| d.changed) {
        ctx.reload()?;
    }
    Ok(report)
}

/// §6.3's automatic close, run by [`Ctx::load`] ahead of every verb that
/// asks for housekeeping. One kernel call when it is [`due`] — `state.closed`
/// is behind, or no kernel sweep has run since a binary that did not know
/// `swept` wrote the stamps — see the module docs.
///
/// A **refusal** does not fail the verb it runs ahead of: nothing has been
/// written and nothing is stamped closed, so the close is tried again on the
/// next command, and the refusal is printed by name on stderr (except inside
/// the TUI, whose screen stderr would shred). Refusing every verb instead
/// would leave a tree the kernel cannot close unusable except by hand (§4.3's
/// own example week was one, on its open dated `^d1`, until the owner's D7
/// and D8 closed kernel/README.md gap 55). A kernel **fault**, a write
/// conflict or an I/O error still fails the verb.
pub fn auto_close(ctx: &mut Ctx) -> Result<AutoClosed, CliError> {
    if !due(&ctx.state.closed, ctx.today) {
        return Ok(AutoClosed::NotDue);
    }
    match run(ctx, Which::All, &[]) {
        Ok(report) => Ok(AutoClosed::Closed(report)),
        Err(CliError::Kernel(issue)) if !issue.is_fault() => {
            if !kernel_bridge::capturing_kernel_stderr() {
                eprintln!(
                    "tm: the automatic close (§6.3) was refused, so no period was closed and \
                     nothing was written; it runs again on the next command. {}",
                    explain(&issue)
                );
            }
            Ok(AutoClosed::Refused)
        }
        Err(e) => Err(e),
    }
}

/// What [`auto_close`] did, for the housekeeping that runs after it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AutoClosed {
    /// No period has ended since the last close: no kernel call was made.
    NotDue,
    /// The kernel closed what had ended; its report.
    Closed(ReportOut),
    /// The kernel refused the tree by name (printed): nothing was written, and
    /// nothing after it in [`Ctx::load`] may write to that tree either — the
    /// §5.1 waiting timeouts are skipped (kernel/README.md "Stage 4 final,
    /// repair", defect 1).
    Refused,
}

/// A close refusal's message, with what the name most likely means for a
/// close in particular — the two shapes the kernel's week close refuses on
/// real trees are recorded gaps, and saying which one is cheaper than
/// leaving the user to read `Boundary.lean`.
pub fn explain(issue: &KernelIssue) -> String {
    let hint = match issue.name.as_str() {
        "alreadyDemoted" => Some(
            "for a close this is an open line whose item's `[-]` line is not under a month's \
             `# Demoted` — a line with a `# Demoted` record is merged into it (kernel/README.md \
             gap 53), but merging into a `[-]` left in a week file would delete that line; \
             remove one of the two lines by hand",
        ),
        "badHorizon" => Some(
            "for a close this is a rewritten tree the kernel's whole-plan check refuses — a line \
             landing where its file may not hold it; an open dated line in an ended week no \
             longer does this: past due it moves to `backlog.md # Overdue`, otherwise it is \
             demoted keeping its `due:` (the owner's D7 and D8, kernel/README.md gap 55)",
        ),
        "noSection" => Some(
            "for a close this is a line of an ended month under a heading the current month file \
             does not have; the host adds only the month's `# Outcomes` and `# Demoted` and the \
             backlog's `# Overdue` (gap 56)",
        ),
        _ => None,
    };
    match hint {
        Some(h) => format!("{} ({h})", issue.message),
        None => issue.message.clone(),
    }
}

/// [`run`] for the explicit verb: a refusal's message gains [`explain`]'s
/// hint, and keeps its name.
pub fn run_explained(ctx: &mut Ctx, which: Which, drops: &[Id]) -> Result<ReportOut, CliError> {
    run(ctx, which, drops).map_err(|e| match e {
        CliError::Kernel(issue) if !issue.is_fault() => {
            let message = explain(&issue);
            CliError::Kernel(KernelIssue { message, ..issue })
        }
        other => other,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn d(s: &str) -> NaiveDate {
        NaiveDate::parse_from_str(s, "%Y-%m-%d").expect("date")
    }

    #[test]
    fn the_last_ended_periods() {
        // Monday 2026-09-14: Sunday ended, W37 ended, August ended.
        assert_eq!(last_ended_key(Grain::Day, d("2026-09-14")), "2026-09-13");
        assert_eq!(last_ended_key(Grain::Week, d("2026-09-14")), "2026-W37");
        assert_eq!(last_ended_key(Grain::Month, d("2026-09-14")), "2026-08");
        // New year: ISO week 2027-W53 does not exist; 2026-12-28 is W53 of 2026.
        assert_eq!(last_ended_key(Grain::Week, d("2027-01-04")), "2026-W53");
        assert_eq!(last_ended_key(Grain::Month, d("2027-01-01")), "2026-12");
    }

    #[test]
    fn the_gate_is_behind_until_every_grain_is_stamped() {
        let today = d("2026-09-14");
        let mut closed = Closed::default();
        assert!(behind(&closed, today));
        for g in [Grain::Day, Grain::Week, Grain::Month] {
            assert!(advance(&mut closed, g, today));
        }
        assert!(!behind(&closed, today));
        // Current stamps a sweep has not vouched for are still due (a tree
        // the fork-point binary last wrote); once swept, they are not.
        assert!(due(&closed, today));
        closed.swept = true;
        assert!(!due(&closed, today));
        // A period ending makes it due again, swept or not.
        assert!(due(&closed, d("2026-09-15")));
        // Never back.
        assert!(!advance(&mut closed, Grain::Week, d("2026-09-01")));
        assert_eq!(closed.week, Some(IsoWeek::new(2026, 37)));
    }

    #[test]
    fn date_must_name_an_ended_period() {
        let today = d("2026-09-07");
        assert!(check_date(Grain::Day, "2026-09-06", today).is_ok());
        let e = check_date(Grain::Day, "2026-09-07", today).expect_err("today has not ended");
        assert!(e.to_string().contains("periodNotEnded"), "{e}");
        assert!(check_date(Grain::Week, "2026-W36", today).is_ok());
        assert!(check_date(Grain::Week, "2026-W37", today).is_err());
        assert!(check_date(Grain::Month, "2026-08", today).is_ok());
        assert!(check_date(Grain::Month, "2026-09", today).is_err());
    }

    /// The host's "last ended period" is the kernel's `Closed` boundary, not
    /// a second opinion of it: at each instant, a close of each grain takes
    /// the line of the file for the last ended period and leaves the line of
    /// the file for the period containing now.
    #[test]
    fn last_ended_is_the_kernels_closed_boundary() {
        use serde_json::{json, Value};
        for today in ["2026-09-07", "2026-09-13", "2026-09-14", "2026-10-01", "2027-01-04"] {
            let today = d(today);
            for grain in [Grain::Day, Grain::Week, Grain::Month] {
                let (ended, open, section) = match grain {
                    Grain::Day => (
                        Horizon::Day(last_day(today)).path(),
                        Horizon::Day(today).path(),
                        "# Pinned",
                    ),
                    Grain::Week => (
                        Horizon::Week(last_week(today)).path(),
                        Horizon::Week(IsoWeek::from_date(today)).path(),
                        "# Tasks",
                    ),
                    Grain::Month => (
                        Horizon::Month(last_month(today)).path(),
                        Horizon::Month(YearMonth::from_date(today)).path(),
                        "# Outcomes",
                    ),
                };
                let mut docs = Vec::new();
                for (path, id) in [(&ended, "e1"), (&open, "o1")] {
                    let (g, ix) = kernel_bridge::region_of(path).expect("a dated file");
                    docs.push(json!({"path": path, "grain": g, "ix": ix,
                        "lines": [section, format!("- [ ] 3 1b A line ^{id}")]}));
                }
                // The destinations a close of this grain needs.
                let week_now = Horizon::Week(IsoWeek::from_date(today)).path();
                let month_now = Horizon::Month(YearMonth::from_date(today)).path();
                for (path, lines) in [(week_now, json!(["# Tasks"])), (month_now, json!(["# Outcomes", "# Demoted"]))] {
                    if docs.iter().all(|doc| doc["path"] != path.as_str()) {
                        let (g, ix) = kernel_bridge::region_of(&path).expect("dated");
                        docs.push(json!({"path": path, "grain": g, "ix": ix, "lines": lines}));
                    }
                }
                let request = json!({"now": today.format("%Y-%m-%d").to_string(), "blockMin": 60,
                    "docs": docs, "cmds": [{"op": "close", "grain": grain.to_wire()}]});
                let raw = tm_kernel_ffi::call(&request.to_string()).expect("kernel call");
                let resp: Value = serde_json::from_str(&raw).expect("json");
                let ids: Vec<&str> = resp["ok"]["report"]["closes"]
                    .as_array()
                    .unwrap_or_else(|| panic!("{today} {grain:?}: {raw}"))
                    .iter()
                    .filter_map(|e| e["id"].as_str())
                    .collect();
                assert_eq!(ids, vec!["e1"], "{today} {grain:?}: {raw}");
            }
        }
    }

    #[test]
    fn the_summary_is_read_off_the_report() {
        let line = |id: &str, did: CloseDid, stamp: Option<&str>| ClosedLine {
            id: id.into(),
            grain: "week",
            did: did.name(),
            from: "week/2026-W37.md".into(),
            to: "month/2026-09.md".into(),
            stamp: stamp.map(str::to_string),
            min: None,
        };
        let report = ReportOut {
            closes: vec![
                line("p1", CloseDid::MoveReopening, Some("D11")),
                line("x1", CloseDid::Carry, None),
                line("m1", CloseDid::Copy, Some("W37")),
                line("m2", CloseDid::CopyMerging, Some("W37")),
                line("O1", CloseDid::Move, None),
                line("t1", CloseDid::DropIntoParent, None),
                line("m3", CloseDid::CopyFolding, Some("W37")),
            ],
            dropped: vec!["O3".into()],
        };
        // A child dropped into its parent is `dropped`, never `moved`; its
        // parent's folding copy is `demoted`.
        assert_eq!(
            report.summary(),
            Summary { moved: 3, demoted: 4, carried: 1, dropped: 2 }
        );
        assert_eq!(
            report.line("week", "2026-W37"),
            "closed week 2026-W37 · 3 moved · 4 demoted · 1 carried · 2 dropped"
        );
    }
}
