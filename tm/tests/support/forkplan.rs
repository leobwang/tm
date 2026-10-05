//! **The fork's planner as a BACKEND, and the comparand built over any backend**
//! (stage 6 W-39 track H; the owner's D72, README gap 3533).
//!
//! # Why this exists
//!
//! The comparand keyed by class (`support/forkclass.rs`) holds the kernel to "the
//! fork as the shipped binary runs it" (D53) with the registered departures applied
//! by their properties — P45's comparand after a running break, P46, P47, P51, P52,
//! P55, P56. Until W-39 that comparand was built in ONE place, `planner_classes.rs`'
//! fork region, calling the in-tree `tm-core/src/planner.rs` directly — so it could
//! answer only while that file existed, and R3 deleted it. The owner's D72 keeps both
//! kinds of fork comparison past R3: a seeded batch frozen by value (the frozen half),
//! and fresh proptest draws against fork 4748911's planner run OUT of the tree by
//! `tm-oracle plan` (the oracle half).
//!
//! So the comparand is built here, once, over [`ForkPlan`] — anything that plans a day
//! as the shipped binary's fork planned it — and there were two backends until R3:
//!
//! * **the in-tree fork** (InTree, this file's one region, deleted at R3): what the
//!   live checks that the frozen answers were still the in-tree fork's called (and,
//!   until W-45 track C, every bless of a frozen line — README gap 4680: each asks the
//!   oracle now, so none was final at R3);
//! * **the out-of-tree oracle** ([`Oracle`]): fork `4748911` extracted and built by
//!   `kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh`, run as `tm-oracle plan` —
//!   the one backend since R3.
//!
//! [`comparand_answers`] is the ONE definition of the comparand's answers (AGENTS
//! §5.3): the departures are applied to the day's JSON — the frozen lines' own
//! spelling — so the backend is only asked to PLAN, and the frozen lines and the
//! oracle arm cannot apply two different departures. What CAN differ is the two
//! backends' planning, and that is measured only where an oracle has been built
//! (`TM_ORACLE`, D23's shape): the region's cross-check holds the two equal on fresh
//! draws, and `planner_classes.rs`' `the_frozen_lines_are_the_forks_oracle_answer_today`
//! holds the oracle to every frozen line.
//!
//! # What each backend returns, and the one departure that sits between them
//!
//! [`Planned::day`] is the day as the SHIPPED binary's fork draws it — since the owner's
//! D65 the in-tree fork cuts a replayed pause by the day's walls (parity P56) — and
//! [`Planned::fork_day`] is fork 4748911's drawing of the same day, every replayed pause
//! whole, which is what a frozen line's `shipped` holds. The in-tree backend draws the
//! first and reconstructs the second (`as_4748911`, checked by value against `b3c29a3`'s
//! own planner at W-38); the oracle IS fork 4748911 and draws the second, and the first
//! is P56's rule applied by its property ([`p56_cut`]).
//!
//! # What the oracle is fed, and why that is still the fork as the binary ran it
//!
//! Measured at W-39: fork 4748911's `planner::plan` takes NO priorities — its
//! `PlanInput` has no ranking, and its step 4 always runs the fork's own §7 pass over
//! its own lookahead. The shipped binary has fed the fork the KERNEL's ranking since
//! `09d38fa` (stage 5 D10 L8), through two edits that commit made to the fork's day
//! planning and nothing else: the ranking seam (`PlanInput::with_ranking`, step 4 reading
//! the given priorities) and §7.3's IMPOSSIBLE reading the EXACT shortfall (a shortfall
//! of a fraction of a minute is impossible though its floor is 0). `build-oracle.sh`
//! grafts exactly those two onto the extracted fork (`plan-seam.patch`, which fails the
//! build if it does not apply), so the oracle is fork 4748911's planner ranked as the
//! shipped binary ranks it. Everything else the in-tree planner changed since the fork
//! is a refactor that plans the same day (the log handed as its replay, the types moved
//! to `dayplan.rs`, a date read through `planwire::plan_date`, a sum made saturating on
//! sums that fit) or a registered departure (P56, applied here). The oracle reads the
//! world as the fork reads it — its own parser, its own `log::replay` over the same
//! bytes, its own candidate collection — where the binary hands its fork the kernel's
//! replay: T5 holds those two replays equal but for registered numbers the planner does
//! not read, and the cross-check in `planner_invariants.rs`' region holds the two
//! backends' answers equal, value for value, on the fresh draws it is run over while the
//! in-tree fork is here (README gap 3667 says what that leaves).
//!
//! # The fork's OWN reading of the running block, and P81's answer (W-43 track C)
//!
//! P55 and P46 move the running estimate by what the FORK reads as the block's worked minutes
//! (fork `active_run`'s reading). Until W-43 the comparand read that off `Built::worked` — the
//! KERNEL's replay — for every backend. The in-tree fork plans over that same replay, so for it
//! the two were one; fork 4748911 (the oracle) reads its OWN replay, and since the owner's D87
//! the kernel's nets a break the log holds inside the block, which fork 4748911's does not
//! (parity P81). On such a world the oracle was asked with the kernel's minutes and answered
//! another day (README gap 4247), and the land's repair asked it a REORDERED log the kernel
//! happened to read as the fork does — a reading the owner's D92 takes away (README gap 4250).
//! So [`ForkPlan::worked`] is each backend's own reading, and the comparand asks it of the
//! backend it plans with: the oracle answers `tm-oracle plan`'s `worked` op, the in-tree fork
//! the replay it is handed. Since W-44 track C the op is fork 4748911's OWN lines, which
//! `worked-seam.patch` moves out of `active_run` into a method both call — until then the oracle
//! re-typed the selection (README gap 4507) — and [`Oracle::worked`] refuses an oracle that still
//! does. And since W-43 the comparand carries **P81's answer** ([`p81_after`], README gap 4248):
//! on a world whose log holds a break P81 nets, the comparand asked the D87 day, so the frozen
//! lines hold fork 4748911's own answer by value and not P81's rule as a model.

#![allow(dead_code)]

/// Parity P81's reading of a log by fork 4748911's own machine, and the log the fork can be asked
/// P81's day in — `support/p81.rs`, the one definition (W-42 track R), nested here so every suite
/// that builds the comparand reaches it without declaring it.
#[allow(dead_code)]
#[path = "p81.rs"]
mod p81;

/// P85's asked log (`support/p85.rs`, the one definition, W-43 track K), nested here beside P81's
/// for the planner's P85 comparand ([`p85_after`], the W-43 repair, README gap 4367).
#[allow(dead_code)]
#[path = "p85.rs"]
mod p85;

/// FNV-1a-64, the test harness's one definition (`support/fnv.rs`, README gap 4581, W-44 track C):
/// [`day_hash`] digests a serialised day with it, as fork 4748911's `DayPlan::hash` does.
#[allow(dead_code)]
#[path = "fnv.rs"]
mod fnv;

use std::collections::BTreeMap;
use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::Mutex;

use chrono::{DateTime, Duration, FixedOffset, Timelike};
use chrono_tz::Tz;
use serde::Serialize;
use serde_json::{json, Value};

use tm_core::model::Id;
use tm_core::planwire;
use tm_core::priority::Prio;
use tm_core::store::RuntimeState;

use crate::forkclass::{self, Built};
use crate::planreq;

// ---------------------------------------------------------------------------
// The backend
// ---------------------------------------------------------------------------

/// **One call of the fork's planner**: what the shipped binary hands `plan` — a
/// state, an instant, its candidates ranked by the kernel's grants — and the
/// comparand's own variations of it.
pub struct ForkAsk<'a> {
    /// The runtime state planned with (a comparand's state carries P46's or P55's estimate).
    pub state: &'a RuntimeState,
    /// The instant planned at (P45's comparand plans at the break's end).
    pub now: DateTime<Tz>,
    /// Run D60's key in the fork (`forkclass::d60_cands`), or rank the candidates as collected.
    pub d60: bool,
    /// Run D74's split in the fork (parity P64, README gap 3740: §7.5's batches split into
    /// their RUNS, `PlanInput::with_runs`; the oracle's `p64-runs.patch`), or the fork's
    /// group-by. The comparand sets it wherever it sets `d60`; the shipped fork's day never.
    pub p64: bool,
    /// The grants the candidates are ranked by, 1:1 with `Built::cands`.
    pub prios: &'a [Prio],
    /// §9.1's what-if: this many minutes more on this item (fork `PlanOverrides::extending`).
    pub extend: Option<(&'a Id, u32)>,
    /// A line appended to the log before the fork replays it (P45's comparand logs the
    /// break it plans after).
    pub log_line: Option<String>,
}

/// **The fork's answer to one [`ForkAsk`]**, as the frozen lines spell a day.
#[derive(Clone, Debug, PartialEq)]
pub struct Planned {
    /// The day as the shipped binary's fork draws it: a serialised `DayPlan`, P56's
    /// cut applied (D65).
    pub day: Value,
    /// Fork 4748911's drawing of the same day: every replayed pause whole.
    pub fork_day: Value,
    /// The candidates in the fork's §7.4 order (`sorted_candidates`), by id.
    pub ranked: Vec<String>,
}

/// **Anything that plans a day as the shipped binary's fork plans it.**
pub trait ForkPlan {
    /// The fork's day for `ask` over the world `b`.
    fn plan(&self, b: &Built, ask: &ForkAsk<'_>) -> Result<Planned, String>;
    /// **The running block's worked minutes as THIS fork reads them** for the state `st` at the
    /// world's `now` (fork `active_run`'s reading: the log's open block when it is `st`'s running
    /// item, the clock since `started` otherwise; `None` with no block running) — what P55 and
    /// P46 move the estimate by (W-43 track C, README gap 4247): the in-tree fork reads the replay
    /// it is handed (the kernel's), the oracle its own.
    fn worked(&self, b: &Built, st: &RuntimeState) -> Result<Option<u32>, String>;
    /// Fork `planner::diff` of two serialised days: `{moved, added, removed, drift_min}`.
    fn diff(&self, tz: Tz, old: &Value, new: &Value) -> Result<Value, String>;
}

// ---------------------------------------------------------------------------
// The day's JSON
// ---------------------------------------------------------------------------

/// An instant as a frozen day spells it.
pub fn at(v: &Value) -> Option<DateTime<FixedOffset>> {
    DateTime::parse_from_rfc3339(v.as_str()?).ok()
}

fn segments_of(day: &Value) -> &[Value] {
    day["segments"].as_array().map(Vec::as_slice).unwrap_or_default()
}

fn segments_mut(day: &mut Value) -> Option<&mut Vec<Value>> {
    day.get_mut("segments").and_then(Value::as_array_mut)
}

/// **`DayPlan::hash` of a serialised day** — the FNV-1a digest of the rows' eight
/// `Placement` fields in their declared order, each carried as the value the day
/// holds, so the digest of a day the comparand bent on its JSON (P46's row, P47's
/// clip) is the digest of the bent day. `the_hash_of_every_frozen_day_is_its_digest`
/// holds it to the digest every frozen line was written with. The digest is the
/// harness's one FNV-1a-64 (`support/fnv.rs`, README gap 4581), no longer a fold of its own.
pub fn day_hash(day: &Value) -> String {
    #[derive(Serialize)]
    struct Placement<'a> {
        start: &'a Value,
        end: &'a Value,
        kind: &'a Value,
        energy: &'a Value,
        item: &'a Value,
        instance: &'a Value,
        planned_min: &'a Value,
        multiplier: &'a Value,
    }
    let placement: Vec<Placement<'_>> = segments_of(day)
        .iter()
        .map(|s| Placement {
            start: &s["start"],
            end: &s["end"],
            kind: &s["kind"],
            energy: &s["energy"],
            item: &s["item"],
            instance: &s["instance"],
            planned_min: &s["flags"]["planned_min"],
            multiplier: &s["flags"]["multiplier"],
        })
        .collect();
    let body = serde_json::to_string(&placement).expect("a placement serialises");
    fnv::fnv1a64_hex(body.as_bytes())
}

/// A serialised day and its digest — the shape a frozen line's `day` and `shipped` carry.
pub fn frozen_day_json(day: &Value) -> Value {
    json!({"hash": day_hash(day), "day": day})
}

/// **P46's row, by its property** (planner_invariants' w35_p46_row, in the fork region R3 deleted): the running
/// block's reservation — a Block row marked current, with no slot energy, from `now` —
/// carries the fork's own saturating `left`, 0 in overtime.
pub fn p46_row(now: DateTime<Tz>, day: &mut Value) {
    let now = now.fixed_offset();
    for s in segments_mut(day).into_iter().flatten() {
        if s["kind"] == "block" && s["flags"]["current"] == true && s["energy"].is_null() && at(&s["start"]) == Some(now) {
            s["flags"]["planned_min"] = json!(0);
            s["flags"]["note"] = json!("running · 0m left");
        }
    }
}

/// **P47, by its property** (w35_p47_day over w35_pause_open_rows, in the fork region R3 deleted): a wall whose
/// rows span `now` pauses the open row — no `▶`, clipped at the first of those walls'
/// rows that starts after it. Whether the rule fired.
pub fn p47_pause(now: DateTime<Tz>, day: &mut Value) -> bool {
    let now = now.fixed_offset();
    let segs = segments_of(day);
    let mut spans: BTreeMap<String, (DateTime<FixedOffset>, DateTime<FixedOffset>)> = BTreeMap::new();
    for s in segs.iter().filter(|s| s["kind"] == "wall") {
        let (Some(a), Some(z)) = (at(&s["start"]), at(&s["end"])) else { continue };
        let id = s["item"].as_str().unwrap_or_default().to_string();
        let e = spans.entry(id).or_insert((a, z));
        e.0 = e.0.min(a);
        e.1 = e.1.max(z);
    }
    let on_now: Vec<(DateTime<FixedOffset>, Value)> = segs
        .iter()
        .filter(|s| s["kind"] == "wall")
        .filter(|s| spans.get(s["item"].as_str().unwrap_or_default()).is_some_and(|(a, z)| *a <= now && now < *z))
        .filter_map(|s| at(&s["start"]).map(|a| (a, s["start"].clone())))
        .collect();
    if on_now.is_empty() {
        return false;
    }
    let mut hit = false;
    for s in segments_mut(day).into_iter().flatten() {
        if !(s["kind"] == "block" && s["flags"]["open"] == true) {
            continue;
        }
        hit = true;
        s["flags"]["current"] = json!(false);
        let start = at(&s["start"]);
        let cut = on_now.iter().filter(|(a, _)| start.is_some_and(|st| *a > st)).min_by_key(|(a, _)| *a);
        if let Some((a, v)) = cut {
            if at(&s["end"]).is_some_and(|e| *a < e) {
                s["end"] = v.clone();
            }
        }
    }
    hit
}

/// **P55's note, by its property** (`w36_fork_plan`'s): the running block's open row
/// carries the host's worked minutes.
pub fn p55_note(day: &mut Value, running: &str, host: u32) {
    for s in segments_mut(day).into_iter().flatten() {
        if s["kind"] == "block" && s["flags"]["open"] == true && s["item"] == running {
            s["flags"]["note"] = json!(format!("{host}m so far"));
        }
    }
}

/// `[a, b)` with every span cut out — fork `past_segments`' `cut_out` since D65, the
/// kernel's `Planner.cutAll`: the pieces left, ascending, never empty.
pub fn cut_out(
    spans: &[(DateTime<Tz>, DateTime<Tz>)],
    a: DateTime<FixedOffset>,
    b: DateTime<FixedOffset>,
) -> Vec<(DateTime<FixedOffset>, DateTime<FixedOffset>)> {
    let mut pieces = vec![(a, b)];
    for (lo, hi) in spans {
        let (lo, hi) = (lo.fixed_offset(), hi.fixed_offset());
        if hi <= lo {
            continue;
        }
        pieces = pieces
            .into_iter()
            .flat_map(|(x, y)| {
                let mut left = Vec::new();
                if x < y.min(lo) {
                    left.push((x, y.min(lo)));
                }
                if x.max(hi) < y {
                    left.push((x.max(hi), y));
                }
                left
            })
            .collect();
    }
    pieces
}

/// **P56, by its property, on fork 4748911's drawing** (the owner's D65; parity P56):
/// the part of a replayed pause — a Lost row noted `paused`, naming the block — that a
/// calendar wall's blocked span covers is not drawn. The pieces take the row's place
/// ahead of every other row at one `(start, end)`, as the in-tree fork's stable sort
/// puts its replayed past first; `forkplan`'s cross-check holds the result to the
/// in-tree fork's own drawing on every fresh draw while both exist.
pub fn p56_cut(tz: Tz, day: &mut Value, walls: &[(DateTime<Tz>, DateTime<Tz>)]) {
    let Some(segs) = segments_mut(day) else { return };
    let paused = |s: &Value| s["kind"] == "lost" && s["flags"]["note"] == "paused" && !s["item"].is_null();
    let mut pieces: Vec<Value> = Vec::new();
    for s in segs.iter().filter(|s| paused(s)) {
        let (Some(a), Some(b)) = (at(&s["start"]), at(&s["end"])) else { continue };
        for (x, y) in cut_out(walls, a, b) {
            let mut p = s.clone();
            p["start"] = serde_json::to_value(x.with_timezone(&tz)).expect("an instant serialises");
            p["end"] = serde_json::to_value(y.with_timezone(&tz)).expect("an instant serialises");
            pieces.push(p);
        }
    }
    let rest: Vec<Value> = segs.iter().filter(|s| !paused(s)).cloned().collect();
    let mut out: Vec<Value> = pieces.into_iter().chain(rest).collect();
    out.sort_by(|x, y| (at(&x["start"]), at(&x["end"])).cmp(&(at(&y["start"]), at(&y["end"]))));
    *segs = out;
}

// ---------------------------------------------------------------------------
// The comparand's departures, by their properties
// ---------------------------------------------------------------------------

/// **The running block's LOGGED start** — the instant of its own `start` line, where the log holds
/// the block the cache runs open (`Replay::open_block`); `None` otherwise.
pub fn logged_start(b: &Built) -> Option<DateTime<Tz>> {
    let a = b.world.state.active.as_ref()?;
    b.replay.open_block.as_ref().filter(|o| o.id == a.id.as_str()).map(|o| o.started.with_timezone(&b.cfg.tz))
}

/// **P69's comparand state — a start fork 4748911 CAN be asked** (the owner's D89, W-42 track C;
/// README gaps 4133 and 4282). Fork 4748911 puts `.tm/state.json`'s bare `HH:MM` on the plan's
/// date, so it cannot be handed the LOGGED start of a block begun before midnight (parity P69).
/// But it reads `started` in two places only, both in `active_run`: the worked minutes, which it
/// takes from the log's open block whenever the log holds this item's (the clock is its fallback),
/// and `current_block_end`, which is `started` plus whole blocks — so once `started ≤ now` it
/// reads `started` only modulo `block_min`. A start ON THE PLAN'S DATE at one of the logged
/// start's block boundaries, at or before `now`, is therefore a state the fork can be asked whose
/// running block ends where the kernel's — the logged start's first boundary after `now` — does.
/// This is the earliest such boundary at or after the plan's local midnight, spelled as the
/// `HH:MM` the cache holds.
///
/// `None` where P69 does not depart (the cache's clock on the plan's date IS the logged start),
/// where the log holds no open block for the running item (both sides then read the cache's clock on
/// the plan's date: `planwire::state_json`), and where the transformation cannot reach — no boundary on the plan's date at
/// or before `now`, a logged start with seconds (an `HH:MM` cannot carry them: README gap 4134's
/// worlds), or a local clock the zone skips or repeats. Those worlds are held by P69's property
/// ([`p69_day_unmet`]) alone, said rather than forced.
pub fn p69_state(b: &Built, st: &RuntimeState) -> Option<RuntimeState> {
    let a = st.active.as_ref()?;
    let logged = logged_start(b)?;
    let (tz, date) = (b.cfg.tz, b.date());
    if tm_core::capacity::local_dt(tz, date, a.started) == logged {
        return None;
    }
    let bm = i64::from(b.cfg.block_min()) * 60;
    if bm <= 0 {
        return None;
    }
    let (midnight, _) = b.day_bounds();
    let behind = (midnight - logged).num_seconds();
    let blocks = if behind <= 0 { 0 } else { (behind + bm - 1) / bm };
    let at = logged + Duration::seconds(blocks * bm);
    if at > b.world.now || at.second() != 0 || at.nanosecond() != 0 {
        return None;
    }
    let clock = at.time();
    if tm_core::capacity::local_dt(tz, date, clock) != at {
        return None;
    }
    let mut out = st.clone();
    out.active.as_mut()?.started = clock;
    Some(out)
}

/// **P69, by its property, on the kernel's day `k`** (README gaps 3964 and 4090): a running record's
/// start is read from the LOG (parity P69), where fork 4748911 put `.tm/state.json`'s bare `HH:MM` on
/// the plan's date — so no fork input carries P69, and the kernel is held to its property against
/// the fork's own day `fork` (fork 4748911's, by value): the date, window, budget and grants (the
/// ranking the fork was handed) by value; the fixed frame — walls, wind-down, sleep — by value; ONE
/// running row, the block's, from `now` to the first block boundary of the logged start after `now`
/// (`logged` plus the blocks begun since, as fork `current_block_end` counts them); and no such row
/// in `fork`, so P69 departs on the world. Empty when it holds.
pub fn p69_day_unmet(who: &str, fork: &Value, b: &Built, logged: DateTime<Tz>, k: &planwire::KernelDay) -> Vec<String> {
    let now = b.world.now;
    let mut out = Vec::new();
    let Some(a) = b.world.state.active.as_ref() else { return vec![format!("{who}: no running block")] };
    let kv = serde_json::to_value(&k.day).expect("the kernel's day serialises");
    for key in ["date", "window", "budget_blocks", "priorities"] {
        if kv[key] != fork[key] {
            out.push(format!("{who}: {key}: kernel {} fork {}", kv[key], fork[key]));
        }
    }
    let frame = |day: &Value| -> Vec<Value> {
        segments_of(day).iter().filter(|r| matches!(r["kind"].as_str(), Some("wall" | "winddown" | "sleep"))).cloned().collect()
    };
    if frame(&kv) != frame(fork) {
        out.push(format!("{who}: the fixed frame (walls, wind-down, sleep) moved: kernel {} fork {}", Value::Array(frame(&kv)), Value::Array(frame(fork))));
    }
    let bm = i64::from(b.cfg.block_min());
    let boundary = logged + Duration::minutes(((now - logged).num_minutes() / bm + 1) * bm);
    let span = |r: &Value| (at(&r["start"]), at(&r["end"]));
    let is_p69_row = |r: &Value| {
        r["kind"] == "block" && r["item"] == a.id.as_str() && span(r) == (Some(now.fixed_offset()), Some(boundary.fixed_offset()))
    };
    let running: Vec<&Value> = segments_of(&kv).iter().filter(|r| r["flags"]["current"] == true).collect();
    if running.len() != 1 || !is_p69_row(running[0]) {
        out.push(format!("{who}: the kernel's running row is not the block's from now to {boundary}, the logged start's boundary: {running:?}"));
    }
    if segments_of(fork).iter().any(|r| r["flags"]["current"] == true && is_p69_row(r)) {
        out.push(format!("{who}: fork 4748911's day already holds the logged start's row — P69 departs nowhere on it"));
    }
    out
}

/// **P55, by its property** (`planner_invariants`' `w36_fork_plan`): where the host's
/// worked minutes and the fork's reading of the log differ on a day with no running
/// break, the running estimate moves by their difference — so the FORK computes `left`
/// from the host's reading — and the open row carries the host's minutes. `None` where
/// the readings agree. The fork's reading here is the KERNEL's replay (`Built::worked_for`),
/// the in-tree fork's; the comparand asks [`p55_state_at`] with its backend's own.
pub fn p55_state(b: &Built, st: &RuntimeState) -> Option<(RuntimeState, u32)> {
    p55_state_at(b, st, b.worked_for(st))
}

/// [`p55_state`] over a given reading of the fork's worked minutes, `fork` ([`ForkPlan::worked`]).
pub fn p55_state_at(b: &Built, st: &RuntimeState, fork: Option<u32>) -> Option<(RuntimeState, u32)> {
    let host = forkclass::host_worked(b)?;
    let fork = fork?;
    let breaking = st.break_.as_ref().is_some_and(|x| x.started.is_some());
    if breaking || host == fork {
        return None;
    }
    let mut out = st.clone();
    if let Some(a) = out.active.as_mut() {
        a.est_min = fork.saturating_add(a.est_min.saturating_sub(host));
    }
    Some((out, host))
}

/// **P46, by its property** — `planner_invariants`' `w35_is_p46`: a running block, not
/// paused, no break running, its worked minutes at or past its estimate (fork
/// `active_run`'s `left == 0` refusal).
pub fn is_p46(b: &Built, st: &RuntimeState) -> bool {
    is_p46_at(st, b.worked_for(st))
}

/// [`is_p46`] over a given reading of the fork's worked minutes ([`ForkPlan::worked`]).
pub fn is_p46_at(st: &RuntimeState, worked: Option<u32>) -> bool {
    let Some(a) = st.active.as_ref() else { return false };
    let worked = worked.unwrap_or(0);
    let breaking = st.break_.as_ref().is_some_and(|x| x.started.is_some());
    !a.paused && !breaking && worked >= a.est_min
}

/// P46's comparand state — `w35_p46_state`: the estimate raised by a whole day, so the
/// fork reserves the block from its own walls, wind-down and block boundary; unchanged
/// off P46.
pub fn p46_state(b: &Built, st: &RuntimeState) -> RuntimeState {
    p46_state_at(st, b.worked_for(st))
}

/// [`p46_state`] over a given reading of the fork's worked minutes ([`ForkPlan::worked`]).
pub fn p46_state_at(st: &RuntimeState, worked: Option<u32>) -> RuntimeState {
    let mut out = st.clone();
    if is_p46_at(st, worked) {
        if let Some(a) = out.active.as_mut() {
            a.est_min = worked.unwrap_or(0).saturating_add(24 * 60);
        }
    }
    out
}

/// **The kernel's grants for the GROWN request** (parity P52): the request with the
/// running candidate's record carrying the host's grown `remaining` and `plannedMin`
/// (`Planner.PlanReq.growing`'s rewrite), read by the binary's reader — how the kernel
/// ranks the what-if's day. `None` when the extension grows nothing.
pub fn grown_prios(b: &Built) -> Option<Vec<Prio>> {
    let id = forkclass::whatif_item(&b.world.state)?;
    let g = b.cands.iter().find(|c| c.id == *id).and_then(|c| planwire::grown(c, None, b.cfg.block_min(), &b.cfg))?;
    let pw = b.request_world();
    let (mut req, order) = planreq::request(&pw, None);
    for it in req["capacity"]["candidates"]["items"].as_array_mut()?.iter_mut().filter(|it| it["id"] == id.as_str()) {
        it["remaining"] = json!(g.remaining_min);
        it["plan"]["plannedMin"] = json!(g.planned_min);
    }
    let resp = planreq::call(&req);
    planreq::kernel_day_of(&resp, &pw, &order).ok().map(|(_, ans)| ans.prios)
}

/// **R3's request with its capacity section's location replaced** (README gaps 3861 and 3964):
/// `forkclass::kernel_answer_with_grants`' request — the harness's sections, the host's worked
/// minutes and §9.1's what-if — with `capacity.state.loc` set to `loc` when given. The request
/// and the order its candidates were sent in. (W-40 track H's probe of gap 3861, moved here at
/// W-41 so the TUI days and the start days ask through one definition.)
pub fn request_with_loc(b: &Built, loc: Option<&str>) -> (Value, Vec<usize>) {
    let pw = b.request_world();
    let (mut req, order) = planreq::request(&pw, forkclass::whatif_json(b));
    if let Some(worked) = forkclass::host_worked(b) {
        planwire::add_worked_min(&mut req["planner"], worked);
    }
    if let Some(l) = loc {
        req["capacity"]["state"]["loc"] = json!(l);
    }
    (req, order)
}

/// The kernel's day for [`request_with_loc`]'s request with `loc` sent.
pub fn kernel_day_with_loc(b: &Built, loc: &str) -> Result<planwire::KernelDay, String> {
    let (req, order) = request_with_loc(b, Some(loc));
    let resp = planreq::call(&req);
    planreq::kernel_day_of(&resp, &b.request_world(), &order).map(|(k, _)| k)
}

/// **The grants the SHIPPED binary ranks the fork's candidates by** (D53): the kernel's answer to
/// the capacity request with no `planner` section, which is what `kernel_capacity::rank` sends
/// (`tui_common::app_of_world` builds its app over the same) — so a world whose planner section
/// the kernel refuses (parity P68's) still has its shipped fork's day. `loc` as
/// [`request_with_loc`]'s.
pub fn capacity_grants(b: &Built, loc: Option<&str>) -> Result<Vec<Prio>, String> {
    let (mut req, order) = request_with_loc(b, loc);
    req.as_object_mut().ok_or("a request is an object")?.remove("planner");
    let resp = planreq::call(&req);
    planwire::read_capacity_answer(&resp, &order, true).map(|a| a.prios).map_err(|e| format!("capacity: {e}: {}", resp["err"]))
}

/// **P45's comparand after the running break** (README gap 3207): the fork planned
/// where the kernel's P45 restarts the cut — at the break's end (or `now`, once it has
/// overrun) — D60's key and the kernel's ranking, as the comparand runs them, the break read
/// as P45's register row reads it: a REST of the cut, which resets the fork's break counter
/// (the fork resets it at a LOGGED break) only once it has run `break_min` — so the break is
/// logged ending there exactly when it has. Its rows from that instant are the fork's own
/// assignment, rests and kept breaks over its own cut. `None` on a day with no running break.
/// What it does not model, measured and left to P45's owner (README gap 3480):
/// `Look.restfulEnd` also asked that the break END where a free stretch begins.
///
/// **P67 is not this transformation** (W-41 track H, README gap 3958): the owner's D77 made the
/// kernel's running break reset the cut's counter at ANY length, wherever it ends, and that is
/// [`p67_after`] — a departure of its own, under its own flag and home. From W-40 track P until
/// W-41 this function logged the break at any length, so six frozen lines held P67's answer
/// under P45's flag; they were re-blessed back to this rule (by value, `a5dc490^`'s) and given
/// P67's answer beside it.
pub fn p45_after(b: &Built, prios: &[Prio], fp: &dyn ForkPlan) -> Result<Option<Value>, String> {
    after_break(b, prios, fp, true).map(|(p45, _)| p45)
}

/// **P45's and P67's answers after the running break, together**, with D74's split chosen
/// (`runs`, parity P64: the comparand's own is `true`; [`comparand_answers`] asks `false` once,
/// to see whether P64 moved the comparand). `p67` is `None` where it would be `p45`'s rows.
fn after_break(b: &Built, prios: &[Prio], fp: &dyn ForkPlan, runs: bool) -> Result<(Option<Value>, Option<Value>), String> {
    let Some(p45) = p45_rows_with(b, prios, fp, None, runs)? else { return Ok((None, None)) };
    let p67 = p45_rows_with(b, prios, fp, Some(true), runs)?.filter(|z| *z != p45);
    Ok((
        Some(json!({"p45": true, "from": p45.0, "rows": p45.1})),
        p67.map(|(from, rows)| json!({"p67": true, "from": from, "rows": rows})),
    ))
}

/// **P67's comparand after the running break** (the owner's D77; parity P67, README gaps 3480,
/// 3666 and 3958): [`p45_after`]'s fork with the break LOGGED ending where the cut restarts
/// whatever its length — the kernel's running break resets the cut's counter exactly as the
/// same break once `tm break` has logged it (`Planner.PlanReq.sinceBreak`), and is no longer a
/// rest of the cut. **Present only where P67 DEPARTS from P45** — the two readings plan
/// different rows from that instant, which takes a break shorter than `break_min` — as `p52`
/// is present only where it is not `full`: where it is absent, the line's `p45` IS P67's
/// comparand too, and `forkclass::compare_line` holds the kernel to whichever the line carries,
/// `p67` first. `{"p67": true, "from", "rows"}`, its flag in its home.
pub fn p67_after(b: &Built, prios: &[Prio], fp: &dyn ForkPlan) -> Result<Option<Value>, String> {
    after_break(b, prios, fp, true).map(|(_, p67)| p67)
}

/// **The fork's rows after the running break, with the break's `log_line` chosen** — `None`:
/// P45's own rule, the break logged once it has run `break_min` ([`p45_after`]); `Some(true)`:
/// logged at any length, P67's ([`p67_after`]); `Some(false)`: left unlogged. README gap 3480's
/// readings of one span. `(from, rows)`, `None` on a day with no running break.
pub fn p45_rows(b: &Built, prios: &[Prio], fp: &dyn ForkPlan, logged: Option<bool>) -> Result<Option<(String, Vec<Value>)>, String> {
    p45_rows_with(b, prios, fp, logged, true)
}

fn p45_rows_with(
    b: &Built,
    prios: &[Prio],
    fp: &dyn ForkPlan,
    logged: Option<bool>,
    runs: bool,
) -> Result<Option<(String, Vec<Value>)>, String> {
    // The comparand plans from P69's start wherever it does (`comparand_with`, the owner's D89).
    let p69 = p69_state(b, &b.world.state);
    let st = p69.as_ref().unwrap_or(&b.world.state);
    let Some(brk) = st.break_.as_ref().filter(|x| x.started.is_some()) else { return Ok(None) };
    let tz = b.cfg.tz;
    // The kernel's reading of the running break's start — the binary's (P73,
    // `BreakState::started_at`), as the transformation stands for the kernel's departure
    // (the W-41 repair, README gap 4143).
    let Some(t) = brk.started_at(tz, b.world.now) else { return Ok(None) };
    let (_, day_end) = b.day_bounds();
    let e = (t + Duration::minutes(i64::from(brk.planned_min))).min(day_end).max(b.world.now);
    let taken = (e - t).num_minutes();
    // P45 reads the break as a rest of the cut, logged once it has run `break_min`; P67 (D77)
    // logs it at any length, and asks `Some(true)` (README gap 3958).
    let log_line = logged.unwrap_or(taken >= i64::from(b.cfg.day.break_min)).then(|| {
        format!(
            "{{\"t\":\"{}\",\"ev\":\"break\",\"planned_min\":{},\"actual_min\":{taken}}}\n",
            t.to_rfc3339(),
            brk.planned_min
        )
    });
    let p = fp.plan(b, &ForkAsk { state: st, now: e, d60: true, p64: runs, prios, extend: None, log_line })?;
    let e_fixed = e.fixed_offset();
    let rows: Vec<Value> = segments_of(&p.day).iter().filter(|s| at(&s["start"]).is_some_and(|a| a >= e_fixed)).cloned().collect();
    Ok(Some((e.to_rfc3339(), rows)))
}


/// **The fork's answers for one stored world** — the ONE definition of what a frozen line
/// holds beside its world (`forkclass::ANSWERS`): the shipped day, the comparand (D57's
/// P46/P47 and D60's P51 applied by their properties, P55's host minutes, P56's drawing)
/// with its flags, on a running-block day the what-ifs, and on a break day P45's
/// comparand after the break — over the kernel's grants `prios`, with `fp` planning.
///
/// **Since the W-40 land step the comparand runs D74's split in the fork** (parity P64, README
/// gap 3740): every comparand plan asks `p64` (`PlanInput::with_runs`, the oracle's
/// `p64-runs.patch`) exactly where it asks `d60`, and the shipped fork's day never does. Where
/// the runs MOVE an answer — the same world planned with the fork's group-by gives a different
/// `day`, `whatif` or `p45` — the line carries `p64: {"p64": true}`, the flag D64's gate reads
/// (`forkclass::d64_allows`), as `d60: {"p51": …}` is P51's.
///
/// **Since the owner's D89 (W-42 track C, README gaps 4133 and 4282) the comparand carries P69**:
/// where the kernel reads a running block's start off the log and [`p69_state`] reaches the
/// world, the comparand, its what-if and the rows after a running break plan from that start —
/// P55's and P46's states composed over it as everywhere — and the line carries `p69:
/// {"p69": true}`; the shipped day never does.
pub fn comparand_answers(b: &Built, prios: &[Prio], fp: &dyn ForkPlan) -> Result<Value, String> {
    let mut with = comparand_with(b, prios, fp, true)?;
    let without = comparand_with(b, prios, fp, false)?;
    let p64 = ["day", "whatif", "p45", "p67", "p81"].iter().any(|k| with[*k] != without[*k]);
    if p64 {
        with["p64"] = json!({"p64": true});
    }
    Ok(with)
}

/// The comparand's answers with D74's split chosen: `runs = true` is the comparand.
fn comparand_with(b: &Built, prios: &[Prio], fp: &dyn ForkPlan, runs: bool) -> Result<Value, String> {
    let st = &b.world.state;
    let now = b.world.now;
    let tz = b.cfg.tz;
    // The SHIPPED fork's day is fork 4748911's (P56: the in-tree fork was changed to agree
    // with the kernel's drawing of a meeting's pause at W-37 track T).
    let shipped_p = fp.plan(b, &ForkAsk { state: st, now, d60: false, p64: false, prios, extend: None, log_line: None })?;
    let shipped = shipped_p.fork_day.clone();
    let p56 = shipped != shipped_p.day;
    // P69 (the owner's D89): where the kernel reads the running block's start off the log and
    // the fork can be asked with a start on the plan's date at one of its boundaries, the
    // comparand — and its what-if — plan from THAT start (`p69_state`); the shipped day never.
    let p69 = p69_state(b, st);
    let st = p69.as_ref().unwrap_or(st);
    // The running block's worked minutes as THIS backend's fork reads them (W-43 track C, README
    // gap 4247): what P55 and P46 move the estimate by. One reading serves every state below —
    // they differ from `st` in the estimate alone, which no reading reads.
    let fork_worked = fp.worked(b, st)?;
    // P55: on a day whose host reading of the running block's worked minutes is not the
    // fork's, the comparand reads the host's (`p55_state_at`).
    let p55 = p55_state_at(b, st, fork_worked);
    let st1 = p55.as_ref().map_or_else(|| st.clone(), |(s, _)| s.clone());
    let st2 = p46_state_at(&st1, fork_worked);
    let comparand_p = fp.plan(b, &ForkAsk { state: &st2, now, d60: true, p64: runs, prios, extend: None, log_line: None })?;
    // P51: D60's key moved the fork's §7.4 order (`forkclass::is_p51`'s reading).
    let p51 = comparand_p.ranked != shipped_p.ranked;
    let mut comparand = comparand_p.day;
    let p46 = is_p46_at(&st1, fork_worked);
    if p46 {
        p46_row(now, &mut comparand);
    }
    let p47 = p47_pause(now, &mut comparand);
    if let Some((_, host)) = p55 {
        if let Some(a) = st.active.as_ref() {
            p55_note(&mut comparand, a.id.as_str(), host);
        }
    }
    let mut whatif = None;
    if let Some(id) = forkclass::whatif_item(st) {
        let bm = b.cfg.block_min();
        let mut rt = st.clone();
        if let Some(x) = rt.active.as_mut() {
            x.est_min = x.est_min.saturating_add(bm);
        }
        // P55 moves the GROWN estimate (the host's `left` is `est + block − host`): moved
        // before the block is added, the saturation at an overtime `est − host` would give
        // the fork a whole block where the kernel reads what is left of it (found by the
        // frozen `overtime/spent (worked)` line, W-38).
        let rt = p55_state_at(b, &rt, fork_worked).map_or(rt, |(s, _)| s);
        let rt = p46_state_at(&rt, fork_worked);
        let whatif_day = |ps: &[Prio], full: bool| -> Result<Value, String> {
            let ask = ForkAsk { state: &rt, now, d60: true, p64: runs, prios: ps, extend: full.then_some((id, bm)), log_line: None };
            let mut d = fp.plan(b, &ask)?.day;
            p47_pause(now, &mut d);
            fp.diff(tz, &comparand, &d)
        };
        let full = whatif_day(prios, true)?;
        // P52: the fork's full what-if ranked as the kernel ranks the GROWN request, kept
        // only where it is not the shipped TUI's (`full`).
        let grown = match grown_prios(b) {
            Some(pg) => Some(whatif_day(&pg, true)?).filter(|g| *g != full),
            None => None,
        };
        let mut w = json!({"est": whatif_day(prios, false)?, "full": full});
        if let Some(g) = grown {
            w["grown"] = g;
        }
        whatif = Some(w);
    }
    let p52 = whatif.as_ref().is_some_and(|w| !w["grown"].is_null());
    let (p45, p67) = after_break(b, prios, fp, runs)?;
    let p81 = p81_after(b, prios, fp, runs)?;
    let flag = |set: bool, n: &str| {
        set.then(|| Value::Object(std::iter::once((n.to_string(), Value::Bool(true))).collect()))
    };
    Ok(json!({
        "day": frozen_day_json(&comparand),
        "shipped": (shipped != comparand).then(|| frozen_day_json(&shipped)),
        "d57": {"p46": p46, "p47": p47},
        "d60": {"p51": p51},
        "whatif": whatif,
        "p45": p45,
        "p67": p67,
        "p52": flag(p52, "p52"),
        "p55": flag(p55.is_some(), "p55"),
        "p56": flag(p56, "p56"),
        "p69": flag(p69.is_some(), "p69"),
        "p81": p81,
    }))
}

/// **P81's comparand** (the owner's D87, parity P81; W-43 track C, README gap 4248): on a world
/// whose log holds a break P81 nets — read off the log by fork 4748911's own machine
/// (`p81::netted_breaks`), never off the kernel's answer — the comparand asked the D87 day: the
/// world with each netted break given as a `pause` at its start and an `unpause` where the clock
/// restarts (`p81::as_d87_asks`), which fork 4748911's machine nets as the kernel's replay nets the
/// break, with this comparand's own departures and D74's split as asked (`runs`); its `paused` row
/// over each netted span drawn as the break alone (one span, one row, as D65 draws a meeting's
/// pause as the wall) and the day re-digested. `{"p81": true, "hash", "day"}`, the flag in its
/// own home; `None` where P81 nets nothing.
///
/// Until W-43 the frozen lines held P81 by its RULE (`p81::planned_day` on the frozen `day`) and
/// only the in-tree region asked the fork the D87 day (README gap 4248); this is that answer,
/// frozen, from whichever backend plans. Refused by name, never guessed: a D87-asked log P81
/// would still net (it would ask a different day), and a netted span the asked day draws no
/// `paused` row over, inside the day and before `now`.
pub fn p81_after(b: &Built, prios: &[Prio], fp: &dyn ForkPlan, runs: bool) -> Result<Option<Value>, String> {
    let netted = p81::netted_breaks(&b.world.log, &[])?;
    if netted.is_empty() {
        return Ok(None);
    }
    let (log, _) = p81::as_d87_asks(&b.world.log, &netted)?;
    let asked = Built::of(forkclass::ClassWorld { log, ..b.world.clone() });
    let again = p81::netted_breaks(&asked.world.log, &[])?;
    if !again.is_empty() {
        return Err(format!("P81: the log asked the D87 day still holds {} break(s) P81 nets", again.len()));
    }
    let answer = comparand_with(&asked, prios, fp, runs)?;
    let mut day = answer["day"]["day"].clone();
    let (lo, _) = b.day_bounds();
    let (lo, now) = (lo.fixed_offset(), b.world.now.fixed_offset());
    // The shipped binary's fork draws no part of a replayed pause a wall of the day covers (P56,
    // `p56_cut`), so a `paused` row is owed only over what the walls leave of the span, inside the
    // day and before `now`.
    let walls: Vec<(DateTime<Tz>, DateTime<Tz>)> = b.walls().iter().map(|(_, lo, hi, _)| (*lo, *hi)).collect();
    let rows = segments_mut(&mut day).ok_or("P81: the day asked the D87 day has no rows")?;
    for n in &netted {
        let covered = |r: &Value| {
            r["kind"] == "lost"
                && r["flags"]["note"] == "paused"
                && r["item"] == n.id.as_str()
                && at(&r["start"]).is_some_and(|a| a >= n.at)
                && at(&r["end"]).is_some_and(|z| z <= n.restart)
        };
        let before = rows.len();
        rows.retain(|r| !covered(r));
        let owed = cut_out(&walls, n.at.max(lo), n.restart.min(now)).iter().any(|(x, y)| x < y);
        if owed && rows.len() == before {
            return Err(format!("P81: the day asked the D87 day draws no `paused` row of `{}` over the break at {}", n.id, n.at));
        }
    }
    Ok(Some(json!({"p81": true, "hash": day_hash(&day), "day": day})))
}

/// **P85's comparand** (the owner's D92, parity P85; the W-43 repair, README gap 4367): on a world
/// whose log holds a clock start inside a break the replay stepped before it — read off the log by the
/// kernel's own machine model (`p85::restarts`), never off the kernel's answer — the comparand asked the
/// D92 day: the world with each moved start followed by a `pause` of its block stamped where the clock
/// started and an `unpause` stamped at the break's end (`p85::as_asked_log`, P81's netted breaks given
/// their own pair as [`p81_after`] gives them), which fork 4748911's machine nets as the kernel's
/// `restartAt` does; this comparand's own departures and D74's split as asked (`runs`); and the
/// `paused` row over each inserted pair taken off — a stretch no block's clock ran in, which the
/// break's own row already draws — and the day re-digested.  `{"p85": true, "hash", "day"}`; `None`
/// where P85 moves no start.  Refused by name, never guessed: a moved start the asked day draws no
/// `paused` row after, inside the day and before `now`.
pub fn p85_after(b: &Built, prios: &[Prio], fp: &dyn ForkPlan, runs: bool) -> Result<Option<Value>, String> {
    let restarts = p85::restarts(&b.world.log, &[])?;
    if restarts.is_empty() {
        return Ok(None);
    }
    let netted = p81::netted_breaks(&b.world.log, &[])?;
    let (log, _) = p85::as_asked_log(&b.world.log, &netted, &restarts)?;
    // The asked log still STARTS each clock inside its break (the line is kept, so its stamp is the
    // fork's), and the pause stamped at that instant stops it there: both machines then read
    // nothing until the `unpause` at the break's end. So, unlike P81's, the asked log is not
    // re-read for starts P85 moves — each one is still there, and moves nothing.
    let asked = Built::of(forkclass::ClassWorld { log, ..b.world.clone() });
    let answer = comparand_with(&asked, prios, fp, runs)?;
    let mut day = answer["day"]["day"].clone();
    let (lo, _) = b.day_bounds();
    let (lo, now) = (lo.fixed_offset(), b.world.now.fixed_offset());
    let walls: Vec<(DateTime<Tz>, DateTime<Tz>)> = b.walls().iter().map(|(_, lo, hi, _)| (*lo, *hi)).collect();
    let rows = segments_mut(&mut day).ok_or("P85: the day asked the D92 day has no rows")?;
    let spans: Vec<(String, DateTime<FixedOffset>, DateTime<FixedOffset>)> = netted
        .iter()
        .map(|n| (n.id.clone(), n.at, n.restart))
        .chain(restarts.iter().map(|r| (r.id.clone(), r.at, r.restart)))
        .collect();
    for (id, from, to) in &spans {
        let covered = |r: &Value| {
            r["kind"] == "lost"
                && r["flags"]["note"] == "paused"
                && r["item"] == id.as_str()
                && at(&r["start"]).is_some_and(|a| a >= *from)
                && at(&r["end"]).is_some_and(|z| z <= *to)
        };
        let before = rows.len();
        rows.retain(|r| !covered(r));
        let owed = cut_out(&walls, (*from).max(lo), (*to).min(now)).iter().any(|(x, y)| x < y);
        if owed && rows.len() == before {
            return Err(format!("P85: the day asked the D92 day draws no `paused` row of `{id}` over {from}..{to}"));
        }
    }
    Ok(Some(json!({"p85": true, "hash": day_hash(&day), "day": day})))
}

/// **Where two values first differ**, as a path and the two leaves — so a comparison of two
/// whole days names the one row that moved rather than printing both days.
pub fn first_difference(path: &str, a: &Value, b: &Value) -> Option<String> {
    match (a, b) {
        (Value::Object(x), Value::Object(y)) => {
            let keys: std::collections::BTreeSet<&String> = x.keys().chain(y.keys()).collect();
            keys.into_iter().find_map(|k| first_difference(&format!("{path}.{k}"), &x.get(k).cloned().unwrap_or(Value::Null), &y.get(k).cloned().unwrap_or(Value::Null)))
        }
        (Value::Array(x), Value::Array(y)) => {
            if let Some(d) = x.iter().zip(y).enumerate().find_map(|(i, (p, q))| first_difference(&format!("{path}[{i}]"), p, q)) {
                return Some(d);
            }
            (x.len() != y.len()).then(|| format!("{path}: {} element(s) against {}", x.len(), y.len()))
        }
        _ => (a != b).then(|| format!("{path}: {a} against {b}")),
    }
}

// ---------------------------------------------------------------------------
// The out-of-tree oracle: fork 4748911, `tm-oracle plan`
// ---------------------------------------------------------------------------

/// **The oracle's own usage banner**, as it prints it with no mode — what every
/// `TM_ORACLE` arm reads before feeding it (README gap 196: provenance is not
/// freshness).
pub fn oracle_banner(bin: &std::path::Path) -> String {
    let out = Command::new(bin)
        .stdin(Stdio::null())
        .output()
        .unwrap_or_else(|e| panic!("the fork oracle {}: {e}", bin.display()));
    format!("{}{}", String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr))
}

/// **Refuse an oracle without `mode` BY NAME**, before it is fed anything (README gap 196).
pub fn assert_oracle_mode(bin: &std::path::Path, mode: &str) {
    let banner = oracle_banner(bin);
    assert!(
        banner.contains(&format!("tm-oracle {mode}")),
        "the oracle at {} has no `{mode}` mode — it is STALE, whatever its `.oracle-ref` says. \
         Rebuild it: kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh. Its banner reads:\n{banner}",
        bin.display()
    );
}

/// **The oracle at `TM_ORACLE`**, when that is set — `None` otherwise, and every arm
/// that asks it is then inert.
pub fn oracle_path() -> Option<std::path::PathBuf> {
    std::env::var_os("TM_ORACLE").map(std::path::PathBuf::from)
}

/// **The entry of fork 4748911 that reads the running block's worked minutes for the oracle's
/// `worked` op** — `worked-seam.patch`'s, which MOVES fork `active_run`'s own lines into a method both
/// call (README gap 4507). [`Oracle::worked`] refuses an answer that does not name it.
pub const WORKED_READ_BY: &str = "planner::active_worked";

/// **`tm-oracle plan`, running**: one request line in, one answer line out — or, built
/// [`Oracle::with_mode`], another mode of the same protocol (`review`, the fork's week grid,
/// README gap 3718).
pub struct Oracle {
    bin: std::path::PathBuf,
    mode: &'static str,
    io: Mutex<Option<(Child, ChildStdin, BufReader<ChildStdout>)>>,
    /// Requests answered, for the arm's census.
    pub asked: Mutex<u64>,
}

impl Oracle {
    /// The oracle at `bin`, its `plan` mode checked by name before anything is asked.
    pub fn new(bin: std::path::PathBuf) -> Oracle {
        Oracle::with_mode(bin, "plan")
    }

    /// The oracle at `bin` in `mode` — one JSON request per line in, one answer per line out —
    /// the mode checked by name in its usage banner before anything is asked (README gap 196).
    pub fn with_mode(bin: std::path::PathBuf, mode: &'static str) -> Oracle {
        assert_oracle_mode(&bin, mode);
        Oracle { bin, mode, io: Mutex::new(None), asked: Mutex::new(0) }
    }

    /// One request, one answer; `Err` carries the oracle's own refusal or its death.
    pub fn ask(&self, req: &Value) -> Result<Value, String> {
        let mut io = self.io.lock().expect("the oracle's pipe");
        if io.is_none() {
            let mut child = Command::new(&self.bin)
                .arg(self.mode)
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .spawn()
                .map_err(|e| format!("the fork oracle {}: {e}", self.bin.display()))?;
            let stdin = child.stdin.take().expect("stdin");
            let stdout = BufReader::new(child.stdout.take().expect("stdout"));
            *io = Some((child, stdin, stdout));
        }
        let (child, stdin, stdout) = io.as_mut().expect("spawned");
        let line = serde_json::to_string(req).map_err(|e| e.to_string())?;
        let sent = writeln!(stdin, "{line}").and_then(|()| stdin.flush());
        let mut answer = String::new();
        let read = sent.and_then(|()| stdout.read_line(&mut answer));
        match read {
            Ok(n) if n > 0 => {}
            other => {
                let status = child.try_wait().ok().flatten();
                *io = None;
                return Err(format!("the fork oracle stopped answering ({other:?}, exit {status:?})"));
            }
        }
        *self.asked.lock().expect("census") += 1;
        let v: Value = serde_json::from_str(&answer).map_err(|e| format!("the oracle's answer is not JSON: {e}: {answer}"))?;
        match v.get("error") {
            Some(e) => Err(format!("the fork oracle refused: {e}")),
            None => Ok(v),
        }
    }
}

/// **A grant as the oracle builds fork 4748911's `Prio` from it** — its thirteen fields,
/// `u` as the double's shortest text (`inf` for a zero capacity: JSON has no infinity),
/// and the one graft `plan-seam.patch` adds, whether the EXACT shortfall is positive.
pub fn prio_wire(p: &Prio) -> Value {
    let v = serde_json::to_value(p).expect("a grant serialises");
    json!({
        "id": p.id.as_str(), "p": p.p, "class": v["class"], "k": p.k,
        "u": p.u.map(|u| u.to_string()), "bin": p.bin,
        "need_min": p.need_min, "avail_min": p.avail_min, "allocation_min": p.allocation_min,
        "shortfall_min": p.shortfall_min, "shortfall_positive": p.shortfall_min_exact.num > 0,
        "until": p.until.map(|d| d.to_string()), "hysteresis_applied": p.hysteresis_applied, "raw_p": p.raw_p,
    })
}

impl ForkPlan for Oracle {
    fn plan(&self, b: &Built, ask: &ForkAsk<'_>) -> Result<Planned, String> {
        // D60's key, run in the fork: the two order fields `forkclass::d60_cands` rewrites,
        // by id — the oracle rewrites its own collected candidates' fields to them.
        let order: Option<BTreeMap<String, Value>> = ask.d60.then(|| {
            forkclass::d60_cands(&b.cands, ask.prios)
                .iter()
                .map(|c| (c.id.as_str().to_string(), json!([c.root_order, c.own_order])))
                .collect()
        });
        let req = json!({
            "op": "plan",
            "world": b.world.to_json(),
            "state": serde_json::to_value(ask.state).map_err(|e| e.to_string())?,
            "now": ask.now.to_rfc3339(),
            "log_line": ask.log_line,
            "order": order,
            "prios": ask.prios.iter().map(prio_wire).collect::<Vec<_>>(),
            "extend": ask.extend.map(|(id, m)| json!([id.as_str(), m])),
            "runs": ask.p64,
        });
        let a = self.ask(&req)?;
        // The fork's candidates are its OWN collection over its own reading of the world;
        // the grants are keyed to the host's. Two different lists would rank by grants
        // the fork never saw, so they are held equal here, by id and order.
        let host: Vec<&str> = b.cands.iter().map(|c| c.id.as_str()).collect();
        let fork: Vec<&str> = a["cands"].as_array().map(Vec::as_slice).unwrap_or_default().iter().filter_map(Value::as_str).collect();
        if host != fork {
            return Err(format!("the fork collects the candidates {fork:?} and the host {host:?}"));
        }
        let mut fork_day = a["day"].clone();
        // The day's priorities are the grants the fork was handed, 1:1 with its
        // candidates: fork 4748911's `Prio` lacks the three exact fields the host's
        // carries, so they are written back as the host's reader spells them.
        fork_day["priorities"] = Value::Array(
            b.cands.iter().zip(ask.prios).map(|(c, p)| json!([c.id.as_str(), p])).collect(),
        );
        let mut day = fork_day.clone();
        let walls: Vec<(DateTime<Tz>, DateTime<Tz>)> = b.walls().iter().map(|(_, lo, hi, _)| (*lo, *hi)).collect();
        p56_cut(b.cfg.tz, &mut day, &walls);
        let ranked = a["ranked"].as_array().map(Vec::as_slice).unwrap_or_default().iter().filter_map(Value::as_str).map(str::to_string).collect();
        Ok(Planned { day, fork_day, ranked })
    }

    fn diff(&self, _tz: Tz, old: &Value, new: &Value) -> Result<Value, String> {
        let a = self.ask(&json!({"op": "diff", "old": old["segments"], "new": new["segments"]}))?;
        Ok(a["diff"].clone())
    }

    /// Fork 4748911's own reading, asked of `tm-oracle plan`'s `worked` op (W-43 track C, README
    /// gap 4460) — an oracle built before W-43 refuses the op by name, and is stale (gap 196).
    ///
    /// **Since W-44 track C the answer must name the fork's own entry that read it** (README gap
    /// 4507): `worked-seam.patch` moves fork `active_run`'s reading, unchanged, into a method the op
    /// calls, and the answer says `"read_by": "planner::active_worked"`. An oracle built before W-44
    /// answers the same minutes through a selection the oracle RE-TYPED, which made the comparand
    /// partly code this repository owns — so its answer is refused as STALE by name, not trusted.
    fn worked(&self, b: &Built, st: &RuntimeState) -> Result<Option<u32>, String> {
        let req = json!({
            "op": "worked",
            "world": b.world.to_json(),
            "state": serde_json::to_value(st).map_err(|e| e.to_string())?,
            "now": b.world.now.to_rfc3339(),
            "log_line": Value::Null,
        });
        let a = self.ask(&req).map_err(|e| {
            if e.contains("unknown op") {
                format!("{e} — an oracle built before W-43 has no `worked` op: it is STALE, rebuild it (build-oracle.sh)")
            } else {
                e
            }
        })?;
        if a["read_by"] != WORKED_READ_BY {
            return Err(format!(
                "the oracle's `worked` answer is not read by fork 4748911's own lines (read_by {}, not {WORKED_READ_BY:?}) \
                 — an oracle built before W-44 re-types `active_run`'s selection: it is STALE, rebuild it (build-oracle.sh)",
                a["read_by"]
            ));
        }
        match &a["worked"] {
            Value::Null => Ok(None),
            Value::Number(n) => n.as_u64().and_then(|m| u32::try_from(m).ok()).map(Some).ok_or_else(|| format!("the oracle's `worked` is {n}")),
            other => Err(format!("the oracle's `worked` answer is {other}, not minutes")),
        }
    }
}

