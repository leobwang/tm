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
//! answer only while that file exists, and R3 deletes it. The owner's D72 keeps both
//! kinds of fork comparison past R3: a seeded batch frozen by value (the frozen half),
//! and fresh proptest draws against fork 4748911's planner run OUT of the tree by
//! `tm-oracle plan` (the oracle half).
//!
//! So the comparand is built here, once, over [`ForkPlan`] — anything that plans a day
//! as the shipped binary's fork plans it — and the two backends are:
//!
//! * **the in-tree fork** ([`InTree`], this file's one region, deleted at R3): what the
//!   re-bless of every frozen line and the live check that the frozen answers are
//!   still the fork's have always called;
//! * **the out-of-tree oracle** ([`Oracle`]): fork `4748911` extracted and built by
//!   `kernel/tm-kernel-ffi/examples/oracle/build-oracle.sh`, run as `tm-oracle plan`.
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

#![allow(dead_code)]

use std::collections::BTreeMap;
use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::Mutex;

use chrono::{DateTime, Duration, FixedOffset};
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
/// holds it to the digest every frozen line was written with.
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
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for byte in body.as_bytes() {
        h ^= u64::from(*byte);
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    format!("{h:016x}")
}

/// A serialised day and its digest — the shape a frozen line's `day` and `shipped` carry.
pub fn frozen_day_json(day: &Value) -> Value {
    json!({"hash": day_hash(day), "day": day})
}

/// **P46's row, by its property** (`planner_invariants`' `w35_p46_row`): the running
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

/// **P47, by its property** (`w35_p47_day` over `w35_pause_open_rows`): a wall whose
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

/// **P55, by its property** (`planner_invariants`' `w36_fork_plan`): where the host's
/// worked minutes and the fork's reading of the log differ on a day with no running
/// break, the running estimate moves by their difference — so the FORK computes `left`
/// from the host's reading — and the open row carries the host's minutes. `None` where
/// the readings agree.
pub fn p55_state(b: &Built, st: &RuntimeState) -> Option<(RuntimeState, u32)> {
    let host = forkclass::host_worked(b)?;
    let fork = b.worked_for(st)?;
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
    let Some(a) = st.active.as_ref() else { return false };
    let worked = b.worked_for(st).unwrap_or(0);
    let breaking = st.break_.as_ref().is_some_and(|x| x.started.is_some());
    !a.paused && !breaking && worked >= a.est_min
}

/// P46's comparand state — `w35_p46_state`: the estimate raised by a whole day, so the
/// fork reserves the block from its own walls, wind-down and block boundary; unchanged
/// off P46.
pub fn p46_state(b: &Built, st: &RuntimeState) -> RuntimeState {
    let mut out = st.clone();
    if is_p46(b, st) {
        let worked = b.worked_for(st).unwrap_or(0);
        if let Some(a) = out.active.as_mut() {
            a.est_min = worked.saturating_add(24 * 60);
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

/// **P45's comparand after the running break** (README gap 3207): the fork planned
/// where the kernel's P45 restarts the cut — at the break's end (or `now`, once it has
/// overrun), the break a REST that resets the cut's break counter when it is at least
/// `break_min` long (`Look.restfulEnd`; the fork resets its counter at a logged break, so
/// one is logged ending there) — D60's key and the kernel's ranking, as the comparand
/// runs them. Its rows from that instant are the fork's own assignment, rests and kept
/// breaks over its own cut. `None` on a day with no running break. What it does not
/// model, measured and left to P45's owner (README gap 3480): `Look.restfulEnd` also
/// asks that the break END where a free stretch begins, and a logged break resets the
/// fork's counter at any length — so the kernel's running break and the same break once
/// ended are two readings of one span.
pub fn p45_after(b: &Built, prios: &[Prio], fp: &dyn ForkPlan) -> Result<Option<Value>, String> {
    p45_rows(b, prios, fp, None).map(|r| r.map(|(from, rows)| json!({"p45": true, "from": from, "rows": rows})))
}

/// **P45's comparand after the break, with the break's `log_line` chosen** — [`p45_after`]'s
/// rows (`None`: the comparand's own rule, the break logged once it has run `break_min`), or
/// with the break logged or left unlogged whatever its length (`Some(true)`, `Some(false)`):
/// README gap 3480's two readings of one span, the second of which is the kernel's where the
/// break does not end where a free stretch begins. `(from, rows)`, `None` on a day with no
/// running break.
pub fn p45_rows(b: &Built, prios: &[Prio], fp: &dyn ForkPlan, logged: Option<bool>) -> Result<Option<(String, Vec<Value>)>, String> {
    let st = &b.world.state;
    let Some(brk) = st.break_.as_ref().filter(|x| x.started.is_some()) else { return Ok(None) };
    let Some(started) = brk.started else { return Ok(None) };
    let tz = b.cfg.tz;
    let t = tm_core::capacity::local_dt(tz, b.date(), started);
    let (_, day_end) = b.day_bounds();
    let e = (t + Duration::minutes(i64::from(brk.planned_min))).min(day_end).max(b.world.now);
    let taken = (e - t).num_minutes();
    let log_line = logged.unwrap_or(taken >= i64::from(b.cfg.day.break_min)).then(|| {
        format!(
            "{{\"t\":\"{}\",\"ev\":\"break\",\"planned_min\":{},\"actual_min\":{taken}}}\n",
            t.to_rfc3339(),
            brk.planned_min
        )
    });
    let p = fp.plan(b, &ForkAsk { state: st, now: e, d60: true, prios, extend: None, log_line })?;
    let e_fixed = e.fixed_offset();
    let rows: Vec<Value> = segments_of(&p.day).iter().filter(|s| at(&s["start"]).is_some_and(|a| a >= e_fixed)).cloned().collect();
    Ok(Some((e.to_rfc3339(), rows)))
}

/// **README gap 3480's two readings, asked of the fork**: whether the kernel's rows from where
/// P45 restarts the cut are, row for row, the fork's own planned with the running break UNLOGGED
/// (`p45_rows(.., Some(false))`, an under-used row's note left to the renderer as
/// `forkday::underused_note_left_to_the_renderer` leaves it) — the kernel's reading of a running
/// break that does not end where a free stretch begins, against the comparand's, which logs it.
/// `false` on a day with no running break.
pub fn gap_3480_explains(b: &Built, prios: &[Prio], fp: &dyn ForkPlan) -> Result<bool, String> {
    let Some((from, rows)) = p45_rows(b, prios, fp, Some(false))? else { return Ok(false) };
    let kday = forkclass::kernel_answer(b)?;
    let kv = serde_json::to_value(&kday.day).map_err(|e| e.to_string())?;
    let from = DateTime::parse_from_rfc3339(&from).map_err(|e| e.to_string())?;
    let krows: Vec<Value> = segments_of(&kv).iter().filter(|r| at(&r["start"]).is_some_and(|a| a >= from)).cloned().collect();
    let want: Vec<Value> = rows
        .iter()
        .map(|r| crate::forkday::underused_note_left_to_the_renderer(r, &krows).unwrap_or_else(|| r.clone()))
        .collect();
    Ok(krows == want)
}

/// **The fork's answers for one stored world** — the ONE definition of what a frozen line
/// holds beside its world (`forkclass::ANSWERS`): the shipped day, the comparand (D57's
/// P46/P47 and D60's P51 applied by their properties, P55's host minutes, P56's drawing)
/// with its flags, on a running-block day the what-ifs, and on a break day P45's
/// comparand after the break — over the kernel's grants `prios`, with `fp` planning.
pub fn comparand_answers(b: &Built, prios: &[Prio], fp: &dyn ForkPlan) -> Result<Value, String> {
    let st = &b.world.state;
    let now = b.world.now;
    let tz = b.cfg.tz;
    // The SHIPPED fork's day is fork 4748911's (P56: the in-tree fork was changed to agree
    // with the kernel's drawing of a meeting's pause at W-37 track T).
    let shipped_p = fp.plan(b, &ForkAsk { state: st, now, d60: false, prios, extend: None, log_line: None })?;
    let shipped = shipped_p.fork_day.clone();
    let p56 = shipped != shipped_p.day;
    // P55: on a day whose host reading of the running block's worked minutes is not the
    // log's, the comparand reads the host's (`p55_state`).
    let p55 = p55_state(b, st);
    let st1 = p55.as_ref().map_or_else(|| st.clone(), |(s, _)| s.clone());
    let st2 = p46_state(b, &st1);
    let comparand_p = fp.plan(b, &ForkAsk { state: &st2, now, d60: true, prios, extend: None, log_line: None })?;
    // P51: D60's key moved the fork's §7.4 order (`forkclass::is_p51`'s reading).
    let p51 = comparand_p.ranked != shipped_p.ranked;
    let mut comparand = comparand_p.day;
    let p46 = is_p46(b, &st1);
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
        let rt = p55_state(b, &rt).map_or(rt, |(s, _)| s);
        let rt = p46_state(b, &rt);
        let whatif_day = |ps: &[Prio], full: bool| -> Result<Value, String> {
            let ask = ForkAsk { state: &rt, now, d60: true, prios: ps, extend: full.then_some((id, bm)), log_line: None };
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
    let flag = |set: bool, n: &str| {
        set.then(|| Value::Object(std::iter::once((n.to_string(), Value::Bool(true))).collect()))
    };
    Ok(json!({
        "day": frozen_day_json(&comparand),
        "shipped": (shipped != comparand).then(|| frozen_day_json(&shipped)),
        "d57": {"p46": p46, "p47": p47},
        "d60": {"p51": p51},
        "whatif": whatif,
        "p45": p45_after(b, prios, fp)?,
        "p52": flag(p52, "p52"),
        "p55": flag(p55.is_some(), "p55"),
        "p56": flag(p56, "p56"),
    }))
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

/// **`tm-oracle plan`, running**: one request line in, one answer line out.
pub struct Oracle {
    bin: std::path::PathBuf,
    io: Mutex<Option<(Child, ChildStdin, BufReader<ChildStdout>)>>,
    /// Requests answered, for the arm's census.
    pub asked: Mutex<u64>,
}

impl Oracle {
    /// The oracle at `bin`, its `plan` mode checked by name before anything is asked.
    pub fn new(bin: std::path::PathBuf) -> Oracle {
        assert_oracle_mode(&bin, "plan");
        Oracle { bin, io: Mutex::new(None), asked: Mutex::new(0) }
    }

    /// One request, one answer; `Err` carries the oracle's own refusal or its death.
    pub fn ask(&self, req: &Value) -> Result<Value, String> {
        let mut io = self.io.lock().expect("the oracle's pipe");
        if io.is_none() {
            let mut child = Command::new(&self.bin)
                .arg("plan")
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
}

// BEGIN THE FORK PLANNER — deleted with tm-core/src/planner.rs at R3 (README gap 3533)
use tm_core::dayplan::{DayPlan, SegFlags, SegKind, Segment};
use tm_core::planner::{self, PlanOverrides};

/// **The in-tree fork** — `tm-core/src/planner.rs`, as the shipped binary runs it
/// (`planning::build_ranked`: `plan` over the kernel's grants, D53). R3 deletes it.
pub struct InTree;

/// **Fork 4748911's drawing of a replayed pause** (parity P56, README gap 3320): W-37
/// track T changed the in-tree fork's `past_segments` to agree with P56 — the part of a
/// replayed Pause a wall of the day covers is cut out — so the SHIPPED fork's day on a
/// line whose log holds a meeting's pause cannot be recomputed from the in-tree fork. This
/// is `b3c29a3`'s `past_segments` for the one kind T changed: every `paused` Lost row the
/// in-tree fork drew is taken out, and each of the day's replayed Pause segments is put back
/// WHOLE (clipped to the day's start and to `now`, `done` when the log closed its item
/// today), ahead of every other row at one `(start, end)` as `plan`'s stable sort puts the
/// replayed past first. On a day whose replay holds no Pause a wall touches it is the
/// in-tree day exactly. The frozen P56 lines were checked BY VALUE against `b3c29a3`'s own
/// planner built in a scratch clone (README, W-38 track H). Since W-39 over the replay and
/// the instant the day was planned from (it read the world's, which is the same on every
/// ask whose fork drawing a comparand reads).
fn as_4748911(b: &Built, replay: &tm_core::log::Replay, now: DateTime<Tz>, day: &DayPlan) -> DayPlan {
    let Some(d) = replay.day(day.date) else { return day.clone() };
    let tz = b.cfg.tz;
    let (lo, _) = b.day_bounds();
    let mut past: Vec<Segment> = Vec::new();
    for seg in &d.segments {
        let tm_core::log::SegmentKind::Pause { id } = &seg.kind else { continue };
        let start = seg.start.with_timezone(&tz).max(lo);
        let end = seg.end.with_timezone(&tz).min(now);
        if end <= start {
            continue;
        }
        past.push(Segment {
            start,
            end,
            kind: SegKind::Lost,
            energy: None,
            item: Some(Id::new(id.clone())),
            instance: None,
            flags: SegFlags {
                done: d.done.iter().any(|x| x == id),
                note: Some("paused".to_string()),
                ..SegFlags::default()
            },
        });
    }
    let mut out = day.clone();
    let rest: Vec<Segment> = day
        .segments
        .iter()
        .filter(|s| !(s.kind == SegKind::Lost && s.flags.note.as_deref() == Some("paused")))
        .cloned()
        .collect();
    out.segments = past.into_iter().chain(rest).collect();
    out.segments.sort_by(|a, z| a.start.cmp(&z.start).then(a.end.cmp(&z.end)));
    out
}

/// **A serialised day's rows as the fork's `diff` reads them** — each row's start, end,
/// kind (a batch's members with it) and item; `diff` reads nothing else.
fn day_of_json(tz: Tz, v: &Value) -> Result<DayPlan, String> {
    let when = |x: &Value, what: &str| at(x).map(|t| t.with_timezone(&tz)).ok_or_else(|| format!("{what}: {x}"));
    let date = v["date"].as_str().and_then(|d| chrono::NaiveDate::parse_from_str(d, "%Y-%m-%d").ok()).ok_or("the day's date")?;
    let window = (when(&v["window"][0], "window")?, when(&v["window"][1], "window")?);
    let mut day = DayPlan::empty(date, window, v["budget_blocks"].as_u64().unwrap_or(0) as u32);
    for s in segments_of(v) {
        let kind = match &s["kind"] {
            Value::String(k) => match k.as_str() {
                "block" => SegKind::Block,
                "break" => SegKind::Break,
                "routine" => SegKind::Routine,
                "wall" => SegKind::Wall,
                "rest" => SegKind::Rest,
                "optional" => SegKind::Optional,
                "winddown" => SegKind::WindDown,
                "sleep" => SegKind::Sleep,
                "lost" => SegKind::Lost,
                other => return Err(format!("a row of kind `{other}`")),
            },
            k => SegKind::Batch(
                k["batch"].as_array().ok_or_else(|| format!("a row of kind {k}"))?.iter().filter_map(Value::as_str).map(Id::new).collect(),
            ),
        };
        day.segments.push(Segment {
            start: when(&s["start"], "start")?,
            end: when(&s["end"], "end")?,
            kind,
            energy: None,
            item: s["item"].as_str().map(Id::new),
            instance: None,
            flags: SegFlags::default(),
        });
    }
    Ok(day)
}

impl ForkPlan for InTree {
    fn plan(&self, b: &Built, ask: &ForkAsk<'_>) -> Result<Planned, String> {
        let replay = match &ask.log_line {
            Some(l) => crate::chokepoint::replay_of_text(&format!("{}{l}", b.world.log), b.cfg.tz),
            None => b.replay.clone(),
        };
        let cands = if ask.d60 { forkclass::d60_cands(&b.cands, ask.prios) } else { b.cands.clone() };
        let ov = ask.extend.map(|(id, m)| PlanOverrides::new().extending(id, m));
        let mut input = planner::PlanInput::new(&b.tree, &replay, &b.cfg, &b.model, ask.state, ask.now)
            .with_ranking(&cands, ask.prios);
        if let Some(ov) = ov.as_ref() {
            input = input.with_overrides(ov);
        }
        let day = planner::plan(&input);
        let fork = as_4748911(b, &replay, ask.now, &day);
        let ranked = tm_core::priority::sorted_candidates(ask.prios, &cands).iter().map(|c| c.id.as_str().to_string()).collect();
        Ok(Planned {
            day: serde_json::to_value(&day).map_err(|e| e.to_string())?,
            fork_day: serde_json::to_value(&fork).map_err(|e| e.to_string())?,
            ranked,
        })
    }

    fn diff(&self, tz: Tz, old: &Value, new: &Value) -> Result<Value, String> {
        let (a, z) = (day_of_json(tz, old)?, day_of_json(tz, new)?);
        serde_json::to_value(planner::diff(&a, &z)).map_err(|e| e.to_string())
    }
}
// END THE FORK PLANNER
