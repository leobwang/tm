//! **Parity P81, carried by value** — the owner's **D87** (README gap 4137): a break taken inside a
//! block is not block time.
//!
//! Fork point `4748911`'s `Machine::step` never touched a block for a `break`, so a block whose clock
//! ran across a logged break was credited the break's minutes (when a `stop` or the next `start` cut
//! it) and its `Block` segment was drawn across the `Break` one. The kernel's replay stops the clock
//! at the break's start and restarts it at the break's end (`Replay.brkFx`). This module is the
//! fork's answer **moved by that rule and nothing else**, computed from the fork's own segments, so a
//! frozen comparison can carry P81 the way `fork.rs` carries P21: every differing leaf is either the
//! one P81 predicts, by value, or a finding.
//!
//! **What it reads, and only that**: the fork's frozen answer. A `Break` segment `[s, e]` that BEGINS
//! inside a `Block` segment `[x, y]` (`x < s < y`) is a break stepped while that block's clock ran;
//! P81 splits the block into `[x, s]` and `[e, y]` (when `e < y`), and — when the block's minutes
//! were the clock's, a cut's credit, which the fork records as the item's ci-unknown minutes on the
//! cut's day — takes the netted minutes off the day's `block_min` and `ci_unknown`, and off the
//! item's `minutes` and `minutes_by_day`. A `done`'s logged `actual_min` is credited as before and is
//! left alone. A break that began BEFORE the block (`s <= x`, README gap 4241) is not P81's: the
//! kernel does not net it either. Nothing here reads the kernel's answer: a kernel that netted the
//! wrong minutes, split the wrong segment or credited the wrong day fails the comparison by name.
//!
//! **What it refuses to guess**: a break inside two blocks at once, a post-break stretch whose day
//! is not its block's, a cut whose day holds no ci-unknown minutes for the block, or a break inside
//! the fork's OPEN block — each is a finding, returned by name, never a transformation.
//!
//! **And where the fork can be asked, it is asked** (W-42 track R, resumed; README gap 4247). The
//! carry above is a model read off segments, and it is no more than that: over T5's 458 live inputs
//! — retro breaks, breaks inside an open block, two breaks in one stretch, a stretch filed on the
//! next day — it disagreed with the kernel 42 times. So the live arm does not carry; it ASKS:
//! [`netted_breaks`] reads which breaks P81 nets by fork 4748911's own machine (file order, its undo
//! mask, the block family's clock — never the kernel's answer), [`as_d87_asks`] gives each one to the
//! fork as a `pause` at its start and an `unpause` where the clock restarts, which fork 4748911's
//! machine nets as the kernel's nets the break, and [`as_asked`] reads that answer back as the
//! answer to the log as given — the inserted `Pause` drawn as the break alone. On every frozen input
//! the live arm also holds this module's carry to that asked answer, so the model is checked against
//! the fork's own machine wherever both can run. Instants are spelled as the fork's answer spells
//! them (chrono's own serialisation: `Z` at a zero offset, `:60` in a leap second).

use std::collections::BTreeMap;

use chrono::{DateTime, FixedOffset};
use serde_json::{Map, Value};

/// What [`carry`] moved, so a comparison can say how much P81 it carried rather than claim it.
#[derive(Default, Debug)]
pub struct P81Tally {
    /// Breaks found inside a block's running stretch (each one a sighting).
    pub breaks: usize,
    /// Minutes netted off cut credits.
    pub minutes: u64,
}

fn at(v: &Value, what: &str) -> Result<DateTime<FixedOffset>, String> {
    let s = v.as_str().ok_or_else(|| format!("P81: {what} is not a string: {v}"))?;
    DateTime::parse_from_rfc3339(s).map_err(|e| format!("P81: {what} `{s}`: {e}"))
}

/// Whole minutes from `a` to `b`, truncated and at least 0 — the replay's `minutesBetween`, per
/// sub-segment (site R8).
fn mins(a: DateTime<FixedOffset>, b: DateTime<FixedOffset>) -> u64 {
    (b - a).num_seconds().max(0) as u64 / 60
}

/// The day the replay files an instant under: the latest day whose wake is at or before it, if
/// within a day of it; else its own local date.
fn day_of(days: &Map<String, Value>, t: DateTime<FixedOffset>) -> Result<String, String> {
    let mut best: Option<(DateTime<FixedOffset>, String)> = None;
    for (d, day) in days {
        if day["wake"].is_null() {
            continue;
        }
        let w = at(&day["wake"], &format!("days.{d}.wake"))?;
        if w <= t && (t - w).num_seconds() < 86_400 && best.as_ref().is_none_or(|(b, _)| w > *b) {
            best = Some((w, d.clone()));
        }
    }
    Ok(best.map(|(_, d)| d).unwrap_or_else(|| t.date_naive().to_string()))
}

fn seg_kind(seg: &Value) -> Option<&str> {
    seg["kind"].as_object().and_then(|o| o.keys().next()).map(String::as_str)
}

/// One `Block` segment: its day, its position in that day's list, its item and its span.
struct BlockSeg {
    day: String,
    idx: usize,
    id: String,
    x: DateTime<FixedOffset>,
    y: DateTime<FixedOffset>,
}

/// **The fork's frozen `Replay` moved by P81.** `Ok((answer, tally))` with the answer's `replay`
/// transformed; `Err(finding)` when the rule meets a shape it will not guess at.
pub fn carry(fork_answer: &Value) -> Result<(Value, P81Tally), String> {
    let mut answer = fork_answer.clone();
    let mut tally = P81Tally::default();
    let replay = answer["replay"].as_object_mut().ok_or("P81: the frozen answer has no `replay` object")?;
    let days = replay
        .get("days")
        .and_then(Value::as_object)
        .cloned()
        .ok_or("P81: the frozen replay has no `days`")?;

    let mut blocks: Vec<BlockSeg> = Vec::new();
    let mut breaks: Vec<(String, DateTime<FixedOffset>, DateTime<FixedOffset>)> = Vec::new();
    for (d, day) in &days {
        for (i, seg) in day["segments"].as_array().into_iter().flatten().enumerate() {
            let (x, y) = (at(&seg["start"], "a segment's start")?, at(&seg["end"], "a segment's end")?);
            match seg_kind(seg) {
                Some("Block") => {
                    let id = seg["kind"]["Block"]["id"].as_str().ok_or("P81: a Block with no id")?.to_string();
                    blocks.push(BlockSeg { day: d.clone(), idx: i, id, x, y });
                }
                Some("Break") => breaks.push((d.clone(), x, y)),
                _ => {}
            }
        }
    }

    // The fork's open block holds a running stretch no segment shows yet.
    if let Some(ob) = replay.get("open_block").filter(|v| !v.is_null()) {
        if let Some(since) = ob.get("since").filter(|v| !v.is_null()) {
            let since = at(since, "open_block.since")?;
            if let Some((d, s, _)) = breaks.iter().find(|(_, s, _)| since < *s) {
                return Err(format!(
                    "P81: the break at {s} (day {d}) began inside the fork's OPEN block — not carried here"
                ));
            }
        }
    }

    // Splits per day: (segment index, the pieces that replace it).
    let mut splits: BTreeMap<String, Vec<(usize, Vec<Value>)>> = BTreeMap::new();
    // Credits to take off: (cut day, item) → minutes.
    let mut credits: BTreeMap<(String, String), u64> = BTreeMap::new();
    for (bd, s, e) in &breaks {
        let inside: Vec<&BlockSeg> = blocks.iter().filter(|k| k.x < *s && *s < k.y).collect();
        let k = match inside.as_slice() {
            [] => continue,
            [k] => *k,
            _ => return Err(format!("P81: the break at {s} (day {bd}) lies inside {} blocks", inside.len())),
        };
        tally.breaks += 1;
        let seg = &days[&k.day]["segments"][k.idx];
        let mut first = seg.clone();
        first["end"] = serde_json::to_value(s).expect("an instant serialises");
        let mut pieces = vec![first];
        let mut kept = mins(k.x, *s);
        if *e < k.y {
            if day_of(&days, *e)? != k.day {
                return Err(format!("P81: the stretch after the break at {s} is not filed on its block's day {}", k.day));
            }
            let mut second = seg.clone();
            second["start"] = serde_json::to_value(e).expect("an instant serialises");
            pieces.push(second);
            kept += mins(*e, k.y);
        }
        splits.entry(k.day.clone()).or_default().push((k.idx, pieces));
        let netted = mins(k.x, k.y) - kept;
        if netted == 0 {
            continue;
        }
        // A cut credits the clock to the item's ci-unknown minutes on the cut's day; a `done`
        // credits its logged minutes, which P81 leaves alone.
        let cut_day = day_of(&days, k.y)?;
        let unknown = days.get(&cut_day).and_then(|d| d["ci_unknown"][&k.id].as_u64()).unwrap_or(0);
        if unknown == 0 {
            continue;
        }
        if unknown < netted {
            return Err(format!(
                "P81: {} holds {unknown} ci-unknown minutes for `{}` on {cut_day}, fewer than the {netted} netted",
                "the fork",
                k.id
            ));
        }
        *credits.entry((cut_day, k.id.clone())).or_default() += netted;
        tally.minutes += netted;
    }

    // Apply the splits, then re-sort each day's segments by start, stably — the replay's own order.
    let days_mut = replay.get_mut("days").and_then(Value::as_object_mut).ok_or("P81: no days")?;
    for (d, mut list) in splits {
        list.sort_by_key(|(i, _)| std::cmp::Reverse(*i));
        let segs = days_mut[&d]["segments"].as_array_mut().ok_or("P81: segments")?;
        for (i, pieces) in list {
            segs.splice(i..=i, pieces);
        }
        let mut keyed: Vec<(DateTime<FixedOffset>, Value)> =
            segs.drain(..).map(|g| (at(&g["start"], "a segment's start").expect("parsed above"), g)).collect();
        keyed.sort_by_key(|(t, _)| *t);
        segs.extend(keyed.into_iter().map(|(_, g)| g));
    }
    for ((d, id), m) in &credits {
        let day = days_mut.get_mut(d).ok_or("P81: the cut's day")?;
        let bm = day["block_min"].as_u64().ok_or("P81: block_min")?;
        day["block_min"] = Value::from(bm - m);
        let unk = day["ci_unknown"].as_object_mut().ok_or("P81: ci_unknown")?;
        let left = unk[id].as_u64().expect("checked above") - m;
        if left == 0 {
            unk.remove(id);
        } else {
            unk.insert(id.clone(), Value::from(left));
        }
    }
    let items = replay.get_mut("items").and_then(Value::as_object_mut).ok_or("P81: items")?;
    for ((d, id), m) in &credits {
        let it = items.get_mut(id).ok_or_else(|| format!("P81: no item `{id}`"))?;
        let total = it["minutes"].as_u64().ok_or("P81: an item's minutes")?;
        it["minutes"] = Value::from(total - m);
        let by_day = it["minutes_by_day"].as_object_mut().ok_or("P81: minutes_by_day")?;
        let on = by_day.get(d).and_then(Value::as_u64).ok_or_else(|| format!("P81: `{id}` has no minutes on {d}"))?;
        if on == *m {
            by_day.remove(d);
        } else {
            by_day.insert(d.clone(), Value::from(on - m));
        }
    }
    Ok((answer, tally))
}

// ---------------------------------------------------------------------------
// The D87 log as fork 4748911 can be ASKED it (W-42 track R, resumed)
// ---------------------------------------------------------------------------

/// **One break P81 nets, as the fork can be told it**: the block whose clock it stopped, the break's
/// own stamp as the log spells it (`at`, the break's start, where the stretch before it ends), and the
/// instant the clock restarts — the later of that stretch's start and the break's end (`Replay.brkFx`'s
/// `pick instLt x e`), in the offset of the instant it came from.
#[derive(Clone, Debug, PartialEq)]
pub struct Netted {
    pub id: String,
    pub at: DateTime<FixedOffset>,
    pub at_text: String,
    pub restart: DateTime<FixedOffset>,
    /// The break line's 1-based line in the log as given (before anything is inserted).
    pub line: u64,
}

/// The log's `t`, as fork `ts` reads it: RFC 3339, else the minute-resolution fallback.
fn stamp(s: &str) -> Option<DateTime<FixedOffset>> {
    DateTime::parse_from_rfc3339(s).ok().or_else(|| DateTime::parse_from_str(s, "%Y-%m-%dT%H:%M%:z").ok())
}

/// The tags whose arms move the block family's clock (`Replay.arm`), and `break`, since D87.
const CLOCK_TAGS: [&str; 8] = ["start", "pause", "unpause", "interrupt", "resume", "stop", "done", "break"];

/// A clock entry: its line, tag, primary id and stamp, and a break's minutes.
#[derive(Clone, Debug)]
struct ClockEntry {
    line: u64,
    tag: String,
    id: Option<String>,
    t: DateTime<FixedOffset>,
    t_text: String,
    minutes: i64,
}

/// **The breaks P81 nets in a log, by fork 4748911's own machine** — the block family's clock read
/// in FILE order over the entries no undo cancelled (fork 4748911's undo mask, `Replay.survivors`: an `undo`
/// takes back the most recent surviving entry of its tag, and of its id when it names one), every
/// line the fork refused skipped (`refused`, its own `warningLines`). A `break` is netted when a
/// block's clock RUNS at its place in the file — not paused, no interruption open — exactly
/// `Replay.brkFx`'s condition; the clock then restarts at the later of its stretch's start and the
/// break's end. Read off the log and the fork's own refusals, never the kernel's answer.
pub fn netted_breaks(text: &str, refused: &[u64]) -> Result<Vec<Netted>, String> {
    let mut stack: Vec<ClockEntry> = Vec::new();
    for (i, raw) in text.split('\n').enumerate() {
        let line = i as u64 + 1;
        if raw.trim().is_empty() || refused.contains(&line) {
            continue;
        }
        let e: Value = serde_json::from_str(raw).map_err(|err| format!("P81: line {line} is not JSON the fork accepted: {err}"))?;
        let tag = e["ev"].as_str().unwrap_or_default().to_string();
        if tag == "undo" {
            let of = e["of"].as_str().unwrap_or_default();
            let id = e["id"].as_str();
            if let Some(k) = stack.iter().rposition(|c| c.tag == of && id.is_none_or(|x| c.id.as_deref() == Some(x))) {
                stack.remove(k);
            }
            continue;
        }
        if !CLOCK_TAGS.contains(&tag.as_str()) {
            continue;
        }
        let t_text = e["t"].as_str().unwrap_or_default().to_string();
        let t = stamp(&t_text).ok_or_else(|| format!("P81: line {line}'s stamp `{t_text}` does not read"))?;
        let minutes = e["actual_min"].as_i64().or_else(|| e["planned_min"].as_i64()).unwrap_or(0);
        stack.push(ClockEntry { line, tag, id: e["id"].as_str().map(str::to_string), t, t_text, minutes });
    }
    // The block family's clock (`Replay.arm`): the open block's id, its stretch's start, paused; and
    // whether an interruption is open.
    let mut block: Option<(String, Option<DateTime<FixedOffset>>, bool)> = None;
    let mut interrupted = false;
    let mut out = Vec::new();
    for c in &stack {
        let same = |b: &Option<(String, Option<DateTime<FixedOffset>>, bool)>| b.as_ref().is_some_and(|b| Some(b.0.as_str()) == c.id.as_deref());
        match c.tag.as_str() {
            "start" => block = Some((c.id.clone().unwrap_or_default(), (!interrupted).then_some(c.t), false)),
            "pause" => {
                if let Some(b) = block.as_mut().filter(|b| Some(b.0.as_str()) == c.id.as_deref() && !b.2) {
                    b.1 = None;
                    b.2 = true;
                }
            }
            "unpause" => {
                if let Some(b) = block.as_mut().filter(|b| Some(b.0.as_str()) == c.id.as_deref() && b.2) {
                    b.2 = false;
                    if !interrupted {
                        b.1 = Some(c.t);
                    }
                }
            }
            "interrupt" => {
                if let Some(b) = block.as_mut() {
                    b.1 = None;
                }
                interrupted = true;
            }
            "resume" => {
                if let Some(b) = block.as_mut().filter(|b| !b.2 && b.1.is_none()) {
                    b.1 = Some(c.t);
                }
                interrupted = false;
            }
            "stop" | "done" => {
                if same(&block) {
                    block = None;
                }
            }
            "break" => {
                if let Some(b) = block.as_mut() {
                    if let Some(x) = b.1 {
                        let end = c.t + chrono::Duration::minutes(c.minutes);
                        let restart = if x < end { end } else { x };
                        out.push(Netted { id: b.0.clone(), at: c.t, at_text: c.t_text.clone(), restart, line: c.line });
                        b.1 = Some(restart);
                    }
                }
            }
            _ => {}
        }
    }
    Ok(out)
}

/// **The log fork 4748911 is asked P81's day in**: each netted break's line between a `pause` of its
/// block stamped as the break is (the stretch before it closes there, as `brkFx`'s `closeSub` closes
/// it) and an `unpause` stamped where the clock restarts, which fork 4748911's machine nets as the
/// kernel's nets the break. The lines inserted, 1-based in the new log, are returned with it.
///
/// **Refused by name, never guessed: an `undo` that would take an inserted line back.**  An `undo` of a
/// `pause` or an `unpause` takes back the most recent surviving one of its tag (and id), so a later one
/// in the log could take back a line this inserted where the log's own line was meant — the fork would
/// then be asked another log than P81's.  The asked log's own mask is read, and an inserted line that
/// does not survive it is a finding.
pub fn as_d87_asks(text: &str, netted: &[Netted]) -> Result<(String, Vec<u64>), String> {
    let mut out: Vec<String> = Vec::new();
    let mut inserted = Vec::new();
    for (i, raw) in text.split('\n').enumerate() {
        let line = i as u64 + 1;
        match netted.iter().find(|n| n.line == line) {
            Some(n) => {
                out.push(serde_json::json!({"t": n.at_text, "ev": "pause", "id": n.id}).to_string());
                inserted.push(out.len() as u64);
                out.push(raw.to_string());
                let restart = serde_json::to_value(n.restart).expect("an instant serialises");
                out.push(serde_json::json!({"t": restart, "ev": "unpause", "id": n.id}).to_string());
                inserted.push(out.len() as u64);
            }
            None => out.push(raw.to_string()),
        }
    }
    // The asked log's mask over its pauses and unpauses: every inserted one must survive it.
    let mut stack: Vec<(u64, String, Option<String>)> = Vec::new();
    for (i, raw) in out.iter().enumerate() {
        let Ok(e) = serde_json::from_str::<Value>(raw) else { continue };
        let tag = e["ev"].as_str().unwrap_or_default();
        match tag {
            "undo" => {
                let of = e["of"].as_str().unwrap_or_default();
                let id = e["id"].as_str();
                if let Some(k) = stack.iter().rposition(|c| c.1 == of && id.is_none_or(|x| c.2.as_deref() == Some(x))) {
                    if inserted.contains(&stack[k].0) {
                        return Err(format!("P81: an undo at line {} of the asked log would take back the {of} inserted at line {}", i + 1, stack[k].0));
                    }
                    stack.remove(k);
                }
            }
            "pause" | "unpause" => stack.push((i as u64 + 1, tag.to_string(), e["id"].as_str().map(str::to_string))),
            _ => {}
        }
    }
    Ok((out.join("\n"), inserted))
}

/// **The fork's answer to that log, read as its answer to the log as given, with P81's drawing**: the
/// `Pause` segment each inserted pair drew (the break's own `Break` segment is the span, drawn alone —
/// one span, one row, as D65 draws a meeting's pause as the wall) taken off; the entry count less the
/// lines inserted; and each refused line numbered as in the log as given.
pub fn as_asked(answer: &Value, netted: &[Netted], inserted: &[u64]) -> Result<Value, String> {
    let mut a = answer.clone();
    let days = a["replay"]["days"].as_object_mut().ok_or("P81: the asked answer has no days")?;
    for n in netted.iter().filter(|n| n.at < n.restart) {
        let mut hit = false;
        for day in days.values_mut() {
            if let Some(segs) = day["segments"].as_array_mut() {
                let before = segs.len();
                segs.retain(|s| {
                    !(seg_kind(s) == Some("Pause")
                        && s["kind"]["Pause"]["id"] == n.id.as_str()
                        && at(&s["start"], "").ok() == Some(n.at)
                        && at(&s["end"], "").ok() == Some(n.restart))
                });
                hit |= segs.len() < before;
            }
        }
        if !hit {
            return Err(format!("P81: the fork drew no Pause for the pair inserted around the break at {}", n.at));
        }
    }
    let entries = a["entries"].as_u64().ok_or("P81: the asked answer has no entry count")?;
    a["entries"] = Value::from(entries - inserted.len() as u64);
    let lines: Vec<u64> = a["warningLines"].as_array().ok_or("P81: no warningLines")?.iter().filter_map(Value::as_u64).collect();
    let mut back = Vec::new();
    for l in lines {
        if inserted.contains(&l) {
            return Err(format!("P81: the fork refused a line this module inserted (line {l})"));
        }
        back.push(Value::from(l - inserted.iter().filter(|i| **i < l).count() as u64));
    }
    a["warningLines"] = Value::Array(back);
    Ok(a)
}

// ---------------------------------------------------------------------------
// P81 on a planned day, by its property (W-42 track R, resumed)
// ---------------------------------------------------------------------------

/// **P81 on a planned day, by its property** — the fork's frozen day for a world whose log holds
/// breaks P81 nets ([`netted_breaks`]): each Block row of the break's block that the break falls
/// inside — on the `worked` days, the running block's open row `[x, …)` — is cut where the clock
/// stopped: a replayed row `[x, at]`, drawn as fork `past_segments` draws a closed stretch (not open,
/// not current, no note, `done` as the day's other rows of the item are), and the row it was, from
/// the restart on (none when the break outlasts it); the rows re-sorted by start, stably. The caller
/// re-digests the day (`forkplan::frozen_day_json`), which this module cannot reach. Read off the
/// fork's own day and the log, never the kernel's answer — and a netted break no Block row of its
/// block holds is refused by name, never placed. `the_frozen_classes_are_the_forks_answer_today`
/// holds this rule to fork 4748911 asked the D87 day ([`as_d87_asks`]) while the fork is in the tree.
pub fn planned_day(day: &Value, netted: &[Netted]) -> Result<Value, String> {
    let mut d = day.clone();
    let segs = d["segments"].as_array_mut().ok_or("P81: the day has no rows")?;
    let mut order: Vec<&Netted> = netted.iter().collect();
    order.sort_by_key(|n| n.at);
    for n in order {
        let k = segs
            .iter()
            .position(|s| {
                s["kind"] == "block"
                    && s["item"] == n.id.as_str()
                    && at(&s["start"], "").is_ok_and(|a| a < n.at)
                    && at(&s["end"], "").is_ok_and(|z| n.at < z)
            })
            .ok_or_else(|| format!("P81: no Block row of `{}` holds the break at {} the log nets", n.id, n.at))?;
        let done = segs.iter().any(|s| s["item"] == n.id.as_str() && s["flags"]["done"] == true);
        let row = segs[k].clone();
        let mut past = row.clone();
        past["end"] = serde_json::to_value(n.at).expect("an instant serialises");
        past["energy"] = Value::Null;
        past["instance"] = Value::Null;
        past["flags"] = serde_json::json!({
            "current": false, "deferred": false, "done": done, "ghost": false, "hot": false,
            "mandatory": false, "multiplier": null, "note": null, "open": false,
            "planned_min": null, "underused": false
        });
        let mut pieces = vec![past];
        if at(&row["end"], "").is_ok_and(|z| n.restart < z) {
            let mut rest = row;
            rest["start"] = serde_json::to_value(n.restart).expect("an instant serialises");
            pieces.push(rest);
        }
        segs.splice(k..=k, pieces);
    }
    let mut keyed: Vec<(DateTime<FixedOffset>, Value)> = Vec::new();
    for s in segs.drain(..) {
        keyed.push((at(&s["start"], "a row's start")?, s));
    }
    keyed.sort_by_key(|(t, _)| *t);
    segs.extend(keyed.into_iter().map(|(_, s)| s));
    Ok(d)
}
