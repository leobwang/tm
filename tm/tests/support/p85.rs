//! **Parity P85, carried by value** — the owner's **D92** (README gap 4241): a break that runs INTO a
//! block's start is not block time.
//!
//! A `break` line is written when the break ends, so a block's clock that starts inside a logged break is
//! the mark of a log the binary did not write in normal use — `tm start` ends a running break before it
//! logs its `start` — and generated logs are full of it (`loggen`'s breaks outlast its 22-minute gap: 22
//! in the generated month). Fork point `4748911`'s clock started at the `start` whatever break the log had
//! stepped, so the block was credited (when a `stop` or the next `start` cut it) and drawn across the
//! break's tail, while `tm stop`'s minutes (`Replay::idle_min_since`) netted it. The kernel's replay starts
//! every clock — at a `start`, an `unpause` or a `resume` — at the end of the last break it stepped when
//! the clock's instant falls inside it (`Replay.restartAt`). This module is the fork's answer **moved by
//! that rule and nothing else**, as `p81.rs` is for D87, applied after it.
//!
//! **What [`carry`] reads, and only that**: the fork's frozen answer. A `Block` segment `[x, y]` whose
//! start falls inside a `Break` segment `[s, e]` (`s <= x < e`) is a clock started inside a break; P85
//! starts it at `e` — the segment becomes `[e, y]`, or goes when the break outlasts it — and, when the
//! block's minutes were a cut's credit (the fork records those as the item's ci-unknown minutes on the
//! cut's day), takes the netted minutes off that day's `block_min` and `ci_unknown`, and off the item's
//! `minutes` and `minutes_by_day`. The fork's open block, when its clock started inside a break, starts
//! at the break's end. Nothing here reads the kernel's answer.
//!
//! **What it refuses to guess**: a stretch inside two breaks at once, a stretch whose new start is filed
//! on another day than the fork filed it, a cut whose day holds too few ci-unknown minutes for the block —
//! each a finding, returned by name.
//!
//! **And where the fork can be asked, it is asked** ([`restarts`], [`as_asked_log`], [`as_asked_answer`]):
//! each clock start P85 moves, read off the log by the kernel's own machine (file order, the undo mask's
//! survivors, the fork's own refusals — never the kernel's answer), is given to the fork as a `pause` of
//! the block stamped where the clock started and an `unpause` stamped at the break's end, immediately after
//! the line that started it — which fork 4748911's machine nets as the kernel's `restartAt` does — and the
//! answer is read back with those `Pause` segments taken off.

use std::collections::BTreeMap;

use chrono::{DateTime, FixedOffset};
use serde_json::{Map, Value};

/// What [`carry`] moved, so a comparison can say how much P85 it carried rather than claim it.
#[derive(Default, Debug)]
pub struct P85Tally {
    /// Clock starts found inside a break (each one a sighting).
    pub starts: usize,
    /// Minutes netted off cut credits.
    pub minutes: u64,
}

fn at(v: &Value, what: &str) -> Result<DateTime<FixedOffset>, String> {
    let s = v.as_str().ok_or_else(|| format!("P85: {what} is not a string: {v}"))?;
    DateTime::parse_from_rfc3339(s).map_err(|e| format!("P85: {what} `{s}`: {e}"))
}

/// Whole minutes from `a` to `b`, truncated and at least 0 — the replay's `minutesBetween`, per
/// sub-segment (site R8).
fn mins(a: DateTime<FixedOffset>, b: DateTime<FixedOffset>) -> u64 {
    (b - a).num_seconds().max(0) as u64 / 60
}

/// The day the replay files an instant under: the latest day whose wake is at or before it, if
/// within a day of it; else its own local date (`p81.rs`' rule).
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

/// **The fork's frozen `Replay` moved by P85** (apply it after `p81::carry`). `Ok((answer, tally))`;
/// `Err(finding)` when the rule meets a shape it will not guess at.
pub fn carry(fork_answer: &Value) -> Result<(Value, P85Tally), String> {
    let mut answer = fork_answer.clone();
    let mut tally = P85Tally::default();
    let replay = answer["replay"].as_object_mut().ok_or("P85: the frozen answer has no `replay` object")?;
    let days = replay
        .get("days")
        .and_then(Value::as_object)
        .cloned()
        .ok_or("P85: the frozen replay has no `days`")?;

    let mut breaks: Vec<(String, DateTime<FixedOffset>, DateTime<FixedOffset>)> = Vec::new();
    for (d, day) in &days {
        for seg in day["segments"].as_array().into_iter().flatten() {
            if seg_kind(seg) == Some("Break") {
                breaks.push((d.clone(), at(&seg["start"], "a Break's start")?, at(&seg["end"], "a Break's end")?));
            }
        }
    }
    let covering = |x: DateTime<FixedOffset>| -> Result<Option<DateTime<FixedOffset>>, String> {
        let hits: Vec<_> = breaks.iter().filter(|(_, s, e)| *s <= x && x < *e).collect();
        match hits.as_slice() {
            [] => Ok(None),
            [(_, _, e)] => Ok(Some(*e)),
            _ => Err(format!("P85: the clock started at {x} lies inside {} breaks", hits.len())),
        }
    };

    // The fork's open block: a clock that started inside a break starts at its end.
    if let Some(ob) = replay.get_mut("open_block").filter(|v| !v.is_null()) {
        if let Some(since) = ob.get("since").filter(|v| !v.is_null()).cloned() {
            let x = at(&since, "open_block.since")?;
            if let Some(e) = covering(x)? {
                tally.starts += 1;
                ob["since"] = serde_json::to_value(e).expect("an instant serialises");
            }
        }
    }

    // Per day: (segment index, the piece that replaces it, or none).
    let mut edits: BTreeMap<String, Vec<(usize, Option<Value>)>> = BTreeMap::new();
    let mut credits: BTreeMap<(String, String), u64> = BTreeMap::new();
    for (d, day) in &days {
        for (i, seg) in day["segments"].as_array().into_iter().flatten().enumerate() {
            if seg_kind(seg) != Some("Block") {
                continue;
            }
            let (x, y) = (at(&seg["start"], "a Block's start")?, at(&seg["end"], "a Block's end")?);
            let Some(e) = covering(x)? else { continue };
            tally.starts += 1;
            let id = seg["kind"]["Block"]["id"].as_str().ok_or("P85: a Block with no id")?.to_string();
            let piece = if e < y {
                if day_of(&days, e)? != *d {
                    return Err(format!("P85: the stretch of `{id}` restarted at {e} is not filed on its day {d}"));
                }
                let mut p = seg.clone();
                p["start"] = serde_json::to_value(e).expect("an instant serialises");
                Some(p)
            } else {
                None
            };
            edits.entry(d.clone()).or_default().push((i, piece));
            let netted = mins(x, y) - if e < y { mins(e, y) } else { 0 };
            if netted == 0 {
                continue;
            }
            // A cut credits the clock to the item's ci-unknown minutes on the cut's day; a `done` credits
            // its logged minutes, which P85 leaves alone (`p81.rs`' rule).
            let cut_day = day_of(&days, y)?;
            let unknown = days.get(&cut_day).and_then(|dd| dd["ci_unknown"][&id].as_u64()).unwrap_or(0);
            if unknown == 0 {
                continue;
            }
            let taken = credits.get(&(cut_day.clone(), id.clone())).copied().unwrap_or(0);
            if unknown < taken + netted {
                return Err(format!(
                    "P85: the fork holds {unknown} ci-unknown minutes for `{id}` on {cut_day}, fewer than the {} netted",
                    taken + netted
                ));
            }
            *credits.entry((cut_day, id)).or_default() += netted;
            tally.minutes += netted;
        }
    }

    let days_mut = replay.get_mut("days").and_then(Value::as_object_mut).ok_or("P85: no days")?;
    for (d, mut list) in edits {
        list.sort_by_key(|(i, _)| std::cmp::Reverse(*i));
        let segs = days_mut[&d]["segments"].as_array_mut().ok_or("P85: segments")?;
        for (i, piece) in list {
            match piece {
                Some(p) => segs[i] = p,
                None => {
                    segs.remove(i);
                }
            }
        }
        // Re-sort by start, stably — the replay's own order.
        let mut keyed: Vec<(DateTime<FixedOffset>, Value)> =
            segs.drain(..).map(|g| (at(&g["start"], "a segment's start").expect("parsed above"), g)).collect();
        keyed.sort_by_key(|(t, _)| *t);
        segs.extend(keyed.into_iter().map(|(_, g)| g));
    }
    for ((d, id), m) in &credits {
        let day = days_mut.get_mut(d).ok_or("P85: the cut's day")?;
        let bm = day["block_min"].as_u64().ok_or("P85: block_min")?;
        day["block_min"] = Value::from(bm - m);
        let unk = day["ci_unknown"].as_object_mut().ok_or("P85: ci_unknown")?;
        let left = unk[id].as_u64().expect("checked above") - m;
        if left == 0 {
            unk.remove(id);
        } else {
            unk.insert(id.clone(), Value::from(left));
        }
    }
    let items = replay.get_mut("items").and_then(Value::as_object_mut).ok_or("P85: items")?;
    for ((d, id), m) in &credits {
        let it = items.get_mut(id).ok_or_else(|| format!("P85: no item `{id}`"))?;
        let total = it["minutes"].as_u64().ok_or("P85: an item's minutes")?;
        it["minutes"] = Value::from(total - m);
        let by_day = it["minutes_by_day"].as_object_mut().ok_or("P85: minutes_by_day")?;
        let on = by_day.get(d).and_then(Value::as_u64).ok_or_else(|| format!("P85: `{id}` has no minutes on {d}"))?;
        if on == *m {
            by_day.remove(d);
        } else {
            by_day.insert(d.clone(), Value::from(on - m));
        }
    }
    Ok((answer, tally))
}

// ---------------------------------------------------------------------------
// The D92 log as fork 4748911 can be ASKED it
// ---------------------------------------------------------------------------

/// **One clock start P85 moves** — `support/p81.rs`' `Restarted`, read off the log by the one model of the
/// block family's clock both parity numbers share (`p81::clock_read`).
pub use super::p81::Restarted as Restart;

/// **The clock starts P85 moves in a log, by the kernel's own machine** — `p81::clock_read`'s second half: the
/// file order, the undo mask's survivors and the fork's own refusals, the last break's span remembered, and a
/// clock that starts — at a `start`, an `unpause` or a `resume` — inside it started at its end
/// (`Replay.restartAt`). Never the kernel's answer.
pub fn restarts(text: &str, refused: &[u64]) -> Result<Vec<Restart>, String> {
    super::p81::clock_read(text, refused).map(|c| c.restarts)
}

/// **The log fork 4748911 is asked the D87 and D92 day in**: each break P81 nets between a `pause` of
/// its block stamped as the break is and an `unpause` stamped where the clock restarts (`p81.rs`' own
/// shape, `p81::as_d87_asks`), and each clock start P85 moves followed by a `pause` of its block stamped
/// where the clock started and an `unpause` stamped at the break's end — which fork 4748911's machine nets
/// as the kernel's does. The lines inserted, 1-based in the new log, are returned with it.
///
/// **Refused by name, never guessed: an `undo` that would take an inserted line back** (`p81.rs`' rule).
pub fn as_asked_log(text: &str, n81: &[super::p81::Netted], r85: &[Restart]) -> Result<(String, Vec<u64>), String> {
    let mut out: Vec<String> = Vec::new();
    let mut inserted = Vec::new();
    for (i, raw) in text.split('\n').enumerate() {
        let line = i as u64 + 1;
        if let Some(n) = n81.iter().find(|n| n.line == line) {
            out.push(serde_json::json!({"t": n.at_text, "ev": "pause", "id": n.id}).to_string());
            inserted.push(out.len() as u64);
            out.push(raw.to_string());
            let r = serde_json::to_value(n.restart).expect("an instant serialises");
            out.push(serde_json::json!({"t": r, "ev": "unpause", "id": n.id}).to_string());
            inserted.push(out.len() as u64);
        } else if let Some(r) = r85.iter().find(|r| r.line == line) {
            out.push(raw.to_string());
            out.push(serde_json::json!({"t": r.at_text, "ev": "pause", "id": r.id}).to_string());
            inserted.push(out.len() as u64);
            let e = serde_json::to_value(r.restart).expect("an instant serialises");
            out.push(serde_json::json!({"t": e, "ev": "unpause", "id": r.id}).to_string());
            inserted.push(out.len() as u64);
        } else {
            out.push(raw.to_string());
        }
    }
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
                        return Err(format!("P85: an undo at line {} of the asked log would take back the {of} inserted at line {}", i + 1, stack[k].0));
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

/// **The fork's answer to that log, read as its answer to the log as given, with P81's and P85's
/// drawing**: the `Pause` segment each inserted pair drew taken off (`[break, restart]` for P81 — the
/// break's own `Break` segment is the span, drawn alone — and `[clock start, break's end]` for P85, a
/// stretch no block's clock ran in); the entry count less the lines inserted; and each refused line
/// numbered as in the log as given.
pub fn as_asked_answer(answer: &Value, n81: &[super::p81::Netted], r85: &[Restart], inserted: &[u64]) -> Result<Value, String> {
    let mut a = answer.clone();
    let days = a["replay"]["days"].as_object_mut().ok_or("P85: the asked answer has no days")?;
    let mut drawn: Vec<(String, DateTime<FixedOffset>, DateTime<FixedOffset>)> = Vec::new();
    for n in n81.iter().filter(|n| n.at < n.restart) {
        drawn.push((n.id.clone(), n.at, n.restart));
    }
    for r in r85.iter().filter(|r| r.at < r.restart) {
        drawn.push((r.id.clone(), r.at, r.restart));
    }
    for (id, s, e) in &drawn {
        let mut hit = false;
        for day in days.values_mut() {
            if let Some(segs) = day["segments"].as_array_mut() {
                let before = segs.len();
                segs.retain(|g| {
                    !(seg_kind(g) == Some("Pause")
                        && g["kind"]["Pause"]["id"] == id.as_str()
                        && at(&g["start"], "").ok() == Some(*s)
                        && at(&g["end"], "").ok() == Some(*e))
                });
                hit |= segs.len() < before;
            }
        }
        if !hit {
            return Err(format!("P85: the fork drew no Pause for the pair inserted for `{id}` at {s}"));
        }
    }
    let entries = a["entries"].as_u64().ok_or("P85: the asked answer has no entry count")?;
    a["entries"] = Value::from(entries - inserted.len() as u64);
    let lines: Vec<u64> = a["warningLines"].as_array().ok_or("P85: no warningLines")?.iter().filter_map(Value::as_u64).collect();
    let mut back = Vec::new();
    for l in lines {
        if inserted.contains(&l) {
            return Err(format!("P85: the fork refused a line this module inserted (line {l})"));
        }
        back.push(Value::from(l - inserted.iter().filter(|i| **i < l).count() as u64));
    }
    a["warningLines"] = Value::Array(back);
    Ok(a)
}
