//! **A meeting that paused the running block is drawn as the WALL ALONE, and
//! the pause is SAID when it is logged** — the owner's D65 (stage 6 W-37 track
//! T, parity P56, README gaps 3044, 3141 and 3142).
//!
//! `plan-basic`'s calendar holds `^g1 Meeting w/ host at:2026-09-07T12:50/13:50`.
//! A block started at 12:00 runs into it, and D61 (P53) logs a `pause` at the
//! wall's start and an `unpause` at its end. Until D65 that pause was:
//!
//! * **drawn twice** — `tm plan` showed the meeting's Wall row AND a `paused`
//!   Lost row over the same span, a span `tm review day` counts as `lost 0`
//!   (gaps 3044, 3142);
//! * **silent** — nothing said the fifty minutes had been netted out, and the
//!   day file's journal held `12:00 start ^t4` and `14:20 done ^t4` and no
//!   pause line, where a typed `tm pause` writes one (gap 3141).
//!
//! Every test reads the bytes a user reads: the plan's segments, the review's
//! lost minutes, stderr, and the day file.

mod cli_common;

use cli_common::Tm;
use serde_json::Value;

/// The day file the journal lines land in.
const DAY: &str = "day/2026-09-07.md";

/// The notice D65 prints, for `^t4` and `^g1`.
const NOTICE: &str = "paused ^t4 for Meeting w/ host 12:50–13:50";

/// A day with `^t4` started at 12:00, fifty minutes before the meeting.
fn running_before_the_meeting() -> Tm {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok_at("2026-09-07T12:00:00-05:00", &["start", "^t4", "--energy", "4"]);
    tm
}

/// `(kind, start, end, item, text)` of every segment of `tm --json plan` at `at`.
fn segments(tm: &Tm, at: &str) -> Vec<(String, String, String, Option<String>, String)> {
    let plan = tm.json_at(at, &["plan"]);
    plan["segments"]
        .as_array()
        .cloned()
        .unwrap_or_default()
        .iter()
        .map(|s| {
            let st = |k: &str| s[k].as_str().unwrap_or_default().to_string();
            (st("kind"), st("start"), st("end"), s["item"].as_str().map(str::to_string), st("text"))
        })
        .collect()
}

/// The journal lines of the day file (`## Log`), in file order.
fn journal(tm: &Tm) -> Vec<String> {
    let text = tm.read(DAY);
    let mut out = Vec::new();
    let mut inside = false;
    for line in text.lines() {
        if line.starts_with("## ") {
            inside = line == "## Log";
            continue;
        }
        if inside && !line.trim().is_empty() {
            out.push(line.to_string());
        }
    }
    out
}

/// The minutes of every Lost segment of the plan — what `tm plan` draws as lost.
fn drawn_lost_min(segs: &[(String, String, String, Option<String>, String)]) -> u32 {
    let min = |hhmm: &str| -> u32 {
        let (h, m) = hhmm.split_once(':').unwrap_or(("0", "0"));
        h.parse::<u32>().unwrap_or(0) * 60 + m.parse::<u32>().unwrap_or(0)
    };
    segs.iter().filter(|s| s.0 == "lost").map(|s| min(&s.2).saturating_sub(min(&s.1))).sum()
}

/// **The drive, pinned (D65's first half).**  After the meeting, `tm plan`
/// draws the meeting as its Wall row and no Lost row over it, and the lost
/// minutes the plan draws are the lost minutes `tm review day` counts: zero.
#[test]
fn a_meeting_that_paused_the_block_is_drawn_as_the_wall_alone() {
    let tm = running_before_the_meeting();
    let segs = segments(&tm, "2026-09-07T14:10:00-05:00");
    let over_meeting: Vec<_> = segs
        .iter()
        .filter(|s| s.1.as_str() < "13:50" && s.2.as_str() > "12:50")
        .collect();
    assert_eq!(
        over_meeting.iter().map(|s| s.0.as_str()).collect::<Vec<_>>(),
        vec!["wall"],
        "the meeting is drawn as its Wall row and nothing else: {over_meeting:?}"
    );
    // Since the owner's D68 (P59) a replayed pause is drawn as a PAUSE — kind
    // `pause`, `paused <dur>` — so "no paused row" is asked of that kind: the
    // meeting's pause left nothing outside the wall to draw.
    assert!(
        !segs.iter().any(|s| s.0 == "pause" || s.4.contains("paused")),
        "no pause row is drawn: {segs:?}"
    );
    let review = tm.json_at("2026-09-07T14:11:00-05:00", &["review", "day"]);
    assert_eq!(review["review"]["lost_min"], 0, "{review}");
    assert_eq!(
        drawn_lost_min(&segs),
        0,
        "`tm plan` and `tm review day` read one lost figure for the day: {segs:?}"
    );
    // The meeting was still netted out: the stretch before it ends at its start.
    assert!(
        segs.iter().any(|s| s.0 == "block" && s.1 == "12:00" && s.2 == "12:50"),
        "{segs:?}"
    );
}

/// **The pause is said (D65's second half), once, while the meeting runs.**
/// The first verb inside the meeting prints the one line naming the block and
/// the wall on stderr — stdout stays the verb's own, `--json` included — and
/// writes the day file's journal line a typed `tm pause` writes, at the wall's
/// start. The next verb says nothing more; the one after the meeting ended
/// writes the `unpause` line, at the wall's end, and says nothing either.
#[test]
fn the_pause_is_said_once_and_journaled_at_the_walls_start() {
    let tm = running_before_the_meeting();
    let during = tm.run_at("2026-09-07T13:20:00-05:00", &["--json", "now"]);
    assert_eq!(during.code, 0, "{}", during.stderr);
    assert!(during.stderr.contains(NOTICE), "the notice names the block and the wall: {:?}", during.stderr);
    let _: Value = serde_json::from_str(&during.stdout).expect("stdout is still the verb's JSON");
    assert!(journal(&tm).contains(&"12:50 pause ^t4".to_string()), "{:?}", journal(&tm));

    let again = tm.run_at("2026-09-07T13:25:00-05:00", &["now"]);
    assert_eq!(again.code, 0);
    assert!(!again.stderr.contains("paused ^t4 for"), "said once: {:?}", again.stderr);

    let after = tm.run_at("2026-09-07T14:10:00-05:00", &["now"]);
    assert_eq!(after.code, 0);
    assert!(!after.stderr.contains("paused ^t4 for"), "the unpause is not announced: {:?}", after.stderr);
    let j = journal(&tm);
    let at = |l: &str| j.iter().position(|x| x == l);
    assert!(at("12:50 pause ^t4").is_some() && at("13:50 unpause ^t4").is_some(), "{j:?}");
    assert!(at("12:50 pause ^t4") < at("13:50 unpause ^t4"), "{j:?}");
    assert_eq!(j.iter().filter(|l| l.contains("pause ^t4")).count(), 2, "each written once: {j:?}");
}

/// **A verb run only after the meeting ended says it once and journals both**,
/// in order — the automatic close's catching-up shape.
#[test]
fn a_verb_after_the_meeting_says_it_once_and_journals_the_pair() {
    let tm = running_before_the_meeting();
    let out = tm.run_at("2026-09-07T14:10:00-05:00", &["now"]);
    assert_eq!(out.code, 0, "{}", out.stderr);
    assert_eq!(out.stderr.matches("paused ^t4 for").count(), 1, "{:?}", out.stderr);
    assert!(out.stderr.contains(NOTICE), "{:?}", out.stderr);
    let j = journal(&tm);
    let pair: Vec<&String> = j.iter().filter(|l| l.contains("pause ^t4")).collect();
    assert_eq!(pair, vec!["12:50 pause ^t4", "13:50 unpause ^t4"], "{j:?}");
}

/// **One spelling for both writers**: the line a typed `tm pause` writes is
/// the line D61's automatic pause writes, stamped at its own instant.
#[test]
fn a_typed_pause_writes_the_journal_line_the_wall_writes() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T12:30:00-05:00", &["pause"]);
    tm.ok_at("2026-09-07T12:40:00-05:00", &["pause"]);
    let j = journal(&tm);
    assert!(j.contains(&"12:30 pause ^t4".to_string()) && j.contains(&"12:40 unpause ^t4".to_string()), "{j:?}");
}

/// **A pause that straddles the meeting keeps the minutes outside it** — the
/// rule is a cut, not a drop (AGENTS §5.8: it does not over-bite).  The user
/// paused at 12:40, before the meeting, so the wall wrote nothing (the timer
/// was already stopped), and resumed at 14:00, after it: the plan draws the
/// paused stretch before the meeting and the one after it, and the meeting as
/// its Wall row alone.
#[test]
fn a_pause_that_straddles_the_meeting_is_drawn_outside_it() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T12:40:00-05:00", &["pause"]);
    let out = tm.ok_at("2026-09-07T14:00:00-05:00", &["pause"]);
    assert!(!out.stderr.contains("paused ^t4 for"), "the wall paused nothing: {:?}", out.stderr);
    let segs = segments(&tm, "2026-09-07T14:10:00-05:00");
    // Drawn as a pause since the owner's D68 (P59): kind `pause`, `paused <dur>`.
    let paused: Vec<(String, String)> = segs
        .iter()
        .filter(|s| s.0 == "pause" && s.4.contains("paused"))
        .map(|s| (s.1.clone(), s.2.clone()))
        .collect();
    assert_eq!(
        paused,
        vec![("12:40".to_string(), "12:50".to_string()), ("13:50".to_string(), "14:00".to_string())],
        "the paused minutes outside the meeting are drawn, the meeting is not: {segs:?}"
    );
    assert!(
        segs.iter().any(|s| s.0 == "wall" && s.1 == "12:50" && s.2 == "13:50"),
        "{segs:?}"
    );
}

/// **A pause no wall touches is drawn whole**: paused 12:10–12:30, before the
/// meeting. Fork 4748911 drew it whole as a `lost 20m … paused` row; since the
/// owner's D68 (P59) it is drawn whole as a pause, `paused 20m`, kind `pause`.
#[test]
fn a_pause_no_wall_touches_is_drawn_whole() {
    let tm = running_before_the_meeting();
    tm.ok_at("2026-09-07T12:10:00-05:00", &["pause"]);
    tm.ok_at("2026-09-07T12:30:00-05:00", &["pause"]);
    let segs = segments(&tm, "2026-09-07T12:45:00-05:00");
    assert!(
        segs.iter().any(|s| s.0 == "pause" && s.1 == "12:10" && s.2 == "12:30" && s.4.contains("paused 20m")),
        "{segs:?}"
    );
}
