//! **The facts D14 ports though nothing reads them**, pinned as an oracle
//! (design §4 Q7 option (b), §22.1; step R11 under the owner's D14).
//!
//! `ItemReplay.{stops, extended_min, done_at, partial_done_at}`,
//! `Replay.{closes, dropped_items, open_interrupt, longest_leak, interrupts}`
//! and `DayReplay.{replans_today, last_plan_hash, loc_changes, dropped,
//! longest_leak}` have no reader in the binary and appear in no output. The
//! design's default deleted them before the port; D14 keeps them, the kernel
//! derives them in phase C, and W1's day records carry them. Until the switch
//! the Rust replay is the reference, and after it this file's snapshots are:
//! every value of [`Replay::ported_facts`] over the four corpus logs and
//! loggen's 1-month logs at both rates, in `America/Chicago`, plus the open
//! interruption at every line prefix of `three-days` (no whole log ends
//! inside one).

#[path = "../../tm/tests/support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

#[path = "../../tm/tests/support/loggen.rs"]
#[allow(dead_code)]
mod loggen;

use chrono_tz::Tz;
use tm_core::log::Replay;

const TZ: Tz = chrono_tz::America::Chicago;

fn corpus(name: &str) -> String {
    let path = format!("{}/../kernel/corpus/logs/{name}.jsonl", env!("CARGO_MANIFEST_DIR"));
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{path}: {e}"))
}

fn replay(text: &str) -> Replay {
    chokepoint::replay_of_text(text, TZ)
}

#[test]
fn three_days_ported_facts() {
    let r = replay(&corpus("three-days"));
    let f = r.ported_facts();
    // Every family carries a value on this log (the fixture exercises
    // `extend`, `stop`, a partial `done`, `close`, `drop`, `loc`, interruptions
    // and plans), so the snapshot pins more than empty containers.
    assert_eq!(f.closes.len(), 2);
    assert_eq!(f.interrupts.len(), 2);
    assert_eq!(f.longest_leak.map(|l| l.min), Some(25));
    assert_eq!(f.items.values().map(|i| i.stops).sum::<u32>(), 1);
    assert_eq!(f.items.values().map(|i| i.extended_min).sum::<u32>(), 60);
    assert_eq!(f.items.values().map(|i| i.partial_done_at.len()).sum::<usize>(), 2);
    assert_eq!(f.days.values().map(|d| d.loc_changes.len()).sum::<usize>(), 4);
    assert_eq!(f.days.values().map(|d| d.dropped.len()).sum::<usize>(), 1);
    insta::assert_json_snapshot!("three_days", f);
}

#[test]
fn energy_14d_ported_facts() {
    insta::assert_json_snapshot!("energy_14d", replay(&corpus("energy-14d")).ported_facts());
}

#[test]
fn review_14d_ported_facts() {
    insta::assert_json_snapshot!("review_14d", replay(&corpus("review-14d")).ported_facts());
}

#[test]
fn malformed_ported_facts() {
    insta::assert_json_snapshot!("malformed", replay(&corpus("malformed")).ported_facts());
}

#[test]
fn loggen_one_month_ported_facts() {
    for (rate, name) in [(loggen::Rate::Forty, "loggen_1mo_40"), (loggen::Rate::SixtyOne, "loggen_1mo_61")] {
        let r = replay(&loggen::text(&loggen::log(rate, 30)));
        let f = r.ported_facts();
        assert!(!f.closes.is_empty() && !f.dropped_items.is_empty() && !f.interrupts.is_empty(), "{name}");
        assert!(f.items.values().any(|i| i.stops > 0), "{name}: a stop");
        assert!(f.items.values().any(|i| i.extended_min > 0), "{name}: an extend");
        assert!(f.items.values().any(|i| !i.partial_done_at.is_empty()), "{name}: a partial done");
        insta::assert_json_snapshot!(name, f);
    }
}

#[test]
fn three_days_open_interrupt_at_every_prefix() {
    let text = corpus("three-days");
    let lines: Vec<&str> = text.lines().collect();
    let open: Vec<(usize, serde_json::Value)> = (0..=lines.len())
        .filter_map(|k| {
            let r = replay(&lines[..k].join("\n"));
            r.ported_facts().open_interrupt.map(|i| (k, serde_json::to_value(i).expect("json")))
        })
        .collect();
    assert!(!open.is_empty(), "some prefix ends inside an interruption");
    insta::assert_json_snapshot!("three_days_open_interrupt_by_prefix", open);
}

#[test]
fn the_ported_facts_are_the_replay_fields_themselves() {
    // The view borrows; it neither filters nor recomputes. Checked on every
    // log above against the plain fields.
    let logs = [
        corpus("three-days"),
        corpus("energy-14d"),
        corpus("review-14d"),
        corpus("malformed"),
        loggen::text(&loggen::log(loggen::Rate::Forty, 30)),
        loggen::text(&loggen::log(loggen::Rate::SixtyOne, 30)),
    ];
    for text in &logs {
        let r = replay(text);
        let f = r.ported_facts();
        assert_eq!(f.closes, &r.closes[..]);
        assert_eq!(f.dropped_items, &r.dropped_items);
        assert_eq!(f.open_interrupt, r.open_interrupt.as_ref());
        assert_eq!(f.longest_leak, r.longest_leak.as_ref());
        assert_eq!(f.interrupts, &r.interrupts[..]);
        assert_eq!(f.days.len(), r.days.len());
        for (d, day) in &r.days {
            let p = &f.days[d];
            assert_eq!(p.replans_today, day.replans_today);
            assert_eq!(p.last_plan_hash, day.last_plan_hash.as_deref());
            assert_eq!(p.loc_changes, &day.loc_changes[..]);
            assert_eq!(p.dropped, &day.dropped[..]);
            assert_eq!(p.longest_leak, day.longest_leak);
        }
        assert_eq!(f.items.len(), r.items.len());
        for (id, it) in &r.items {
            let p = &f.items[id.as_str()];
            assert_eq!((p.stops, p.extended_min), (it.stops, it.extended_min));
            assert_eq!(p.done_at, &it.done_at[..]);
            assert_eq!(p.partial_done_at, &it.partial_done_at[..]);
        }
    }
}
