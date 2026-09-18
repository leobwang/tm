//! **T16 `rust_unit_reserve_is_the_kernels`** (stage 5 D10 step L8, host half;
//! design `kernel/design/stage5/stage5-D9-D10-design.md` §13.8, kernel/README.md
//! gap 94).
//!
//! Two reserves over capacities stay Rust until stage 6: `planner.rs`'s week
//! allocation and `tui/queue.rs`'s "fits". Since L8 both run in exact units over
//! the kernel's days (`tm_core::capacity::reserve_units`,
//! `available_until_units`). This proptest holds that reserve to the kernel's own
//! pass (`Capacity.lean`'s `reserveRest`/`reserveOut`, reached through the
//! capacity wire, no harness op):
//!
//! * **the days** are the kernel's: day 0 derived by the kernel from a stored
//!   window of a random length (stage 6 step L9 — `day0` is no longer an
//!   argument, so the generator moves the *window*), and six future days mixed
//!   at random six-decimal lounge weights, so the units are not whole minutes;
//! * **the grants**: random dated candidates (level, minutes, due within the
//!   week) are served by the kernel's EDF pass and, in the same order (due, then
//!   request order), by Rust's unit reserve over the kernel's days — each
//!   deadline's availability and allocation must be identical;
//! * **the remaining units**: 42 probes, one per level and day, are undated
//!   candidates with a floor of 0 minutes to that day, so the kernel reports, as
//!   each probe's availability, the units its pass left at levels ≥ the probe's
//!   up to that day (`Look.a_floor_answer_reads_what_the_pass_left`); Rust's
//!   remaining units must be the same numbers.
//!
//! 256 cases. The zone is UTC (the wire needs one; walls are none).
//!
//! Every request carries a `log` section beside its `capacity` section since L9:
//! day 0 is derived from the replay of the same call (D24's seam), and a
//! capacity request without one is refused `day0WithoutLog`. These logs are
//! empty, so today has no sleep reading and no energy report.

#[allow(dead_code)]
#[path = "../src/cli/tz_table.rs"]
mod tz_table;

use chrono::{Duration, NaiveDate};
use proptest::prelude::*;
use serde_json::{json, Value};
use tm_core::capacity::{available_until_units, reserve_units, upto_units, UnitCapacity, CAP_DEN};

const TODAY: &str = "2026-09-07";

fn today() -> NaiveDate {
    NaiveDate::parse_from_str(TODAY, "%Y-%m-%d").expect("a date")
}

/// The `log` section every capacity request carries since step L9: genesis in one
/// call over an empty log, asking for the facts the seam hands the capacity reader.
const LOG_SECTION: &str =
    r#"{"ckpt":null,"from":1,"lines":[],"terminated":true,"reseal":null,"want":{"facts":true,"headersFrom":null,"render":[]},"sealed":null}"#;

/// The request: no documents, the given weights, a stored window of `hours` hours
/// from 07:00 (day 0's, which the kernel derives) and the candidates.
fn request(tz: &Value, weights: &[u32; 7], hours: u32, cands: &[(u8, u32, u8)]) -> String {
    let week = ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"];
    let p_config: serde_json::Map<String, Value> = week
        .iter()
        .zip(weights)
        .map(|(k, w)| (k.to_string(), json!({"num": w.to_string(), "den": "1000000"})))
        .collect();
    let arrival: serde_json::Map<String, Value> = week.iter().map(|k| (k.to_string(), json!("07:00"))).collect();
    let step = |from: u64, to: Option<u64>, level: u8| {
        json!({"from": {"num": from, "den": 1}, "to": to.map(|t| json!({"num": t, "den": 1})), "level": level})
    };
    let mut items: Vec<Value> = cands
        .iter()
        .enumerate()
        .map(|(i, (ci, rem, due))| {
            json!({"id": format!("d{i}"), "ci": ci, "rootPrio": null, "remaining": rem,
                   "due": (today() + Duration::days(i64::from(*due))).to_string(), "window": false, "wall": false,
                   "optional": false, "overdue": false, "mandatory": false, "hot": false, "yesterday": null,
                   // Section 8.2 step 5's nine, all plain (stage 6 P5a): section 7's
                   // pass does not read them (`prioritiesWithFloors_ignores_the_plan_facts`).
                   "plan": {"plannedMin": 0, "multiplier": {"num": 1, "den": 1}, "loc": "any", "splittable": true, "cap": null, "state": " ", "blockedBy": [], "wallToday": false}})
        })
        .collect();
    for ci in 0..6u8 {
        for k in 0..7i64 {
            items.push(json!({"id": format!("probe{ci}-{k}"), "ci": ci, "rootPrio": null, "remaining": 0,
                "due": null, "window": false, "wall": false, "optional": false, "overdue": false,
                "mandatory": false, "hot": false, "yesterday": null,
                "plan": {"plannedMin": 0, "multiplier": {"num": 1, "den": 1}, "loc": "any", "splittable": true, "cap": null, "state": " ", "blockedBy": [], "wallToday": false},
                "floor": {"left": 0, "until": (today() + Duration::days(k)).to_string()}}));
        }
    }
    let body = json!({
        "docs": [],
        "now": TODAY,
        "blockMin": 60,
        "tz": tz,
        "capacity": {
            "pLounge": {"config": p_config},
            "arrival": {"config": arrival},
            "prior": {
                "lounge": [step(0, Some(4), 5), step(4, Some(8), 3), step(8, None, 1)],
                "home": [step(0, Some(6), 3), step(6, None, 2)],
            },
            "homeMaxCi": 3,
            "day": {"breakMin": 20, "breakAfterBlocks": 2, "minLastBlockMin": 30,
                    "windowHours": {"num": 8, "den": 1}, "windowCap": "19:00", "budgetRatio": {"num": 3, "den": 4},
                    "windDown": "21:30", "bed": "22:00"},
            "priority": {"bins": [{"num": 1, "den": 2}, {"num": 1, "den": 4}, {"num": 1, "den": 10}],
                         "safety": {"num": 13, "den": 10}, "defaultPriority": 3},
            "days": 7,
            "at": format!("{TODAY}T07:00:00+00:00"),
            "state": {"date": TODAY, "window": {"from": "07:00", "to": hhmm(7 * 60 + hours * 60)},
                      "budget": 6, "arrival": null, "loc": "lounge", "allowHome": false},
            "posterior": {"fullHours": {"num": 3, "den": 1}, "zeroHours": {"num": 6, "den": 1}},
            "sleep": {"shiftModel": null, "shiftConfig": {"neg": false, "num": 1, "den": 1},
                      "underHours": {"num": 7, "den": 1}},
            "candidates": {"hysteresis": false, "items": items},
        }
    })
    .to_string();
    // The `log` section is spliced as text beside `capacity` (the checkpoint's keys are read in
    // build order, so nothing about a section may go through `serde_json::Value`).
    format!(r#"{{"log":{LOG_SECTION},{}"#, &body[1..])
}

/// `HH:MM` of a minute of the day.
fn hhmm(min: u32) -> String {
    format!("{:02}:{:02}", min / 60, min % 60)
}

fn units(v: &Value) -> u128 {
    v.as_str().and_then(|s| s.parse::<u128>().ok()).unwrap_or_else(|| panic!("a digit string: {v}"))
}

fn check(tz: &Value, weights: [u32; 7], hours: u32, cands: Vec<(u8, u32, u8)>) -> Result<(), TestCaseError> {
    let raw = tm_kernel_ffi::call(&request(tz, &weights, hours, &cands)).expect("kernel call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    let la = &resp["ok"]["lookahead"];
    prop_assert!(la.is_object(), "{}", raw);
    let days: Vec<UnitCapacity> = la["days"]
        .as_array()
        .expect("days")
        .iter()
        .map(|d| UnitCapacity {
            date: NaiveDate::parse_from_str(d["day"].as_str().expect("day"), "%Y-%m-%d").expect("date"),
            units: std::array::from_fn(|l| units(&d["numAt"][l])),
        })
        .collect();
    prop_assert_eq!(days.len(), 7);
    let grants = la["grants"].as_array().expect("grants");
    prop_assert_eq!(grants.len(), cands.len() + 42);

    // The pass, in Rust: due ascending, request order on a tie, R1's ceiling need.
    let mut order: Vec<usize> = (0..cands.len()).collect();
    order.sort_by_key(|&i| (cands[i].2, i));
    let mut work = days.clone();
    for i in order {
        let (ci, rem, due) = cands[i];
        let due = today() + Duration::days(i64::from(due));
        let need = u128::from((u64::from(rem) * 13).div_ceil(10)) * CAP_DEN;
        let avail = available_until_units(&work, due, ci);
        let take = need.min(avail);
        let n = upto_units(&work, due);
        let got = reserve_units(&mut work[..n], take, ci);
        prop_assert_eq!(got, take);
        prop_assert_eq!(units(&grants[i]["avail"]), avail, "avail of {}", grants[i]);
        prop_assert_eq!(units(&grants[i]["allocation"]), got, "allocation of {}", grants[i]);
    }
    // What the pass left, level by level and day by day.
    for ci in 0..6u8 {
        for k in 0..7i64 {
            let g = &grants[cands.len() + usize::from(ci) * 7 + k as usize];
            // Answered at its floor: `until` is the floor's day (a floor the pass left
            // nothing for is `0/0`, HOT by parity P2, still at its floor).
            let day = (today() + Duration::days(k)).to_string();
            prop_assert_eq!(g["until"].as_str(), Some(day.as_str()), "{}", g);
            let left = available_until_units(&work, today() + Duration::days(k), ci);
            prop_assert_eq!(units(&g["avail"]), left, "what the pass left: {}", g);
        }
    }
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn rust_unit_reserve_is_the_kernels(
        weights in proptest::array::uniform7(0u32..=1_000_000),
        hours in 1u32..=11,
        cands in proptest::collection::vec((0u8..6, 0u32..900, 0u8..7), 1..12),
    ) {
        thread_local! {
            static TZ: Value = tz_table::probe(chrono_tz::UTC).to_wire();
        }
        TZ.with(|tz| check(tz, weights, hours, cands))?;
    }
}

/// A fixed case, pinned by hand. **Restated at step L9**, because `day0` stopped
/// being an argument: the stored window is 07:00-08:00, so the kernel derives one
/// 60-minute block, at the lounge prior's `0-4` level 5 (`[0,0,0,0,0,60]`, where
/// this case used to hand in `[0,0,60,0,0,60]`). Every number it asserts is
/// unchanged, because all four read the level-5 hour: `d0` (level 2, 30 minutes,
/// due Tuesday) is listed before `d1` (level 5, 50 minutes, need 65, due Monday),
/// EDF serves `d1` first, and it takes all 60 of Monday's level-5 minutes
/// (IMPOSSIBLE, 5 short). Served in request order, `d0` would have taken those
/// same minutes first and left `d1` 21. The whole comparison holds too.
#[test]
fn a_fixed_case_is_served_earliest_deadline_first() {
    let tz = tz_table::probe(chrono_tz::UTC).to_wire();
    let cands = vec![(2u8, 30u32, 1u8), (5, 50, 0)];
    let raw = tm_kernel_ffi::call(&request(&tz, &[500_000; 7], 1, &cands)).expect("call");
    let resp: Value = serde_json::from_str(&raw).expect("json");
    let grants = resp["ok"]["lookahead"]["grants"].as_array().expect("grants");
    assert_eq!(units(&grants[1]["avail"]), 60 * CAP_DEN, "{raw}");
    assert_eq!(units(&grants[1]["allocation"]), 60 * CAP_DEN, "{raw}");
    assert_eq!(grants[1]["class"], "impossible", "{raw}");
    assert_eq!(units(&grants[1]["shortfall"]), 5 * CAP_DEN, "{raw}");
    let mut day = vec![UnitCapacity { date: today(), units: [0, 0, 0, 0, 0, 60 * CAP_DEN] }];
    reserve_units(&mut day, 39 * CAP_DEN, 2);
    assert_eq!(day[0].units[5], 21 * CAP_DEN, "request order would have left d1 21 minutes");
    assert!(check(&tz, [500_000; 7], 1, cands).is_ok());
}
