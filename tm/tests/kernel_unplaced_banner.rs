//! **D67 through the FFI: the day SAYS why an owed impossible item has no row**
//! (stage 6 W-38, track K; README gap 3160, parity P58).
//!
//! The owner's D67 keeps §8.2 step 5 greedy — the fork's `pick`, which never
//! reads a grant — and asks the day to NAME why an impossible item step 5's
//! filter admitted before the walk found no place. The kernel writes the reason
//! (`Planner.PlanReq.dayUnplaced`, `diagnostics.unplaced` on the wire), the
//! host's codec reads it (`planwire::read_plan`) and the banner prints it
//! (`emit::render_banners`, `tm plan`'s `IMPOSSIBLE` lines).
//!
//! **Which binary this drives.** Until R3 the shipped `tm plan` plans with the
//! fork's `planner::plan`, which names nothing, so no shipped path prints the
//! reason yet: this test drives the KERNEL's planner through `tm_kernel_call`
//! and the codec R3 swaps in, on a hand-written world, and renders the banner
//! from the decoded day — the surface R3 ships.
//!
//! The world: a late arrival (14:00, so the window is 14:00–19:00 and the day
//! has fewer slots than the budget), `^h1` due TODAY and short 50 blocks, ci 0,
//! splittable — it fits every slot and step 5 serves it first (D60: the
//! earlier-due impossible item) — and `^p1` due TOMORROW, short too, ATOMIC and
//! capped at three blocks today (`max:3b/d`), so it needs one unbroken
//! 180-minute run. `^h1` takes every slot, so every run `^p1` fits went to
//! work ranked before it: the day names it `no run left`.

mod planner_common;

use planner_common::{at, date, of_texts, DayPlanner, Kernel};
use chrono::NaiveTime;
use tm_core::dayplan::NoPlace;
use tm_core::model::Id;
use tm_core::store::RuntimeState;

const WEEK: &str = "# Tasks\n\
- [ ] 0 50b Hard task due:2026-09-07 ^h1\n\
- [ ] 2 50b Plain task max:3b/d atomic due:2026-09-08 ^p1\n";

fn late_state() -> RuntimeState {
    RuntimeState {
        date: Some(date("2026-09-07")),
        wake: Some(NaiveTime::from_hms_opt(7, 0, 0).expect("time")),
        arrival: Some(NaiveTime::from_hms_opt(14, 0, 0).expect("time")),
        loc: Some("lounge".to_string()),
        ..RuntimeState::default()
    }
}

fn world() -> planner_common::Fixture {
    of_texts(&[("week/2026-W37.md", WEEK)], "")
}

/// **The kernel's day names `^p1`, and the banner says why** — the reason
/// crosses the wire, the codec reads it, and `tm plan`'s banner line carries
/// it after the shortfall.
#[test]
fn the_kernel_names_the_atomic_item_its_run_was_taken_from() {
    let fx = world();
    let state = late_state();
    let now = at("2026-09-07", 14, 0);
    let day = Kernel.day(&fx, &state, now);
    let listed: Vec<&str> = day.diagnostics.impossible.iter().map(|(i, _, _)| i.as_str()).collect();
    assert!(listed.contains(&"h1") && listed.contains(&"p1"), "both are impossible: {listed:?}");
    // `^h1` holds the day; `^p1` holds nothing.
    let held: Vec<String> = day
        .segments
        .iter()
        .filter(|s| s.kind.is_work())
        .flat_map(|s| s.items())
        .map(|i| i.as_str().to_string())
        .collect();
    assert!(held.iter().any(|i| i == "h1"), "{held:?}");
    assert!(!held.iter().any(|i| i == "p1"), "{held:?}");
    assert_eq!(day.diagnostics.unplaced, vec![(Id::new("p1"), NoPlace::NoRunLeft)]);
    let banners = tm_core::emit::render_banners(&day, &fx.tree, &fx.cfg);
    // The drive's record (`--nocapture`): the rows and the banner lines `tm plan`
    // prints (`IMPOSSIBLE {banner}`, `tm/src/cli/planning.rs`).
    for s in &day.segments {
        println!("{} {:?} {:?}", tm_core::dayplan::fmt_clock(s.start), s.kind, s.item.as_ref().map(|i| i.as_str()));
    }
    for b in &banners {
        println!("IMPOSSIBLE {b}");
    }
    let p1 = banners
        .iter()
        .find(|b| b.contains("Plain task"))
        .unwrap_or_else(|| panic!("no banner for ^p1: {banners:?}"));
    assert!(p1.ends_with(" · not placed: no run left"), "{p1}");
    // `^h1` is placed, so its banner says nothing more than the shortfall.
    let h1 = banners.iter().find(|b| b.contains("Hard task")).expect("a banner for ^h1");
    assert!(!h1.contains("not placed"), "{h1}");
}

/// **A budget the walk spends is named `budget spent`**: the same world with
/// a budget of one block — `^h1` takes the first slot and spends it, and the
/// walk passes the slots `^p1`'s runs start at.
#[test]
fn a_budget_the_walk_spends_is_named() {
    let fx = world();
    let state = RuntimeState { budget: Some(1), ..late_state() };
    let now = at("2026-09-07", 14, 0);
    let day = Kernel.day(&fx, &state, now);
    assert_eq!(day.diagnostics.unplaced, vec![(Id::new("p1"), NoPlace::BudgetSpent)]);
    let banners = tm_core::emit::render_banners(&day, &fx.tree, &fx.cfg);
    assert!(
        banners.iter().any(|b| b.contains("Plain task") && b.ends_with(" · not placed: budget spent")),
        "{banners:?}"
    );
}

/// **The reason is printed and not serialised** (README gap 3351): the
/// diagnostics `tm plan --json` and `.tm/last_plan.json` write carry no
/// `unplaced` key on a day that names an item — the name is the one thing that
/// differs from the fork's day, and it reaches the banner. (The fork's half —
/// the kernel's day serialises the fork's diagnostics keys, key for key — is in
/// this file's fork region, which R3 deleted.)
#[test]
fn the_json_keeps_the_forks_diagnostics_shape() {
    let fx = world();
    let now = at("2026-09-07", 14, 0);
    let named = Kernel.day(&fx, &late_state(), now);
    assert!(!named.diagnostics.unplaced.is_empty());
    let v = serde_json::to_value(&named.diagnostics).expect("serialises");
    assert!(v.get("unplaced").is_none(), "{v}");
}

/// **An impossible item no slot admits is named too** (README gap 3523, the
/// W-38 repair): the same world with `^p1` at `loc:home` on a lounge day — §8.2
/// step 5's filter admits it at no slot, so no walk dropped it — was listed
/// IMPOSSIBLE and named nothing; the day now names it `no slot admits it`, and
/// the banner says so after the shortfall.
#[test]
fn an_impossible_item_no_slot_admits_is_named() {
    let week = WEEK.replace("atomic due:2026-09-08 ^p1", "atomic loc:home due:2026-09-08 ^p1");
    assert_ne!(week, WEEK);
    let fx = of_texts(&[("week/2026-W37.md", &week)], "");
    let day = Kernel.day(&fx, &late_state(), at("2026-09-07", 14, 0));
    let listed: Vec<&str> = day.diagnostics.impossible.iter().map(|(i, _, _)| i.as_str()).collect();
    assert!(listed.contains(&"p1"), "^p1 is impossible: {listed:?}");
    assert_eq!(day.diagnostics.unplaced, vec![(Id::new("p1"), NoPlace::NoSlotAdmits)]);
    let banners = tm_core::emit::render_banners(&day, &fx.tree, &fx.cfg);
    assert!(
        banners.iter().any(|b| b.contains("Plain task") && b.ends_with(" · not placed: no slot admits it")),
        "{banners:?}"
    );
}

