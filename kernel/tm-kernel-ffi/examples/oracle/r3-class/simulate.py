#!/usr/bin/env python3
"""**R3's deletion of the class it orphans, applied to a tree** (stage 6 W-46 track C;
kernel/README.md gap 4752, restated as a class there).

    python3 simulate.py <tree>

`<tree>` holds the switch (`refs/archive/w45/r3-switch`, or the step that lands it) and
track C's commit.  This deletes `deletion-functions.txt` and `deletion-tests.txt`
(delete_fns.py), makes the line edits below, removes the one snapshot only a deleted test
wrote, and prints what it did.  Every edit names its anchor and FAILS when the anchor is not
there exactly once, so a tree that drifted from the one this was measured on is loud, never
half-edited.  It is what W-46 track C ran in its simulation clone (README "W-46 track C"
section 4), and what the step that lands R3 runs -- the switch deletes exactly this.

What the edits are, by class:

* `priority.rs`: `struct Edf`, which only `compute` built, and the `use` of the two names the
  deletion removes (a warning, then an error, otherwise);
* tm-core/src's and tm/src's own tests that READ a deleted function to assert something the
  binary keeps: the `travel-day` flag read as `has_flag("travel-day")` (the body of
  `Item::is_travel_day`), and the open block's worked minutes read off its two fields (the body
  of `OpenBlock::worked_min_at`, as `tm/tests/support/replay.rs`' `open_worked_min_at` reads it)
  -- tm-core/src and tm/src are not track C's to edit, so the switch makes these;
* the assertions of a deleted function's own behaviour inside a test that stays:
  `capacity::remaining_budget`'s two in `window_and_budget_for_the_spec_day`, and
  `Model::p_lounge_on`'s config fallback in `energy_fit.rs` (the kernel's `mkInput?` is the one
  reader of that fallback since L5);
* the imports the deleted tests alone used.
"""
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))

EDITS = [
    ("tm-core/src/priority.rs", "use crate::capacity::{self, available_until, DayCapacity, Exact};",
     "use crate::capacity::{self, Exact};"),
    ("tm-core/src/priority.rs", """/// The outcome of one EDF reservation (§7.3).
#[derive(Clone, Copy, Debug)]
struct Edf {
    avail_min: u32,
    allocation_min: u32,
    u: f64,
    until: NaiveDate,
}

""", ""),
    ("tm-core/src/grammar.rs", "assert!(it.is_travel_day());", 'assert!(it.has_flag("travel-day"));'),
    ("tm-core/src/ics.rs", "assert!(flight.is_travel_day());", 'assert!(flight.has_flag("travel-day"));'),
    ("tm-core/src/ics.rs", '!item.is_travel_day() && !item.has_flag("manual")',
     '!item.has_flag("travel-day") && !item.has_flag("manual")'),
    ("tm/src/tui/mod.rs", ".map(|b| b.worked_min_at(now));",
     ".map(|b| b.worked_min + b.since.map_or(0, |s| now.signed_duration_since(s).num_minutes().max(0) as u32));"),
    ("tm-core/tests/capacity_slots.rs", """    assert_eq!(remaining_budget(budget, 2), 4);
    assert_eq!(remaining_budget(budget, 9), 0);
""", ""),
    ("tm/tests/energy_fit.rs", """    assert_eq!(
        model.p_lounge_on(Weekday::Tue, &cfg),
        *cfg.expected.p_lounge.get(Weekday::Tue)
    );
""", ""),
    ("tm-core/tests/capacity_lookahead.rs", """use chrono::{DateTime, NaiveDate, NaiveTime, Weekday};
use chrono_tz::Tz;
use tm_core::capacity::{
    available_until, cut_slots, energize, local_dt, lookahead, reserve, upto, week_grid,
    window_and_budget, DayCapacity, EnergyCtx, Slot, WallsByDate,
};
use tm_core::config::Config;
use tm_core::energy::{Hhmm, Model, Posterior};
use tm_core::grammar;
use tm_core::model::{Loc, Shape};""", """use chrono::{DateTime, NaiveDate, NaiveTime};
use chrono_tz::Tz;
use tm_core::capacity::{local_dt, WallsByDate};
use tm_core::config::Config;
use tm_core::grammar;
use tm_core::model::Shape;"""),
    ("tm-core/tests/capacity_slots.rs", """use tm_core::capacity::{
    budget_blocks, cut_slots, cut_slots_around, cut_slots_from, energize, free_intervals, local_dt,
    remaining_budget, window_and_budget, Break, EnergyCtx, Slot, SlotKind,
    SlotOrBreak,
};
use tm_core::config::Config;
use tm_core::energy::{Model, Posterior};
use tm_core::model::Loc;""", """use tm_core::capacity::{budget_blocks, window_and_budget};
use tm_core::config::Config;"""),
    ("tm/tests/priority_regressions.rs", "use tm_core::model::{Id, InstanceKey, Period};", "use tm_core::model::{Id, Period};"),
]

REMOVED = ["tm-core/tests/snapshots/capacity_lookahead__lookahead_plan_basic_week.snap"]


def main():
    tree = sys.argv[1]
    for lst in ("deletion-functions.txt", "deletion-tests.txt"):
        out = subprocess.run([sys.executable, os.path.join(HERE, "delete_fns.py"), os.path.join(HERE, lst), tree],
                             capture_output=True, text=True)
        sys.stdout.write(out.stdout)
        if out.returncode != 0:
            sys.exit(f"{lst}: {out.stderr.strip()}")
    for path, old, new in EDITS:
        p = os.path.join(tree, path)
        text = open(p, encoding="utf-8").read()
        n = text.count(old)
        if n != 1:
            sys.exit(f"{path}: the edit's anchor occurs {n} times, not once: {old[:70]!r}")
        open(p, "w", encoding="utf-8").write(text.replace(old, new))
        print(f"{path}: edited ({len(old.splitlines())} line(s) -> {len(new.splitlines())})")
    for path in REMOVED:
        p = os.path.join(tree, path)
        if not os.path.exists(p):
            sys.exit(f"{path}: not there to remove")
        os.remove(p)
        print(f"{path}: removed")


if __name__ == "__main__":
    main()
