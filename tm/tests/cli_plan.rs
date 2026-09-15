//! `tm plan` and `tm now` (§8, §13) against a temp `plan/`.
//!
//! These are the CLI's tests, not the planner's: they assert the *contract*
//! around §8.2 — exit codes, the files written, the events appended (§10.1),
//! the `--json` schema and the properties §8.3, §9 and §11 require of a
//! replan. Which item lands in which slot is `tm-core`'s to pin
//! (`tm-core/tests/planner_*.rs`); what a segment or a diff must *say* about
//! it is pinned here.

mod cli_common;

use cli_common::{schema, Tm};

/// The `HH:MM` a segment or diff field carries.
fn hhmm(v: &serde_json::Value) -> &str {
    v.as_str().unwrap_or_else(|| panic!("HH:MM, got {v}"))
}

/// That `HH:MM` as minutes since midnight.
fn min_of_day(v: &serde_json::Value) -> i64 {
    let (h, m) = hhmm(v).split_once(':').expect("HH:MM");
    h.parse::<i64>().expect("hours") * 60 + m.parse::<i64>().expect("minutes")
}

#[test]
fn plan_writes_the_generated_section_the_svg_and_the_event() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["arrive", "lounge"]);

    let out = tm.run_at("2026-09-07T10:42:00-05:00", &["plan"]);
    assert_eq!(out.code, 0, "{}", out.stderr);

    // §4.3: the plan lives between the markers, and only there.
    let day = tm.read("day/2026-09-07.md");
    assert!(day.contains("<!-- tm:plan start 10:42 -->"), "{day}");
    assert!(day.contains("<!-- tm:plan end -->"), "{day}");
    assert!(day.contains("# Pinned"), "the human sections survive");
    assert!(day.contains("## Log"), "the append-only section survives");
    assert!(tm.exists("day/2026-09-07.svg"));
    assert!(tm.read("day/2026-09-07.svg").starts_with("<svg"));

    assert!(tm.events().contains(&"plan".to_string()));
    assert!(tm.exists(".tm/last_plan.json"));
    assert!(tm.state()["last_plan_hash"].is_string());
}

#[test]
fn a_replan_that_moves_nothing_is_not_logged_twice() {
    // §10.1's `plan` entry feeds §11's "replans and drift" monitor, so it must
    // mark a day that actually moved. §8.3: `plan()` is pure — same input,
    // same `DayPlan` — so re-running `tm plan` at the same instant with
    // nothing changed leaves both the count and `last_plan_hash` where they
    // were. Re-cutting the day two hours later is a real replan: §8.2 step 3
    // slices free time from `now`, the tail drops, and that *is* logged, with
    // the drift §11 measures.
    let tm = Tm::new();
    tm.ok(&["arrive", "lounge"]);
    let plans = |tm: &Tm| tm.events().iter().filter(|e| *e == "plan").count();
    let first = plans(&tm);
    assert_eq!(first, 1, "§13: `arrive` plans the day");
    let hash = tm.state()["last_plan_hash"].clone();
    assert!(hash.is_string(), "{}", tm.state());

    tm.ok(&["plan"]);
    assert_eq!(
        plans(&tm),
        first,
        "the day did not move, so it is not a replan"
    );
    assert_eq!(tm.state()["last_plan_hash"], hash, "§8.3: same plan");

    tm.ok_at("2026-09-07T11:00:00-05:00", &["plan"]);
    assert_eq!(plans(&tm), first + 1, "a day re-cut from 11:00 did move");
    assert_ne!(tm.state()["last_plan_hash"], hash);
    let ev = tm.last_ev("plan");
    assert!(
        ev["drift_min"].as_u64().is_some_and(|d| d > 0),
        "§10.1: the replan carries its drift: {ev}"
    );
    assert!(ev["replans_today"].as_u64().is_some(), "{ev}");
}

#[test]
fn plan_json_has_the_documented_shape() {
    // §13: every verb accepts `--json`. The document is §8's `DayPlan` — the
    // window and budget of §8.1, the timeline of §8.2, the diagnostics its
    // step 8 emits and §7's priorities — plus the files this run wrote.
    let tm = Tm::new();
    tm.ok(&["arrive", "lounge"]);
    let json = tm.json(&["plan"]);
    for key in [
        "date",
        "window",
        "budget_blocks",
        "blocks_done",
        "hash",
        "segments",
        "diagnostics",
        "priorities",
        "wrote",
    ] {
        assert!(json.get(key).is_some(), "missing {key} in {json}");
    }
    assert_eq!(json["window"].as_array().map(Vec::len), Some(2));

    // §8.2 emits a day, not an empty list: every segment says when it runs,
    // what kind it is and — for a slot — the energy it was cut at (§8.2
    // step 3), which is what the day file and the TUI render from.
    let segs = json["segments"].as_array().expect("segments");
    assert!(!segs.is_empty(), "the planner placed nothing: {json}");
    for seg in segs {
        for key in [
            "start", "end", "minutes", "kind", "energy", "item", "mark", "text",
        ] {
            assert!(seg.get(key).is_some(), "missing segments[].{key} in {seg}");
        }
    }
    // §8.2 step 3: a Block is a slot, so it reports the energy it was cut at
    // — the number §4.3's rows lead with and §8.3's energy filter works on.
    assert!(
        segs.iter()
            .any(|s| s["kind"] == "block" && s["energy"].is_u64()),
        "no block carries its slot energy: {json}"
    );
    // §8.2 step 8's diagnostic set, by name.
    let diag = &json["diagnostics"];
    for key in [
        "underused",
        "a_capacity_lost",
        "hot",
        "impossible",
        "conflicts",
        "blocked",
        "deferred",
        "waiting",
    ] {
        assert!(diag.get(key).is_some(), "missing diagnostics.{key} in {json}");
    }
    insta::assert_json_snapshot!("plan_schema", schema(&json));
}

/// §8.5's prior is a step function of hours since wake, and `tm wake` is
/// optional: arriving without it is a normal day. Both the planner and `Ctx`
/// take the weekday's expected arrival for the wake nobody logged (§8.4, §16's
/// `[expected] arrival` — 07:00 on a Monday), so the morning sits at the top
/// of the curve. Falling back to the start of the day instead put 09:00 at
/// `hsw` 9, in the curve's `3`/`2` tail, and every ci-4 and ci-5 item was
/// ineligible for the whole day.
#[test]
fn a_day_without_tm_wake_still_plans_demanding_work() {
    let tm = Tm::new();
    tm.ok(&["arrive", "lounge"]);
    assert!(tm.state()["wake"].is_null(), "no wake was logged");

    let json = tm.json(&["plan"]);
    let peak = json["segments"]
        .as_array()
        .expect("segments")
        .iter()
        .filter(|s| s["kind"] == "block")
        .filter_map(|s| s["energy"].as_u64())
        .max();
    assert_eq!(peak, Some(5), "the morning is worth a ci-5 block: {json}");

    // `tm plan --week` cuts today's column through `Ctx` rather than the
    // planner; one wake means one answer.
    let week = tm.json(&["plan", "--week"]);
    let today = &week["days"][0];
    assert_eq!(today["date"], "2026-09-07");
    assert!(
        today["minutes_at_level"][5].as_u64().unwrap_or(0) > 0,
        "the lookahead sees the same energy 5 the plan does: {today}"
    );
}

#[test]
fn plan_week_renders_the_capacity_grid() {
    let tm = Tm::new();
    tm.ok(&["arrive", "lounge"]);
    let json = tm.json(&["plan", "--week"]);
    assert_eq!(json["week"], "2026-W37");
    assert_eq!(json["days"].as_array().map(Vec::len), Some(7));
    assert!(json["grid"].as_str().unwrap_or_default().contains("day"));
    insta::assert_json_snapshot!("plan_week_schema", schema(&json));
}

#[test]
fn plan_diff_compares_against_the_stored_plan() {
    // §9 and §14: `--diff` answers "what moved, and why" against the stored
    // plan; §11 defines the drift it reports as "Σ minutes segments moved".
    // Diffing against a plan that is still current moves nothing; a day
    // re-cut two hours later moves, and `drift_min` is then exactly the sum
    // of the moves the diff lists — one row per item, however many blocks
    // that item holds.
    let tm = Tm::new();
    tm.ok(&["arrive", "lounge"]);
    tm.ok(&["plan"]);

    let same = tm.json(&["plan", "--diff"]);
    let same = &same["diff"];
    assert_eq!(same["had_previous"], true);
    assert_eq!(same["drift_min"], 0, "{same}");
    for key in ["added", "removed", "moved"] {
        assert_eq!(
            same[key].as_array().map(Vec::len),
            Some(0),
            "nothing changed, so nothing {key}: {same}"
        );
    }

    let json = tm.json_at("2026-09-07T11:00:00-05:00", &["plan", "--diff"]);
    let diff = &json["diff"];
    assert_eq!(diff["had_previous"], true);
    let moved = diff["moved"].as_array().expect("moved");
    assert!(!moved.is_empty(), "two hours on, the day moved: {diff}");

    let mut ids: Vec<&str> = Vec::new();
    let mut sum = 0;
    for m in moved {
        assert_ne!(m[1], m[2], "a `moved` row moved: {m}");
        sum += (min_of_day(&m[2]) - min_of_day(&m[1])).abs();
        ids.push(m[0].as_str().expect("id"));
    }
    assert_eq!(
        diff["drift_min"].as_i64(),
        Some(sum),
        "§11: drift is Σ minutes moved: {diff}"
    );
    let mut once = ids.clone();
    once.sort_unstable();
    once.dedup();
    assert_eq!(
        ids.len(),
        once.len(),
        "an item with two blocks moves once: {diff}"
    );
    // Every item the new plan dropped is named, and none is claimed twice.
    let removed: Vec<&str> = diff["removed"]
        .as_array()
        .expect("removed")
        .iter()
        .filter_map(|v| v.as_str())
        .collect();
    assert!(
        removed.iter().all(|r| !ids.contains(r)),
        "an item is moved or removed, not both: {diff}"
    );
    insta::assert_json_snapshot!("plan_diff_schema", schema(diff));
}

#[test]
fn plan_explain_answers_for_one_item_without_writing() {
    let tm = Tm::new();
    tm.ok(&["arrive", "lounge"]);
    let before = tm.read("day/2026-09-07.md");
    let out = tm.run(&["plan", "--explain", "^d1"]);
    assert_eq!(out.code, 0, "{}", out.stderr);
    // §13's example shape: `p = k(3) + bin(u=… → +1) = 4; …`.
    assert!(out.stdout.contains("p = "), "{}", out.stdout);
    assert!(out.stdout.contains("deps"), "{}", out.stdout);
    assert_eq!(tm.read("day/2026-09-07.md"), before, "explain writes nothing");

    let json = tm.json(&["plan", "--explain", "^d1"]);
    assert!(json["explain"].as_str().unwrap_or_default().contains("p = "));
    assert_eq!(json["wrote"].as_array().map(Vec::len), Some(0));
}

#[test]
fn now_reports_the_running_block_and_the_next_segments() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["arrive", "lounge"]);

    // Nothing has been started, so there is no Active block (§10.2) — but the
    // day still has a shape: §13's `current` is the segment `now` sits in and
    // `next` the three that follow it.
    let idle = tm.json(&["now"]);
    assert_eq!(idle["active"], serde_json::Value::Null);
    assert_eq!(idle["date"], "2026-09-07");
    assert_eq!(idle["now"], "09:00");
    let current = &idle["current"];
    assert!(
        hhmm(&current["start"]) <= "09:00" && "09:00" < hhmm(&current["end"]),
        "`current` contains `now`: {current}"
    );
    let next = idle["next"].as_array().expect("next");
    assert_eq!(next.len(), 3, "§13: the next three segments: {idle}");
    let mut cursor = hhmm(&current["start"]).to_string();
    for seg in next {
        let start = hhmm(&seg["start"]);
        assert!(
            start >= "09:00" && start > cursor.as_str(),
            "`next` runs forwards from `now`: {idle}"
        );
        cursor = start.to_string();
    }
    insta::assert_json_snapshot!("now_schema", schema(&idle));

    tm.ok(&["start", "^t4", "--energy", "4"]);
    let json = tm.json_at("2026-09-07T09:30:00-05:00", &["now"]);
    assert_eq!(json["active"]["id"], "t4");
    assert_eq!(json["active"]["elapsed_min"], 30);
    assert_eq!(json["active"]["title"], "Claude Code drafts tests");
    // §9: the Active block keeps its slot across a replan, so the block `now`
    // is inside is that item, marked ▶ and running to the end of its estimate
    // (started 09:00, `est:` 1b) — the timeline agrees with `state.json`.
    assert_eq!(json["current"]["item"], "t4");
    assert_eq!(json["current"]["kind"], "block");
    assert_eq!(json["current"]["mark"], "▶");
    assert_eq!(json["current"]["end"], "10:00");
    assert_eq!(json["current"]["minutes"], 30, "{}", json["current"]);
    assert_eq!(json["next"].as_array().map(Vec::len), Some(3));
    // The idle snapshot above pins an empty `active`; the running block has a
    // shape of its own (§17 M5: `--json` schemas snapshot-tested).
    insta::assert_json_snapshot!("now_active_schema", schema(&json));
}

#[test]
fn a_new_day_plans_the_new_day() {
    // §8.1: the window and budget belong to the arrival *day*; §6.3 exists
    // precisely because commands are run on days with no `wake`/`arrive`. The
    // first such command must not plan — and rewrite — yesterday's day file.
    let tm = Tm::new();
    tm.ok_at("2026-09-07T07:00:00-05:00", &["arrive", "lounge"]);
    assert_eq!(tm.state()["window"][0], "07:00");

    let json = tm.json_at("2026-09-08T11:00:00-05:00", &["plan"]);
    assert_eq!(json["date"], "2026-09-08");
    assert_eq!(json["window"][0], "11:00");
    let wrote: Vec<&str> = json["wrote"]
        .as_array()
        .expect("wrote")
        .iter()
        .filter_map(|w| w.as_str())
        .collect();
    assert_eq!(wrote, ["day/2026-09-08.md", "day/2026-09-08.svg"]);
    assert_eq!(tm.state()["date"], "2026-09-08");

    // Yesterday's file — which the §6.3 auto-close has just closed — is left
    // exactly as the close left it.
    let yesterday = tm.read("day/2026-09-07.md");
    assert!(
        !yesterday.contains("<!-- tm:plan start 11:00 -->"),
        "{yesterday}"
    );
    assert_eq!(tm.json_at("2026-09-08T11:01:00-05:00", &["now"])["date"], "2026-09-08");
}

#[test]
fn allow_home_lifts_the_home_energy_cap() {
    // §8.2 step 3: at home slot energy is capped at `home_max_ci` (3) unless
    // `--allow-home` says otherwise, so the week grid gains high-energy
    // minutes today.
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.ok(&["arrive", "home"]);
    let capped = tm.json(&["plan", "--week"]);
    let free = tm.json(&["plan", "--week", "--allow-home"]);
    let high = |v: &serde_json::Value| -> u64 {
        v["days"][0]["minutes_at_level"][4].as_u64().unwrap_or(0)
            + v["days"][0]["minutes_at_level"][5].as_u64().unwrap_or(0)
    };
    assert_eq!(high(&capped), 0, "the home cap holds without the flag");
    assert!(high(&free) > 0, "--allow-home lifts it: {free}");

    // And the *day* is re-cut too: `build()` never passed the flag into
    // `PlanInput`, so the flag lifted only the lookahead the EDF pass sizes
    // and `tm plan --allow-home` returned a byte-identical segment list.
    let energies = |v: &serde_json::Value| -> Vec<u64> {
        v["segments"]
            .as_array()
            .expect("segments")
            .iter()
            .filter_map(|s| s["energy"].as_u64())
            .collect()
    };
    let day_capped = tm.json(&["plan"]);
    let day_free = tm.json(&["plan", "--allow-home"]);
    assert!(
        energies(&day_capped).iter().all(|e| *e <= 3),
        "the home cap holds on the day: {:?}",
        energies(&day_capped)
    );
    assert!(
        energies(&day_free).iter().any(|e| *e > 3),
        "--allow-home lifts it on the day too: {:?}",
        energies(&day_free)
    );
}

#[test]
fn plan_needs_a_plan_directory() {
    let tm = Tm::empty();
    let out = tm.run(&["plan"]);
    assert_eq!(out.code, 1);
    assert!(out.stderr.contains("config.toml"), "{}", out.stderr);
}

/// §4.3's row grid, written by the §1.2 renderer.
///
/// `tm plan` used to write the day file with a private stand-in in
/// `cli/render.rs`: no `pN` column, no `(actual)` cell, no `───  window ends`
/// divider, the estimate already multiplied, the title repeated in the note
/// column — and a text that disagreed with what `tm tui` drew for the same
/// `DayPlan`. Both now go through `tm_core::emit`.
#[test]
fn the_generated_section_is_the_spec_4_3_grid() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.run_at("2026-09-07T07:00:00-05:00", &["arrive", "lounge"]);
    tm.run_at("2026-09-07T07:02:00-05:00", &["start", "^t1", "--energy", "5"]);
    tm.run_at("2026-09-07T08:09:00-05:00", &["done"]);
    let out = tm.run_at("2026-09-07T10:42:00-05:00", &["plan"]);
    assert_eq!(out.code, 0, "{}", out.stderr);

    let day = tm.read("day/2026-09-07.md");
    let section: Vec<&str> = day
        .lines()
        .skip_while(|l| !l.starts_with("<!-- tm:plan start"))
        .skip(1)
        .take_while(|l| !l.starts_with("<!-- tm:plan end"))
        .collect();
    let body = section.join("\n");

    // The finished block: `ci`, `pN`, `✓`, `@parent`, the *written* estimate
    // and the actual in its own parenthesised cell.
    let done = section
        .iter()
        .find(|l| l.contains("Read ch.6 §1–2"))
        .unwrap_or_else(|| panic!("no finished row in\n{body}"));
    assert_eq!(
        *done, "07:02  5    ✓ Read ch.6 §1–2               @m3  1b  (67m)",
        "\n{body}"
    );

    // §4.3's `15:10  1 p0 ⚠  Pick up package  20m  due today`: a Window-shaped
    // task is placed like a routine but keeps its `ci`, `pN` and `⚠`.
    let hot = section
        .iter()
        .find(|l| l.contains("Pick up package"))
        .unwrap_or_else(|| panic!("no ^a3 row in\n{body}"));
    assert!(hot.contains(" 1 p0 ⚠ "), "{hot}");
    assert!(hot.ends_with("due today"), "{hot}");

    // The divider where the budget runs out.
    assert!(
        section.iter().any(|l| l.contains("───") && l.contains("window ends")),
        "no window-ends divider in\n{body}"
    );

    // A routine names itself once — the title cell, never the note column.
    let lunch = section
        .iter()
        .find(|l| l.contains("lunch"))
        .unwrap_or_else(|| panic!("no lunch row in\n{body}"));
    assert_eq!(lunch.matches("lunch").count(), 1, "{lunch}");
    let wind = section
        .iter()
        .find(|l| l.contains("wind-down"))
        .unwrap_or_else(|| panic!("no wind-down row in\n{body}"));
    assert_eq!(wind.matches("wind-down").count(), 1, "{wind}");

    // Columns line up: every `@parent` starts at the same display column.
    // Counted in `char`s, not bytes — `§`, `–` and `✓` are multi-byte and one
    // column wide, and no row with an `@parent` carries a wide glyph.
    let parents: Vec<usize> = section
        .iter()
        .filter_map(|l| l.char_indices().position(|(i, c)| c == '@' && i > 0))
        .collect();
    assert!(!parents.is_empty());
    assert!(
        parents.windows(2).all(|w| w[0] == w[1]),
        "the @parent column drifts: {parents:?}\n{body}"
    );

    // §12.1: the SVG is the day bar, 24 h wake-to-wake with the ghost row.
    let svg = tm.read("day/2026-09-07.svg");
    assert!(svg.contains("aria-label=\"day bar 2026-09-07\""), "{svg}");
    assert!(svg.contains("id=\"tm-lost\""), "hatch patterns are missing");
    assert!(svg.contains("class=\"ghost\""), "no ghost row");
    assert!(
        svg.contains("· ci5 · @O1</title>"),
        "§12.1's `title · duration · ci · p · @root` tooltip is missing:\n{svg}"
    );
}

/// §11: "Plan honesty … warning at `tm plan` when > 1.1". The number was in
/// `--json` but the human run said nothing.
#[test]
fn plan_warns_when_the_day_is_planned_above_a_realistic_budget() {
    let tm = Tm::new();
    tm.ok(&["wake", "06:05", "--slept", "8h10m"]);
    tm.run_at("2026-09-07T07:00:00-05:00", &["arrive", "lounge"]);
    let out = tm.run_at("2026-09-07T07:10:00-05:00", &["plan"]);
    let honesty = tm.run_at("2026-09-07T07:10:00-05:00", &["--json", "plan"]).json()
        ["diagnostics"]["plan_honesty"]
        .as_f64()
        .expect("plan_honesty");
    assert!(honesty > 1.1, "the fixture day is meant to be over-planned: {honesty}");
    assert!(
        out.stdout.contains("plan honesty"),
        "no §11 warning in\n{}",
        out.stdout
    );
}

// ---------------------------------------------------------------------------
// Stage 5 D10 L8: the week's capacity and every priority come from the kernel
// ---------------------------------------------------------------------------

/// An exact `{num, den}` pair on `--json` (the owner's D15): two digit strings
/// (D17), read as `u128`.
fn exact(v: &serde_json::Value) -> (u128, u128) {
    let part = |k: &str| {
        let s = v[k].as_str().unwrap_or_else(|| panic!("{k} is a digit string in {v}"));
        assert!(!s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()), "{k} in {v}");
        s.parse::<u128>().expect("fits u128")
    };
    let (n, d) = (part("num"), part("den"));
    assert!(d >= 1, "{v}");
    (n, d)
}

/// **The mixture reaches the week grid, as floors beside exact values** (the
/// owner's D10 and D15; kernel/README.md parity P1).  `plan-basic`'s
/// `[expected] p_lounge` is 0.9 on Tuesday: the fork's threshold put the whole
/// day at the lounge (4h at level 5, 2h at level 4), and the kernel's day is
/// `0.9 · lounge + 0.1 · home`, the home day capped at level 3 by `home_max_ci`:
/// 3h36 at 5, 1h48 at 4 and 36m at 3.  With Wednesday's weight set to 0.333 the
/// day is no longer whole minutes: every `minutes_at_level` is the floor of its
/// own exact value, and `total` is the floor of the exact total.
#[test]
fn plan_week_shows_the_kernels_mixture_as_floors_beside_exact_values() {
    let tm = Tm::new();
    let cfg = tm.read("config.toml").replace("Wed = 0.9", "Wed = 0.333");
    std::fs::write(tm.plan.join("config.toml"), cfg).expect("config");
    tm.ok(&["arrive", "lounge"]);
    let json = tm.json(&["plan", "--week"]);
    let days = json["days"].as_array().expect("days");
    assert_eq!(days.len(), 7);
    let tuesday = &days[1];
    assert_eq!(tuesday["date"], "2026-09-08");
    assert_eq!(tuesday["minutes_at_level"], serde_json::json!([0, 0, 0, 36, 108, 216]), "{tuesday}");
    let wednesday = &days[2];
    assert_eq!(exact(&wednesday["minutes_at_level_exact"][5]), (1998, 25), "0.333 × 240: {wednesday}");
    assert_eq!(exact(&wednesday["minutes_at_level_exact"][3]), (6003, 25), "0.667 × 360: {wednesday}");
    assert_eq!(wednesday["minutes_at_level"], serde_json::json!([0, 0, 0, 240, 39, 79]), "{wednesday}");
    for day in days {
        let mut sum = (0u128, 1u128);
        for l in 0..6 {
            let (n, d) = exact(&day["minutes_at_level_exact"][l]);
            assert_eq!(day["minutes_at_level"][l].as_u64(), Some((n / d) as u64), "{day}");
            sum = (sum.0 * d + n * sum.1, sum.1 * d);
        }
        let (tn, td) = exact(&day["total_exact"]);
        assert_eq!(day["total"].as_u64(), Some((tn / td) as u64), "{day}");
        assert_eq!(tn * sum.1, sum.0 * td, "total_exact is the exact sum: {day}");
    }
    // Wednesday's total is the floor of 79.92 + 39.96 + 240.12 = 360, not 79 + 39 + 240 = 358.
    assert_eq!(wednesday["total"], 360, "{wednesday}");
    let grid = json["grid"].as_str().expect("grid");
    assert!(grid.contains("Tue 09-08     6h  3h36  1h48   36m"), "{grid}");
    assert!(grid.contains("Wed 09-09     6h  1h19   39m    4h"), "{grid}");
}

/// **A weight the kernel cannot read fails every capacity verb by file and
/// key, and nothing else** (design §13.2, §20's L6 row; parity P26; D17).
#[test]
fn a_weight_outside_its_domain_fails_capacity_verbs_by_file_and_key() {
    let tm = Tm::new();
    std::fs::create_dir_all(tm.plan.join(".tm")).expect(".tm");
    std::fs::write(tm.plan.join(".tm/model.json"), r#"{"p_lounge": {"Mon": 1.2}}"#).expect("model");
    for args in [&["plan"][..], &["plan", "--week"], &["now"]] {
        let out = tm.run(args);
        assert_eq!(out.code, 1, "{args:?}: {}{}", out.stdout, out.stderr);
        assert!(
            out.stderr.contains(".tm/model.json: p_lounge.Mon = 1.2 is outside [0, 1]"),
            "{args:?}: {}",
            out.stderr
        );
    }
    // A verb that plans after it writes refuses before it writes anything.
    let out = tm.run(&["arrive", "lounge"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(out.stderr.contains(".tm/model.json: p_lounge.Mon = 1.2"), "{}", out.stderr);
    assert!(!tm.log().iter().any(|e| e["ev"] == "arrive"), "{:?}", tm.log());
    // A verb that computes no capacity still runs.
    tm.ok(&["add", "Buy stamps", "--to", "week"]);
    tm.ok(&["triage"]);
    // More than 18 decimal places in config.toml is named there.
    std::fs::remove_file(tm.plan.join(".tm/model.json")).expect("rm model");
    let cfg = tm.read("config.toml").replace("Sat = 0.5", "Sat = 0.0000000000000000001");
    std::fs::write(tm.plan.join("config.toml"), cfg).expect("config");
    let out = tm.run(&["plan"]);
    assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains("config.toml: expected.p_lounge.Sat = ") && out.stderr.contains("(at most 18)"),
        "{}",
        out.stderr
    );
    // The places are the file's, not its nearest double's (W-3 audit, D10, D17): 19
    // written places are refused even where the double has 17 (`0.12345678901234568`)
    // or 1 (`0.1`), in config.toml and in .tm/model.json alike.
    for v in ["0.1234567890123456789", "0.1000000000000000001"] {
        let cfg = tm.read("config.toml").replace("Sat = 0.0000000000000000001", &format!("Sat = {v}"));
        std::fs::write(tm.plan.join("config.toml"), cfg).expect("config");
        let out = tm.run(&["plan", "--week"]);
        assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
        let want = format!("config.toml: expected.p_lounge.Sat = {v} has 19 decimal places (at most 18)");
        assert!(out.stderr.contains(&want), "{}", out.stderr);
        let cfg = tm.read("config.toml").replace(&format!("Sat = {v}"), "Sat = 0.0000000000000000001");
        std::fs::write(tm.plan.join("config.toml"), cfg).expect("config");
    }
    let cfg = tm.read("config.toml").replace("Sat = 0.0000000000000000001", "Sat = 0.5");
    std::fs::write(tm.plan.join("config.toml"), cfg).expect("config");
    tm.ok(&["plan", "--week"]);
    for v in ["0.1234567890123456789", "0.1000000000000000001"] {
        std::fs::write(tm.plan.join(".tm/model.json"), format!(r#"{{"p_lounge": {{"Tue": {v}}}}}"#)).expect("model");
        let out = tm.run(&["plan", "--week"]);
        assert_eq!(out.code, 1, "{}{}", out.stdout, out.stderr);
        let want = format!(".tm/model.json: p_lounge.Tue = {v} has 19 decimal places (at most 18)");
        assert!(out.stderr.contains(&want), "{}", out.stderr);
    }
    // Eighteen written places are accepted.
    std::fs::write(tm.plan.join(".tm/model.json"), r#"{"p_lounge": {"Tue": 0.123456789012345678}}"#).expect("model");
    tm.ok(&["plan", "--week"]);
}

/// **Gap 98: a deadline past the kernel's 3,660-day lookahead is clamped, and
/// the binary says so** (parity P30).  The plan still runs.
#[test]
fn a_due_past_the_lookahead_cap_is_clamped_and_said() {
    let tm = Tm::new();
    let week = tm.read("week/2026-W37.md");
    std::fs::write(
        tm.plan.join("week/2026-W37.md"),
        format!("{week}- [ ] 3 30m A far deadline due:2038-09-07 ^far1\n"),
    )
    .expect("week");
    let out = tm.run(&["plan"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(
        out.stderr.contains("the capacity lookahead is clamped to 3660 days (through 2036-09-13"),
        "{}",
        out.stderr
    );
    // Ten years out is inside the cap: nothing is said.
    std::fs::write(
        tm.plan.join("week/2026-W37.md"),
        format!("{week}- [ ] 3 30m A far deadline due:2036-09-07 ^far1\n"),
    )
    .expect("week");
    let out = tm.run(&["plan"]);
    assert_eq!(out.code, 0, "{}{}", out.stdout, out.stderr);
    assert!(!out.stderr.contains("clamped"), "{}", out.stderr);
}
