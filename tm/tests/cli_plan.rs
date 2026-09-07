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
}

#[test]
fn plan_needs_a_plan_directory() {
    let tm = Tm::empty();
    let out = tm.run(&["plan"]);
    assert_eq!(out.code, 1);
    assert!(out.stderr.contains("config.toml"), "{}", out.stderr);
}
