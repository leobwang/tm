//! **D80's two refusals, on the worlds the binary builds** — stage 6 W-41, track K
//! (the owner's D80; README gaps 3780, 3785 and 1984; parity P71 and P72).
//!
//! `PlanWire.planReqRefusal` refuses, by name, the two requests fork 4748911 can
//! never produce: a day whose evening runs past the calendar's last second
//! (`eveningPastTheCalendar`) and a candidate whose `ci` on the wire is not the
//! `ci` the kernel reads in the plan file (`ciDisagrees <id> wire <w> plan <p>`).
//! D80 says why the second may refuse nothing real: a disagreeing `ci` had been
//! seen on none of the measured days. This file is the measurement, by value and
//! with its denominators: every frozen class line, every seeded batch line, every
//! driven line, every frozen P56 day and every frozen `plan-basic` day, and a fresh
//! draw of generated days, each asked of the kernel as the binary will ask at R3
//! (`forkclass::kernel_answer_with_grants`' request, and `planner_classes.rs`'
//! for the `plan-basic` days) — and no D80 refusal on any of them is the assertion.
//! The two remaining frozen sets, the four fixture days and the three conference
//! days, are asked by their own tests (`planner_fixtures.rs`, `planner_w39_conference.rs`),
//! which fail by name on any refusal. A disagreement found here would be a finding
//! to report, never a refusal to ship.
//!
//! It also drives the second refusal through the FFI on a world the generator
//! builds, with one candidate's `ci` moved on the wire: the refusal names the
//! candidate, the wire's value and the plan's, and the world unmoved is planned.
//! (The first is driven in `kernel_planner_wire.rs`, where a raw request can sit
//! on the calendar's last day.)

#[path = "support/replay.rs"]
#[allow(dead_code)]
mod chokepoint;

#[allow(dead_code)]
#[path = "support/planreq.rs"]
mod planreq;

#[allow(dead_code)]
#[path = "support/forkday.rs"]
mod forkday;

#[allow(dead_code)]
#[path = "support/forkclass.rs"]
mod forkclass;

#[allow(dead_code)]
#[path = "support/plangen.rs"]
mod plangen;

#[allow(dead_code)]
#[path = "support/srcwalk.rs"]
mod srcwalk;

#[allow(dead_code)]
#[path = "support/forkplan.rs"]
mod forkplan;

#[allow(dead_code)]
#[path = "support/forkp56.rs"]
mod forkp56;

#[allow(dead_code)]
mod planner_common;

use chrono::DateTime;
use serde_json::Value;
use tm_core::config::Config;
use tm_core::planwire;
use tm_core::store::RuntimeState;

use forkclass::{Built, ClassWorld};

/// The request the binary will build at R3 for a world, exactly as
/// `forkclass::kernel_answer_with_grants` builds it (the what-if and the host's
/// worked minutes included).
fn request_of(b: &Built) -> Value {
    let pw = b.request_world();
    let (mut req, _order) = planreq::request(&pw, forkclass::whatif_json(b));
    if let Some(worked) = forkclass::host_worked(b) {
        planwire::add_worked_min(&mut req["planner"], worked);
    }
    req
}

/// How many requests the census asked, and what became of them.
#[derive(Debug, Default)]
struct Census {
    /// Requests asked.
    asked: usize,
    /// Of those, answered with a day — the ones `planReqRefusal` passed.
    planned: usize,
    /// Refused by a D80 clause, by name.
    d80: Vec<String>,
    /// Refused before `planReqRefusal` ran — so D80 was NOT asked of them.
    other: Vec<String>,
    /// Candidates whose wire `ci` was compared with the plan's (on the planned).
    cands: usize,
}

impl Census {
    fn ask(&mut self, what: &str, req: &Value) {
        self.asked += 1;
        let resp = planreq::call(req);
        match planwire::planner_refusal(&resp) {
            Some(r) if r == "eveningPastTheCalendar" || r.starts_with("ciDisagrees ") => {
                self.d80.push(format!("{what}: {r}"));
            }
            Some(r) => self.other.push(format!("{what}: {r}")),
            None if resp["ok"]["plan"]["day"].is_string() => {
                self.planned += 1;
                self.cands += req["capacity"]["candidates"]["items"].as_array().map_or(0, Vec::len);
            }
            None => self.other.push(format!("{what}: {}", &resp.to_string()[..resp.to_string().len().min(200)])),
        }
    }
}

/// **No frozen, batch, driven or freshly generated day trips a D80 clause.**
#[test]
fn no_frozen_batch_driven_or_generated_day_is_refused_by_d80() {
    let tz = Config::default().tz;
    let mut frozen = Census::default();
    let p56 = forkp56::p56_lines();
    // The TUI's thirteen worlds and P68's and P69's two (W-41 track H's frozen lines,
    // added to this census at W-41's land step, which composed them with track K's
    // D80: README gap 4120). Each world is rebuilt from its own line, as the lines'
    // own comparisons rebuild it.
    let tui = jsonl_lines("fork-4748911-planner-tui.jsonl");
    let starts = jsonl_lines("fork-4748911-planner-starts.jsonl");
    for (set, lines) in [
        ("class", forkclass::frozen_lines()),
        ("batch", forkclass::batch_lines()),
        ("driven", forkclass::driven_lines()),
        ("p56", &p56),
        ("tui", &tui),
        ("starts", &starts),
    ] {
        for (i, line) in lines.iter().enumerate() {
            let world = ClassWorld::of_json(&line["world"], tz)
                .unwrap_or_else(|e| panic!("{set} line {i}: the frozen world reads back: {e}"));
            frozen.ask(&format!("{set} line {i}"), &request_of(&Built::of(world)));
        }
    }
    // The frozen `plan-basic` days (W-38): the corpus tree at each line's instant and
    // stored state, asked with the request `planner_classes.rs`' `basic_fork_day` builds.
    let fx = planner_common::load_with_log("plan-basic", Some(planner_common::BASIC_LOG));
    for line in forkday::frozen_basic_days() {
        let state: RuntimeState = serde_json::from_value(line["state"].clone()).expect("a stored state");
        let now = DateTime::parse_from_rfc3339(line["now"].as_str().unwrap_or_default())
            .expect("an instant")
            .with_timezone(&fx.cfg.tz);
        let date = planwire::plan_date(&state, now);
        let cands = tm_core::priority::collect_candidates(&fx.tree, &fx.replay, &fx.cfg, &fx.model, date, now);
        let w = planner_common::planreq::World {
            docs: &fx.docs, log: &fx.log, tree: &fx.tree, cfg: &fx.cfg, state: &state, now, cands: &cands, replay: &fx.replay,
        };
        let (req, _order) = planner_common::planreq::request(&w, None);
        frozen.ask(&format!("basic {}", line["name"].as_str().unwrap_or("?")), &req);
    }
    let mut fresh = Census::default();
    for draw in forkclass::class_draws("W-41 track K, D80's census", None).take(64) {
        let b = Built::of(forkclass::world_of(&draw));
        fresh.ask(&format!("draw {}", draw.index), &request_of(&b));
    }
    println!(
        "D80 census — frozen: {} asked, {} planned, {} candidates' ci compared, {} refused by D80, {} refused before it; \
         fresh draws: {} asked, {} planned, {} candidates, {} refused by D80, {} refused before it",
        frozen.asked, frozen.planned, frozen.cands, frozen.d80.len(), frozen.other.len(),
        fresh.asked, fresh.planned, fresh.cands, fresh.d80.len(), fresh.other.len()
    );
    assert!(frozen.d80.is_empty() && fresh.d80.is_empty(), "D80 refused a day the binary builds:\n  {}",
        frozen.d80.iter().chain(&fresh.d80).cloned().collect::<Vec<_>>().join("\n  "));
    // The denominators (AGENTS §9.2): every frozen line reached `planReqRefusal`, and
    // the census compared candidates at all.
    assert!(frozen.other.is_empty(), "a frozen line was refused before D80 was asked:\n  {}", frozen.other.join("\n  "));
    assert_eq!(frozen.planned, frozen.asked, "{frozen:?}");
    assert_eq!(
        frozen.asked,
        forkclass::frozen_lines().len() + forkclass::batch_lines().len() + forkclass::driven_lines().len()
            + p56.len() + tui.len() + starts.len() + forkday::frozen_basic_days().len(),
        "every frozen line was asked: {frozen:?}"
    );
    assert!(frozen.cands > 0 && fresh.planned > 0, "{frozen:?} {fresh:?}");
    assert!(tui.len() == 13 && starts.len() == 2, "the TUI's 13 lines and the 2 start lines: {} and {}", tui.len(), starts.len());
}

/// A frozen fixture's lines, beside the class lines (`forkday::frozen_path`'s directory).
fn jsonl_lines(name: &str) -> Vec<Value> {
    let path = forkday::frozen_path().with_file_name(name);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("{}: {e}", path.display()))
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| serde_json::from_str(l).unwrap_or_else(|e| panic!("{}: a line does not parse: {e}", path.display())))
        .collect()
}

/// **D80 (b) through the FFI**: one candidate's wire `ci` moved off the plan's is
/// refused, naming the candidate, the wire's value and the plan's; unmoved, the same
/// world is planned.
#[test]
fn a_candidate_whose_wire_ci_is_not_its_plans_is_refused_naming_both() {
    let tz = Config::default().tz;
    let line = forkclass::frozen_lines()
        .iter()
        .find(|l| {
            let b = Built::of(ClassWorld::of_json(&l["world"], tz).expect("a frozen world"));
            !request_of(&b)["capacity"]["candidates"]["items"].as_array().map_or(true, Vec::is_empty)
        })
        .expect("a frozen line with a candidate");
    let b = Built::of(ClassWorld::of_json(&line["world"], tz).expect("a frozen world"));
    let mut req = request_of(&b);
    let unmoved = planreq::call(&req);
    assert_eq!(planwire::planner_refusal(&unmoved), None, "the frozen world is planned: {unmoved}");
    let item = &mut req["capacity"]["candidates"]["items"][0];
    let id = item["id"].as_str().expect("an id").to_string();
    let plan = item["ci"].as_u64().expect("a ci");
    let wire = (plan + 1) % 6;
    item["ci"] = serde_json::json!(wire);
    let resp = planreq::call(&req);
    assert_eq!(
        planwire::planner_refusal(&resp),
        Some(format!("ciDisagrees {id} wire {wire} plan {plan}").as_str()),
        "{resp}"
    );
}
