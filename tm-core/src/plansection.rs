//! **The `planner` section as the binary sends it, composed once** (the W-46 audit, README gap
//! 4890) — its own module, beside `planwire`, so `planwire::planner_json` stays the section's
//! codec root that check 13's reader of the host's requests starts from (`sentkeys.host_sections`:
//! a section's root is its `<section>_json` that no function of ITS module composes).

use chrono::DateTime;
use chrono_tz::Tz;
use serde_json::Value;

use crate::config::Config;
use crate::model::Id;
use crate::planwire;
use crate::priority::Candidate;
use crate::store::RuntimeState;
use crate::tree::Tree;

/// **The `planner` section as the binary sends it, composed ONCE** (the W-46
/// audit, README gap 4890): the routine instances of the planned date, §9.1's
/// what-if when `extend` names one ([`planwire::whatif_json`]), the section
/// ([`planwire::planner_json`]) and the running block's worked minutes to `now`
/// ([`planwire::running_worked_min`], [`planwire::add_worked_min`]). Until the audit
/// [`planwire::whatif_json`] was one body called by three compositions — the binary's
/// `kernel_capacity::planner_ask_from`, the TUI harness's planner and
/// `forkclass`' answer — so a bend in the binary's CALL (`blocks + 1`) met no
/// comparison: driven by the W-46 audit's reuse critic, the whole workspace
/// passed while the shipped overtime box named a drop fork 4748911's did not.
/// The binary and every harness that builds the binary's section call this;
/// `extend` is the one argument a caller still spells, and the binary's tests
/// hold it to the box's `+1 block` (`tui::tests`).
#[allow(clippy::too_many_arguments)]
pub fn planner_section(
    state: &RuntimeState,
    replay: &crate::log::Replay,
    now: DateTime<Tz>,
    tz: Tz,
    tree: &Tree,
    cands: &[Candidate],
    cfg: &Config,
    extend: Option<(&Id, u32)>,
) -> Value {
    let date = planwire::plan_date(state, now);
    let routines = planwire::routine_instances(cands, tree, now, date, tz);
    let overtime = extend.map(|(id, blocks)| planwire::whatif_json(cands, id, blocks, cfg));
    let mut planner = planwire::planner_json(state, replay, now, tz, &routines, overtime);
    if let Some(worked) = planwire::running_worked_min(state, replay, tz, now, now.date_naive(), now.fixed_offset()) {
        planwire::add_worked_min(&mut planner, worked);
    }
    planner
}
