import TmKernel
/-!
# The outstanding goals of stages 3 to 6, as statements

`PLAN-lean-kernel.md` §5 has four stages left and describes them in prose.
Prose can be skimmed past, and a goal nobody can state precisely is a goal
nobody has understood.  So every remaining obligation that *can* be written
down is written down here as a Lean `theorem` whose statement elaborates
against the real kernel and whose proof is `sorry`.

Three properties this file has, and each is load-bearing:

1. **Nothing imports it.**  `TmKernel.lean` does not, and no module of the
   library does.  Its `sorry`s therefore cannot reach a proved theorem, and
   `check.sh`'s axiom audit over `Check.lean` is what enforces that: if a
   `sorryAx` ever appears there, this file leaked.
2. **It elaborates on its own**, exactly as `Check.lean` does:
   `LEAN_PATH=.lake/build/lib/lean lean Goals.lean`.  A statement that
   typechecks is guaranteed to be well-formed and to name real definitions;
   `sorry` warnings are the point, errors are not.
3. **The count is a burn-down.**  `check.sh` check 7 reports how many goals
   stand.  A stage that discharges one moves the theorem into its real module
   and **deletes it here**, and the number drops.  It is not a score to
   maximise: adding a goal is admitting a debt, not making progress.

`totality.py` bans `sorry` in every module of the library and excludes this
file by name — see the comment there.

## Legend

Each goal carries the plan's own verdict letters:

* **P\*** — provable, not yet built.  The default.
* **R\*** — **expected refutation.**  The plan (§3.3) records six laws that are
  false as written and compiled the refutations; the ones below are the ones it
  expects to go the same way.  A goal that turns out false is a finding, and
  discharging it means proving the *negation* and renaming it accordingly.
* **?** — open and expensive.  §6.2.4's two relational laws.

## Provisional signatures, and where this file refuses to invent one

Where stage 3–6 vocabulary does not exist yet the choice was made per goal.
A provisional `def … := sorry` is declared **only** where the spec settles the
signature; each one says so at its declaration and says what stage 5 or 6 is
free to widen.  Everything else is listed below as prose, because an honest
"not stateable until X exists" is worth more than a plausible signature the
stage then has to fight.

**Not stateable yet, with what would have to exist first:**

* **D1 and D2 — the recurrence denotation** (§5.1, plan §3.2).  The plan fixes
  the *shape*: one denotation `Log → Instant → Option Occurrence`, with the
  four `Recur` constructors kept as syntax.  `Field.Recur` exists, and since
  stage 5 D9 step B3 so does the log's typed event: `Log.Event` and `Log.Entry`,
  read by `Log.readLine`, with `routine{item, inst, status}`, `skip{item, inst}`
  and `Log.parseInstanceStatus`.  (This note used to say "`PlanCore.log` is
  `List String`"; `PlanCore` has no log field, and no commit on this branch gave
  it one.)  What does not
  exist yet is the replay that turns those events into instance states (stage 5
  C1–C6, `Replay.lean`).  Until it does, "exactly one pending instance" (§5.1's
  AfterDone rule, which is D1)
  and the classification pair `calendar_is_history_independent` /
  `afterDone_is_history_dependent` cannot be written at all.  Declaring an
  `Occurrence` here would fix the log model, which is stage 5's decision.
* **D2's epoch.**  `Rule.everyNDays n` carries a period and no anchor, so
  `every:3d` has no epoch to count from.  That is a **spec gap**, not a false
  theorem: there is nothing to state until §5 says what the epoch is.
* **F6 — `close day` double-counted `est:` against logged minutes.**  Needs
  `done_minutes` (§6.4), which is a replay of `.tm/log.jsonl`.  Same blocker as
  D1.  What *was* stated, `close_writes_every_estimate_through_demoteEst`, is
  refuted (stage 4 step 7, `210daad`); the half that does not need the log was
  `close_keeps_every_remaining_estimate`, restated at README gap 53 as
  `close_reads_every_remaining_estimate_through_demoteEst` (Close.lean), and at goal
  B3's repair as `close_reads_every_remaining_estimate_through_demoteEst_and_the_fold`.
* **F3 and G1 — generated-block ownership.**  "The kernel owns the bytes of
  every generated block" is §4's **A** verdict — single ownership, architecture
  rather than type theory, and the plan says not to credit the compiler for an
  **A** row.  The acceptance is a Rust test asserting the day-section text is
  byte-identical across the file, `tm now`, `tm tui` and `tm plan --json`.
* **`ClosePolicy`'s five rows** (plan §3.2's named residue): copy-versus-move
  disposition, the off-chain `backlog#Overdue` target, child-folding, stamp
  accrual, exemptions.  *Landed 2026-09-12 (stage 4 step 2)* as
  `Tm.closePolicy : Grain → ClosePolicy` in `Close.lean`, read by `close`
  rather than passed to it, each row pinned by a bridge theorem; the overdue
  target and the child fold are `Owed` columns (stage 5, gap 22), not
  behaviour.  *Since 2026-09-13 (the owner's D7, stage 4 final step 2)* the overdue
  target is behaviour — `OverdueRule`, the week row's `toBacklogOverdue`, bridged by
  `closePolicy_routes_overdue_only_at_week` — and only the child fold is `Owed`.
  *Since 2026-09-13 (stage 4 final step 4, goal B3's repair)* the child fold is
  behaviour too — `ChildRule`, the week row's `dropIntoParent`, bridged by
  `closePolicy_drops_children_only_at_week` — and the table owes nothing.
* **R7 — how future-day capacity mixes lounge and home by `p_lounge`**
  (README gap 26, in the `Arith.lean` block).  Whether the planner floors the mixture per
  level, per day, or carries it exact into the EDF pass is a **decision** the
  planner has to make and state.  A decision is not a proof obligation.
* **Stage 5's parity harness** — kernel versus the Rust `f64` path over the
  fixture corpus, agreeing except at the six stated rounding sites.  That is a
  measurement, and `check.sh` is where it belongs.
* **Stage 3's panic probe** — "returns `KernelFault`, not exit 0".  Every Lean
  function here is total by construction, so there is nothing to state on this
  side; the probe is a Rust test against the shim.
* **§6.1's `dayPlan_ok` at its real eligibility** (stage 6, track G).  The
  eleven checkers, their reflection lemmas, `planOk`, `checks_all` and the
  eleven one-line bridges are built and proved in `PlanCheck.lean`, and the
  **eligibility-free half of the lift is a theorem there**, not a goal:
  `PlanCheck.dayPlan_ok_core`, re-proved at the W-14 land step over the day step
  P1 produces and carrying the two hypotheses that day makes necessary (README
  gap 385).  The other four checks compare
  two candidates and have to be restricted to comparable ones (design §6.3),
  and that predicate — `eligibleAt`, design §15 — is step **P5**'s.  Until it
  exists the whole-battery lift is **not stateable**: `∀ el, planOk el r
  (dayPlan r) = true` is the *unrestricted* claim §6.3 refutes, and `∃ el, …` is
  satisfied by the predicate that answers `false`.  So it is here as prose and
  not as a `sorry`, and the step that writes `eligibleAt` states it.
* **§7.1's bin ladder is deliberately absent.**  Three of its four edges are
  halvings and the fourth is 1/10, so it does not derive; the only property it
  supports is antitonicity, and that is already proved
  (`Arith.rungs_antitone`, `Arith.binOf_antitone`).  Restating it as a goal
  would be manufacturing debt.

## A note for whoever edits this next

Prefer statements over stable vocabulary — `Grain`, `Cal`, `Arith`, `Field`,
`applyCmd`, `Core`'s field views.  Statements that mention `Site`, `archive`,
`demotionsOriented` or `orientPair` are the ones a change to the
demotion-orientation model will move.
-/
namespace Tm
namespace Goals

open Field (Shape Recur Dur DurUnit DT Stamp Flag)

/-! ############################################################################
# STAGE 3 — the boundary: `dispatch`, and the text path's last unproved step

Plan §5: "`shim.c`, `build.rs`, `dispatch` for `move`/`demote`/`readopt`/`drop`/
`edit`/`rank`/`add`".  All seven verbs are on the wire now: `rank` landed
2026-09-09 (L20a/L20b — `rank_is_idempotent`,
`rank_preserves_the_order_of_the_others`), and `add` landed at 9840ea8 —
`ReqCmd.add` (Boundary.lean:815), its `parseCmd` case (:838) and its
`applyCmd` case (:991) — built on `freshId` with L21 proved
(`add_assigns_a_fresh_id`, pigeonhole over `digitsOf`-rendered candidates,
not a retry loop), and the L22 refutation sweep is done —
`move_has_an_inverse_command` was refuted as `move_has_no_inverse_command`
(Boundary.lean), general over the seven `ReqCmd` shapes at the two-item
witness.  What remains of stage 3 is the three JSON/newline edge laws below.
README gap 13 —
`Id`'s *shape* — is STILL a human decision: `add` shipped digit ids,
consistent with the recorded resolution (weaken the spec — digits are a
subset of `[a-z0-9]`) and with no other, but the decision itself remains owed
to the human.
############################################################################ -/

/-! ## Boundary.lean — README gap 6 and gap 12: the JSON/string edge

The theorems of stage 2 begin at `ReqDoc` (a `List (List Char)`) and end at
`renderDocAt`'s `List (List Char)`.  The JSON edge and the newline split sat
between that and the wire.  Both are discharged now (the two blocks below,
2026-09-12); what remains outside any theorem is the host's agreement with the
kernel's parser, printer and splitter, which the FFI and corpus suites evidence. -/

/- **`the_json_edge_round_trips` is discharged, renamed
`the_response_call_emits_parses_back` (2026-09-12, J-route step 3).**  The goal
was stated over `Lean.Json.parse ∘ Lean.Json.compress`, whose `partial def`s
make it neither provable nor refutable (README "Gap 39 REPRICED"); its doc
comment licensed the narrowing to the code `call` runs.  `call` now reads with
the kernel's structural `jparse` and writes with `jemit` (`TmKernel/Json.lean`,
no `Lean.Json` on the wire), `jparse_jemit` is the round trip for every `JVal`
unconditionally, and `the_response_call_emits_parses_back (input : String) :
jparse (call input).toList = .ok (respond input.toList)` is its instance at the
exported function — a theorem of `Boundary.lean`, audited in `Check.lean`.
`call_refuses_the_real_duplicate_id_request` is its end-to-end witness on the
FFI suite's own bytes.  The statement over `Lean.Json` is not restated: no
kernel code path consumes `Lean.Json` any more.  The host-agreement obligation
— serde_json reads what `jemit` writes and writes what `jparse` reads — is what
the FFI and corpus suites evidence.  See the README's J5–J6 block. -/

/- **Gap 12's two goals are discharged at the char representation
(2026-09-12).**  `a_file_splits_into_the_lines_it_was_joined_from_char`
(unconditional round trip over the kernel's own structural `Tm.splitOn`, the
splitter on the wire path) and `joining_lines_is_not_injective_char` (the
expected refutation, renamed to its negation and proved by `decide` on the
witness `[['a','\n','b']]`) are theorems of `Text.lean`, audited in
`Check.lean`.  The `String.splitOn`-level statements that stood here are not
restated: the legacy splitter is kernel-stuck (README gap 38) and no kernel
code path consumes it; the host-agreement obligation — Rust's `split('\n')`
computes what `Tm.splitOn '\n'` computes, empty segments included — is what
the FFI corpus tests evidence.  See the 2026-09-12 README block. -/

/-! ## Plan.lean / Boundary.lean — README gap 16: CLOSED 2026-09-09

All three loader conjuncts are discharged in `Boundary.lean`:
`the_loader_builds_sites_in_range`, `the_loader_builds_oriented_demotions`,
`the_loader_builds_a_normalized_plan`.  The sites and orientation halves read
per-entity facts off `buildEntities_spec` and case on the filter list in the
shape `buildEntity_renders` started.  `normalized` assembles three facts —
`splitDoc_prose_nodup`/`splitDoc_items_nodup`/`splitDoc_slots_separated`
(the index partition), `placements_slot_nodup` (no two request lines name one
slot), and `store_lines_nodup` (the store renders each line once) — so
`itemCheck: rankCollision` is now unreachable from a request that loaded. -/

/- **Gap 4 is closed.**  `Cmd.setEstE` now writes through the field setter
`Field.setEst`, so the request path and `Core.est` share one reader pair, and
the law `the_command_path_writes_what_the_field_path_reads` is a theorem of
`Cmd.lean` — discharged from this file, audited in `Check.lean`.  The
stage-one `Nat` setter survives as `Cmd.setEstFoldE`, fold arithmetic used
only by `demoteEst`; the stage-4 rollup goals may read either view. -/

/-! ############################################################################
# STAGE 4 — `close`, `autoClose`, `ClosePolicy`; laws L16–L19, L27

Plan §5: "close idempotent at library *and* CLI level; a 3-month-stale tree
catches up losing nothing; the two behaviour changes landed with assent".
Read "the two behaviour changes" as **one**: D1, `close day` targets the week
containing *now* (`closeTo`), taken with the owner's assent on 2026-09-12.  The
second, "week→month is the month of today", was never a behaviour change —
fork-point `horizon::close_week` already computes `closeTo week now` — and was
withdrawn at stage 4 step 1 (README "Stage 4 opens", AGENTS §10.2).
§4's F1, F2 and F4 are discharged here; B1–B3 are re-owed at the fold level.
At stage 4's close one goal of this section stood: B3, on gap 22 (closed at stage 4
final step 3, D6).  It is refuted and renamed at stage 4 final step 4, with the `max`
law beside it; **no goal of stage 4 stands**.
############################################################################ -/

/- **`close` is real (2026-09-12, stage 4 step 2).**  The provisional
`def close (g : Grain) (now : Day) : Transform := sorry` that stood here is
replaced by `Tm.close` in `TmKernel/Close.lean`, with the signature it declared:
the grain, the instant, `Transform` as the shape, and `ClosePolicy` read from a
table indexed by `Grain` rather than passed.  Every goal below that names
`close` now elaborates against that definition.  `close_spec` is its
denotation; the README's stage-4 step-2 block records what it does and what it
scopes out.  (Since goal B3's repair the signature also takes the block length,
`close g now bm`: the week row's child fold adds a `1b` child to a `30m` one.) -/

/- **`autoClose` is real (2026-09-12, stage 4 step 4).**  The provisional
`def autoClose (now : Day) : Transform := sorry` that stood here is replaced by
`Tm.autoClose` in `TmKernel/Close.lean`, with the signature it declared: each
grain's close once, in `autoCloseOrder = [day, week, month]` — coarsest last. -/

/- **`close_is_idempotent` (L16) is discharged (2026-09-12, stage 4 step 3)** —
proved as stated in `Close.lean`, audited in `Check.lean`.  The engine was the
narrowed neighbour below, `close_leaves_no_line_it_would_take`, not this file's
over-strong L18: the second run's candidate set is empty.  Its doc comment says
which idempotence it is — the fold on `WfPlan` at one `g` and one `now`, not
§6.3's `state.json` one. -/

/- **`close_leaves_no_live_line_in_a_closed_region` (L18 at plan level) is refuted
(2026-09-13, stage 4 step 7, `210daad`)** — renamed to its negation
`close_leaves_live_lines_in_a_closed_region` and proved in `Boundary.lean` on the
loaded week witness, audited in `Check.lean`.  It was stated over every line, and
§6.3 leaves settled, recurring and wall lines in a closed file (`^t1`, `[x]`).
The narrowed law is `close_leaves_no_line_it_would_take` (Close.lean), with its
unpacked reading `close_leaves_no_unfinished_line_in_a_closed_region`. -/

/- **`close_week_and_close_month_commute` (L17) is refuted (2026-09-12, stage 4
step 3)** — renamed to its negation `close_week_and_close_month_do_not_commute`
and proved in `Boundary.lean` on a loaded plan, audited in `Check.lean`.  The
reason this goal gave is wrong under D1: at one instant neither close sees the
other's output, and `two_closes_at_one_instant_commute_on_skeletons`
(`Close.lean`) proves every line's file, box, bytes and tombstone agree
whenever both orders succeed.  The orders differ only in rank — both land a line at the end of
the open month's `# Demoted`.  So the order the next goal fixes decides line
order inside a shared section, and nothing else. -/

/- **L19a–c are gone (2026-09-12, stage 4 step 4)**, each with a proof of what
it states or of its negation, audited in `Check.lean`:
`autoClose_is_each_grain_once` (L19a) and `autoClose_catches_up_in_one_step`
(F1 / L19b) are proved as stated in `Close.lean`; `autoClose_runs_every_period_it_passes`
(F1 / L19c) is refuted — it quantified over the `[x]`, recurring and done-outcome
lines §6.3 leaves in a closed file — renamed to its negation
`autoClose_leaves_lines_in_periods_it_passes` and proved in `Boundary.lean` on a
loaded plan three months stale.  Its narrowing is `autoClose_strands_no_unfinished_line`
(Close.lean): no line any close would take survives, at any grain.  The F1
double stamp was `autoClose_stamps_each_line_at_most_once`, restated at README gap
53 as `autoClose_appends_at_most_one_stamp_or_merges_each_line` (Close.lean). -/

/- **`close_never_demotes_a_wall` (F4) and
`close_writes_every_estimate_through_demoteEst` (B1–B3) are refuted (2026-09-13,
stage 4 step 7, `210daad`)** — renamed to their negations
`close_does_not_leave_every_wall_as_it_was` and
`close_writes_a_line_demoteEst_does_not`, proved in `Boundary.lean` on the loaded
week witness, audited in `Check.lean`.  F4's `f.val = e.val` forbade the carry
of a wall still ahead (`^x1`); B1–B3 equated the whole line and so forbade the
`demoted:` stamp (`^m2`).  The narrowed laws, in `Close.lean`:
`close_never_demotes_a_wall_but_may_carry_it` (box, bytes and tombstone kept;
only the file may change), `close_rewrites_a_line_only_by_stamping_it`, and the
estimate half step 2 owed, `close_keeps_every_remaining_estimate`, built on
`Field.remainingOf_setDemoted` (Line.lean).  The last two were restated at README
gap 53, when a close began merging into a standing record:
`close_rewrites_a_line_only_by_stamping_or_merging_it` and
`close_reads_every_remaining_estimate_through_demoteEst` — and again at goal B3's
repair, when a close began folding dropped children into their parents' records:
`close_rewrites_a_line_only_by_stamping_merging_or_folding_it` and
`close_reads_every_remaining_estimate_through_demoteEst_and_the_fold`. -/

/- **`close_day_stamps_a_day_stamp` is discharged (2026-09-12, stage 4 step
2)** — proved as stated in `Close.lean`, audited in `Check.lean`.  D1 kept the
stamp `demoted:D<dd>`, and the table's day row names `StampRule.dayOfMonth`;
`closeStamp_names_the_closed_grain` is the bridge that makes a day row stamping
`W` a build failure. -/

/- **`close_week_folds_a_dropped_child_into_its_parent` (B3) is refuted (2026-09-13,
stage 4 final step 4)** — renamed to its negation
`close_week_does_not_add_a_dropped_child_to_its_parent` and proved in `Boundary.lean` on
the loaded fold witness (`closeFoldWitness`: `^p2`, `6b`, with its dropped `1b` subtask
`^c3` carries 300 minutes, not 350), audited in `Check.lean`.  Its statement added a
dropped child's remaining to its parent's; spec §6.4 makes a parent's own estimate
cover its decomposition (`remaining(item)`: its own `est` if set, else `est_original`,
else Σ over children), so the addition double-counts.  The negation is stated
quantifier for quantifier; the goal's `close week now p` is `close week now bm p`
there, at the `bm` the goal already bound, because the close now reads the block
length (the child fold adds a `1b` child to a `30m` one).  The law beside it, in
`Close.lean`, is fork-point `horizon::demote_est`'s documented choice "Folding
children": `close_week_folds_dropped_children_by_max` — a line the week row files
forward carries `max(what it carried, Σ own remaining of the children dropped with
it)` — with both directions (`close_week_lifts_a_parent_its_dropped_children_outweigh`,
`close_week_keeps_a_parent_that_covers_its_dropped_children`), the child's side
(`close_week_drops_a_child_with_its_parent`), and what the goal meant and holds:
`close_week_keeps_a_dropped_childs_remaining_in_its_parents_record`.  Non-vacuity:
`close_week_folds_dropped_children_by_max_is_not_vacuous` (both directions) and
`close_week_drops_a_child_with_its_parent_is_not_vacuous`.

**Stage 4's goal count is zero.** -/

/- **`lifecycle_commands_commute` (L27) is refuted (2026-09-12, stage 4 step 3)**
— renamed to its negation `lifecycle_commands_do_not_commute` and proved in
`Boundary.lean` (a demote/readopt pair at one id: `readopt` first answers
`notDemoted`), audited in `Check.lean`.  The product question it surfaced is not
answered by that: whether lifecycle pairs that both succeed *should* commute
(R7's `demote ^m1 ; move ^m1 week`) is AGENTS §10.5 q7, the owner's, stage 6. -/

/-! ############################################################################
# STAGE 5 — recurrence, rollups, priority, capacity

Plan §5: "parity harness: kernel vs Rust over the fixture corpus agrees except
at the six stated rounding sites".  The recurrence half of this stage is in the
header's not-yet-stateable list; what follows is the half that has vocabulary.
############################################################################ -/

/- **§6.4's `remaining` and §5.4's series head are real (2026-09-14, stage 5 step 1).**
The provisional `remainingMin` and `seriesHead` that stood here are replaced by
`Tm.remainingMin` and `Tm.seriesHead` in `TmKernel/Tree.lean`, with the signatures
they declared.  Of this section's five goals, `the_series_head_is_not_settled` and
`the_series_head_ranks_first` are proved as stated (`Tree.lean`).  The three §6.4 rows
were stated over every item and with no `dur:` row; fork-point `Tree::remaining_inner`
answers `0` for a Done or Dropped item and `Item::own_remaining` reads `dur:` before the
children, so each is refuted as written on a loaded plan (`Boundary.lean`:
`remaining_is_not_the_est_key_on_a_settled_line`,
`remaining_does_not_fall_back_to_the_leading_estimate_on_a_settled_line`,
`remaining_does_not_sum_the_children_over_a_dur`), with the law that holds beside each
(`remaining_is_the_est_key_when_set_and_unsettled`,
`remaining_falls_back_to_the_leading_estimate_when_unsettled`,
`remaining_sums_the_children_when_unsettled_with_no_dur`).  README "Stage 5 step 1". -/

/- **§7's `prio` and §7.4's `hysteresis` are real (2026-09-14, stage 5 step 2).**
The provisional `prio` and `hysteresis` that stood here are replaced by `Tm.prio` and
`Tm.hysteresis` in `TmKernel/Priority.lean`, with the signatures they declared.  All six
goals of this block are proved as stated there: `prio_of_hot_is_zero`,
`prio_is_clamped`, `prio_is_antitone_in_utilisation`,
`hysteresis_improves_by_at_most_one_bin`, `hysteresis_worsens_freely` and
`hysteresis_never_delays_hot`.  `hysteresis` follows fork-point
`priority::apply_hysteresis`, which passes a raw `0` before comparing.  README "Stage 5
step 2". -/

/- **§7.3's EDF pass is real, over D10's rational minutes (2026-09-14, stage 5 step 3).**
The provisional `DayCapacity`, `Deadline` and `edf` that stood here are replaced by
`Tm.DayCapacity`, `Tm.Deadline` and `Tm.edf` in `TmKernel/Capacity.lean`.  D10 makes a
level's expected minutes an exact rational, so `DayCapacity.minutesAt : Fin 6 → Nat` became
numerators `numAt` over one positive denominator `den : Den` that `edf` now takes, with
`c.minutesAt den l : Arith.Pos` the rational.  The three goals are proved over that
representation, which is the generalising restatement D10 forces, not a weakening:
`edf_keeps_the_days` (the statement unchanged but for `den`), `edf_only_spends_capacity`
(`Q.le` of the rationals, with `edf_only_spends_numerators` the provisional statement verbatim
over the numerators at every denominator), and `edf_reserves_only_before_the_deadline`
(equality of the rationals).  README "Stage 5 step 3". -/

/- **§8.1's window (E7) is real, in stage 5 (2026-09-14, stage 5 D10 step L2).**
The owner's D12 pulls stage 6's window into stage 5, so STAGE 6's E7 block — the real
`wallsInside`, the provisional `windowEnd` and the goals `the_window_end_solves_the_equation`
and `the_window_end_is_the_least_solution` — is deleted here and its vocabulary lives in
`TmKernel/Lookahead.lean` (`Look.windowEnd`, `Look.windowBase`, `Look.wallOverlap`).  Both
goals were **false as written** against fork-point `capacity::window_and_budget`, which clips
walls at the arrival, merges them and counts their overlap, and clamps the base to the
arrival: `Look.the_window_end_is_not_the_least_solution_as_stage_6_wrote_it` (a wall
straddling the base end) and `Look.the_window_end_does_not_solve_the_equation_as_stage_6_wrote_it`
(an arrival after the cap), with `Look.wallsInside` kept only for the refutations.  Restated
over `Look.wallOverlap` and `Look.windowBase`, both are proved under the same names
(§3.1 item 3; restated to the oracle's overlap semantics, refuted as written).  Stage 6's
`dayPlan` reuses `Look.windowEnd`; the burn-down drops by 2.  README "Stage 5 D10 L2". -/

/- **§7.1's undo mask is real (2026-09-14, stage 5 D9 step C1).**
The four C1 goals of design §15 were added here as written, elaborated against
`TmKernel/Replay.lean` (17 goals, no error), and discharged in the same step, so the
burn-down stays at 13: `Replay.survivors_snoc_event`, `Replay.survivors_snoc_undo` and
`Replay.a_cancelled_event_is_never_revived` are proved as stated, and
`Replay.a_dangling_undo_dangles_in_every_extension` is proved **without** §15's `hl` and
`hu`, which it does not need (§15's statement is that theorem applied to fewer
arguments).  README "Stage 5 D9 C1". -/

/- **§6.2's day index is real (2026-09-14, stage 5 D9 step C2).**
The three C2 goals of design §15 were added here **restated in chrono's order**, elaborated against
`TmKernel/Replay.lean` (16 goals, no error), and discharged in the same step, so the burn-down stays
at 13.  §15 wrote them on `Cal.Instant.nanos`; the fork sorts `DateTime`s and tests
`t.signed_duration_since(w) < Duration::hours(24)`, which differ from nanosecond counts at a leap
second, and each statement as written is false of the fork's index
(`Replay.dayOf_is_the_wake_date_within_a_day_by_nanos_is_refuted`,
`Replay.a_wake_day_is_shorter_than_a_day_by_nanos_is_refuted`,
`Replay.keptWakes_append_of_later_by_nanos_is_refuted`).  Restated with `(Cal.durationBetween w t).1 <
86400` and `Cal.Instant`'s `<`, all three are proved as restated:
`Replay.dayOf_is_the_wake_date_within_a_day`, `Replay.a_wake_day_is_shorter_than_a_day` and
`Replay.keptWakes_append_of_later` (each checked against its restated goal by a scratch `example`).
README "Stage 5 D9 C2". -/

/- **§8.2's machine is real for the block family (2026-09-15, stage 5 D9 step C3).**
The three C3 goals of design §15 were added here as written, elaborated against
`TmKernel/Replay.lean` (16 goals, no error), and discharged in the same step, so the burn-down stays
at 13: `Replay.applyEffects_touches_only_named_keys` (the frame law),
`Replay.every_known_event_has_an_arm` (one header effect per entry, whatever its kind) and
`Replay.credit_conserves_the_day_minutes` (a day's ci minutes and ci-unknown minutes add up to its
block minutes, the stop-then-done replacement included) are proved as stated, each checked against
its goal by a scratch `example`.  §8.2's witness `an_extend_changes_only_the_bookkeeping` (not a goal
here) is false under the owner's D14, which ports `extended_min`:
`Replay.an_extend_changes_more_than_the_bookkeeping`, with the law beside it,
`Replay.an_extend_changes_only_the_bookkeeping_and_its_extended_minutes`.  README "Stage 5 D9 C3". -/

/- **§8.2's completion family is real (2026-09-15, stage 5 D9 step C4).**
The C4 goals of design §15 were added here, elaborated against `TmKernel/Replay.lean` (16 goals, no
error), and discharged in the same step, so the burn-down stays at 13, each checked against its goal by a
scratch `example`.  Quirk Q6(b) is ported faithfully (gap 118): `Replay.an_instance_is_its_last_record_in_file_order`
(fork `instances[item][inst]` holds the last surviving `routine` or `skip` in file order) is proved as
stated; `Replay.last_done_is_the_latest_by_instant` is proved with §15's `Replay.doneInstants z i` taking
no zone (a completion's instant does not read one: `doneInstants i`), and
`Replay.last_done_is_the_first_of_the_latest` says what the running maximum is (the first of the latest
by chrono's order).  `Replay.instances_and_last_done_order_differently` (§15's `∃ …`) is stated as a
retro append whose instance record is strictly earlier than `last_done`.  Beside them, carried note 3:
design §8.4's "a since filter commutes with max" is refuted
(`Replay.a_since_filter_does_not_commute_with_the_latest_by_instant`), and the kernel keeps both of fork
`LatestNamed`'s instants (`Replay.named_keeps_the_latest_by_instant_and_the_latest_by_local_date`).
README "Stage 5 D9 C4". -/

/- **§8.2's day header and records family is real (2026-09-15, stage 5 D9 step C5).**
The C5 goals were added here, elaborated against `TmKernel/Replay.lean` (17 goals, no error), and discharged in
the same step, so the burn-down stays at 13, each checked against its proof by a scratch `example`.
`Replay.energy_obs_slept_is_the_days_first_logged_sleep` (§15's late binding: an energy observation that is not a
start's reads the first surviving wake in file order of its day, a wake logged after it included) is proved as
stated.  Design §8.2 lists the other three as witnesses; they were stated here as laws where a law exists:
`Replay.the_first_leak_maximum_wins` (fork `longest_leak` is the running maximum of the survivors' leak gaps under
a strictly-longer replacement, so the first of equal maxima stays; witness
`Replay.the_first_of_equal_leaks_is_the_longest`), `Replay.a_demote_stamp_reads_the_week_or_date_key` (every
demotion carries `Log.stampFromKey` of its `from`; witness `Replay.the_demote_stamps_of_a_week_a_date_and_a_month_key`),
and `Replay.idle_and_idle_since_read_different_orders` (§8.4's two-line log, as `∃ …`: `lastEffective` is the
last line and `Replay.lastTOn`, fork `DaySeam.last_t`, the latest instant).  Quirk Q6(g) is ported with its
separating witness `Replay.the_calendar_today_is_not_the_replays_day_after_midnight`; **Q6(f) was ported here and
fixed at W-12** (gap 86), its witness now
`Replay.an_undo_of_a_close_cancels_its_own_period_and_an_older_one_still_cancels_the_latest`, which keeps the old
spelling's behaviour as its own conjunct.  README "Stage 5 D9 C5". -/

/- **§8.4's view is real: the facts, the observations and the headers (2026-09-15, stage 5 D9 step C6).**
The two C6 goals of design §15 were added here, elaborated against `TmKernel/Replay.lean` (15 goals, no error), and
discharged in the same step, so the burn-down stays at 13, each checked against its proof by a scratch `example`.
`Replay.every_dated_output_names_its_day_key` is proved for every effect (§15's statement, over an entry's effects,
is it given fewer arguments), with `Replay.Effect.day?` the day of the dated record an effect writes and
`Replay.Key.date?` the date a key names; the global longest leak, an all-time aggregate whose record carries a day,
is keyed `global`, and `Replay.every_leak_is_on_a_day_its_idle_record_names` shows its gap's day is named by the
same entry's idle record.  §15's `observations_are_in_file_order` is **false as stated**, over every list of
entries: an `energy` entry listed twice gives two observations on one line
(`Replay.observations_are_not_in_file_order_when_a_line_repeats`).  The law holds on the log op's entries, whose
lines strictly increase: `Replay.observations_are_in_file_order_on_increasing_lines`.  README "Stage 5 D9 C6". -/

/- **§7.3's undo law is real (2026-09-15, stage 5 D9 step C7).**
The three C7 goals of design §15 were added here, with `Replay.undosFor` taking the offset `ctx.now` is written at
(`o`, which the stamp of an `Entry` needs), elaborated against `TmKernel/Replay.lean` (16 goals, no error), and
discharged in the same step, so the burn-down stays at 13, each checked against its proof by a scratch `example`.
`Replay.undoing_a_command_replays_the_log_without_it` is proved **without** §15's `hl`, which it does not need (the
mask's half is about entries, not lines; §15's statement is that theorem given fewer arguments), in two halves:
`Replay.undoing_a_command_leaves_the_survivors_of_the_log_without_it` (the mask) and
`Replay.the_view_reads_only_the_survivors` (the replay sizes its maps by the log's length, and the view reads them
through `get` and their keys).  Beside it, `Replay.undoing_the_last_command_replays_the_log_without_it` (`M = []`) and
`Replay.undoing_a_command_answers_every_fact_query_as_the_log_without_it` (through `ask`).  The two quirk witnesses
are proved as stated: `Replay.undo_of_a_silent_verb_cancels_an_older_event` (Q6(d), gap 84; the law beside it,
`Replay.a_silent_verb_undo_cancels_nothing_iff_no_survivor_has_its_name`) and
`Replay.undo_after_housekeeping_cancels_the_housekeeping` (Q6(f), gap 86), with the refutation twin in the law's own
conclusion, `Replay.the_undo_law_fails_without_untouchedBy`.  README "Stage 5 D9 C7". -/

/-! ############################################################################
# STAGE 5 — D9 window (W1, added: the burn-down rises by 16) → discharged in W2
Design `kernel/design/stage5/stage5-D9-D10-design.md` §9.5 and §15's W block, elaborated against
`TmKernel/Seal.lean`.  `T₀` is the day a checkpoint was sealed at, `T` the request's day, `L` its
ledger day; `a` the folded lines, `r` the unfolded lines known when it was sealed (a prefix of the
tail `b`).

**A deliberate debt** (§14.5's W1 row): these sixteen goals and the six provisional definitions
below enter at W1 and leave at W2, which discharges them by §9.5's route.  A goal false as stated
is refuted and renamed with the correct law beside it; a narrowed window law is not allowed (the
owner's D5 and D11).

**Restated from §15 where the repo differs** (README "Stage 5 D9 W1", recorded disagreements):
§15 writes `Replay.ask (Replay.replayDoc z ls)` and `(Replay.replayDoc z ls).obs` over lines; no
`Log.Line` type existed and `replayDoc` takes entries, so W1 adds `Log.Line` and
`Seal.replayLines z ls` (`Replay.replayDoc` over `Log.lineEntries ls`) and the goals read it.
`Seal.Q` is `Replay.Q` (carried note 3).  The laws over `ask` compare views, never `Facts` values:
a resumed checkpoint's maps are sized differently (C7's `SameReadings`, carried note 4).
**W2, part 1** discharged law 1's four goals and law 11 (`Seal.the_answer_reads_the_replay`,
`Seal.a_day_record_is_the_replays_day`, `Seal.a_window_record_is_the_replays_window`,
`Seal.seal_partition_is_the_replay`, `Seal.sealed_and_live_observations_are_the_replays`, in `SealLaw.lean`);
eleven goals and the six provisional definitions remained.
**W2, part 2** discharged law 2 (`Seal.resume_is_replay`, through the codec round trips as rewrites), law 3
(`Seal.resume_answer_ignores_the_policy`), the `now` anchor (`Seal.an_accepted_resume_covers_now`), law 8
(`Seal.resume_from_empty_is_replay`) and its pair (`Seal.resume_from_empty_never_refuses_by_guard`), in
`SealLaw2D.lean`–`SealLaw2F.lean`; the real `Seal.resume` (`SealResume.lean`) replaced its provisional definition, so
the goals below read it.  Its reseal (`Seal.resealOf`) is not built yet and returns `none`: laws 6, 6's pair and 7
hold vacuously of it and are **not** discharged.  Six goals and five provisional definitions remained.
**W2, part 3** discharged law 4 (`Seal.resume_keeps_the_sealed_records`, `SealLaw4.lean`) and law 5 in both directions
(`Seal.resume_ok_iff`, `SealLaw5B.lean`), with the real `Seal.reachFree` and `Seal.tagsClear` (`SealReach.lean`)
replacing their provisional definitions.  Four goals (laws 6, 6's pair, 7 and 9) and three provisional definitions
(`foldPoint`, `sealDay`, `genesis`) remained.
**W2, part 4b** built the reseal (`Seal.resealOf`, `Seal.foldPoint`, `Seal.sealDay` in `SealResume.lean`; the
provisional `foldPoint` and `sealDay` are deleted) and discharged law 6's pair (`Seal.a_reseal_never_seals_past_now`,
`SealLaw6Pair.lean`).  Laws 6 and 7 read the real reseal and are not vacuous: they remain, with law 9 and the
provisional `genesis` (README "Stage 5 D9 W2, part 4b").
**W2, part 4c** discharged law 6 (`Seal.reseal_is_seal`) and law 7 (`Seal.a_resealed_checkpoint_accepts_its_own_suffix`),
in `SealLaw6.lean`: the reseal's parts are named (`SealRsDefs.lean`), an accepted resume and a valid cut are unpacked as
entries (`SealLaw6Ctx.lean`), the resealed checkpoint and records are the seal's at the cut (`SealLaw6Ckpt.lean`), and the
resealed checkpoint is sealable and its suffix meets law 5's reach condition at the new ledger day (`SealLaw6Seal.lean`);
a checkpoint's own suffix leaves no undo dangling (`Seal.tagsClear_self`).  Law 9 and the provisional `genesis` remain
(README "Stage 5 D9 W2, part 4c").
**W2, part 4d** replaced the provisional `genesis` with the chunked rebuild with exact pops (`Seal.genesis`,
`SealGenesis.lean`) and discharged law 9 (`Seal.chunked_genesis_is_one_replay`, `SealLaw9.lean`): genesis' loop keeps law
9's invariant on every stack entry (`Seal.genLoop_ok`, one call by `Seal.genesis_call` through laws 2, 4, 6 and 7), and
the last call's answer with the records returned reads the replay by law 1.  The W block's sixteen goals are discharged
(README "Stage 5 D9 W2, part 4d").
############################################################################ -/

/-! ############################################################################
# STAGE 6 — the planner; §8.3's invariants; L24 and L25

Plan §5: "D1–D14 decidable-checked on every plan the corpus produces;
`planner_invariants.rs` green at 256 cases through the FFI".  L26 is "decidable
over the produced `DayPlan`", so the output type is what has to exist and the
input mostly does not.

**The five provisional declarations that stood here are gone** (stage 6 step
P0, `Planner.lean`): `SegKind`, `Seg`, `DayPlan`, `PlanReq` and `dayPlan` are
real now, and so are `segItems`, `assignedOf` and `blockSeconds`.  `Seg` moved
from minutes-since-midnight to `Look.Slot`'s **absolute seconds** (README gap
256), which is why every statement below reads `s.val.start`/`s.val.stop`.
Only `edfNumbers` stays provisional; design §5.5 gives it to step **P4**.

**NO GOAL BELOW MAY BE DISCHARGED UNTIL ITS STEP HAS LANDED.**  Design §6.4
says which step makes each goal real: P1 the two wall laws, P2 wind-down, P3
the break and one-block laws, P5 the remaining six, G2 and G3 the two
relational ones — **and §6.4's P1 row is wrong about one of the two**
(README gap 347).

**Step P2 has landed** (`Planner.lean`, §8.2 step 2: today's window instances
placed mandatory-first inside their own windows or at a free `pref:` anchor, the
rest deferred to step 6, and the wind-down and sleep rows that close the day).
It discharges **nothing here**, and design §14.2's P2 row — which gives it
`plan_places_no_demanding_block_after_wind_down` — is **wrong for the same reason
§6.4's P1 row was** (README gaps 347 and **430**): that goal quantifies over a
**Block** row, P2 places the WindDown row it is *about* but no Block, so the
statement is still vacuous over `dayPlan` and a discharge would be AGENTS §5.2's
own "a theorem that compiles and means nothing".  It becomes real at **P5**.  What P2
proved outright instead is `Planner.the_wind_down_row_runs_to_bed` — the evening
half of the same sentence, over the produced plan.

**Step P1 has landed** (`Planner.lean`, §8.2 step 1: the walls, the running
interruption, the replayed past, the conflicts and the travel-day zeroing).
`plan_never_moves_a_wall` is **gone from this file**: it is **false as it was
written here** — a `buffer:` puts a second Wall row in front of the event and a
wall past local midnight is clipped to the day — and it left as
`Planner.plan_never_moves_a_wall_as_stage_6_wrote_it_is_refuted` with the
restatement `Planner.plan_never_moves_a_wall` and the general form
`Planner.a_wall_row_comes_from_the_index` beside it (AGENTS §3.1 item 3, D5).

`plan_places_no_block_over_a_wall` **stays**, and staying is the point: step 1
places no Block of its own, so the statement is vacuous over `dayPlan` today
and a discharge would be AGENTS §5.2's theorem that compiles and means nothing.
It becomes real at **P5**.  The tripwire that says so is
`Planner.the_day_assigns_nothing_after_now_until_the_assign_step_lands`, which
is audited in `Check.lean` and which P5 must delete; while it compiles, no goal
below that quantifies over an assigned Block is worth discharging.

**Two goals below are stated in SECONDS after the W-14 repair** (README gap
392): `plan_does_not_overbook` and `plan_reserves_one_block_at_a_time`.  P0's
port to absolute seconds folded the *floored* `Seg.minutes`, which tolerates 59 s
of unbudgeted work per Block row where the minutes-since-midnight form it
replaced could not express a sub-minute overrun at all — a weakening of the
obligation, disclosed nowhere.  Seconds on both sides is the faithful port; it is
identical on minute-aligned rows and strictly stronger on the rows `pastRows`
can produce, which are clipped at `min stop now`.  `Planner.blockMinutes` is
`Planner.blockSeconds` now, and `PlanCheck`'s two checkers moved with them.

**The machinery that will discharge them is already built** (track G,
`PlanCheck.lean`, design §6): eleven decidable checkers, eleven reflection
lemmas, `planOk`/`planOkCore`, `checks_all`, and one bridge per goal, so each
discharge below is one line the day its step lands.  What landed with it is
`PlanCheck.dayPlan_ok_core`, the lift over the seven eligibility-free checks,
as a **theorem in a shipped module** rather than a goal — track G wrote it over
P0's empty day, and this run's merge is where P1's own body had to re-prove it
(README gap 385).  A goal below is still not dischargeable from it: seven of the
eleven checks are vacuous over a day whose only rows are walls, the replayed
past and the running interruption, and `dayPlan_ok_core` says exactly that much
and no more.
############################################################################ -/

open Planner

/-- **L26 / §8.3 "no overbooking" (P\*), stage 6.**  Σ Block minutes ≤
`remaining_budget × block_min`.  Decidable over the produced `DayPlan`, which is
what L26 promises.

Design §6.3 records this as **false as written** against the fork (§8.2 choice
5b gives the running block its minutes whatever the budget says); it is
restated with the Active reservation excluded, **and its refutation, in step
P5** — never here and never without the witness (AGENTS §3.1 item 3).

**Stated in seconds** (W-14 repair, gap 392).  Until this repair it read
`blockMinutes (dayPlan r) ≤ budget × blockMin` with `blockMinutes` folding the
*floored* `Seg.minutes`, which tolerates 59 s of unbudgeted work per Block row.
The minutes-since-midnight form this replaced at `c754cce` could not express a
sub-minute overrun, so the port had quietly made the obligation weaker; seconds
on both sides is the faithful one.  See `Planner.blockSeconds`. -/
theorem plan_does_not_overbook (r : PlanReq) :
    blockSeconds (dayPlan r) ≤ (dayPlan r).budgetBlocks * (dayPlan r).blockMin * 60 := sorry

/-- **E1 (P\*), stage 6.**  No block is longer than one block.  The shipped bug:
"the Active reservation covered the whole remaining estimate; a 6b item
swallowed 355 minutes".

**Stated in seconds**, for the reason above (W-14 repair, gap 392): `s.val.minutes
≤ blockMin` admits a Block of `blockMin` minutes and 59 seconds, and `pastRows`
clips a replayed row at `min stop now` — an arbitrary second. -/
theorem plan_reserves_one_block_at_a_time (r : PlanReq) (s : WfSeg)
    (hs : s ∈ (dayPlan r).segments) (hk : s.val.kind = SegKind.block) :
    s.val.stop - s.val.start ≤ (dayPlan r).blockMin * 60 := sorry

/-- **L26 / §8.3 "energy filter" (P\*), stage 6.**  Every block has
`item.ci ≤ slot.energy`.  `effectiveCi` (Plan.lean) is §3.2's inheritance walk,
already proved — this is the planner honouring it.  Rules out E8's shape: two
readers of an item's `ci` disagreeing about eligibility. -/
theorem plan_respects_the_energy_filter (r : PlanReq) (s : WfSeg) (i : Id) (lvl : Fin 6)
    (hs : s ∈ (dayPlan r).segments) (hk : s.val.kind = SegKind.block)
    (hi : s.val.item = some i) (he : s.val.energy = some lvl) :
    (effectiveCi r.plan.val i).val ≤ lvl.val := sorry

/-- **L26 / §8.3 "no segment overlaps a Wall" (P\*), stage 6.**  On absolute
seconds, so a wall that crosses midnight is covered. -/
theorem plan_places_no_block_over_a_wall (r : PlanReq) (b w : WfSeg)
    (hb : b ∈ (dayPlan r).segments) (hw : w ∈ (dayPlan r).segments)
    (hbk : b.val.kind = SegKind.block) (hwk : w.val.kind = SegKind.wall) :
    b.val.stop ≤ w.val.start ∨ w.val.stop ≤ b.val.start := sorry

/-- **E5 (P\*), stage 6.**  The same statement for breaks: "free positions
included breaks" is the shipped defect, and §8.2 step 3 puts "a break of
`break_min` after every `break_after_blocks` blocks" into the slot list, so a
planner that treats free time as free will place work on top of one. -/
theorem plan_places_no_block_over_a_break (r : PlanReq) (b k : WfSeg)
    (hb : b ∈ (dayPlan r).segments) (hk : k ∈ (dayPlan r).segments)
    (hbk : b.val.kind = SegKind.block) (hkk : k.val.kind = SegKind.brk) :
    b.val.stop ≤ k.val.start ∨ k.val.stop ≤ b.val.start := sorry

/-- **L26 / §8.3 "no ci ≥ 4 Block after wind-down" (P\*), stage 6.**  §8.2 step
2: "sleep and wind-down define the hard end of the day".

**P2 landed the WindDown row and did NOT discharge this** (README gap 430): the
statement is about a **Block** row and no step before P5 places one, so it is
vacuous over `dayPlan` today exactly as `plan_places_no_block_over_a_wall` is.
`Planner.the_wind_down_row_runs_to_bed` is the half P2 could prove. -/
theorem plan_places_no_demanding_block_after_wind_down (r : PlanReq) (b w : WfSeg) (i : Id)
    (hb : b ∈ (dayPlan r).segments) (hw : w ∈ (dayPlan r).segments)
    (hbk : b.val.kind = SegKind.block) (hwk : w.val.kind = SegKind.windDown)
    (hi : b.val.item = some i) (hafter : w.val.start ≤ b.val.start) :
    (effectiveCi r.plan.val i).val < 4 := sorry

/-- **L26 / §8.3 "monotone rank" (P\*), stage 6.**  "For two candidates with
equal `p` and equal `ci`, the one with the lower line order is never left
unassigned while the other is assigned."

Stated with `rootPrio` and `effectiveCi` standing in for §7's `p`, because
`prio` above is stage 5's and takes a bin this statement has no way to produce.
When stage 5 lands, the honest form replaces `rootPrio … = rootPrio …` with
equality of the computed priority; the shape of the goal does not change.

Design §6.3 records this as **false as written** — §8.2 step 5 skips a
`loc:`-constrained, `atomic` or `max:`-capped item for reasons no §8.3
invariant is about — and gives the restatement plus its refutation to **P5**. -/
theorem plan_is_monotone_in_rank (r : PlanReq) (i j : Id) (e f : Entity)
    (hi : r.plan.val.store.get i = some e) (hj : r.plan.val.store.get j = some f)
    (hp : rootPrio r.plan.val i = rootPrio r.plan.val j)
    (hc : effectiveCi r.plan.val i = effectiveCi r.plan.val j)
    (hdoc : e.val.live.doc = f.val.live.doc)
    (hlt : e.val.live.rank < f.val.live.rank)
    (hass : j ∈ assignedOf (dayPlan r)) :
    i ∈ assignedOf (dayPlan r) := sorry

/-- **L26 / §8.3 "HOT before queue" (P\*), stage 6.**  Stated over §7.2's `hot`
**flag**, which is in the grammar (`Field.Flag.hot`) and so needs nothing from
stage 5.  The `u ≥ 1` half of HOT is the next goal's business.  Design §6.3
gives its restatement and refutation to **P5**. -/
theorem plan_puts_hot_before_the_queue (r : PlanReq) (i j : Id) (e f : Entity) (sj : WfSeg)
    (hi : r.plan.val.store.get i = some e) (hj : r.plan.val.store.get j = some f)
    (hhot : Flag.hot ∈ e.val.flags) (hnot : Flag.hot ∉ f.val.flags)
    (hsj : sj ∈ (dayPlan r).segments) (hji : sj.val.item = some j) :
    ∃ si ∈ (dayPlan r).segments, si.val.item = some i ∧
      si.val.start ≤ sj.val.start := sorry

/-- **Provisional (stage 6), and the last one in this file.**  §7.3's two
numbers for one candidate: its `need` and the capacity available to it by its
due date, after earlier deadlines have reserved.  Stage 5's `edf` produces
both — design §5.5: this becomes `(g.deadline.need, g.avail)` from
`Cap.grantOf` over `r.caps`, in step **P4**, and since the burn-down counts
`theorem`s and not `def`s, check 7 does **not** move on the day it goes. -/
def edfNumbers (r : PlanReq) (i : Id) : Nat × Nat := sorry

/-- **L26 / §8.3 "impossible never dropped" (P\*), stage 6.**  §7.3: "IMPOSSIBLE
items are still scheduled with everything available; the banner names the item
and the shortfall".  Rules out the failure that silently looks like success —
an item the day cannot fit vanishing from the plan instead of appearing with a
shortfall.  `Arith.isImpossible` and `Arith.impossible_imp_hot` are proved
already; what is owed is that the planner acts on them.  Design §6.3 gives its
restatement and refutation to **P5**. -/
theorem plan_never_drops_an_impossible_item (r : PlanReq) (i : Id) (e : Entity)
    (hget : r.plan.val.store.get i = some e)
    (himp : Arith.isImpossible (edfNumbers r i).1 (edfNumbers r i).2 = true) :
    i ∈ assignedOf (dayPlan r) := sorry

/-- **E2 (P\*), stage 6, §7.5.**  Batching gathers in key order and does not
reach past an equal-`ci` candidate that ranks ahead of it.  The shipped bug did
exactly that, and the effect is invisible in the output: the batch looks
correct and the skipped item simply never appears.  Design §6.3 gives its
restatement and refutation to **P5**. -/
theorem plan_never_batches_past_an_equal_ci_candidate (r : PlanReq) (s : WfSeg)
    (ids : BatchIds) (i j : Id) (e f : Entity)
    (hs : s ∈ (dayPlan r).segments) (hk : s.val.kind = SegKind.batch ids)
    (hi : i ∈ ids.val) (hj : j ∉ ids.val)
    (hie : r.plan.val.store.get i = some e) (hjf : r.plan.val.store.get j = some f)
    (hci : effectiveCi r.plan.val i = effectiveCi r.plan.val j)
    (hdoc : e.val.live.doc = f.val.live.doc)
    (hrank : f.val.live.rank < e.val.live.rank) :
    j ∈ assignedOf (dayPlan r) := sorry

/-! ## L24 and L25 — the two relational laws

Plan §6.2.4: these relate **two runs** of a greedy fold — real inductions, not
`decide`.  `inventory` budgets tail-drop alone at plausibly a week and has a
working 882-line proptest at 256 cases that has empirically caught things.

**The plan's recommendation was: keep the proptest, state the law in Lean,
prove it last or never.  The owner's D5 supersedes it** — relational laws keep
being proved, L24 and L25 included, and a two-run theorem a change breaks is
re-proved in that step, never downgraded to a property test and never deleted.
They are stated here so that the choice is visible in the burn-down rather than
absent from it, and design §7 prices them at ≈ 3,000 proof lines together. -/

/-- **L24 (?), stage 6, §8.3 tail-drop — relational; proved under D5.**
"Removing minutes from the day (interrupt, overrun, downgrade) never changes
the set of assigned items except by removing a suffix in key order (Active item
excepted)."  Stated over the budget, which is the cleanest of the three ways
minutes leave a day.

**The owner's D29 restates this, and the restatement is step G2's, not P0's.**
As written it is FALSE against the fork: §8.2 choice 5b reserves the running
block before the budget is consulted, so shrinking the budget can drop items
ranking ahead of the Active item while it stays, and the result is not a
prefix.  D29's form erases the Active item from both sides —
`∃ n, (assignedOf (dayPlan r')).erase a = ((assignedOf (dayPlan r)).erase a).take n`
— and ships with `plan_tail_drop_as_stage_6_wrote_it_is_refuted` and its
witness **in the same commit**.  It is left as written here because a
restatement without its refutation is a weakening (AGENTS §3.1 item 3).

**W-15 re-derived what is blocking, with a builder in hand** (README gaps 348,
366, 452).  A concrete `PlanReq` can be written down now
(`PlannerWit.theRequest`), and two things came out of it.  *Choice 5b's witness
still needs P5*: `PlannerWit.the_budget_does_not_reach_the_assigned_set_until_the
_assign_fold_lands` proves the budget cannot reach `assignedOf` at all while the
assign fold is unwritten, so `plan(budget)` and `plan(budget − Δ)` are the same
list and the counterexample D29 names is unreachable.  *And the statement below
is false for a second reason nobody had recorded*: its hypotheses pin five views
of `PlanReq` and leave `run` free, while D24's seam put the day's past half
inside `run` —
`PlannerWit.plan_tail_drop_as_stage_6_wrote_it_is_refuted_by_the_run_it_does_not_pin`,
with `PlannerWit.erasing_the_active_item_does_not_repair_a_law_whose_run_is_free`
beside it, which shows D29's erasure does **not** repair that hole for any
choice of erased item.  So the restatement this goal is to become owes one more
hypothesis (`r'.run = r.run`, or one run throughout) before it can be proved.

The window is one pair now, not two numbers. -/
theorem plan_tail_drop (r r' : PlanReq)
    (hplan : r'.plan = r.plan) (hnow : r'.now = r.now)
    (hwin : r'.window = r.window)
    (hbm : r'.blockMin = r.blockMin) (hless : r'.budgetBlocks ≤ r.budgetBlocks) :
    ∃ n : Nat, assignedOf (dayPlan r') = (assignedOf (dayPlan r)).take n := sorry

/-- **L25 (?), stage 6, §8.3 stability — relational; proved under D5.**  "A
replan changes no segment with `end ≤ now`."  The first half of §8.3's bullet
("same input → identical `DayPlan`") is free and is not restated.

`nowSec` is an absolute second now, not minutes since midnight.  Design §6.3
records that this is **false as written** — the running block and the running
interruption *grow* rather than move (`SegFlags.isOpen`), so a segment settled
in run 1 is present but not equal in run 2 — and gives the restatement, the
refutation and `an_open_segment_only_extends` to step **G3**. -/
theorem plan_is_stable_across_a_replan (r r' : PlanReq) (nowSec : Nat) (s : WfSeg)
    (hplan : r'.plan = r.plan) (hwin : r'.window = r.window)
    (hbm : r'.blockMin = r.blockMin) (hbb : r'.budgetBlocks = r.budgetBlocks)
    (hs : s ∈ (dayPlan r).segments) (hend : s.val.stop ≤ nowSec) :
    s ∈ (dayPlan r').segments := sorry

end Goals
end Tm
