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
  `PlanCheck.dayPlan_ok_core_given_the_budget`, re-proved at the W-14 land step over the day step
  P1 produces and carrying the two hypotheses that day makes necessary (README
  gap 385).  The other four checks compare
  two candidates and have to be restricted to comparable ones (design §6.3),
  and that predicate — eligibleAt, design §15 — is step **P5**'s.  Until it
  exists the whole-battery lift is **not stateable**: `∀ el, planOk el r
  (dayPlan r) = true` is the *unrestricted* claim §6.3 refutes, and `∃ el, …` is
  satisfied by the predicate that answers `false`.  So it is here as prose and
  not as a `sorry`, and the step that writes eligibleAt states it.
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

**W-43 track K (2026-10-03): THIS SECTION HOLDS ONE GOAL AGAIN, and check 7 reads 1** —
`plan_places_no_block_over_a_break`, whose refutation stood on a break the log holds running INTO a block's start
and fell when the owner's D92 had the kernel net it as the host does (README gaps 4241 and 4362; the goal and why it
cannot be proved or refuted honestly today are below `open Planner`).  What follows was written when it held none.
**W-41 (2026-10-01): THIS SECTION HOLDS NO GOAL, and check 7 reads 0** — the owner's D80 refused by name the two
requests its last goal's statement was false at, and track K proved it as written over every request the decoder
accepts (the note where it stood, below; README "Stage 6 — W-41 track K").  The two paragraphs below are the W-39
repair's and W-39's records, as they stood.
**W-39 repair (2026-09-30): THIS SECTION HOLDS ONE GOAL AGAIN, and check 7 reads 1** —
`plan_places_no_demanding_block_after_wind_down`, whose refutation fell when the kernel's window stopped running
past the night (README gaps 3556 and 3713).  What follows was written when it held none.
**W-39 (2026-09-30): THIS SECTION HOLDS NO GOAL, and check 7 reads 0.**  Track K refuted the last
six as stage 6 wrote them and proved each law beside it under its own short name (README "Stage 6
— W-39 track K", gaps 3540-3556); the land step composed them with tracks A, T and H and they close
over A's changed definitions.  Every count and every "NO GOAL BELOW MAY BE DISCHARGED" below is the
record of how the section stood when that paragraph was written, not a count of what remains (README
gap 3553).

Plan §5: "D1–D14 decidable-checked on every plan the corpus produces;
`planner_invariants.rs` green at 256 cases through the FFI".  L26 is "decidable
over the produced `DayPlan`", so the output type is what has to exist and the
input mostly does not.

**The five provisional declarations that stood here are gone** (stage 6 step
P0, `Planner.lean`): `SegKind`, `Seg`, `DayPlan`, `PlanReq` and `dayPlan` are
real now, and so are `segItems`, `assignedOf` and `blockSeconds`.  `Seg` moved
from minutes-since-midnight to `Look.Slot`'s **absolute seconds** (README gap
256), which is why every statement below reads `s.val.start`/`s.val.stop`.
**No provisional declaration is left in this file**: `edfNumbers` was the last one and step
**P4** took it (`Planner.edfNumbers`), which the section below says in full.  *(This sentence
read "Only `edfNumbers` stays provisional; design §5.5 gives it to step P4" until the W-17
repair — a stale citation contradicted by this same file two hundred lines down, and check 3
cannot read doc comments.)*

**TWO GOALS BELOW ARE ONE LINE FROM LEAVING THIS FILE, AND BOTH WOULD BE
VACUOUS** (W-18, track G).  `plan_respects_the_energy_filter`'s hypothesis
`he : s.val.energy = some lvl` on a Block row is **refuted** by
`PlanCheck.no_block_row_of_the_day_carries_a_slot_energy_on_an_unassigned_day`, and
`plan_never_batches_past_an_equal_ci_candidate`'s `hk : s.val.kind = SegKind.batch
ids` by `PlanCheck.the_day_has_no_batch_row_on_an_unassigned_day` — both for **every** `PlanReq`, not
at one witness.  So each is `exact absurd …` away and the burn-down could read
**7** today.  It reads **9**, and the two are left here on purpose: a discharge
whose subject is empty is AGENTS §5.2's theorem that compiles and means nothing,
and check 7's number would stop being true.  This is the same call P1 made for
the wall goal (README gap 347), P2 for the wind-down goal (gap 430) and P3 for
the break goal (gap 551) — the difference is that the emptiness is now **proved**
rather than observed, so the refusal is evidenced and the two theorems are the
build-time walls **P5** must break.

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

**Step P3 has landed** (`Planner.lean`, §8.2 step 3 and choice 5b: the cut on
L3's own `Look.cutSlots`, the slot energies on L4's own `Look.energizeToday`, and
the **running block reserved** before the routines and before the cut).  It
discharges **one** goal, and it is the first of the thirteen to leave this file.

`plan_reserves_one_block_at_a_time` is **gone from this file**: it is **false as
it was written here** — the day's Block rows include the ones `Planner.pastRows`
replays from the log, and a Block the log holds can run longer than `block_min`
(shorten `[day] block_min` after a morning of hour-long blocks and the day the
planner produces has one) — and it left as
`PlannerWit.plan_reserves_one_block_at_a_time_as_stage_6_wrote_it_is_refuted`
with the restatement `Planner.plan_reserves_one_block_at_a_time` beside it
(AGENTS §3.1 item 3, D5).  The restatement is over the Block rows that start
**at or after `now`** — the fork's own `assigned_set(day, w.now)` restriction
(`planner_invariants.rs:470`) — and it is **not vacuous**: §8.2 choice 5b's
reservation is such a row, and `PlannerWit.the_reserved_day_assigns_the_running
_block` computes one.

`plan_respects_the_energy_filter` **is gone from this file as of W-30 (track
G)**, and unlike the three below it the reason is not `PlanCheck`'s finding 1.
The goal reads an item's `ci` with `Tm.effectiveCi`, out of the **plan store**;
§8.2 step 5's own filter reads it off `Look.Cand.ci`, the **capacity wire**; and
nothing in this tree made the two agree.  At
`PlannerWit.theBusyRequest` the plan does not hold `^c4` at all, so the store
answers §3.1's default `3` while the cursor placed the group at a slot of energy
`2` — the goal asks `3 ≤ 2`.  That is **E8's shape**, two readers of an item's
`ci` disagreeing about eligibility, which is exactly what this goal's own doc
comment said it ruled out; what ruled it out was nothing.  So the goal is **false
as it was written here** and it left the way the three below left:
`PlannerWit.plan_respects_the_energy_filter_as_stage_6_wrote_it_is_refuted` with
the restatement `PlanCheck.plan_respects_the_energy_filter` beside it (AGENTS
§3.1 item 3, D5).  The restatement carries two hypotheses and neither is a
restriction of the day: `hnopast` is finding 1, and `hpay` is
`PlanCheck.AssignedRowsPay`, which `PlanCheck.AssignedRowsPay_of_a_paying
_decoder` discharges from the fifth decoder clause.  It is **not vacuous**:
`PlannerWit.the_paying_request_assigns_and_the_battery_passes` is a request whose
cursor fills a slot, whose Block row carries a slot energy and names an item the
store holds, and whose decoder pays — the first such row in this kernel.

`plan_places_no_block_over_a_break` **is gone from this file as of W-18 (track
G)**, and the sentence that stood here — *"it stays, for the reason P1's and P2's
goals stayed: step 3 cuts the breaks but places no Break row"* — was true about
the **cut's** breaks and wrong about the day's.  Every Break row of the day is a
replayed one (`Planner.a_break_row_is_a_replayed_row`, still the theorem that
says so), and a log that records a `break` while a block is running puts a Break
row **inside** a Block row — neither of them the planner's doing, which is
`PlanCheck`'s finding 1 (README gap 385) for the third time after E1 and the wall
law.  So the goal is **false as it was written here** and it left the way those
two left: PlannerWit.plan_places_no_block_over_a_break_as_stage_6_wrote_it_is_refuted
(deleted at W-43 track K, its goal back below) computed on a day whose log breaks at 07:30 inside `m1`'s 07:05–08:05
block, with the restatement `PlanCheck.plan_places_no_block_over_a_break` beside
it (AGENTS §3.1 item 3, D5).  The restriction is E1's own — Block rows that start
**at or after `now`**, the fork's `assigned_set(day, w.now)` — and it is **not
vacuous**: `PlannerWit.the_break_law_applies_at_the_census_request` applies it to
choice 5b's reservation beside a Break row the morning's log holds.  **P5 must
re-prove it** when the assign fold puts Blocks of its own into that set, and P5
still owes the *cut's* breaks (`kept_breaks`, README gap 551), which is a
different sentence from this one.

`plan_places_no_block_over_a_wall` **is gone from this file as of W-17 (track
G)**, and the sentence that stood here — *"it stays, and staying is the point: the
only Block row the planner places before P5 is the Active reservation"* — is left
as the record of what was true when it was written.  What it missed is that the
goal quantified over **every** Block row of the day, the replayed ones included,
and a Block the log holds can sit under a wall the calendar acquired afterwards:
`PlanCheck`'s own finding 1 (README gap 385), the clause step P3 used for E1 and
nobody took twice.  So the goal is **false as it was written here**, and it left
the way E1 left —
`PlannerWit.plan_places_no_block_over_a_wall_as_stage_6_wrote_it_is_refuted`
computed on a request whose meeting moved onto an already-worked hour, with the
restatement `PlanCheck.plan_places_no_block_over_a_wall` beside it (AGENTS §3.1
item 3, D5).  The restriction is E1's own — Block rows that start **at or after
`now`**, the fork's `assigned_set(day, w.now)` — and it is **not vacuous**: choice
5b's reservation is such a row.  **P5 must re-prove it** when the assign fold puts
Blocks of its own into that set.  The tripwire for the set itself is
`Planner.the_day_assigns_after_now_the_running_block_and_what_step_five_chose` — which P3
restated from `…_until_the_assign_step_lands`, because choice 5b's reservation
made the empty-list form false — and which P5 must delete.

**Two goals were stated in SECONDS after the W-14 repair** (README gap
392): plan_does_not_overbook and `plan_reserves_one_block_at_a_time` (the
second is discharged above; the first left this file at W-31, refuted).  P0's
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
`PlanCheck.dayPlan_ok_core_given_the_budget`, the lift over the seven eligibility-free checks,
as a **theorem in a shipped module** rather than a goal — track G wrote it over
P0's empty day, and this run's merge is where P1's own body had to re-prove it
(README gap 385).  A goal below is still not dischargeable from it directly:
the six block-side checks it discharges are about the rows the log replays and
the one row choice 5b reserves, and nothing else.

**W-17 (track G) took two things out of that.**  `PlanCheck.dayPlan_ok_core_from_now_given_the_budget`
is the same conjunction over the same seven checkers with `dayPlan_ok_core_given_the_budget`'s
`hnopast` — *the log holds no Block for today* — **gone**: `PlanCheck.withoutPast`
names the restriction §8.3 is about rather than assuming it away, and the lift
then holds for every request, whatever the log holds.  Both lifts are kept; they
are incomparable and nothing is weakened (D5).  And
`PlannerWit.the_battery_census_over_a_produced_day` stopped the vacuity being a
matter of reading: it **computes**, over the day the planner produces at
`theStoredRequest`, that **five** of the eleven checkers have a subject and six
do not.  All eleven **refuse** a mutation of that day
(`the_battery_bites_over_a_produced_day`), which is AGENTS §5.8's other direction
and was three of eleven before that run.

**W-18 (track G) settled the ratio and split the question in two.**  The repo
carried three numbers for one question — five of eleven at `theStoredRequest`,
four of seven at `theRunningRequest`, and gap 650's four checkers — measured at
three different populations.  There is now **one** request and **one** ratio:
`PlannerWit.the_battery_census_at_the_census_request` computes **seven of the
eleven** with a subject at `PlannerWit.theCensusRequest`, the §4.3 Wednesday with
`m1` running, a store that holds the calendar's wall **and** the morning's two
tasks, and a log that holds a **break**.  The two it adds over W-17's five cost
no step at all: `wallsUnmoved` wanted a store holding the wall the day places,
and `noBlockOverABreak` wanted a log with a break in it — **gap 650 gave the
second to P5 and that was wrong**.  The remaining **four** are not a request
question and are no longer counted: `PlanCheck.no_block_row_of_the_day_carries_a
_slot_energy_on_an_unassigned_day`, `PlanCheck.no_block_row_of_the_day_reaches_the_wind_down_on_an_unassigned_day`,
`PlanCheck.the_day_has_no_batch_row_on_an_unassigned_day` and
PlanCheck.the_day_names_no_impossible_item (the last refuted at W-33, when P8's first half
wrote the field) prove, for **every** `PlanReq`, that
no witness can give `energyFilterOk`, `noDemandingAfterWindDown`,
`batchDoesNotReachPast` or `impossibleKept` a subject — P5's three and P8's one,
each now a build-time wall its step must delete.

**W-19 (track G) proved the nine is a CEILING, and refuted two of the thirteen
below.**  `PlanCheck.dayPlan_ok_from_now_except_the_two_comparisons_on_an_unassigned_day` records its
two missing conjuncts — `monotoneInRank` and `hotBeforeQueue` — as *missing*.
They are **false**: at `PlannerWit.theQueuedRequest` (the census request with
`m1`'s two log lines removed and `m2` running) both answer `false` at the
permissive eligibility, on the whole day and on `PlanCheck.withoutPast`'s day
alike, with **no mutation at all** — and the other nine answer `true` at that
same request (`PlannerWit.the_other_nine_hold_where_the_two_fail`).  So the
`∀ el` form of design §6.1's lift is refuted both ways round
(`PlannerWit.dayPlan_ok_at_every_eligibility_is_refuted`,
`PlannerWit.dayPlan_ok_from_now_at_every_eligibility_is_refuted`), and with it
`plan_is_monotone_in_rank` and `plan_puts_hot_before_the_queue` below.  **The
burn-down did not move**: both restatements need Planner.eligibleAt, which is
P5's, so both goals stay here beside `plan_tail_drop`, refuted and standing.
README gaps 850 and 851.

**W-21 (track G) made the ratio a function and the ceiling a theorem — and that
is why four of the nine below are NOT discharged.**  `PlanCheck.subjectOf` is
the subject census keyed on each check's own `PlanCheck.CheckName` and filtered
over `PlanCheck.checksOf`'s own list, so the count is the compiler's;
`PlannerWit.the_census_ratio` computes **seven** at
`PlannerWit.theCensusRequest`, which is exactly what W-18 settled by hand.
`PlanCheck.the_census_ceiling_is_seven_on_an_unassigned_day` then proves seven is a **ceiling over
every request**, because the four W-18 named have no subject at any of them
(`PlanCheck.energyFilter_has_no_subject_on_an_unassigned_day` and its three siblings).

**That gives the burn-down a computed rule where it had a judgement.**
`plan_respects_the_energy_filter` and
`plan_never_batches_past_an_equal_ci_candidate` are PROVABLE today with no extra
hypothesis at all — their `s.val.energy = some lvl` and
`s.val.kind = SegKind.batch ids` are satisfied by no day `Planner.dayPlan`
produces (`PlanCheck.no_block_row_of_the_day_carries_a_slot_energy_on_an_unassigned_day`,
`PlanCheck.the_day_has_no_batch_row_on_an_unassigned_day`) — and
`plan_places_no_demanding_block_after_wind_down` is the same once `hnowcal` is
added.  **None is discharged**, because each would be AGENTS §5.2's theorem that
compiles and means nothing: `PlanCheck.energyFilter_has_no_subject_on_an_unassigned_day`,
`PlanCheck.batch_has_no_subject_on_an_unassigned_day` and `PlanCheck.windDown_has_no_subject_on_an_unassigned_day` now
PROVE the quantifier empty at **every** `PlanReq`, where W-18 argued it.  They
stay until P5 and P5/P7 give them a subject.

**The fourth is a finding rather than an application of that rule.**
`PlanCheck.impossibleKept`'s subject is `Planner.Diagnostics.impossible` and
PlanCheck.impossible_has_no_subject proved it empty at every request (refuted at W-33: the
field is written now) — but
the impossibility goal that stood below was **not** stated over that list.
It is stated over `Planner.edfNumbers`, whose hypothesis a real candidate can
satisfy, with a conclusion about `Planner.assignedOf`.  So the checker being
vacuous does not make the goal provable and the two are not the same statement;
the step that bridges them — filling `Diagnostics.impossible` from §7.3's grants
— is **P8**'s.  README gap 1065.

**And §6.1's lift is ELEVEN of eleven as a THEOREM about a class**, where W-20
left eleven standing only at one request and only by a `decide` on the last
conjunct (`PlannerWit.the_quiet_battery_passes_at_the_quiet_request`).
`PlanCheck.dayPlan_ok_on_a_quiet_unassigned_day` is the ∀-statement: every quiet
request, every eligibility satisfying `PlanCheck.WorkAnchored` — an `el` that
admits a candidate only at a row §8.2 step 5 could assign into.  That is a
third repair for README gap 960, and unlike
the two gap 960 named it touches neither the checker nor the planner, so
`plan_puts_hot_before_the_queue` below is **not** restated and the burn-down
does not move.  What P5 owes for it is one line: that Planner.eligibleAt is
`PlanCheck.WorkAnchored`.  `PlanCheck.planOk_antitone` is why a hypothesis on
`el` is the right shape — `planOk` is antitone in the eligibility, so
`PlannerWit.permissive` is the top and W-19's ceiling argument is now a theorem
rather than a reading.  **The burn-down stayed 9 and no goal was added.**

**W-22 (track G) took §6.1's lift OFF the class axis, and the burn-down still did not
move.**  `PlanCheck.dayPlan_ok_from_now_on_an_unassigned_day` is design §6.1's `PlanCheck.planOk` at eleven of
eleven over `PlanCheck.withoutPast`'s day — the rows §8.3's laws are about — for **every**
request and every `PlanCheck.SlotAnchored` eligibility, where W-20 and W-21 reached eleven
only on the *quiet* class.  `PlannerWit.the_census_requests_are_not_quiet` is why that
matters: the quiet class has **one** inhabitant in the whole witness set, and the new lift
fires at three requests including the one where the same lift at `PlannerWit.permissive` is
refuted.  `PlanCheck.the_census_ceiling_from_now_is_four_on_an_unassigned_day` is what it is worth — at most four
of the eleven can have a subject on that day at any request — and
`PlannerWit.the_eleven_from_now_is_four_checkers_biting` reaches it, against the quiet class's
**one**.

**Which number to quote is settled in one place and nowhere else**: `PlanCheck.lean`'s W-22
section header carries the table of the three questions a *"N of the eleven"* can answer, and
says which is the honest headline — the SUBJECT count, whose one figure is **seven**, the
whole-day ceiling `PlanCheck.the_census_ceiling_is_seven_on_an_unassigned_day` proves and
`PlannerWit.the_census_ratio` reaches.  Every sentence below and every sentence in
`PlanCheck.lean`, `PlannerWit.lean`, `Check.lean` and `Negative.lean` was re-read against the
computed census at W-22 and agrees with it; the one that named two days and gave one number
now names the day.

**And none of the nine below is dischargeable by any of it.**  §8.2 step 7 landed between W-21
and W-22 and `PlannerWit.step_seven_gave_no_checker_a_subject` computes that it gave no
checker a subject — the eleven-entry census at `PlannerWit.theOptionalRequest`, the only
request whose day carries Optional rows, is **equal to** `PlannerWit.theRequest`'s.  So W-21's
rule stands unchanged: `plan_respects_the_energy_filter`,
`plan_never_batches_past_an_equal_ci_candidate` and
`plan_places_no_demanding_block_after_wind_down` are provable and would each be AGENTS
§5.2's statement that compiles and means nothing; the impossibility goal is P8's
(README gap 1065) and LEFT this file at W-32, refuted; the two comparisons need their P5
restatement and plan_does_not_overbook got its own at W-31 (refuted, then
`PlanCheck.plan_does_not_overbook_where_nothing_runs`); and `plan_tail_drop` and `plan_is_stable_across_a_replan` are G2 and G3.

**The one sentence a later step must not inherit backwards.**  It is tempting to read
`PlanCheck.dayPlan_ok_core_given_the_budget`'s `hblk` — *every Block row of the day is the reservation* — as
evidence that §8.2 step 5's fold is now under the battery.  It is evidence of the **opposite**:
`Planner.dayRows`' own doc comment records that step 5's Block and Batch rows are **not in the
day**, and `hblk` holds *because* they are absent.  The fold induction design §6.2 prices at
≈ 4,500 proof lines has no subject in this tree and no line of it is claimed by any run so far.

**W-23 (track G) closed the ELIGIBILITY axis of that lift on the WHOLE day, and the burn-down
still did not move.**  `PlanCheck.dayPlan_ok_is_the_core_seven_on_an_unassigned_day` says §6.1's eleven over the
whole day **is** §6.1's seven — a `Bool` equality, at every request, at every
`PlanCheck.FromNowAnchored` eligibility, with nothing assumed about the log.  So no goal below
is waiting on an eligibility any more: the four checks that take one are vacuous on every day
this kernel produces, and what stands between the lift and the whole day is the **replayed
past**, which is not one of the eleven's subjects and not the fold's.  The two bounds are both
witnessed: `PlannerWit.dayPlan_ok_at_every_slot_anchored_eligibility_on_the_whole_day_is_refuted`
is the eligibility one (W-22's `PlanCheck.SlotAnchored` is two thirds of what P5 owes, not all
of it), and `PlannerWit.the_core_seven_is_false_on_three_whole_days` is the other, on three
days this module already builds.

**And §8.2 step 8 landed between W-22 and W-23 and gave no checker a subject either** — for a
reason that is structural rather than measured, which is the one improvement W-23 makes on the
form of W-21's and W-22's answers.  `PlanCheck.lean` imports `TmKernel.Planner` and **not**
`TmKernel.Emit`; `Emit.lean` is that module's sibling, downstream of the battery.  So no
checker of the eleven can read a cell, no row text can be any checker's subject, and P8 could
not have moved the census whatever it emitted.  What P8 was owed by name is a different
sentence and it is **not** paid: the impossibility goal (refuted and gone at W-32) still needed
`Planner.Diagnostics.impossible` filled from §7.3's grants (README gap 1065), and
`Planner.dayDiagnostics` still leaves that field at `Planner.Diagnostics.empty`'s value.

**W-24 (track G) closed the LOG axis the same way, and the burn-down still did not move.**
`PlanCheck.PastPays` is what the replayed past owes §6.1's seven, in **four** named clauses —
no replayed Block longer than one block, none over a span the walls blocked, none over a
break the log records, and the Blocks already worked inside the budget — and
`PlanCheck.dayPlan_ok_core_of_a_paying_past_on_an_unassigned_day` is the whole-day lift with `hnopast` **gone**.
Three of the seven owe the log nothing at all, which is why `PastPays` has four fields and not
six.  `PlanCheck.PastPays_of_no_past_block_on_an_unassigned_day` makes `PlanCheck.dayPlan_ok_core_given_the_budget` a corollary and
`PlannerWit.the_paying_past_holds_where_hnopast_does_not` is the request where the new lift
fires and the old one cannot — the §4.3 Wednesday, whose morning worked two blocks, so the
whole-day lift now reaches a real day for the first time
(`PlannerWit.the_eleven_hold_on_the_whole_day_of_a_worked_morning`, eleven of eleven, by the
lift and not by a `decide`).  The bound in the other direction is four days, one per clause
(`PlannerWit.every_refuted_day_refutes_its_own_clause`), the fourth built here because nothing
in the witness set reached the `budget` clause.

**One of the nine below was REFUTED by that fourth day, and it stays.**
plan_does_not_overbook is **false as written** —
`PlannerWit.plan_does_not_overbook_as_stage_6_wrote_it_is_refuted` at
`PlannerWit.theOverBudgetRequest`, a day with **nothing running** whose log worked two blocks
against a budget of one — which is *not* the reason design §6.3 row 1 records, and that row's
own restatement is refuted with it
(`PlannerWit.the_designs_restatement_of_the_overbooking_law_is_refuted_too`).  It stays for
W-19's reason at the two comparisons: the restriction that survives is
`PlanCheck.withoutPast`'s day, where `PlanCheck.overbook_has_no_subject_from_now_on_an_unassigned_day` proves the
law **vacuous**, so a discharge would be AGENTS §5.2's theorem that compiles and means
nothing.  README gaps 1390-1393.

**W-25 (track G) closed the WALL axis, the third and last `∀` over the request, and the
burn-down still did not move.**  `PlanCheck.PlainStore` names what the lift had been asking —
*every* interval-shaped entity of the plan carries no `buffer:` and lies inside the day being
planned — and `PlanCheck.WallsArePlain` is what `wallsUnmoved` actually needs: the same five
clauses at the entities a **Wall row of the produced day** names.
`PlanCheck.dayPlan_ok_core_of_plain_walls_on_an_unassigned_day` and
`PlanCheck.dayPlan_ok_on_the_whole_day_of_plain_walls_on_an_unassigned_day` are §6.1's seven and eleven from the
restriction; the blanket forms are kept and are now corollaries
(`PlanCheck.WallsArePlain_of_a_plain_store`).  **The blanket was false of an ordinary week
file**: `PlannerWit.theOffDayRequest` is the census Wednesday with one Thursday line added to
its calendar document, `PlannerWit.the_blanket_plainness_is_false_at_the_off_day_request`
refutes it there, and `PlannerWit.the_eleven_hold_where_the_blanket_fails` is §6.1's eleven on
that whole day.  All three bounds of the lift are now named and all three are witnessed in
both directions; what is left in its hypotheses is three decidable `Bool`s the decoder owes
(README gap 346) and one `Nat` comparison.

**TWO OF THE NINE BELOW WERE REFUTED THAT WEEK AND BOTH STAY.**  W-24 refuted
plan_does_not_overbook; W-25 refuted `plan_is_stable_across_a_replan`, and again **not** for
the reason design §6.3 records.
`PlannerWit.plan_is_stable_across_a_replan_as_stage_6_wrote_it_is_refuted_by_the_run_it_does
_not_pin` is `plan_tail_drop`'s hole at a second goal: the hypotheses pin `plan`, `window`,
`blockMin` and the budget and leave **`run`** free, so `PlannerWit.theRequest` and
`PlannerWit.theQuietRequest` satisfy every one of them and disagree about the day's whole past
half.  Design §6.3 row 3's own restatement — *over segments that are `end ≤ now` and **not
`open`*** — is refuted by the same pair
(`PlannerWit.the_designs_restatement_of_the_stability_law_is_refuted_too`), because the witness
row carries `isOpen = false`.  **And it could not have helped**:
`Planner.SegFlags.isOpen` is set at exactly **one** construction site in this kernel,
`Planner.interruptRows`, while §8.2 choice 5b's reservation — the row that *grows* — leaves it
at its default (`PlannerWit.the_reservation_row_is_not_marked_open`, every request;
`PlannerWit.no_row_of_the_days_this_tree_builds_is_open`, four days including two with a block
running).  So the design's restatement, ported verbatim, would exclude the interruption and
keep the row it was written to exclude.  README gaps 1500-1503.


**WHICH OF THE NINE ARE REACHABLE, AND WHAT EACH WAITS ON.**  Eight runs have discharged none
and said so honestly.  The list was written at W-24, re-verified at W-25 and W-26, and
**re-verified again at W-28 against what W-27 changed** — item by item, against the tree rather
than against the previous run's prose; **no entry moved**, and every blocker below was
re-checked by the command the W-28 README block records.  **None of the nine is reachable
today**, and the reasons are two steps and one edit *(the list below is W-28's, kept as
written; **W-29 re-asked it against step P9 and three entries moved** — the W-29 block after
item 9 is where each entry's answer now lives)*:

1. plan_does_not_overbook — **P5**.  Refuted above; reachable when step 5's fold puts Block
   rows at or after `now` into the day, which is what gives the surviving restriction a
   subject.
2. `plan_respects_the_energy_filter` — **P5**.  Provable today and **vacuous**
   (`PlanCheck.energyFilter_has_no_subject_on_an_unassigned_day`, every request): it wants a Block row carrying a
   slot energy, which only an assignment into an energised slot produces.
3. `plan_places_no_demanding_block_after_wind_down` — **P5**.  Same, with `hnowcal`
   (`PlanCheck.windDown_has_no_subject_on_an_unassigned_day`): it wants a Block row at or after the wind-down, and
   step 7's three kinds are not Blocks.
4. `plan_is_monotone_in_rank` — **P5**.  Refuted at W-19; the restatement needs
   Planner.eligibleAt, which **is declared nowhere in this tree** — `Planner.Ranked.gatherable`
   is its slot half and the item half does not exist.
5. `plan_puts_hot_before_the_queue` — **P5**.  Same refutation, same missing predicate; P5 also
   owes the one line that Planner.eligibleAt is `PlanCheck.FromNowAnchored`.
6. plan_never_drops_an_impossible_item — **P8**.  `Planner.dayDiagnostics` still leaves
   `Planner.Diagnostics.impossible` at `Planner.Diagnostics.empty`'s value, so §7.3's grants
   have never been written into it (README gap 1065).  *(W-28's sentence, false since W-33:
   `Planner.PlanReq.dayImpossible` writes the field, and the goal itself left this file at
   W-32 — W-33 repair, gap 2565.)*  It is the only one of the nine that is
   **not** P5's.
7. `plan_never_batches_past_an_equal_ci_candidate` — **P5**.  Provable today and vacuous
   (`PlanCheck.batch_has_no_subject_on_an_unassigned_day`): it wants a Batch row, which is step 5's batch split.
8. `plan_tail_drop` — **G2**, which waits on G1, which waits on P5.  Re-verified at W-25:
   it is **refuted** (`PlannerWit.plan_tail_drop_as_stage_6_wrote_it_is_refuted_by_the_run_it
   _does_not_pin`, W-15) and it owes a hypothesis before D29's restatement can be written —
   `r'.run = r.run`, or the law over one run.  Its *other* half, §8.2 choice 5b's prefix
   failure, is unreachable until P5:
   the busy day's budget witness said the budget cannot reach `assignedOf` at all — a claim
   REFUTED at W-38 (`PlannerWit.the_budget_does_not_move_the_assigned_set_at_the_busy_request_is_refuted`; the budget does move it,
   `PlannerWit.the_budget_moves_the_assigned_set_at_the_busy_request`).  **G2 is NOT in the tree** — no restatement,
   no `Negative.lean` cheat — and a run that only pins the run would discharge it **vacuously**
   for the same reason, which is W-19's call and AGENTS §5.2's.
9. `plan_is_stable_across_a_replan` — **G3**, the same chain, and **refuted at W-25** for the
   same unpinned field, with design §6.3 row 3's own restatement refuted beside it (see the
   W-25 paragraph above).  **G3 is NOT in the tree either**: of design §15's three G3
   declarations, the refutation is now written and the restatement and
   an_open_segment_only_extends are not — and that second one has **no subject** (the names
   are un-backticked because check 8 is right to ask: neither is declared anywhere), because
   the reservation is not marked `open` and no witness request has an interruption.  G3 owes
   three repairs and only the first has a counterexample: pin the run; drop or restate `hwin`,
   which is false of every genuine replan-later pair
   (the hour-later pair that moved the window, REFUTED at W-39 track A as
   `PlannerWit.an_hour_later_changes_one_field_and_moves_the_window_is_refuted` once the planner read
   the day's logged arrival; on a day whose arrival is logged `hwin` HOLDS of a genuine replan-later
   pair, `PlannerWit.an_hour_later_changes_one_field_and_keeps_the_window_the_log_anchors`, and
   `PlannerWit.an_hour_later_moves_the_window_of_a_day_with_no_arrival` is the day that still moves —
   README gaps 3581 and, for the law that was proved, 3550); and tie the free
   second-argument bound of the law below to `r.now`, because free it admits *every* row and
   the law then says the two days are equal up to inclusion.  What the law is actually about is **not** refuted:
   `PlannerWit.an_hour_later_keeps_every_row_that_had_settled` is the one genuine replan pair
   this tree can build, over the three rows that had settled, and it holds.

**AND THE R3 AXIS, WHICH IS THE ONE THE LIST DID NOT CARRY** (W-26, asked for by R3's own
brief; **re-verified at W-28**).  **Not one of the nine is downstream of R3.**  Step R3 deletes
the fork's planner in Rust with its last caller; it adds no row to `Planner.dayRows`, fills no
field of `Planner.Diagnostics`, and declares no predicate.  So every entry above is *reachable
before R3* — the blocker is the same one edit and the same two steps whether R3 has happened or
not — and **none of them is made reachable by R3**.  A run planning R3 should take nothing from
this list except that it is not waiting on it.

**D48 did not move that column either, and W-28 checked rather than assumed it.**  The wire R3
used to own is R2's now, and W-27 landed its REQUEST half; R3 is purely the deletion.  What R3
*is* owed is not a goal above but a **statement**: §8.3's segment-free hole (README gap 1529),
which `PlanCheck.holeFree` states and `PlanCheck.holeFreeFrom` states with its leading blind
spot closed, and which is deliberately not in `PlanCheck.checksOf` because the emission rule
that would make it true lives in the Rust planner R3 deletes (gap 1621).

**What R2 changed, checked rather than assumed, at ALL THREE of its landed halves — and the
third landed DURING W-28, so this paragraph is the LAND STEP's, not a track's.**  R2's first
half put the kernel's *cells* on the wire (`EmitWire.rowsOfReq`, `tm/tests/kernel_row_cells.rs`)
and its item-line generators behind one reader.  W-27's second half (D48) put the planner's
**inputs** on it: `PlanWire.readPlannerSection` decodes `state`, `routines` and `overrides`,
`PlanWire.readBatchMaxMin` decodes §16's fifth `[priority]` key, and `PlanWire.callExport` is
now the package's one export.  **W-28's third half — D48's RESPONSE half — reaches
`Planner.dayPlan`, and R2 IS COMPLETE.**  The sentence that stood here until this merge said
neither half reached it, and cited runPlanner_with_a_readable_section_answers_as_runRows —
spelled without backticks because the response half **deleted** it, the statement being false of
the definition now.  Re-swept at the land step: `Planner.dayPlan` has **two** code callers,
`Emit.rowsOf` (Emit.lean:388) and `PlanWire.runPlanner` (PlanWire.lean:1181), the second across
the FFI; no wire function calls `Emit.rowsOf`; and of `PlanWire`'s fourteen mentions of
`dayPlan` **two are code** and the rest prose.

**And none of that moves an entry above, which is the point of saying it here.**  What R2's
third half bought is *observation*, not emission: `tm/tests/planner_invariants.rs` now compares
the kernel's day to the fork's, so the `Planner.dayRows` edit below stops being unobserved the
moment it is made.  The edit itself is **not made**, and the sentence below about
`Planner.dayRows` is unchanged at W-28: its body is still
`sortRows ((stepOneSegs ++ dayRoutineSegs ++ reservationSegs ++ optionalRows ++ restRows).map
segOf)`, with no row of step 5's in it.  The six entries that wait on that edit wait on it
still; what has changed is only that making it is now instrumented rather than blind.

**D48 HAS NO REMAINING HALF, and what stands between here and R3 is the DELETION and nothing
else.**  The RESPONSE half (README gap **1667**, CLOSED at W-28) builds a `Planner.PlanReq` from
the decoded values and emits `dayPlan`'s seven keys, and the argument for landing it before the
`Planner.dayRows` edit — this campaign's own evidence, D19 and the stage-5 switch that took four
runs — has been discharged rather than restated: the edit will be instrumented when it is made.
What R3 still owes is `tm-core/src/planner.rs` and its last caller, gap 94's two reserves, and
gap 116 closed or deliberately recorded; none of those is an entry above either.

**A tenth thing the lift waits on, and it is not a goal — and W-28 moved it.**  W-26 named
§6.1's fourth and last axis: `PlanCheck.DecoderPays`, the request decoder's four clauses, three
decidable `Bool`s and one `Nat` comparison (README gap 346), and measured **one of the four**
with a payer (`PlannerWit.mkPlanReq?_ok_wallsAgree`).  **There is no fifth axis**:
`PlanCheck.dayPlan_ok_on_the_whole_day_of_a_paying_decoder_on_an_unassigned_day` has exactly four hypotheses, one per
axis, and `PlannerWit.the_eleven_hold_with_every_axis_named` fires it at `theCensusRequest`.

W-27's wire pays a **second** clause.  `PlanWire.readActive` reads `state.active` through
`Planner.mkActive?` — the constructor `Planner.PlanReq.activeAgrees` is defined against — so
`PlannerWit.a_request_whose_state_the_wire_read_pays_the_active_clause` discharges the clause
`PlannerWit.the_builder_accepts_a_running_block_it_never_checked` proves the *builder* never
can.  The decoder census is **two of four**.  Of the other two: `day` is unpaid because nothing
calls `Look.mkDayCfg?` (README gap 1623), and `nowCal` is **one second short rather than
unchecked** — `PlannerWit.an_at_the_wire_accepted_is_inside_the_calendar` gives
`now.sec < LogStamp.yearEnd` from the wire's own constructor, the clause wants
`now.sec + 1 < LogStamp.yearEnd`, and
`PlannerWit.the_instant_bound_is_one_second_wider_than_the_now_clause` exhibits the single
instant between them.  The `active` payer's hypothesis **still has no caller, and the condition
this sentence used to name as the missing one has landed** (the W-28 repair step, README gap
1871's own class).  D48's
RESPONSE half is built — `PlanWire.planReqOf` assembles a `PlanReq` from the wire's values in
the same tree as this file — and the payer is *still* uncalled, because `planReqOf` hands the
eight fields over without going through `PlannerWit.mkPlanReq?`, which is the constructor the
payer is stated against.  So the axis and that half are **not** one obligation; the remaining
one is a caller for the payer, and it is README gap 1870.

**Six of the nine wait on ONE edit, and it is not a proof.**  `Planner.PlanReq.assignFold`,
`Planner.PlanReq.finalAssign`, `Planner.PlanReq.keptBreaks` and `Planner.PlanReq.occupiedNow`
are all built and proved; `Planner.dayRows` is
`sortRows ((stepOneSegs ++ dayRoutineSegs ++ reservationSegs ++ optionalRows ++ restRows).map
segOf)` and holds **no row of step 5's**.  That is D19's switch-shaped change, it is what
makes `PlanCheck`'s four emptiness theorems false and takes `PlanCheck.dayPlan_ok_core_given_the_budget`'s
`hblk` with them, and until it is made every one of the six is a statement about an empty
quantifier.  **The fold induction design §6.2 prices at ≈ 4,500 lines still has no subject in
this tree and no line of it is claimed by any run so far.**

**And "before R1" is behind the tree.**  R1 — design §14.4's one-renderer step, which kills
the *defect* G1 — **landed at `6b05f50`**, with `tm/tests/one_renderer.rs` beside it.  The two
G1s of this design are different things (design §3.4's finding about "F3", at a second name):
the *step* G1 is track G's lift and has not landed, and nothing below waits on the Rust
retirement.

**W-29 (track G) ASKED THE LIST A DIFFERENT QUESTION, AND THREE ENTRIES MOVED.**  Every list
above asks *"is this reachable **today**"* and answers no.  D50 names the edit that changes the
answer — step **P9**, which composes §8.2 step 5's Block and Batch rows into `Planner.dayRows`
— so the question this run put to all nine is *"what does P9 do to this entry"*, and the answer
is **not** the same for all nine.  Three kinds, and the list below says which each is.

**First, the two facts P9 lands on, both established this run and both in `PlanCheck.lean`.**

* **Step 6 keeps §8.2 step 5's filter, and nobody had proved it.**  A composed row is read off
  `Planner.PlanReq.finalAssign` — step **6**'s answer, as `Planner.PlanReq.restRows` already is
  — and `Planner.PlanReq.assignFold_ok` is about step **5**'s.  `deferWalk` carried `PlacedOk`,
  two lengths and `used`, and **not** `AssignOk`, so the energy filter, the `loc:` filter and
  the wind-down rule stopped at step 5's answer and the rows would have acquired a subject with
  no invariant to reach for.  `PlanCheck.finalAssign_ok` is that invariant, landed **before**
  the rows: step 6 only ever frees a slot (`Planner.PlanReq.displaceInto`) and re-places through
  `Planner.PlanReq.assignStep`, §8.2 step 5's own body, so the three clauses survive.  A repair
  and not a finding — but AGENTS §5.2's difference between *holding* and *being proved to hold*
  is the whole of this campaign.
* **And a FIFTH thing the request decoder owes, which is a finding.**  Every clause
  `AssignOk` carries is stated over `Planner.Group.ci`, which `Planner.groupOf` reads off
  `Look.Cand.ci` — the **wire's** reading of an item's `ci`.  Every checker of the battery that
  asks about an item's `ci` reads `Tm.effectiveCi r.plan.val i` — the **plan's** §3.2
  inheritance walk — and `Tm.effectiveCi` of an id the store does not hold answers `3` rather
  than refusing.  Nothing in this tree says the two agree and `PlanCheck.DecoderPays` has no
  clause for it.  **That is E8's shape**, which is the defect
  `plan_respects_the_energy_filter`'s own doc comment says it rules out, sitting in the seam
  between the wire and the plan.  `PlanCheck.candsAgree` states it as a property over the
  candidate list — an enumeration a candidate must **join to be exempt**, because
  `PlanCheck.candPlanView` answers `none` for an id the plan does not hold and the clause then
  fails by name — and `PlannerWit.the_busy_request_does_not_pay_the_fifth_decoder_clause` is a
  request already in this tree where it is `false`: `theBusyRequest`'s four candidates are not
  items of its plan at all, the wire says `ci = 3, 3, 5, 2` and the plan says `3` for every one
  of them, and the cursor puts the one the wire calls `ci 2` into two slots at energy **2**.
  Nine runs of `∀`-lifts never met it because **every request those lifts fire at sends no
  candidate** (`PlannerWit.the_lifts_own_request_pays_the_fifth_clause_for_nothing`), and
  `PlanCheck.candsAgree_of_no_cands` passes those for nothing.  README gap **1984**.

**The nine, against P9.**

1. plan_does_not_overbook — **P9 gave it a SUBJECT and not a proof.**  Refuted at W-24; the
   surviving restriction is `PlanCheck.withoutPast`'s day, where
   `PlanCheck.overbook_has_no_subject_from_now_on_an_unassigned_day` proves it vacuous — and
   since P9 landed (`2374820`) that theorem carries `hnoassign : r.assignedRows = []`, so the
   vacuity is exactly the restriction P9's rows end.  The proof is then two facts and **neither is the fold's filter**:
   `Planner.the_deferred_pass_stays_inside_the_budget` bounds the number of **blocks**, and
   `Look.SlotShape`
   bounds one slot's **seconds** at `60 * blockMin` (a `.block` slot is exactly that and a
   `.short` slot is strictly less).  `AssignOk` deliberately carries neither — its own doc
   comment gives `g.live` and the atomic run to "the step that emits rows".  So: reachable at
   **P9 + a seconds-from-blocks lemma**, and design §6.3's restatement over
   `remainingBudget` rather than `DayPlan.budgetBlocks` still has to be written (the two
   disagree on a day with blocks already done — `Planner.dayPlan_budgetBlocks`).
2. `plan_respects_the_energy_filter` — **P9 makes it PROVABLE, and the proof is in the tree as
   of this run.**  `PlanCheck.an_assigned_member_is_under_its_slots_energy` is its content at
   the assignment: `PlanCheck.finalAssign_ok` for the filter,
   `PlanCheck.a_member_of_an_assigned_group_carries_its_ci` for the group's `ci` bounding every
   member, and `PlanCheck.candsAgree` for the wire-to-plan step.  What P9 owes beside the
   composition is the row-to-member bridge its own emitter's equation gives, **and a decoder
   that pays the fifth clause** — without it the goal is not merely unproved, it is **false**
   at `theBusyRequest`.
3. `plan_places_no_demanding_block_after_wind_down` — **the same, at the same three facts**:
   `PlanCheck.an_assigned_member_after_the_wind_down_is_not_demanding`.  One more bridge than
   entry 2: the goal quantifies over a **WindDown row** and the lemma over
   `Planner.PlanReq.windDownSec`, which `Planner.the_wind_down_row_runs_to_bed` ties together.
4. `plan_is_monotone_in_rank` — **P9 changes NOTHING.**  Refuted at W-19 and the restatement
   needs Planner.eligibleAt, which is declared nowhere.  **And the refutation survives P9**,
   which is not obvious and was checked rather than assumed: `PlannerWit.theQueuedRequest`
   sends **no candidate**, so its cursor fills no slot and a composition whose rows are a
   `filterMap` over `slotOf` adds no row to that day.
5. `plan_puts_hot_before_the_queue` — **the same, for the same reason and at the same request.**
6. plan_never_drops_an_impossible_item — **P9 changes nothing; it is P8's.**
   `Planner.dayDiagnostics` still leaves `Planner.Diagnostics.impossible` at
   `Planner.Diagnostics.empty`'s value (README gap 1065).  *(W-29's sentence, false since
   W-33, which wrote the field — W-33 repair, gap 2565.)*  P9 populates `assignedOf`, which is
   this goal's *conclusion*, and leaves its *hypothesis* — `Arith.isImpossible` over
   `Planner.edfNumbers` — with nothing acting on it.
7. `plan_never_batches_past_an_equal_ci_candidate` — **P9 gives it a SUBJECT and not a proof**,
   and the gap is wider than "the fold has not landed".  Its antecedent wants a **Batch** row,
   which P9's emitter produces when a group has more than one member.  The half it rests on is
   proved — `Planner.gatherBatch_fst_is_a_prefix_of_its_ci`, gathering cannot reach past an
   equal-`ci` candidate it left behind — but the **conclusion** is that the skipped candidate is
   in `assignedOf`, and a candidate that becomes a group of its own is assigned only if the
   cursor finds it a slot inside the budget.  So the goal owes a restatement at P5/P9 and not
   only a subject.
8. `plan_tail_drop` — **P9 WAS what this entry had been waiting on, and it is the only one of
   the nine that P9 unblocks outright.**  A `∀`-theorem over **every** request said the budget
   cannot reach `assignedOf` at all; P9 (`2374820`) made it **false** and deleted it, and what
   stood in its place was a witness form — at `theBusyRequest`, budgets 0 through 5 all give
   four assigned rows, README gap **1904** — REFUTED at W-38 (its zero never reached the
   planner: `PlannerWit.the_budget_does_not_move_the_assigned_set_at_the_busy_request_is_refuted`), and the busy day's budget
   DOES move the assigned set (`PlannerWit.the_budget_moves_the_assigned_set_at_the_busy_request`).  `Planner.remainingBudget` is what `Planner.PlanReq.assignFold` folds
   against.  So §8.2 choice 5b's prefix failure becomes constructible and D29's restatement
   becomes writable.  It still owes the hypothesis W-15 found (`r'.run = r.run`, or the law
   over one run), which is not P9's.
9. `plan_is_stable_across_a_replan` — **P9 changes nothing.**  Refuted at W-25 on the same
   unpinned `run`, and its three owed repairs — pin the run, drop or restate `hwin`, tie the
   free second-argument bound to `r.now` — are none of them about an assigned block.

**TWO ∀-THEOREMS WERE BUILD-TIME TRIPWIRES P9 HAD TO DELETE OR REFUTE**, both stated over
every request rather than at a witness, so the composition could not land green beside them.
**P9 landed in the same run (`2374820`) and deleted both, each with a computed refutation** —
the budget theorem of entry 8, and the `Planner`-side theorem that the day assigns nothing
after `now` but the running block (which P3 already restated once for the same reason), now
`Planner.the_day_assigns_after_now_the_running_block_and_what_step_five_chose`.  The four
emptiness theorems were the other three walls and P9 did **not** delete them: it restated each
on a named subdomain, so they are
`PlanCheck.no_block_row_of_the_day_carries_a_slot_energy_on_an_unassigned_day`,
`PlanCheck.no_block_row_of_the_day_reaches_the_wind_down_on_an_unassigned_day`,
`PlanCheck.the_day_has_no_batch_row_on_an_unassigned_day` and
`PlanCheck.the_census_ceiling_is_seven_on_an_unassigned_day`, each carrying
`hnoassign : r.assignedRows = []`.  That is a real loss of domain and it is priced as README
gap **1902**.

**AND THE CENSUS NUMBER DID NOT MOVE, WHICH THIS ENTRY PREDICTED IT WOULD.**  Written before
P9 landed, it called seven *"the one number in this repository that P9 must move"*.  It did
not: on the merged tree the census ratio computed **seven** (it reads six since D63,
`PlannerWit.the_census_ratio_is_six_since_D63`, W-37 track K) and was
green beside a composed `Planner.dayRows`.  The reason is the fact both tracks of W-29
measured independently — `theCensusRequest` sends **no candidate**, so the cursor fills no slot
and a composition whose rows are a `filterMap` over `Planner.Assign.slotOf` adds nothing to its
day.  The number moves when a request carries candidates, which is README gap **1905**; the
falsified prediction is recorded at the merge as gap **2000**.

**AND GAP 1529 IS NOT ENABLEABLE BY P9 — asked, computed, answered NO.**  §8.3's segment-free
hole was stated *"for the moment the day carries assigned blocks"*, and the reading behind that
was `Planner.PlanReq.restRows`' own filter: a slot the cursor filled gets **no** Rest row, and
today it gets no Block row either, so an assigned slot is a hole the composition would plug.
That reading is right about one *class* of hole and wrong about the property.
`PlannerWit.the_hole_survives_where_the_composition_adds_no_row` is the settling computation:
at `PlannerWit.theRequest` the cursor fills **no** slot, so a composition whose rows are a
`filterMap` over `Planner.Assign.slotOf` adds no row to that day at all — and that day fails
`PlanCheck.holeFree` **and** `PlanCheck.holeFreeFrom`, on the whole day and on
`PlanCheck.futureHalf`'s rows alike.  The holes there are between the rows the day already has:
the stretch between two cut slots, and the stretch between the last slot and the wind-down.
Gap 1529 stays where W-28 left it — R3 enables it, not P9 — and `PlanCheck.holeFree` and
`PlanCheck.holeFreeFrom` stay out of `PlanCheck.checksOf`.  README gap **1988**.

############################################################################ -/

open Planner

/-- **E5 (P\*), stage 6 — BACK in this file since W-43 track K (the owner's D92, README gap 4362).**  The same
statement for breaks: "free positions included breaks" is the shipped defect, and §8.2 step 3 puts "a break of
`break_min` after every `break_after_blocks` blocks" into the slot list, so a planner that treats free time as free
will place work on top of one.

**Why it is back.**  It left at W-18 refuted on a day whose log held a break inside `m1`'s running block, and when the
owner's D87 netted that one, W-42 track R moved the refutation to a break logged before `m1`'s `start` and lasting into
it (README gap 4241) — a day the replay credited and drew across while the host's `Replay::idle_min_since` netted the
overlap: two readings of one block's minutes.  D92 makes them one (`Replay.restartAt`, parity P85;
`PlannerWit.the_into_break_day_keeps_its_block_off_the_break`), and a refutation that stood on a kernel defect is not
a discharge (the campaign's lesson 4), so the refutation went and the goal returned, as D92's own row says.

**Why it is neither proved nor refuted here.**  As written it is false — but only (1) on runs no replay builds,
because `PlanReq.run` is any `Seal.Run`, and (2) on replay-built runs only through logs the kernel and the host still
read two ways: a break logged ahead of a block's `start` but begun after it (README gap **4361**,
`PlannerWit.the_mid_break_day_lays_a_block_across_a_break`; the binary writes it with a `--now` in the past), and an
interruption logged while a break runs (gap 4340, until the owner's D90 makes `tm interrupt` end the break first).
Neither is a discharge.  The debt is to close gap 4361 and then either prove the law over the runs the decoder builds
or refute it on a world with one reading.  `PlanCheck.plan_places_no_block_over_a_break`, the law over the Block rows
that start at or after `now`, stays proved beside it. -/
theorem plan_places_no_block_over_a_break (r : PlanReq) (b k : WfSeg)
    (hb : b ∈ (dayPlan r).segments) (hk : k ∈ (dayPlan r).segments)
    (hbk : b.val.kind = SegKind.block) (hkk : k.val.kind = SegKind.brk) :
    b.val.stop ≤ k.val.start ∨ k.val.stop ≤ b.val.start := sorry

/-! **plan_does_not_overbook has LEFT this file** (stage 6, run **W-31**, track G).  It read

    theorem plan_does_not_overbook (r : PlanReq) :
      blockSeconds (dayPlan r) ≤ (dayPlan r).budgetBlocks * (dayPlan r).blockMin * 60

— L26 / §8.3's "no overbooking", Σ Block seconds against `remaining_budget × block_min`, in
seconds on both sides since the W-14 repair (gap 392; the `blockMinutes` form it replaced
floored per row and tolerated 59 s of unbudgeted work per Block).

**It is FALSE, and it went by refute-and-rename** (AGENTS §3.2, §3.1 item 3).  The refutation
is `PlannerWit.plan_does_not_overbook_as_stage_6_wrote_it_is_refuted` and has been in the tree
since **W-24**: at `PlannerWit.theOverBudgetRequest` the log closed two blocks against a stored
budget of one — 7 200 s against a 3 600 s cap — with **nothing running**, so it is not design
§6.3 row 1's cause (§8.2 choice 5b) but `PlanCheck`'s finding 1, the replayed past.  Design
§6.3's own proposed restatement falls to the same request
(`PlannerWit.the_designs_restatement_of_the_overbooking_law_is_refuted_too`).

**Why it stayed for six runs after its refutation, and why it moved now.**  W-24's own doc
comment gave the reason: the restatement over the rows §8.3 is about was **vacuous** —
`PlanCheck.overbook_has_no_subject_from_now_on_an_unassigned_day` — so shipping one would have
been AGENTS §5.2's theorem that compiles and means nothing.  **P9 composed §8.2 step 5's rows
into the day and that stopped being true**:
`PlannerWit.the_overbooking_sum_has_a_subject_where_the_fold_filled_slots` computes the same
sum at **zero** on a day the fold left alone and **positive** on two days it filled.

The restatements are `PlanCheck.plan_does_not_overbook_where_nothing_runs` and
`PlanCheck.plan_does_not_overbook_from_now_where_nothing_runs`: `PlanCheck.noOverbook` — which
is `checksCore`'s own first checker and the `hbudget` every lift in that file carries — *is*
the goal wherever `Planner.RuntimeIn.activeId` is `none`, because `PlanCheck.withoutActive`
then removes no row.  They fire at `PlannerWit.the_overbook_restatement_fires_on_a_worked_morning`
(a log that worked a block) and at
`PlannerWit.the_overbook_restatement_fires_where_the_fold_filled_slots` (a day the fold filled
two slots).  README gap **2020** is the residue: `noOverbook` itself on a day the fold filled
needs the count of occupied `Planner.Assign.slotOf` entries against
`Planner.PlanReq.finalAssign`'s `used`, and nothing in this tree relates the two. -/

/-! **plan_places_no_demanding_block_after_wind_down has LEFT this file** (stage 6, run **W-41**, track K; the owner's
D80, README gaps 3780, 3785 and 1984).  It read

    theorem plan_places_no_demanding_block_after_wind_down (r : PlanReq) (b w : WfSeg) (i : Id)
      (hb : b ∈ (dayPlan r).segments) (hw : w ∈ (dayPlan r).segments)
      (hbk : b.val.kind = SegKind.block) (hwk : w.val.kind = SegKind.windDown)
      (hi : b.val.item = some i) (hafter : w.val.start ≤ b.val.start) :
      (effectiveCi r.plan.val i).val < 4

— L26 / §8.3's "no `ci ≥ 4` Block after wind-down".  It came back at the W-39 repair (README gap 3713) and stayed
through W-40 because its only falsifying requests were two the fork can never produce: a day whose evening runs past
the calendar's last second, where the rows' clock (`Planner.clampSec`) squeezes the reservation and the WindDown row
onto one second (`PlannerWit.the_wind_down_goal_fails_where_the_kernels_clock_merges_the_last_evening`), and a
candidate whose `ci` on the wire is below its plan's on a window past the night.  **D80 refuses both by name**
(`PlanWire.planReqRefusal`: `eveningPastTheCalendar`, `ciDisagrees`, parity P71 and P72), and the goal is **proved AS
WRITTEN over every request the decoder accepts**:
`PlannerWit.plan_places_no_demanding_block_after_wind_down_on_every_request_the_decoder_accepts` — its statement is
this one with the single hypothesis `PlanWire.planReqOf parts bm q = .ok r`.  The law it stands on is
`PlanCheck.plan_places_no_demanding_block_after_wind_down`, restated under the goal's own name over D80 (b)'s clause
(`Planner.PlanReq.ciDisagreement = none`, weaker than W-39's `candsAgree`) and the wind-down inside the calendar, which
D80 (a)'s clause implies; the decoder pays both (`PlanWire.planReqOf_pays_the_evening_and_the_ci`).  It has a subject on
a request both clauses accept — the eve of the 2026 fall-back, a Block after its WindDown row
(`PlannerWit.the_wind_down_law_has_a_subject_on_the_eve`, `PlannerWit.the_eve_pays_both_of_d80s_clauses`).  The
statement with NO hypothesis stays false, at the last evening, and that is the request the decoder now refuses
(`PlannerWit.the_last_evening_is_refused_by_name`).  **The burn-down is 0.** -/

/-! **plan_is_monotone_in_rank has LEFT this file** (stage 6, run **W-39**, track K).  It read: two
siblings of one document at equal `rootPrio` and equal `effectiveCi`, the first written first —
the second assigned only if the first is.  **FALSE, four ways**:
`PlannerWit.plan_is_monotone_in_rank_as_stage_6_wrote_it_is_refuted` (W-19),
`PlannerWit.plan_is_monotone_in_rank_is_refuted_at_a_paying_day` (W-32, `loc:`),
`PlannerWit.monotone_rank_over_step_fives_filter_before_the_walk_is_refuted` (W-37, contiguity) and
PlannerWit.plan_is_monotone_in_rank_is_refuted_by_the_split (W-39, §7.5's split, gap 3546; a dead
name since W-40, when the owner's D74 split each batch into RUNS and that day stopped refuting it) —
and the candidate order fails even at the slot the other took
(`PlannerWit.monotone_rank_in_the_candidate_order_at_the_taken_slot_is_refuted`, since W-40 across a
`ci`).  **Restated** in the order step 5 serves its GROUPS, at D66's filter before the walk — W-39 gave
that law this goal's name; since W-40 it is `PlanFold.plan_is_monotone_in_rank_in_the_served_group_order`
— and since **W-40** (D74, D77) over the CANDIDATE order, at the same filter:
`PlanCheck.plan_is_monotone_in_rank` — an item strictly ahead of another at one `ci` that fits the slot
the other's row of the day stands at holds a work row no later.  README gaps 3526, 3542 and 3714. -/

/-! **plan_puts_hot_before_the_queue has LEFT this file** (stage 6, run **W-39**, track K).  It read:
an item carrying `hot` has a row starting no later than every row carrying an item that does not.
**FALSE, three times**: `PlannerWit.plan_puts_hot_before_the_queue_as_stage_6_wrote_it_is_refuted`
(W-19), `PlannerWit.hotBeforeQueue_is_false_on_a_quiet_day` (W-20, the quantifier reaches a Wall
row) and `PlannerWit.plan_puts_hot_before_the_queue_is_refuted_at_a_day_that_assigns_and_pays`
(W-32).  **Restated** in the order §8.2 step 5 serves its groups — W-39 gave that law this goal's
name; since W-40 it is `PlanFold.plan_puts_hot_before_the_queue_in_the_served_group_order` — a HOT
group (§7.4 key `p = 0`) that fits, before the walk, a slot a queue group (`p > 0`) took holds a work
row of the day starting no later than that group's; and since **W-40** (D77) over what the user sees:
`PlanCheck.plan_puts_hot_before_the_queue` — a HOT item that fits, before the walk, the slot of a row
holding only queue items holds a work row starting strictly earlier.  README gaps 3543 and 3714. -/

/-! **`edfNumbers` has left this file** (stage 6 step P4).  It was the last
provisional `def` here: §7.3's two numbers for one candidate, its `need` and
the capacity available to it by its due date after earlier deadlines have
reserved.  It is now `Planner.edfNumbers`, a projection of the grant
`Look.prioritiesWithFloors` gives that candidate, and the goal below reads it
through `open Planner`.  **The burn-down did not move**, because check 7 counts
`^theorem ` and not `def`s — design §5.5 says so and this is the step that
makes it true.

Its **units** are not design §5.5's.  The design wrote the pair as
`(g.deadline.need, g.avail)`; `Grant.avail` is a numerator over the pass's
denominator and `Deadline.need` is whole minutes, so `Arith.isImpossible` over
that pair compares a 10^18-scaled number with a count of minutes and answers
`false` for every candidate with any capacity at all.  `Planner.edfNumbers`
scales the need (`need * Look.capDen`), and
`Planner.edfNumbers_is_the_grants_own_impossibility` is the theorem that the
hypothesis below now says what `Grant.impossible` says. -/

/-! **plan_never_drops_an_impossible_item has LEFT this file** (stage 6, run **W-32**, track G).
It read

    theorem plan_never_drops_an_impossible_item (r : PlanReq) (i : Id) (e : Entity)
      (hget : r.plan.val.store.get i = some e)
      (himp : Arith.isImpossible (edfNumbers r i).1 (edfNumbers r i).2 = true) :
      i ∈ assignedOf (dayPlan r)

— L26 / §8.3's "impossible never dropped", §7.3's *"IMPOSSIBLE items are still scheduled with
everything available; the banner names the item and the shortfall"*.

**It is FALSE, and it went by refute-and-rename** (AGENTS §3.2, §3.1 item 3).  The refutation is
`PlannerWit.plan_never_drops_an_impossible_item_as_stage_6_wrote_it_is_refuted` and ships in the
same commit, at `PlannerWit.theImpossibleRequest` — a day that **assigns and pays**, whose `^m1`
is an item of its own plan, needs 100 000 minutes by the end of today, has no capacity left to it
and is not in `Planner.assignedOf (Planner.dayPlan …)`.  §7.3's promise is about **capacity** and
the planner drops that item on **energy**: it is `ci:5` and no slot this Wednesday cuts is that
good.  So the goal asked §8.2 step 5 for a guarantee no filter in it makes.

**Why it could be written down at all only now.**  Until this run **no request in this tree could
satisfy its hypothesis**: every candidate of all 45 carries `due = none`, so `Look.Cand.enters`
refuses it, `Planner.PlanReq.grantFor` is `none`, and `Planner.edfNumbers_without_a_grant` gives
the `(0, 0)` pair whose `Arith.isImpossible` is `false`.
`PlannerWit.the_first_impossible_candidate_this_tree_has_had` is the first `true` the test has
ever answered about a request, and `PlannerWit.pCandDue` is the candidate that produces it.

The restatement is `PlanCheck.impossibleKept`, which is **already** one of §6.1's eleven.  It
was proved inside the W-31 paying lift until W-37, when D66 made it read step 5's own filter and
that lift was refuted (PlannerWit.dayPlan_ok_on_the_whole_day_of_a_paying_decoder_is_refuted, W-37; proved again at W-38 under D67 as `PlanCheck.dayPlan_ok_on_the_whole_day_of_a_paying_decoder`, the check holding on every day, `PlanCheck.impossibleKept_on_every_day`;
`PlanCheck.dayPlan_ok_on_the_whole_day_of_a_paying_decoder_is_the_impossible_check` reduces the
whole paying day to this one check, and README gap 3160 was what was owed, closed by D67): it reads the
day's own `Planner.Diagnostics.impossible` — the id and its exact shortfall — rather than
recomputing the numbers, which is what design §6.1 requires of a check over a produced `DayPlan`.
**Its subject was empty at every request and every eligibility until W-33**, which
PlanCheck.impossible_has_no_subject said unconditionally, because `Planner.dayDiagnostics` never
wrote that field.  W-33 filled it from `Planner.edfNumbers` (`Planner.PlanReq.dayImpossible`,
closing README gap **2321**), refuted that theorem, and the check now has a subject and FAILS at
`PlannerWit.theUnassignedImpossibleRequest`, `PlannerWit.theQuietImpossibleRequest` and, at
step 5's own energy clause, `PlannerWit.theTwoImpossibleRequest` — README gap **2510**, the
owner's question.  *(This paragraph kept the old present tense through the W-33 merge, with only
a parenthesis added; rewritten in the W-33 repair, gap 2565.)* -/

/-! **plan_never_batches_past_an_equal_ci_candidate has LEFT this file** (stage 6, run **W-39**,
track K).  E2 read: a Batch row holding `i` and not `j`, the two one document's siblings at one
`ci` with `j` written first, puts `j` in `assignedOf (dayPlan r)`.  **FALSE, two ways**:
`PlannerWit.plan_never_batches_past_an_equal_ci_candidate_is_refuted_at_a_paying_day` (W-32, a
`loc:` the day cannot meet) and PlannerWit.plan_never_batches_past_an_equal_ci_candidate_is_refuted_by_the_split
(W-39, §7.5's split on a paying day — README gap 3546; a dead name since W-40, when the owner's D74
split each batch into RUNS).  **Restated** as what E2's `break` buys: every Batch row holds members of
one of §7.5's batches, and every batch is a run of consecutive equal-`ci` entries of step 4's order —
W-39 gave that law this goal's name; since W-40 it is
`PlanCheck.a_batch_row_holds_members_of_one_run_of_its_ci`, over `PlanFold.batchLoop_is_a_run_of_its_ci`
— and since **W-40** (D74, D77) with the goal's own conclusion over the CANDIDATE order:
`PlanCheck.plan_never_batches_past_an_equal_ci_candidate` — an item strictly ahead, at the row's `ci`,
of an item a Batch row holds, that fits the row's slot before the walk, holds a work row no later.
README gaps 3547, 3548 and 3714. -/

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

/-! **plan_tail_drop has LEFT this file** (stage 6, run **W-39**, track K).  It read: two requests
agreeing on `plan`, `now`, `window` and `blockMin`, the second with no more budget, assign the
second's items as a prefix of the first's.  **FALSE** as written — it pins five views and leaves
`run` free (`PlannerWit.plan_tail_drop_as_stage_6_wrote_it_is_refuted_by_the_run_it_does_not_pin`,
W-15, with `PlannerWit.erasing_the_active_item_does_not_repair_a_law_whose_run_is_free`).
**Restated and PROVED** (D5, D29): `PlanFold.plan_tail_drop` — two requests that plan the same day
(the same replayed past, reservation, energised cut, breaks, location and wind-down, and the same
groups as step 5 reads them) and differ in the budget left: the smaller budget's assigned items are
a prefix of the larger's in the day's row order; D29's own form, the Active item erased, is
`PlanFold.plan_tail_drop_with_the_active_item_erased`, and both fire with a block running
(`PlannerWit.the_tail_drop_law_fires_with_a_block_running`).  README gap 3549. -/

/-! **plan_is_stable_across_a_replan has LEFT this file** (stage 6, run **W-39**, track K).  It read:
two requests agreeing on `plan`, `window`, `blockMin` and the budget, and a free instant `nowSec`:
every row of the first day ending by that instant is a row of the second.  **FALSE** as written — the run
is free (`PlannerWit.plan_is_stable_across_a_replan_as_stage_6_wrote_it_is_refuted_by_the_run_it_does_not_pin`,
W-25), as is design §6.3 row 3's restatement
(`PlannerWit.the_designs_restatement_of_the_stability_law_is_refuted_too`).  **Restated and PROVED**
(D5): `PlanFold.plan_is_stable_across_a_replan` — a replan of the same log's day, at the same walls
and plan, at a later `now`: every row that ended BEFORE `now` and is not open is a row of the later
day.  Both exclusions are forced by a witness
(`PlannerWit.the_stability_law_needs_the_row_to_have_ended_before_now`,
`PlannerWit.the_stability_law_needs_the_row_to_be_closed`), and the law fires an hour later
(`PlannerWit.the_stability_law_fires_an_hour_later`).  README gap 3550.

**Restated again at W-40 track P over a replan after a LOGGED VERB** (the owner's D77, README gap 3714):
`PlanStable.plan_is_stable_across_a_replan_after_a_logged_verb` takes a later record that EXTENDS the earlier one —
every segment and every closed id kept — in place of `htr`, and keeps every closed row that ended before `now` **up to
its `done` flag, which can only rise**: a `tm done` after `now` raises it on an earlier block of the same item, fork
`past_segments`' own rule, so the exact form over an extension is refuted
(`PlannerWit.plan_is_stable_across_a_replan_over_an_extending_record_exactly_is_refuted`); it is exact where the later
record closes nothing new (`PlanStable.plan_is_stable_across_a_replan_after_a_verb_that_closes_nothing`), and the
W-39 form is its corollary (`PlanStable.plan_is_stable_across_a_replan_of_the_same_record`). -/

end Goals
end Tm
