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
  four `Recur` constructors kept as syntax.  `Field.Recur` exists; `Log` does
  not.  `PlanCore.log` is `List String`, JSONL held verbatim, and there is no
  event type, no `done inst=…`, no `skip inst=…`.  Until a parsed `LogEvent`
  exists, "exactly one pending instance" (§5.1's AfterDone rule, which is D1)
  and the classification pair `calendar_is_history_independent` /
  `afterDone_is_history_dependent` cannot be written at all.  Declaring an
  `Occurrence` here would fix the log model, which is stage 5's decision.
* **D2's epoch.**  `Rule.everyNDays n` carries a period and no anchor, so
  `every:3d` has no epoch to count from.  That is a **spec gap**, not a false
  theorem: there is nothing to state until §5 says what the epoch is.
* **F6 — `close day` double-counted `est:` against logged minutes.**  Needs
  `done_minutes` (§6.4), which is a replay of `.tm/log.jsonl`.  Same blocker as
  D1.  What *is* stated is `close_writes_every_estimate_through_demoteEst`,
  which is the half that does not need the log.
* **F3 and G1 — generated-block ownership.**  "The kernel owns the bytes of
  every generated block" is §4's **A** verdict — single ownership, architecture
  rather than type theory, and the plan says not to credit the compiler for an
  **A** row.  The acceptance is a Rust test asserting the day-section text is
  byte-identical across the file, `tm now`, `tm tui` and `tm plan --json`.
* **`ClosePolicy`'s five rows** (plan §3.2's named residue): copy-versus-move
  disposition, the off-chain `backlog#Overdue` target, child-folding, stamp
  accrual, exemptions.  The plan calls it "a typed table indexed by `Grain`"
  and names the rows but not their types.  `close` below is declared without
  it, because a `close` that reads a global table needs no policy argument;
  the table itself is stage 4's to design.
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
`edit`/`rank`/`add`".  Five of those seven are `ReqCmd` constructors already
(`move`, `drop`, `est`, `demote`, `readopt`); `rank` and `add` are not, and are
the two provisional signatures this stage needs.
############################################################################ -/

/-! ## Cmd.lean / Boundary.lean — the two missing verbs -/

/-- **Provisional (stage 3).**  `tm rank ^id <n>` (§13's verb list; §7.4 "line
order is your rank within a priority class").  A `Transform` is the settled
shape: the plan value in, a plan value or a structured `KErr` out.  It takes no
`Dest`, because §6.3's `rank` moves a line *within* its own file — that is what
distinguishes it from `move`, and it is why it cannot reuse `Relocation`. -/
def cmdRank (i : Id) (n : Nat) : Transform := sorry

/-- **Provisional (stage 3).**  `tm add`'s id generator.  §3.1 wants "4 chars of
`[a-z0-9]`" and README gap 13 records that `Id` is `List Char` instead, so the
*type* is not settled — but the **signature** is: the boundary already carries a
`seed` on the wire (plan §3.4), and freshness is a question about the ids that
exist.  Stage 3 may narrow the return type; the goal below survives it. -/
def freshId (seed : Nat) (existing : List Id) : Id := sorry

/-- **L21 (P\*), stage 3.**  `tm add` assigns an id no item already has —
`assigned ∩ existing = ∅` in plan §3.3.  Rules out the shipped
duplicate-id class re-entering through the *creation* path after
`no_two_lines_of_one_id_in_one_path` closed it on the mutation path. -/
theorem add_assigns_a_fresh_id (seed : Nat) (existing : List Id) :
    freshId seed existing ∉ existing := sorry

/-- **L20a (P\*), stage 3.**  `tm rank ^id n` is idempotent: ranking a line
where it already is changes nothing.  Rules out a rank command that renumbers
on every invocation and so makes `tm rank` a source of spurious diffs. -/
theorem rank_is_idempotent (i : Id) (n : Nat) (p q : WfPlan)
    (h : cmdRank i n p = .ok q) : cmdRank i n q = .ok q := sorry

/-- **L20b (P\*), stage 3.**  `tm rank` is order-preserving on everything it did
not name: two other items sharing a document keep their relative order.  Rules
out the renumbering that would silently reshuffle §7.4's tie-break — the sort
key is `(p, root_line_order, own_line_order)`, so a rank command that permutes
the others changes the plan for items the user never touched. -/
theorem rank_preserves_the_order_of_the_others (i : Id) (n : Nat) (p q : WfPlan)
    (j k : Id) (hj : j ≠ i) (hk : k ≠ i) (ej ek fj fk : Entity)
    (hjp : p.val.store.get j = some ej) (hkp : p.val.store.get k = some ek)
    (hjq : q.val.store.get j = some fj) (hkq : q.val.store.get k = some fk)
    (h : cmdRank i n p = .ok q)
    (hdoc : ej.val.live.doc = ek.val.live.doc)
    (hlt : ej.val.live.rank < ek.val.live.rank) :
    fj.val.live.rank < fk.val.live.rank := sorry

/-- **L22 (R\*), stage 3 — expected refutation.**  "`undo ∘ cmd = id` on the
nose."  Plan §3.3: a move assigns a *fresh* rank in the destination, so no
command can restore the old one; `move_out_and_back_is_not_the_inverse`
(Boundary.lean) already shows it for one composite, and this is the general
form — **no** command whatever inverts a move.  Discharging it means proving
the negation, and the consequence is already written in the plan: **`tm undo`
must replay the log, never apply an inverse.** -/
theorem move_has_an_inverse_command :
    ∃ inv : ReqCmd → ReqCmd, ∀ (p q : WfPlan) (i : Id) (n : Nat),
      applyCmd (.move i n) p = .ok q → applyCmd (inv (.move i n)) q = .ok p := sorry

/-! ## Boundary.lean — README gap 6 and gap 12: the JSON/string edge

The theorems of stage 2 begin at `ReqDoc` (a `List (List Char)`) and end at
`renderDocAt`'s `List (List Char)`.  `Json.parse`, `Json.compress`,
`String.toList`/`String.ofList` and the newline split sit between that and the
wire, and none of them is proved.  Since gap 1 closed, this is the **only**
unproved step on the text path. -/

/-- **P\*, stage 3, README gap 6.**  A value the kernel emits survives its own
serializer.  Rules out `call` returning text the host cannot read back — the
failure mode that is invisible to every theorem stage 2 proved, because they
all stop one layer inside this one.

**Suspected to need narrowing rather than refuting.**  `Lean.Json` carries a
`JsonNumber` with an exponent, and the general statement may be false at
representations the kernel never builds.  The honest discharge is the same
statement restricted to the fragment `run` emits (objects, arrays, strings and
`Nat` literals); if it does not hold there either, that is a finding. -/
theorem the_json_edge_round_trips (j : Lean.Json) :
    Lean.Json.parse j.compress = .ok j := sorry

/-- **P\*, stage 3, README gap 12.**  A file's bytes split into lines and joined
back are the same bytes.  This is the host's half of the document round trip
and the kernel's theorems assume it. -/
theorem a_file_splits_into_the_lines_it_was_joined_from (s : String) :
    "\n".intercalate (s.splitOn "\n") = s := sorry

/-- **R\*, stage 3, README gap 12 — expected refutation, and the reason gap 12
is a gap.**  The *other* composition fails: a request line containing a literal
newline round trips as one line inside the kernel and becomes two lines on
disk, and nothing in the kernel notices.  Discharging this means proving the
negation and then deciding what the boundary does about it — reject such a
line, or escape it. -/
theorem joining_lines_is_injective :
    ∀ ls : List String, ("\n".intercalate ls).splitOn "\n" = ls := sorry

/-! ## Plan.lean / Boundary.lean — README gap 16: checked, not constructed

Two of the trio are discharged as of 2026-09-09 in `Boundary.lean`:
`the_loader_builds_sites_in_range` and `the_loader_builds_oriented_demotions`.
Both read per-entity facts off `buildEntities_spec` and case on the filter
list in the shape `buildEntity_renders` started.  What remains is the rank
half: `splitDoc` hands each line index to exactly one of prose and items, so
`itemCheck: rankCollision` is unreachable from a request — but the chain from
the rank assignment to the per-document `(docRanks p k).Nodup` under the
`decide` is unwritten. -/

/-- **P\*, stage 3, README gap 16.**  Ranks within a document are distinct in
every plan the loader builds, because `splitDoc` hands each line index to
exactly one of prose and items.  Discharging it makes `itemCheck:
rankCollision` unreachable from a request. -/
theorem the_loader_builds_a_normalized_plan (docs : List ReqDoc) (items : List (Id × Entity))
    (h : buildEntities (placementsOf 0 docs) = .ok items) :
    normalized (loadCore docs items) = true := sorry

/-- **P\*, stage 3, README gap 4.**  Two readers of `est:` still coexist on the
command path: `Cmd.setEstE` and the `est` request go through the stage-one
`Nat`-valued `viewRemaining`, while the entity reads the field-level
`viewRemainingDur`.  They do not disagree about the bytes
(`the_two_est_setters_write_the_same_token`), but they are not one function,
and "two readers of one slot" is the exact shape of the defect this kernel
exists to remove.  This goal says the command path writes what the field path
reads; discharging it, or collapsing the two functions, closes gap 4. -/
theorem the_command_path_writes_what_the_field_path_reads (v : Nat) (e : Entity) :
    (setEstE v e).val.est = some (Dur.simple v DurUnit.minutes) := sorry

/-! ############################################################################
# STAGE 4 — `close`, `autoClose`, `ClosePolicy`; laws L16–L19, L27

Plan §5: "close idempotent at library *and* CLI level; a 3-month-stale tree
catches up losing nothing; the two behaviour changes landed with assent".
§4's F1, F2 and F4 are discharged here; B1–B3 are re-owed at the fold level.
############################################################################ -/

/-- **Provisional (stage 4).**  §6.3's lifecycle at one grain, as plan §3.3
defines it: "fold over `{ i ∈ dom | live site is in a region of grain g Closed
at now }`, applying `demoteEst` into `closeTo g now`, subject to
`ClosePolicy g`".

Three parts of the signature are settled and one is not.  Settled: the grain,
the instant (a `Day`; the kernel is day-resolution, README gap 10), and
`Transform` as the shape.  Not settled: `ClosePolicy`, which is why it is not an
argument — the plan calls it a table *indexed by* `Grain`, so `close g` can read
it without being handed it, and stage 4 stays free to design its rows.

The destination is found by **region**, not by file name: `docRegion` gives each
document's horizon and `closeTo g now` gives the target, so `close` needs
nothing from README gap 10's missing file-name grammar. -/
def close (g : Grain) (now : Day) : Transform := sorry

/-- **Provisional (stage 4).**  §6.3's "runs automatically on the first command
after the period ends".  Plan §3.3: because `closeTo` targets *now* rather than
the successor, catch-up is one step and `auto_close`'s sixteen-period iteration
collapses to "close each grain once, coarsest last". -/
def autoClose (now : Day) : Transform := sorry

/-- **L16 (P\*), stage 4.**  `close g` is idempotent.  Plan §3.3 gives the proof
shape: after the fold no entity's live site is in a closed region of grain `g`
(the next goal), so the second run folds over the empty set.  Rules out F2 —
`close month --drop ^id` doing nothing after auto-close — by making "already
closed" a fact about the plan value rather than a flag in `state.json`. -/
theorem close_is_idempotent (g : Grain) (now : Day) (p q : WfPlan)
    (h : close g now p = .ok q) : close g now q = .ok q := sorry

/-- **L18 at plan level (P\*), stage 4.**  `closeTo_target_is_open` (Grain.lean)
says the *target region* is open; this says the *fold's output* is.  It is the
engine of L16, and it is what the derived close target buys: with
`targetContaining` the fold's own output can land back in scope and neither
this nor idempotence goes through (plan §3.2(a) — one of the two behaviour
changes that need assent before stage 4). -/
theorem close_leaves_no_live_line_in_a_closed_region
    (g : Grain) (now : Day) (p q : WfPlan) (h : close g now p = .ok q)
    (i : Id) (e : Entity) (hget : q.val.store.get i = some e) (r : Region)
    (hr : docRegion q.val e.val.live.doc = some r) (hg : r.grain = g) :
    ¬ Closed r now := sorry

/-- **L17 (R\*), stage 4 — expected refutation.**  "`close week ∘ close month`
commutes."  It should not: a week close files into the month, so running the
month close first sees a different set.  Discharging it means proving the
negation and recording the order `autoClose` therefore has to use — which is
the *reason* the next goal fixes an order rather than leaving one open. -/
theorem close_week_and_close_month_commute (now : Day) (p : WfPlan) :
    (close week now p).bind (close month now) = (close month now p).bind (close week now) :=
  sorry

/-- **L19a (P\*), stage 4.**  `autoClose` is exactly "close each grain once,
coarsest last" — plan §3.3.  Rules out F1's shape at the root: the sixteen-
period loop is gone, so there is no iteration bound to get wrong and no
`none`-versus-`some` case scattered through it. -/
theorem autoClose_is_each_grain_once (now : Day) (p : WfPlan) :
    autoClose now p
      = (close day now p).bind (fun q => (close week now q).bind (close month now)) := sorry

/-- **F1 / L19b (P\*), stage 4.**  A tree three months stale catches up in one
call and stays caught up.  Rules out `auto_close` stamping skipped periods
closed *unrun* — here there is no stamp to get out of step with the work,
because "closed" is read off the plan and not off `state.json`. -/
theorem autoClose_catches_up_in_one_step (now : Day) (p q : WfPlan)
    (h : autoClose now p = .ok q) : autoClose now q = .ok q := sorry

/-- **F1 / L19c (P\*), stage 4.**  "Every period *run*", stated as its
observable consequence: after `autoClose` no live line sits in a closed region
at **any** grain.  This is the sentence "a 3-month-stale tree catches up losing
nothing" turns into. -/
theorem autoClose_runs_every_period_it_passes (now : Day) (p q : WfPlan)
    (h : autoClose now p = .ok q) (i : Id) (e : Entity)
    (hget : q.val.store.get i = some e) (r : Region)
    (hr : docRegion q.val e.val.live.doc = some r) :
    ¬ Closed r now := sorry

/-- **F4 (P\*), stage 4 — `ClosePolicy`'s exemptions.**  §6.3's last sentence:
"Recurring items and calendar intervals are never demoted — their instances
expire or persist per §5.3."  `close_week` demoted walls instead of carrying
them; this rules that out.  The hypothesis reads the *line*, so there is no
second copy of "is this a wall" for a policy to disagree with. -/
theorem close_never_demotes_a_wall (g : Grain) (now : Day) (p q : WfPlan)
    (h : close g now p = .ok q) (i : Id) (e f : Entity)
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f)
    (hw : e.val.recur ≠ Recur.none ∨ ∃ a b : DT, e.val.shape = Shape.interval a b) :
    f.val = e.val := sorry

/-- **B1–B3 (P\*), stage 4.**  "A close's measurement is not lost", at the fold
level.  L15 (`demoteEst_conserves`, `demoteEst_respects_user`) is proved for one
entity; what is owed is that `close` is the only thing that writes an estimate
and it writes every one of them *through* `demoteEst`.  Rules out the three
shipped paths that threw a measurement away — `readopt`'s absorb, `demote_one`'s
supersede, and `close_week` failing to fold children — by leaving no other
writer for them to be. -/
theorem close_writes_every_estimate_through_demoteEst (g : Grain) (now : Day) (bm : Nat)
    (p q : WfPlan) (h : close g now p = .ok q) (i : Id) (e f : Entity)
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f) :
    ∃ (userSet : Bool) (rec : Nat), f.val.line = (demoteEst bm userSet rec e).val.line := sorry

/-- **P\*, stage 4, §6.3's day row.**  A day close stamps `demoted:D07`, a week
close stamps `W37`, and `Field.Stamp` knows the difference — so this is
checkable rather than a convention.  Rules out the month review's "≥ 2 stamps"
cut list counting day stamps as week stamps. -/
theorem close_day_stamps_a_day_stamp (now : Day) (p q : WfPlan)
    (h : close day now p = .ok q) (i : Id) (e f : Entity)
    (hp : p.val.store.get i = some e) (hq : q.val.store.get i = some f)
    (hchanged : f.val.stamps ≠ e.val.stamps) :
    ∃ n : Nat, f.val.stamps = e.val.stamps ++ [Stamp.day n] := sorry

/-- **B3 (P\*), stage 4 — and it is blocked on README gap 22.**  §6.3's week
row: "Unfinished children are dropped from the week file (their remaining is
folded into the parent's `est:`)."  The statement needs `parentStep`, and
`Core.parent` is the one §3.1 field still stored and is **always `none`** —
reading it off the line today would make every `week/*.md` in the corpus stop
loading on `parentsTotal`.  So this goal cannot *fire* until gap 22's decision
(derive the field, or demote `parentsTotal` to a report the way `check.rs` has
it) is taken.  It is stated now so the decision is visibly a precondition of
stage 4 and not a surprise inside it. -/
theorem close_week_folds_a_dropped_child_into_its_parent (now : Day) (bm : Nat)
    (p q : WfPlan) (h : close week now p = .ok q) (i j : Id) (ec ep fp fc : Entity)
    (hchild : parentStep p.val j = some i)
    (hcp : p.val.store.get j = some ec) (hip : p.val.store.get i = some ep)
    (hiq : q.val.store.get i = some fp) (hcq : q.val.store.get j = some fc)
    (hdropped : fc.val.status = .settled .dropped) :
    remainingOf bm ep.val.line + remainingOf bm ec.val.line ≤ remainingOf bm fp.val.line := sorry

/-- **L27 (R\*), stage 4 — expected refutation, and an open product question.**
"Any lifecycle pair commutes."  `inventory`'s R7 stands open: `demote ^m1 ;
move ^m1 week` breaks a tree the reverse order does not, and nobody has decided
whether it should.  L27 makes the kernel refuse to be silent about it; it does
not answer it.  Discharging means proving the negation and then *deciding*
(plan §6.2.3) — a decision, not a proof, is the deliverable. -/
theorem lifecycle_commands_commute (c d : ReqCmd) (p : WfPlan) :
    applyAll [c, d] p = applyAll [d, c] p := sorry

/-! ############################################################################
# STAGE 5 — recurrence, rollups, priority, capacity

Plan §5: "parity harness: kernel vs Rust over the fixture corpus agrees except
at the six stated rounding sites".  The recurrence half of this stage is in the
header's not-yet-stateable list; what follows is the half that has vocabulary.
############################################################################ -/

/-! ## §6.4's rollups (`tree.rs`) -/

/-- **Provisional (stage 5).**  §6.4's `remaining(item)`: "`est` if set, else
`est_original`, else Σ over children".  Every input is settled — the two
estimate slots are `Field.viewEstKey` and `Fields.estLead`, the child relation
is `parentStep`, and `blockMin` is what turns a `b` into minutes.  The three
goals below are the three rows of that sentence. -/
def remainingMin (bm : Nat) (p : WfPlan) (i : Id) : Nat := sorry

/-- **P\*, stage 5, §6.4 row 1.**  An explicit `est:` wins.  Rules out C1
re-entering through the rollup: §4.1's `est:` key overrides the leading
estimate at the *line*, and the rollup must not read the other slot. -/
theorem remaining_is_the_est_key_when_set (bm : Nat) (p : WfPlan) (i : Id) (e : Entity)
    (d : Dur) (hget : p.val.store.get i = some e)
    (hd : Field.viewEstKey e.val.line = some d) :
    remainingMin bm p i = Dur.minutes bm d := sorry

/-- **P\*, stage 5, §6.4 row 2.**  With no `est:`, the leading estimate as
written (§3.1's `est_original`) is the value. -/
theorem remaining_falls_back_to_the_leading_estimate (bm : Nat) (p : WfPlan) (i : Id)
    (e : Entity) (d : Dur) (hget : p.val.store.get i = some e)
    (hno : Field.viewEstKey e.val.line = Option.none)
    (hlead : (Field.viewFields e.val.line).estLead = some d) :
    remainingMin bm p i = Dur.minutes bm d := sorry

/-- **P\*, stage 5, §6.4 row 3.**  With neither, the value is the sum over
children.  The recursion is well-founded only because `parentsAcyclic` is part
of `planWf` — which is what F5 (a parent cycle made `close_week` delete every
line in it) becomes once the traversal has to be total. -/
theorem remaining_sums_the_children (bm : Nat) (p : WfPlan) (i : Id) (e : Entity)
    (hget : p.val.store.get i = some e)
    (hno : Field.viewEstKey e.val.line = Option.none)
    (hnolead : (Field.viewFields e.val.line).estLead = Option.none) :
    remainingMin bm p i
      = (p.val.store.dom.filter (fun j => parentStep p.val j == some i)).foldl
          (fun a j => a + remainingMin bm p j) 0 := sorry

/-! ## §5.4's series head (README gap 18) -/

/-- **Provisional (stage 5).**  §5.4: "`## series:<name>` sections hold ordered
items.  Only the **head** — the first item not Done/Dropped — is active; the
rest are invisible to the planner."  `seriesOf` already derives which series a
placement sits in, so a series is a document plus a name and the head is a
function of the plan.  Settled by §5.4; nothing else about series is. -/
def seriesHead (p : WfPlan) (k : DocIx) (name : List Char) : Option Id := sorry

/-- **P\*, stage 5, §5.4.**  The head is not settled — completing it hands the
role to the next line, which is §5.4's whole mechanism. -/
theorem the_series_head_is_not_settled (p : WfPlan) (k : DocIx) (nm : List Char)
    (i : Id) (e : Entity) (h : seriesHead p k nm = some i)
    (hget : p.val.store.get i = some e) (o : Outcome) :
    e.val.status ≠ .settled o := sorry

/-- **P\*, stage 5, §5.4.**  The head is the *first* such line: no unsettled
member of the same series ranks ahead of it.  Rules out "adding a volume =
adding a line at the end" quietly activating the wrong volume. -/
theorem the_series_head_ranks_first (p : WfPlan) (k : DocIx) (nm : List Char)
    (i j : Id) (e f : Entity) (h : seriesHead p k nm = some i)
    (hi : p.val.store.get i = some e) (hj : p.val.store.get j = some f)
    (hsi : seriesOf p.val e.val.live = some nm) (hsj : seriesOf p.val f.val.live = some nm)
    (hk : f.val.live.doc = k) (hun : ∀ o : Outcome, f.val.status ≠ .settled o) :
    e.val.live.rank ≤ f.val.live.rank := sorry

/-! ## §7's priority -/

/-- **Provisional (stage 5).**  §7.2's arithmetic and nothing else: `p = k +
bin(u)`, clamped to `0..=7`, with HOT at zero.  `Arith.Bin` and `Arith.binOf`
already exist and are proved antitone, so this is the one function §7.2 adds on
top of them.  It deliberately does **not** take the candidate: the special
cases (`overdue with on_miss = persist`, a mandatory window instance, the `hot`
flag, `optional.md` at `p = 5`) are selection rules, and they belong with the
planner. -/
def prio (k : Nat) (b : Arith.Bin) : Nat := sorry

/-- **P\*, stage 5, §7.2.**  HOT is `p = 0`, whatever the root priority says.
Rules out a `!4` root pushing a HOT item off the front of the queue. -/
theorem prio_of_hot_is_zero (k : Nat) : prio k Arith.Bin.hot = 0 := sorry

/-- **P\*, stage 5, §7.2.**  "clamp p to 0..=7".  Rules out a bin ladder longer
than the default one silently producing a priority no screen can render. -/
theorem prio_is_clamped (k : Nat) (b : Arith.Bin) : prio k b ≤ 7 := sorry

/-- **P\*, stage 5, §7.1–7.2.**  More pressure is never lower priority: the bin
is antitone in utilisation (`Arith.binOf_antitone`, proved) and `prio` must not
undo it.  This is the monotonicity §8.3's "monotone rank" rests on. -/
theorem prio_is_antitone_in_utilisation (bins : List Arith.Q) (k n₁ a₁ n₂ a₂ : Nat)
    (hd : Arith.utilDefined n₁ a₁ = true)
    (h : Arith.Q.le (Arith.util n₁ a₁) (Arith.util n₂ a₂) = true) :
    prio k (Arith.binOf bins n₂ a₂) ≤ prio k (Arith.binOf bins n₁ a₁) := sorry

/-- **P\*, stage 5, §7.4's hysteresis.**  "`p` may improve (decrease) by at most
one bin per day relative to yesterday's stored `p` unless the new value is 0.
It may worsen freely."  Two numbers in, one out — settled by that sentence, and
it is the only part of §7.4 that is not already a sort. -/
def hysteresis (yesterday raw : Nat) : Nat := sorry

/-- **P\*, stage 5, §7.4.**  Improvement is capped at one step.  Rules out the
day-to-day reshuffling pure utilisation causes — the reason the rule exists. -/
theorem hysteresis_improves_by_at_most_one_bin (y r : Nat) (h : 0 < hysteresis y r) :
    y ≤ hysteresis y r + 1 := sorry

/-- **P\*, stage 5, §7.4.**  Worsening is free: nothing damps an item getting
less urgent. -/
theorem hysteresis_worsens_freely (y r : Nat) (h : y ≤ r) : hysteresis y r = r := sorry

/-- **P\*, stage 5, §7.4.**  The stated exception: `p = 0` is never delayed.
Rules out hysteresis holding a HOT item back for a day, which would make the
damping rule the cause of the overrun it exists to prevent. -/
theorem hysteresis_never_delays_hot (y : Nat) : hysteresis y 0 = 0 := sorry

/-! ## §7.3's EDF pass and §8.4's capacity lookahead -/

/-- **Provisional (stage 5).**  §8.4's `DayCapacity` verbatim: a date and
"minutes of expected capacity at each energy level", indexed 0..5.  The spec
writes the second as `[u32; 6]`; `Fin 6 → Nat` is that. -/
structure DayCapacity where
  day       : Day
  minutesAt : Fin 6 → Nat

/-- **Provisional (stage 5).**  The three numbers §7.3's loop reads off one
dated candidate: `need(item)`, `item.ci`, and its effective due.  Transcribed
from §7.3, not invented — the pass names exactly these. -/
structure Deadline where
  need : Nat
  ci   : Fin 6
  due  : Day

/-- **Provisional (stage 5).**  §7.3's pass: "subtract reserve from cap,
earliest days first, highest matching levels first".  Capacities in,
capacities out; the per-item `u` and the IMPOSSIBLE flag are read off the
before-and-after pair, which is why the reservation is the primitive. -/
def edf (caps : List DayCapacity) (ds : List Deadline) : List DayCapacity := sorry

/-- **P\*, stage 5, §7.3.**  The pass keeps the same days: reservation is
subtraction, not a filter. -/
theorem edf_keeps_the_days (caps : List DayCapacity) (ds : List Deadline) :
    (edf caps ds).length = caps.length := sorry

/-- **P\*, stage 5, §7.3.**  The pass only ever *spends* capacity.  Rules out
E1's shape one layer up: a reservation that grows the pool it draws from makes
every downstream `u` optimistic and nothing downstream can detect it. -/
theorem edf_only_spends_capacity (caps : List DayCapacity) (ds : List Deadline)
    (n : Nat) (c c' : DayCapacity) (l : Fin 6)
    (h : caps[n]? = some c) (h' : (edf caps ds)[n]? = some c') :
    c'.minutesAt l ≤ c.minutesAt l := sorry

/-- **P\*, stage 5, §7.3.**  "what is left after earlier deadlines": a day past
every deadline in the pass is untouched by it.  Rules out an EDF pass that
reserves *after* an item's due date and so reports capacity the item can never
use — which is exactly how a HOT item comes out looking comfortable. -/
theorem edf_reserves_only_before_the_deadline (caps : List DayCapacity) (ds : List Deadline)
    (n : Nat) (c c' : DayCapacity) (l : Fin 6)
    (h : caps[n]? = some c) (h' : (edf caps ds)[n]? = some c')
    (hafter : ∀ d ∈ ds, d.due < c.day) :
    c'.minutesAt l = c.minutesAt l := sorry

/-! ############################################################################
# STAGE 6 — the planner; §8.3's invariants; L24 and L25

Plan §5: "D1–D14 decidable-checked on every plan the corpus produces;
`planner_invariants.rs` green at 256 cases through the FFI".  L26 is "decidable
over the produced `DayPlan`", so the output type is what has to exist and the
input mostly does not.
############################################################################ -/

/-- **Provisional (stage 6).**  §8's `SegKind`, transcribed.  `Batch(Vec<Id>)`
keeps its member list here for the same reason it does there: a batch is one
slot holding several items, and §7.5's ordering rule is about that list. -/
inductive SegKind
  | block | batch (ids : List Id) | brk | routine | wall | rest
  | optional | windDown | sleep | lost
deriving DecidableEq, Repr

/-- **Provisional (stage 6).**  §8's `Segment`, reduced to what §8.3 reads.
Times are minutes since midnight rather than `DateTime`, because README gap 10
records that the kernel has days and no time of day yet; `instance` and `flags`
are omitted because no §8.3 invariant mentions them.  Stage 6 widens this. -/
structure Seg where
  startMin : Nat
  endMin   : Nat
  kind     : SegKind
  energy   : Option (Fin 6)
  item     : Option Id
deriving Repr

/-- **Provisional (stage 6).**  §8's `DayPlan`, minus `diagnostics` and
`priorities` — both are reports, and no §8.3 invariant is about them. -/
structure DayPlan where
  day          : Day
  windowStart  : Nat
  windowEnd    : Nat
  blockMin     : Nat
  budgetBlocks : Nat
  segments     : List Seg

/-- **Provisional (stage 6), and the one place this file constrains a later
stage.**  §8's `PlanInput` names six components and three of them — `cfg`,
`model`, `runtime` — have **no kernel representation at all**.  What is
transcribed here is §8.1's settled half: the plan value, the instant, the
window, the block length and the budget.  Every goal below reads only the
*output*, so widening this record does not disturb any of them; that is why
declaring it is safe and declaring `PlanInput` in full would not be. -/
structure PlanReq where
  plan         : WfPlan
  now          : Day
  windowStart  : Nat
  windowEnd    : Nat
  blockMin     : Nat
  budgetBlocks : Nat

/-- **Provisional (stage 6).**  §8's `pub fn plan(input) -> DayPlan; // pure; no
I/O`.  L23 ("`plan` is pure") is **free and already discharged**: it is a
function, and Lean has no other kind.  That is why there is no purity goal
below. -/
def dayPlan (r : PlanReq) : DayPlan := sorry

/-- The items one segment carries: a batch carries its whole member list
(§7.5's "one block with several of them in key order"), everything else carries
at most one.  A real definition, not a provisional one. -/
def segItems (s : Seg) : List Id :=
  match s.kind with
  | SegKind.batch ids => ids
  | _                 => s.item.toList

/-- The items a plan assigns, in slot order — the list §8.3's two relational
laws compare.  Batched items count as assigned, which is why this is not
`filterMap Seg.item`: §7.5 exists precisely so the `+3` bin gets a slot, and a
definition that lost batch members would make "monotone rank" and "impossible
never dropped" quietly weaker than §8.3 states them. -/
def assignedOf (d : DayPlan) : List Id := d.segments.flatMap segItems

/-- The minutes a plan gives to work blocks. -/
def blockMinutes (d : DayPlan) : Nat :=
  (d.segments.filter (fun s => decide (s.kind = SegKind.block))).foldl
    (fun a s => a + (s.endMin - s.startMin)) 0

/-- **L26 / §8.3 "no overbooking" (P\*), stage 6.**  Σ Block minutes ≤
`remaining_budget × block_min`.  Decidable over the produced `DayPlan`, which is
what L26 promises. -/
theorem plan_does_not_overbook (r : PlanReq) :
    blockMinutes (dayPlan r) ≤ (dayPlan r).budgetBlocks * (dayPlan r).blockMin := sorry

/-- **E1 (P\*), stage 6.**  No block is longer than one block.  The shipped bug:
"the Active reservation covered the whole remaining estimate; a 6b item
swallowed 355 minutes". -/
theorem plan_reserves_one_block_at_a_time (r : PlanReq) (s : Seg)
    (hs : s ∈ (dayPlan r).segments) (hk : s.kind = SegKind.block) :
    s.endMin - s.startMin ≤ (dayPlan r).blockMin := sorry

/-- **L26 / §8.3 "energy filter" (P\*), stage 6.**  Every block has
`item.ci ≤ slot.energy`.  `effectiveCi` (Plan.lean) is §3.2's inheritance walk,
already proved — this is the planner honouring it.  Rules out E8's shape: two
readers of an item's `ci` disagreeing about eligibility. -/
theorem plan_respects_the_energy_filter (r : PlanReq) (s : Seg) (i : Id) (lvl : Fin 6)
    (hs : s ∈ (dayPlan r).segments) (hk : s.kind = SegKind.block)
    (hi : s.item = some i) (he : s.energy = some lvl) :
    (effectiveCi r.plan.val i).val ≤ lvl.val := sorry

/-- **L26 / §8.3 "no segment overlaps a Wall" (P\*), stage 6.** -/
theorem plan_places_no_block_over_a_wall (r : PlanReq) (b w : Seg)
    (hb : b ∈ (dayPlan r).segments) (hw : w ∈ (dayPlan r).segments)
    (hbk : b.kind = SegKind.block) (hwk : w.kind = SegKind.wall) :
    b.endMin ≤ w.startMin ∨ w.endMin ≤ b.startMin := sorry

/-- **E5 (P\*), stage 6.**  The same statement for breaks: "free positions
included breaks" is the shipped defect, and §8.2 step 3 puts "a break of
`break_min` after every `break_after_blocks` blocks" into the slot list, so a
planner that treats free time as free will place work on top of one. -/
theorem plan_places_no_block_over_a_break (r : PlanReq) (b k : Seg)
    (hb : b ∈ (dayPlan r).segments) (hk : k ∈ (dayPlan r).segments)
    (hbk : b.kind = SegKind.block) (hkk : k.kind = SegKind.brk) :
    b.endMin ≤ k.startMin ∨ k.endMin ≤ b.startMin := sorry

/-- **L26 / §8.3 "no ci ≥ 4 Block after wind-down" (P\*), stage 6.**  §8.2 step
2: "sleep and wind-down define the hard end of the day". -/
theorem plan_places_no_demanding_block_after_wind_down (r : PlanReq) (b w : Seg) (i : Id)
    (hb : b ∈ (dayPlan r).segments) (hw : w ∈ (dayPlan r).segments)
    (hbk : b.kind = SegKind.block) (hwk : w.kind = SegKind.windDown)
    (hi : b.item = some i) (hafter : w.startMin ≤ b.startMin) :
    (effectiveCi r.plan.val i).val < 4 := sorry

/-- **L26 / §8.3 "walls never moved" (P\*), stage 6.**  A wall segment sits
where its interval says, not where the planner found room.  §8.2 step 1:
overlapping walls go to `diagnostics.conflicts` and "the planner does not
resolve them".

**Caveat, and it is why this statement will need revisiting:** `Field.DT`
carries a day and a `Clock`, and `Seg` carries minutes-since-midnight, so this
says nothing about a wall that crosses midnight.  When README gap 10's
time-of-day arrives, the right statement is over absolute minutes
(`DT.abs`). -/
theorem plan_never_moves_a_wall (r : PlanReq) (w : Seg) (i : Id) (e : Entity) (a b : DT)
    (hw : w ∈ (dayPlan r).segments) (hk : w.kind = SegKind.wall) (hi : w.item = some i)
    (hget : r.plan.val.store.get i = some e) (hs : e.val.shape = Shape.interval a b) :
    w.startMin = a.time.val ∧ w.endMin = b.time.val := sorry

/-- **L26 / §8.3 "monotone rank" (P\*), stage 6.**  "For two candidates with
equal `p` and equal `ci`, the one with the lower line order is never left
unassigned while the other is assigned."

Stated with `rootPrio` and `effectiveCi` standing in for §7's `p`, because
`prio` above is stage 5's and takes a bin this statement has no way to produce.
When stage 5 lands, the honest form replaces `rootPrio … = rootPrio …` with
equality of the computed priority; the shape of the goal does not change. -/
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
stage 5.  The `u ≥ 1` half of HOT is the next goal's business. -/
theorem plan_puts_hot_before_the_queue (r : PlanReq) (i j : Id) (e f : Entity) (sj : Seg)
    (hi : r.plan.val.store.get i = some e) (hj : r.plan.val.store.get j = some f)
    (hhot : Flag.hot ∈ e.val.flags) (hnot : Flag.hot ∉ f.val.flags)
    (hsj : sj ∈ (dayPlan r).segments) (hji : sj.item = some j) :
    ∃ si ∈ (dayPlan r).segments, si.item = some i ∧ si.startMin ≤ sj.startMin := sorry

/-- **Provisional (stage 6).**  §7.3's two numbers for one candidate: its
`need` and the capacity available to it by its due date, after earlier
deadlines have reserved.  Stage 5's `edf` produces both; this is the hook §8.3
needs to name IMPOSSIBLE and nothing more. -/
def edfNumbers (r : PlanReq) (i : Id) : Nat × Nat := sorry

/-- **L26 / §8.3 "impossible never dropped" (P\*), stage 6.**  §7.3: "IMPOSSIBLE
items are still scheduled with everything available; the banner names the item
and the shortfall".  Rules out the failure that silently looks like success —
an item the day cannot fit vanishing from the plan instead of appearing with a
shortfall.  `Arith.isImpossible` and `Arith.impossible_imp_hot` are proved
already; what is owed is that the planner acts on them. -/
theorem plan_never_drops_an_impossible_item (r : PlanReq) (i : Id) (e : Entity)
    (hget : r.plan.val.store.get i = some e)
    (himp : Arith.isImpossible (edfNumbers r i).1 (edfNumbers r i).2 = true) :
    i ∈ assignedOf (dayPlan r) := sorry

/-- **E2 (P\*), stage 6, §7.5.**  Batching gathers in key order and does not
reach past an equal-`ci` candidate that ranks ahead of it.  The shipped bug did
exactly that, and the effect is invisible in the output: the batch looks
correct and the skipped item simply never appears. -/
theorem plan_never_batches_past_an_equal_ci_candidate (r : PlanReq) (s : Seg) (ids : List Id)
    (i j : Id) (e f : Entity)
    (hs : s ∈ (dayPlan r).segments) (hk : s.kind = SegKind.batch ids)
    (hi : i ∈ ids) (hj : j ∉ ids)
    (hie : r.plan.val.store.get i = some e) (hjf : r.plan.val.store.get j = some f)
    (hci : effectiveCi r.plan.val i = effectiveCi r.plan.val j)
    (hdoc : e.val.live.doc = f.val.live.doc)
    (hrank : f.val.live.rank < e.val.live.rank) :
    j ∈ assignedOf (dayPlan r) := sorry

/-! ## E7 — §8.1's window, which is a fixed point and was solved by iterating -/

/-- The minutes §8.1's `Σ duration(walls inside [arrival, end])` adds.  A real
definition; `windowEnd` below is the provisional one. -/
def wallsInside (arrival stop : Nat) (walls : List (Nat × Nat)) : Nat :=
  (walls.filter (fun w => decide (arrival ≤ w.1 ∧ w.2 ≤ stop))).foldl
    (fun a w => a + (w.2 - w.1)) 0

/-- **Provisional (stage 6).**  §8.1's `end = min(arrival + window_hours,
window_cap) + Σ duration(walls inside [arrival, end])` — the equation names
`end` on both sides.  E7 is `window_and_budget` solving it by iterating; plan
§4 says "totality forces a termination argument or a bound", and that is what
this signature is for. -/
def windowEnd (arrival windowMin windowCap : Nat) (walls : List (Nat × Nat)) : Nat := sorry

/-- **E7a (P\*), stage 6, §8.1.**  It is a solution of the equation. -/
theorem the_window_end_solves_the_equation (arrival windowMin windowCap : Nat)
    (walls : List (Nat × Nat)) :
    windowEnd arrival windowMin windowCap walls
      = min (arrival + windowMin) windowCap
        + wallsInside arrival (windowEnd arrival windowMin windowCap walls) walls := sorry

/-- **E7b (P\*), stage 6, §8.1.**  It is the *least* solution, which is what
makes it a definition rather than a choice — and what makes "a late start gets a
later end and the same budget formula" reproducible rather than dependent on how
many times the loop happened to run. -/
theorem the_window_end_is_the_least_solution (arrival windowMin windowCap m : Nat)
    (walls : List (Nat × Nat))
    (hm : m = min (arrival + windowMin) windowCap + wallsInside arrival m walls) :
    windowEnd arrival windowMin windowCap walls ≤ m := sorry

/-! ## L24 and L25 — the two relational laws

Plan §6.2.4: these relate **two runs** of a greedy fold — real inductions, not
`decide`.  `inventory` budgets tail-drop alone at plausibly a week and has a
working 882-line proptest at 256 cases that has empirically caught things.

**The plan's recommendation, and it is deliberate: keep the proptest, state the
law in Lean, prove it last or never.**  A kernel that proves 25 of 27 laws and
property-tests 2 is not compromised.  They are stated here so that the choice is
visible in the burn-down rather than absent from it — and so that "we decided
not to prove these" cannot be confused with "we forgot". -/

/-- **L24 (?), stage 6, §8.3 tail-drop — relational; keep the proptest.**
"Removing minutes from the day (interrupt, overrun, downgrade) never changes
the set of assigned items except by removing a suffix in key order (Active item
excepted)."  Stated over the budget, which is the cleanest of the three ways
minutes leave a day.  The `Active`-item exception is not modelled here and is
part of what makes this expensive. -/
theorem plan_tail_drop (r r' : PlanReq)
    (hplan : r'.plan = r.plan) (hnow : r'.now = r.now)
    (hws : r'.windowStart = r.windowStart) (hwe : r'.windowEnd = r.windowEnd)
    (hbm : r'.blockMin = r.blockMin) (hless : r'.budgetBlocks ≤ r.budgetBlocks) :
    ∃ n : Nat, assignedOf (dayPlan r') = (assignedOf (dayPlan r)).take n := sorry

/-- **L25 (?), stage 6, §8.3 stability — relational; keep the proptest.**  "A
replan changes no segment with `end ≤ now`."  The first half of §8.3's bullet
("same input → identical `DayPlan`") is free and is not restated. -/
theorem plan_is_stable_across_a_replan (r r' : PlanReq) (nowMin : Nat) (s : Seg)
    (hplan : r'.plan = r.plan) (hws : r'.windowStart = r.windowStart)
    (hbm : r'.blockMin = r.blockMin) (hbb : r'.budgetBlocks = r.budgetBlocks)
    (hs : s ∈ (dayPlan r).segments) (hend : s.endMin ≤ nowMin) :
    s ∈ (dayPlan r').segments := sorry

end Goals
end Tm
