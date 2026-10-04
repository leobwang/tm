import TmKernel.Lookahead
import TmKernel.SealResume
import TmKernel.Recur
import TmKernel.PastCut
/-!
# The planner's vocabulary — §8's `Segment`, `DayPlan` and `PlanInput`, settled (stage 6, step P0)

Fork-point `tm-core/src/planner.rs` is the oracle, read by type and function name:
`planner::SegKind`, `planner::SegFlags`, `planner::Segment`, `planner::Diagnostics`,
`planner::DayPlan`, `planner::PlanInput`, `planner::PlanOverrides`, `planner::Planner::window_and_budget`, and `store::RuntimeState` beside them.

This module holds the planner's **types and their laws**, and — since P1, P2, P3, P5, P6 and
P7 — §8.2's **steps one to seven**.  `dayPlan` is no longer the fork's `DayPlan::empty`: it is
that day with `dayRows` for its segments and `dayDiagnostics` for its diagnostics, so the day
it answers has rows in it.  Step one places today's walls (`wallsToday`, `wallRows`,
`stepOneSegs`, on stage 5's own `Look.wallIxOn`); step two places today's routine instances
and closes the day with §16's wind-down and sleep (`placeStep`, `placedRoutines`,
`routineRow`, `stepTwoSegs`); step three cuts the slots and gives them their energy
(`todaySlots`, `energisedSlots`, argument lists for stage 5's `Look.cutSlots` and
`Look.energizeToday` and not a second cut); step five builds the groups and walks the slots
(`buildGroups`, `assignStep`, `assignFold`, `assignedRows`); **step six places what step two
deferred** (`deferOne`, `deferWalk`, `deferFold`, with `finalRoutines` and `finalAssign` its
two projections, and `dayRoutineSegs` the rows it leaves); and step seven fills what is left
(`optionalRows`, `restRows`).  `dayRows` is the composition of all of them.

*(W-32 repair, README gap **2223** — the SECOND time this paragraph has been false in the way
W-15 repaired it for, and the rot class W-14 opened as gap 393.  It read **"Steps 3 to 7 are
not written here: nothing in this module cuts a slot, assigns a block, or fills a batch"**,
and all three clauses were refuted by this file: at THIS commit `:2825` is "The slots step 5
will assign into", `:4232` is "§8.2 step 5's groups — the batching, the split and one `Group`
per bucket", `:4576` is "§8.2 step 5's assignment", and `:6138`'s `dayRows` composes
`assignedRows`, `optionalRows` and `restRows`.  (Gap 2223 quoted `:2802`, `:4209`, `:4553`
and `:6115`, all four true of `471a7ff`; this header is twenty-three lines longer, so
every anchor below it moved by that, and re-deriving them rather than copying them is AGENTS §5.11.)
Step 6 has been here since `0d52a4d`, 2026-09-19.  Step 8 fills all twelve fields since W-34
(ten since W-33; gap 2511 closed), and P8's emitter, the plan hash, landed at W-34.)*

*Two tripwires, and both have fired.*  P0 left two theorems whose job was to stop compiling on
the day they became false.  **P1 took the first**: `the_day_has_no_segments_until_the_first_step_lands`
is **deleted** — with `dayPlan_diagnostics` and `dayPlan_assigns_nothing_yet`, which P1's body
also made false.  **W-34 took the second**: the_plan_hash_is_a_placeholder_until_the_emitter_lands
is refuted in `PlannerWit` and renamed `dayPlan_planHash`.  `Check.lean`'s blocks record both;
neither is a live description of this module.  Nothing in `Goals.lean` is discharged here.

*(W-15 repair: every clause of this paragraph but the last was false of the code it heads —
the rot class W-14 opened as gap 393, in the stage's central module.  It is re-stated here
against the code, not against the step that first wrote it.)*

## What is settled, and by which rule

* **`Seg` is on `Look.Slot`'s representation — absolute seconds, not minutes since midnight**
  (README gap 256).  `Goals.lean`'s provisional `Seg` carried `startMin`/`endMin`, which is a
  second representation of an instant beside `Cal.Instant` and `Look.Slot` (AGENTS §5.3), and
  `plan_never_moves_a_wall`'s own doc comment recorded the defect it caused — "says nothing
  about a wall that crosses midnight".  On seconds the caveat is not weakened, it is **gone**.
  `Seg.minutes` **calls** `Look.spanMinutes`, the one body `Look.Slot.minutes` is also built
  on (W-14 repair, gap 390).
* **`SegKind` has eleven constructors**, `batch` carrying a **bounded** `BatchIds` (R10) and
  `ghost` naming §12.1's arrival-plan row that the provisional form had no name for.
* **Nothing here re-derives a window, a budget, a cut or an energy.**  `PlanReq` carries
  `Look.Input` whole and reads the window through `Look.day0Window` and the budget through
  `Look.budgetOf` — the definitions stage 5 built (AGENTS §5.3, design §1.1-§1.3).  There is
  no `windowStart`, no `windowEnd`, no `blockMin` and no `budgetBlocks` field on the request:
  every one of them would have been a second copy.
* **The request carries the run, not the log** (D9, D24): `PlanReq.run` is the `Seal.Run` the
  seam exposes, so the past half of the day (fork `Planner::past_segments`) is reachable
  without a second replay.
* **Every ratio is a pair.**  `Diagnostics.planHonesty` is a numerator and a denominator and
  the kernel never divides (AGENTS §4, design §11); the fork's `Option<f64>` is the pair with
  denominator `0`.  `Seg.mult` is an `Arith.Pos`, not the fork's `f64`.
* **Each diagnostic is named** (AGENTS §5.7): `Note` is an inductive with the fork's four
  messages as constructors carrying their arguments, not a prose `String`.  Rendering is P8's.

## Tiers

Everything here is a **type law** or a **function law** (one run, one answer): a smart
constructor refuses or accepts; a setter's view returns what was set; `dayPlan`'s shape is a
projection of its request.  No relational (two-run) law is stated here — L24 and L25 are G2's
and G3's, over the `dayPlan` P5 will have built.

## R10, by name

Bounded here, each with its constructor **and** its rejection theorem:
`BatchIds` (`mkBatch?`), `Seg` (`mkSeg?`), `Capped` and its `IdList` instance
(`Capped.ofList?`, `Capped.cons?`), `PlanHash` (`mkHash?`), `Budget` (`mkBudget?`),
`ActiveBlock` (`mkActive?`), `BreakState` (`mkBreak?`) — `InterruptState` has none since W-41 (D78) —
yesterday's priorities (`mkYesterday?`) and `PlanOverrides` (`mkOverrides?`).

**Reused rather than re-bounded** (design §9's own "reuse" column): `Look.WakeClock.wf` and
its `badWake`; `Field.Clock` for a stored arrival and a stored window; `Field.parseDate`'s
calendar bound for `state.date`; `Look.maxLocName` for the location name; `yesterdayOf?`
for a stored `p`.  Five of §9's twelve rows are already `Look.Today`'s and are read through it
— re-declaring them would have been the defect this module's header warns about.

## D9-21, the recursion rule

`Capped.ofList?`, `mkYesterday?` and `mkOverrides?` recurse over lists the wire can make
large, and each is a `List.length` test plus core's own `List` operations.  `Seg.items` is
core `Subtype.val`/`Option.toList`.

*(W-32 repair, the same gap 2223: this paragraph closed **"`dayPlan` folds over nothing: its
segment list is `[]`"**, which P1 made false and P5 and P6 made false twice over.  `dayPlan`'s
segment list is `dayRows`, and the folds it runs are `placementFold` over the sorted routine
instances, `assignFold` over the energised slots and `deferWalk` over the instances step two
deferred — each bounded by `maxCands` or by the day's own slot count, which is what D9-21
asks of them.)*
-/

namespace Tm
namespace Planner

open Field (Clock)

/-! ## Bounds (R10) -/

/-- §7.5's `batch_max_min` cannot gather more than this many items into one slot, so a
`SegKind.batch` list is bounded. -/
def maxBatch : Nat := 16

/-- The most candidates one day's plan may name — and therefore the length bound of every
diagnostic list, each of which holds at most one entry per candidate. -/
def maxCands : Nat := 1024

/-- §8.1's budget in blocks: a 24-hour window at the shortest block the grammar accepts.  Fork
`capacity::budget_blocks` returns a `u32` with no bound at all; this is R10's. -/
def maxBudget : Nat := 96

/-- `state.last_plan_hash` is 16 lowercase hex digits (fork `DayPlan::hash`). -/
def hashHexLen : Nat := 16

/-- `2 ^ 64`, the width of the fork's FNV-1a digest, stated (R10). -/
def hashBound : Nat := 18446744073709551616

/-! ## A bounded list, once

The nine diagnostic lists, the priority list and the override lists are all "at most one entry
per candidate".  That is **one** concept, so it has one type (AGENTS §5.3) rather than nine
copies of a `length ≤ n` subtype. -/

/-- A list of at most `maxCands` entries. -/
abbrev Capped (α : Type) := { l : List α // l.length ≤ maxCands }

/-- The design's `IdList`. -/
abbrev IdList := Capped Id

/-- The empty one. -/
def Capped.nil {α : Type} : Capped α := ⟨[], by simp⟩

/-- The decoder's constructor: a list the wire sent, refused past the cap. -/
def Capped.ofList? {α : Type} (l : List α) : Option (Capped α) :=
  if h : l.length ≤ maxCands then some ⟨l, h⟩ else none

theorem Capped.ofList?_refuses_past_the_cap {α : Type} (l : List α) (h : maxCands < l.length) :
    Capped.ofList? l = none := by
  unfold Capped.ofList?
  rw [dif_neg (by omega)]

/-- The empty list is accepted, and is `Capped.nil` — what a request with no candidates and a
request with no routines both decode to. -/
theorem Capped.ofList?_nil {α : Type} : Capped.ofList? ([] : List α) = some Capped.nil := rfl

theorem Capped.ofList?_accepts {α : Type} (l : List α) (h : l.length ≤ maxCands) :
    (Capped.ofList? l).map Subtype.val = some l := by
  unfold Capped.ofList?
  rw [dif_pos h]
  rfl

/-- **The producer's answer at the cap** (README gap 322, answered here for step P1's one
producer).  A diagnostic list the day genuinely overflows is **truncated to its first
`maxCands` entries**, never silently emptied and never reordered: the two theorems beside it
say that nothing is lost below the cap and that what is lost is a suffix.  The *decoder's*
constructor stays `Capped.ofList?`, which refuses — a wire value past a bound is a refusal
(R10), a produced list past a bound is a loss the kernel must name. -/
def Capped.ofListTake {α : Type} (l : List α) : Capped α :=
  ⟨l.take maxCands, by simpa using Nat.min_le_left maxCands l.length⟩

theorem Capped.ofListTake_keeps_everything_below_the_cap {α : Type} (l : List α)
    (h : l.length ≤ maxCands) : (Capped.ofListTake l).val = l := by
  simpa [Capped.ofListTake] using List.take_of_length_le h

theorem Capped.ofListTake_is_a_prefix {α : Type} (l : List α) :
    (Capped.ofListTake l).val <+: l := List.take_prefix _ _

/-- The producer's constructor: one more entry, refused at the cap. -/
def Capped.cons? {α : Type} (a : α) (c : Capped α) : Option (Capped α) :=
  if h : (a :: c.val).length ≤ maxCands then some ⟨a :: c.val, h⟩ else none

theorem Capped.cons?_refuses_past_the_cap {α : Type} (a : α) (c : Capped α)
    (h : c.val.length = maxCands) : Capped.cons? a c = none := by
  unfold Capped.cons?
  rw [dif_neg (by simp [h])]

/-- `view ∘ set = id` for the bounded-list setter (R11). -/
theorem Capped.val_cons? {α : Type} (a : α) (c c' : Capped α) (h : Capped.cons? a c = some c') :
    c'.val = a :: c.val := by
  unfold Capped.cons? at h
  split at h
  · injection h with h; exact congrArg Subtype.val h.symm
  · exact absurd h (by simp)

/-! ## `SegKind` — eleven variants, the batch bounded -/

/-- The members one `SegKind.batch` gathers (fork `SegKind::Batch(Vec<Id>)`), bounded (R10). -/
abbrev BatchIds := { l : List Id // l.length ≤ maxBatch }

/-- The smart constructor.  A batch is never built by hand. -/
def mkBatch? (ids : List Id) : Option BatchIds :=
  if h : ids.length ≤ maxBatch then some ⟨ids, h⟩ else none

theorem mkBatch?_refuses_too_many_members (ids : List Id) (h : maxBatch < ids.length) :
    mkBatch? ids = none := by
  unfold mkBatch?
  rw [dif_neg (by omega)]

theorem mkBatch?_accepts (ids : List Id) (h : ids.length ≤ maxBatch) :
    (mkBatch? ids).map Subtype.val = some ids := by
  unfold mkBatch?
  rw [dif_pos h]
  rfl

/-- **The total constructor a row builder needs**, in `Capped.ofListTake`'s own shape: a
`SegKind.batch` is built inside `dayRows`, where there is no `Except` to refuse into and D28
forbids a refusal family, so the bound is taken rather than checked.  `mkBatch?` stays and is
still the decoder's: a wire value that is too long is *refused*, and a group the planner built
is *truncated* — two different questions about the same bound, which is why there are two
constructors and not one with two readings (AGENTS §5.6).

**The truncation never fires on a produced day** (README gap **1900**, closed at W-38 for the day's
rows): its only caller is step 5's `assignedSeg`, and every group step 5 gives a slot is a bounded
batch (`PlanFold.a_filled_slot_assigns_its_groups_members`); `batchIdsOf_of_bounded` below is the
subdomain form (AGENTS §3.1 item 4). -/
def batchIdsOf (ids : List Id) : BatchIds :=
  ⟨ids.take maxBatch, by
    rw [List.length_take]; omega⟩

/-- **And it is the identity on a list the bound already fits** — so a batch row of a group
`PlanReq.a_group_is_a_bounded_batch` covers carries its members and nothing less. -/
theorem batchIdsOf_of_bounded (ids : List Id) (h : ids.length ≤ maxBatch) :
    (batchIdsOf ids).val = ids := by
  show ids.take maxBatch = ids
  exact List.take_of_length_le h

/-- **A truncation loses only the tail** — the half that is true whether or not the bound
fires, and the one `Seg.items` needs. -/
theorem batchIdsOf_is_a_prefix (ids : List Id) : (batchIdsOf ids).val <+: ids :=
  List.take_prefix _ _

/-- **Fork `planner::SegKind`, and §12.1's ghost row.**  Ten of the eleven are the fork's;
`ghost` is the arrival plan the day bar draws behind today's (`.tm/arrival_plan.json`), which
the fork carries as a `SegFlags` bit and which is a *kind* of row, not a mark on one. -/
inductive SegKind
  | block
  | batch (ids : BatchIds)
  | brk
  | routine
  | wall
  | rest
  | optional
  | windDown
  | sleep
  | lost
  | ghost
deriving DecidableEq, Repr

/-- Fork `SegKind::is_work`: the two kinds that spend the block budget. -/
def SegKind.isWork : SegKind → Bool
  | .block => true
  | .batch _ => true
  | _ => false

/-! ## `Note` — what the planner says in prose, named: fork `notes.push`'s sites and
`SegFlags::note`'s sentences, one constructor per site (AGENTS §5.7, "every diagnostic is
named"), the text kept where the terminal is (D30 Q6) — `Emit.noteText` renders them. -/
inductive Note
  /-- `planner.rs:927` — "travel day: no blocks planned (`travel-day` wall today)". -/
  | travelDay
  /-- `planner.rs:1055` — "<id>: no free <dur>m position in <lo>–<hi>; not planned today".
  `lo` and `hi` are absolute seconds, like every other instant here. -/
  | noPosition (id : Id) (durMin lo hi : Nat)
  /-- `planner.rs:2217` — "budget spent: <n> blocks done, the rest of the day is rest". -/
  | budgetSpent (blocksDone : Nat)
  /-- `planner.rs:2646` — "planned <a> of <b> (<p>%)". -/
  | plannedOf (planned total : Nat)
  /-- `planner.rs:1783` — "buffer before <title>", the row a `buffer:` puts in front of a wall.
  The **id** is carried, not the title: a title is text and text is `Emit.lean`'s (D30 Q6). -/
  | bufferBefore (id : Id)
  /-- `planner.rs:1796` — "travel day", on the wall that zeroed the budget. -/
  | travelDayWall
  /-- `planner.rs:2054` — "paused", on a replayed `Pause` segment. -/
  | paused
  /-- `planner.rs:1771`, `planner.rs:2061` — "interruption", on the running interruption's own
  row and on a replayed `Interrupt` segment. -/
  | interruption
  /-- `planner.rs:2065` — a replayed `Break`'s `where`, **the log's own text played back**.
  It is not a new wire value: it reached the kernel inside `Replay.Segment` and R10 bounded it
  at the log line it was read from. -/
  | breakWhere (text : List Char)
  /-- `planner.rs:2076` — a replayed `Idle`'s attribution, the log's own text likewise. -/
  | idleAttributed (text : List Char)
  /-- `planner.rs:1748` — "running · <n>m left", on §8.2 choice 5b's reservation (step P3). -/
  | runningLeft (leftMin : Nat)
  /-- `planner.rs:2026` — "<n>m so far", on `open_block_segment`'s worked stretch (W-34). -/
  | soFar (workedMin : Nat)
deriving DecidableEq, Repr

/-! ## `SegFlags` — the marks, and only the marks

AGENTS §4: a `Bool` predicate on a plain record, never a dependent proof field.  The fork's
`SegFlags` also carries `planned_min`, `multiplier` and `note`, which are **values, not
marks**; they live on `Seg` itself so that this record stays what its name says.  `ghost` is a
`SegKind` (above). -/
structure SegFlags where
  /-- `✓` — already logged done. -/
  done      : Bool := false
  /-- `▶` — the block running at `now`. -/
  current   : Bool := false
  /-- `↓` — slot energy exceeds the item's `ci` by ≥ 2 (§8.2 step 5). -/
  underused : Bool := false
  /-- `⚠` — the item is `p = 0` (§7.2). -/
  hot       : Bool := false
  /-- A mandatory window instance (§5.2). -/
  mandatory : Bool := false
  /-- A routine deferred to §8.2 step 6. -/
  deferred  : Bool := false
  /-- Fork `SegFlags::open`: the segment's end is `now` because the thing it records has not
  finished — the running interruption (§9) and the worked stretch of the running block.  §8.3's
  stability law is about *settled* segments; G3's restatement turns on this bit. -/
  isOpen    : Bool := false
deriving DecidableEq, Repr

/-- No marks. -/
def SegFlags.none : SegFlags := {}

/-! ## `Seg` — one row of the day, on absolute seconds -/

/-- **Fork `planner::Segment`, on stage 5's instant representation.**  `start`/`stop` are
absolute seconds — exactly `Look.Slot`'s UTC `[start, stop)` — so a wall that crosses midnight
is representable and no law about this type needs a midnight caveat (gap 256).

`inst` is the `(item, inst)` pair `Replay.Facts.instances` is keyed by; the kernel has no
`InstanceKey` type and does not need one. -/
structure Seg where
  start   : Nat
  stop    : Nat
  kind    : SegKind
  energy  : Option (Fin 6)
  item    : Option Id
  inst    : Option (Id × Id)
  flags   : SegFlags
  /-- Fork `SegFlags::planned_min`: the minutes the planner set aside (`est × multiplier`). -/
  planned : Option Nat
  /-- Fork `SegFlags::multiplier`, exact.  There is no `Float` in this kernel (AGENTS §4). -/
  mult    : Option Arith.Pos
  /-- Fork `SegFlags::note`, named. -/
  note    : Option Note
deriving DecidableEq, Repr

/-- A segment runs forwards and ends inside the calendar.  The horizon is `Cal.Instant.wf`'s
own — there is one bound on a representable instant in this kernel and this is it. -/
def Seg.wf (s : Seg) : Bool := decide (s.start ≤ s.stop) && Cal.Instant.wf ⟨s.stop, 0⟩

/-- A segment the planner may hold. -/
abbrev WfSeg := { s : Seg // Seg.wf s = true }

/-- Why a segment is refused, by name (AGENTS §5.7). -/
inductive SegErr
  | inverted
  | pastTheHorizon
deriving DecidableEq, Repr

/-- The smart constructor.  `Except`, not `Option`: a refusal carries its name to the
boundary (R5). -/
def mkSeg? (s : Seg) : Except SegErr WfSeg :=
  if h : Seg.wf s = true then .ok ⟨s, h⟩
  else if decide (s.start ≤ s.stop) = true then .error .pastTheHorizon else .error .inverted

theorem mkSeg?_refuses_an_inverted_segment (s : Seg) (h : s.stop < s.start) :
    mkSeg? s = .error .inverted := by
  unfold mkSeg? Seg.wf
  rw [dif_neg (by simp [decide_eq_true_eq]; omega), if_neg (by simp; omega)]

theorem mkSeg?_refuses_past_the_horizon (s : Seg) (hle : s.start ≤ s.stop)
    (h : LogStamp.yearEnd ≤ s.stop) : mkSeg? s = .error .pastTheHorizon := by
  unfold mkSeg? Seg.wf Cal.Instant.wf
  simp only [LogStamp.yearEnd] at h
  rw [dif_neg (by simp; omega), if_pos (by simp [hle])]

theorem mkSeg?_accepts (s : Seg) (h : Seg.wf s = true) :
    (mkSeg? s).map Subtype.val = .ok s := by
  unfold mkSeg?
  rw [dif_pos h]
  rfl

/-- Fork `Segment::minutes`.  **`Look.spanMinutes` is the arithmetic, called and not copied**
(AGENTS §5.3, W-14 repair, gap 390): P0 wrote a second body identical to `Look.Slot.minutes`'
and recorded the copy in a doc comment instead of consuming it. -/
def Seg.minutes (s : Seg) : Nat := Look.spanMinutes s.start s.stop

/-- Fork `Segment::items`: every item this segment holds — one, or a batch's members. -/
def Seg.items (s : Seg) : List Id :=
  match s.kind with
  | .batch ids => ids.val
  | _ => s.item.toList

/-! ### Setters, each with its `view ∘ set = id` (R11) -/

/-- §8.2 step 3 gives a slot its energy after the cut. -/
def Seg.withEnergy (s : Seg) (e : Fin 6) : Seg := { s with energy := some e }

theorem Seg.energy_withEnergy (s : Seg) (e : Fin 6) : (s.withEnergy e).energy = some e := rfl

theorem Seg.withEnergy_touches_only_the_energy (s : Seg) (e : Fin 6) :
    s.withEnergy e = { s with energy := some e } := rfl

theorem Seg.wf_withEnergy (s : Seg) (e : Fin 6) : (s.withEnergy e).wf = s.wf := rfl

/-- §8.2 step 6 hangs the un-placed note on the row it belongs to. -/
def Seg.withNote (s : Seg) (n : Note) : Seg := { s with note := some n }

theorem Seg.note_withNote (s : Seg) (n : Note) : (s.withNote n).note = some n := rfl

theorem Seg.withNote_touches_only_the_note (s : Seg) (n : Note) :
    s.withNote n = { s with note := some n } := rfl

theorem Seg.wf_withNote (s : Seg) (n : Note) : (s.withNote n).wf = s.wf := rfl

/-! ## `Diagnostics` — §8.2 step 8, bounded -/
/-- **Why §8.2 step 5 left a listed impossible item without a row** (D67, P58): the walk's own reasons, and `noSlotAdmits` — its filter admits it at no slot of the day (README gap 3523) — named (`PlanReq.dayUnplaced`). -/
inductive NoPlace | noRunLeft | noSlotLeft | budgetSpent | noSlotAdmits deriving DecidableEq, Repr
/-- **Fork `planner::Diagnostics`.**  Nine lists, `dropped_tail`, and §11's two ratios.  `planHonesty` is a numerator over a
denominator and **nothing here divides** (design §11): the fork's `None` is denominator `0`, and Rust renders the percentage. -/
structure Diagnostics where
  underused     : IdList
  aCapacityLost : Nat
  hot           : IdList
  /-- The item and its shortfall in minutes, exact (§7.3). -/
  impossible    : Capped (Id × Nat)
  conflicts     : Capped (Id × Id)
  blocked       : IdList
  deferred      : IdList
  waiting       : IdList
  notes         : Capped Note
  droppedTail   : IdList
  planHonesty   : Nat × Nat
  restDebtMin   : Nat
  /-- **The fork's whole `impossible` tuple** (W-35, README gaps 2640 and 2743): `(id, shortfall_min, until)`, `until` the day the answer carries — a granted answer's due date, a floor answer's last day — which `tm-core/src/emit.rs` prints as `short by DATE`.
  `impossible` above is its first two components (`dayDiagnostics_impossible_is_the_projection`); the pair's readers are older. -/
  impossibleUntil : Capped (Id × Nat × Nat)
  /-- **The fork's whole `underused` tuple**: `(id, slot energy, item ci)`, one per item per underused work row — `emit.rs`'s
  `↓ slot 4, item 3`.  `underused` is its first component (`dayDiagnostics_underused_is_the_projection`). -/
  underusedLevels : Capped (Id × Fin 6 × Fin 6)
  /-- **The fork's whole `blocked` tuple**: `(id, deps)`, the unsatisfied `after:` list —
  `emit.rs`'s `t5 blocked by t4`.  `blocked` is its first component
  (`dayDiagnostics_blocked_is_the_projection`). -/
  blockedDeps : Capped (Id × List Field.Dep)
  /-- **D67 (P58, README gap 3350)**: every listed impossible item step 5 admitted before the walk and left without a row, and why. -/
  unplaced : Capped (Id × NoPlace)
  /-- **§8.2 step 5's served order** (W-38, README gap 3343): `PlanReq.dayServed`, the walk's `(request position, id, ci)`. -/
  served : Capped (Nat × Id × Fin 6)

/-- Nothing wrong with the day yet. -/
def Diagnostics.empty : Diagnostics :=
  ⟨Capped.nil, 0, Capped.nil, Capped.nil, Capped.nil, Capped.nil, Capped.nil, Capped.nil,
   Capped.nil, Capped.nil, (0, 0), 0, Capped.nil, Capped.nil, Capped.nil, Capped.nil, Capped.nil⟩

/-- The accumulation §8.2 step 8 does, one note at a time.  `Option`, because the list is
bounded (R10) and a setter that silently dropped its argument is the defect this kernel exists
to remove. -/
def Diagnostics.withNote (d : Diagnostics) (n : Note) : Option Diagnostics :=
  (Capped.cons? n d.notes).map (fun c => { d with notes := c })

theorem Diagnostics.notes_withNote (d d' : Diagnostics) (n : Note)
    (h : d.withNote n = some d') : d'.notes.val = n :: d.notes.val := by
  unfold Diagnostics.withNote at h
  cases hc : Capped.cons? n d.notes with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some c =>
    rw [hc] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact Capped.val_cons? n d.notes c hc

theorem Diagnostics.withNote_touches_only_the_notes (d d' : Diagnostics) (n : Note)
    (h : d.withNote n = some d') : d' = { d with notes := d'.notes } := by
  unfold Diagnostics.withNote at h
  cases hc : Capped.cons? n d.notes with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some c => rw [hc] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h; rfl

/-- The same, for the dropped tail §9 reports. -/
def Diagnostics.withDropped (d : Diagnostics) (i : Id) : Option Diagnostics :=
  (Capped.cons? i d.droppedTail).map (fun c => { d with droppedTail := c })

theorem Diagnostics.droppedTail_withDropped (d d' : Diagnostics) (i : Id)
    (h : d.withDropped i = some d') : d'.droppedTail.val = i :: d.droppedTail.val := by
  unfold Diagnostics.withDropped at h
  cases hc : Capped.cons? i d.droppedTail with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some c =>
    rw [hc] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    exact Capped.val_cons? i d.droppedTail c hc

theorem Diagnostics.withDropped_touches_only_the_dropped_tail (d d' : Diagnostics) (i : Id)
    (h : d.withDropped i = some d') : d' = { d with droppedTail := d'.droppedTail } := by
  unfold Diagnostics.withDropped at h
  cases hc : Capped.cons? i d.droppedTail with
  | none => rw [hc] at h; exact absurd h (by simp)
  | some c => rw [hc] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h; rfl

/-! ## The plan's identity -/

/-- **Fork `DayPlan::hash`**: a 64-bit FNV-1a digest of the day's placement, which
`state.last_plan_hash` stores and which decides whether a `plan` event is written.  One type
for the produced digest and for the stored comparand: they are one value in two spellings, and
two representations of it would be exactly AGENTS §5.3's defect with a log write behind it. -/
abbrev PlanHash := { n : Nat // n < hashBound }

/-- The digest of a day nothing has been placed in.  P8 replaces every use of this. -/
def PlanHash.zero : PlanHash := ⟨0, by unfold hashBound; omega⟩

/-- `state.last_plan_hash`, decoded: exactly `hashHexLen` hex digits, big-endian.  The hex
reader is `hexDigit` — this kernel has one (R10, AGENTS §5.3). -/
def mkHash? (cs : List Char) : Option PlanHash :=
  if cs.length ≠ hashHexLen then none
  else match cs.foldl (fun a c => a.bind (fun n => (hexDigit c).map (fun d => n * 16 + d)))
      (some 0) with
    | none => none
    | some n => if h : n < hashBound then some ⟨n, h⟩ else none

theorem mkHash?_refuses_a_short_digest (cs : List Char) (h : cs.length ≠ hashHexLen) :
    mkHash? cs = none := by
  unfold mkHash?
  rw [if_pos h]

theorem mkHash?_refuses_a_non_hex_digit :
    mkHash? "00000000000000g0".toList = none := by decide

theorem mkHash?_accepts :
    (mkHash? "00000000000000ff".toList).map Subtype.val = some 255 := by decide

/-! ## §9's runtime state, and the five rows `Look.Today` does not already carry

`store::RuntimeState` has twelve fields.  **Seven of them already cross and are already
bounded**, decoded by `Boundary.readState`/`readWake` into `Look.Today` and `Look.Input`
(step L9, D24's seam): `date` (`Field.parseDate`'s calendar bound), `wake`
(`Look.WakeClock.wf`, refusal `badWake`), `arrival` and `window` (`Field.Clock`, `Fin 1440`),
`loc` (`Look.maxLocName`), `budget`, and `--allow-home` beside them.  Re-declaring any of them
here would be the second copy this module's header is about, so `PlanReq` reads them through
`Look.Input` and only the rest is defined below.

`closed` is the twelfth and is **not** here: `planner.rs` never reads `runtime.closed` (a grep
over the fork's planner finds no use), and the close tranche's request already carries it. -/

/-- §8.1's budget, bounded (R10).  Fork `capacity::budget_blocks` returns an unbounded `u32`
and `state.budget` is an unbounded `Option<u32>`. -/
abbrev Budget := { n : Nat // n ≤ maxBudget }

def mkBudget? (n : Nat) : Option Budget := if h : n ≤ maxBudget then some ⟨n, h⟩ else none

theorem mkBudget?_refuses_an_impossible_budget (n : Nat) (h : maxBudget < n) :
    mkBudget? n = none := by
  unfold mkBudget?
  rw [dif_neg (by omega)]

theorem mkBudget?_accepts (n : Nat) (h : n ≤ maxBudget) :
    (mkBudget? n).map Subtype.val = some n := by
  unfold mkBudget?
  rw [dif_pos h]
  rfl

/-- **Fork `store::ActiveBlock`** — the running block (§9, §8.2 choice 5b).  `started` is an
absolute instant, not a `NaiveTime`: `Seg` is on seconds and the reservation is a segment. -/
structure ActiveBlock where
  id      : Id
  started : Cal.Instant
  estMin  : Nat
  paused  : Bool
deriving DecidableEq, Repr

/-- A running block planned within the host's width, `Look.maxPlanMinutes` — the fork's `u32` (D81, README gap 3902).
Its START is not bounded by `now` since W-41: D78 plans a start after `now` FROM `now`, as fork 4748911 plans it. -/
def ActiveBlock.wf (a : ActiveBlock) : Bool :=
  decide (a.estMin ≤ Look.maxPlanMinutes)

abbrev WfActive : Type := { a : ActiveBlock // ActiveBlock.wf a = true }

def mkActive? (a : ActiveBlock) : Option WfActive :=
  if h : ActiveBlock.wf a = true then some ⟨a, h⟩ else none

theorem mkActive?_refuses_an_estimate_past_the_width (a : ActiveBlock)
    (h : Look.maxPlanMinutes < a.estMin) : mkActive? a = none := by
  unfold mkActive? ActiveBlock.wf
  rw [dif_neg (by simp; omega)]

/-- **D81 (gap 3902): a running estimate past the day is read** — `tm extend 24h` stores 1,500 minutes and the fork
plans them.  mkActive?_refuses_an_estimate_past_the_day said the day's 1,440 refused it until W-41; this refutes it. -/
theorem mkActive?_reads_an_estimate_past_the_day :
    (mkActive? ⟨['m','1'], ⟨0, 0⟩, Look.maxDayMin + 60, false⟩).map Subtype.val
      = some ⟨['m','1'], ⟨0, 0⟩, 1500, false⟩ := by decide

/-- Fork `state.break.where`, named (AGENTS §5.7) rather than left a free `String`. -/
inductive BreakPlace | walk | seat | bed | phone
deriving DecidableEq, Repr

/-- The place's own word, the one `PlanWire.placeOf?` reads (`PlanWire.placeOf_reads_the_word`, W-35). -/
def BreakPlace.word : BreakPlace → List Char
  | .walk => "walk".toList | .seat => "seat".toList | .bed => "bed".toList | .phone => "phone".toList

/-- **Fork `store::BreakState`** — the running break. -/
structure BreakState where
  started    : Option Cal.Instant
  plannedMin : Nat
  place      : Option BreakPlace
deriving DecidableEq, Repr

/-- A break started at or before `now`, planned within the host's width (`Look.maxPlanMinutes`, D81 gap 3902). -/
def BreakState.wf (now : Cal.Instant) (b : BreakState) : Bool :=
  b.started.all (fun t => decide (t.sec ≤ now.sec)) && decide (b.plannedMin ≤ Look.maxPlanMinutes)

abbrev WfBreak (now : Cal.Instant) := { b : BreakState // BreakState.wf now b = true }

def mkBreak? (now : Cal.Instant) (b : BreakState) : Option (WfBreak now) :=
  if h : BreakState.wf now b = true then some ⟨b, h⟩ else none

/-- The design's name for this row is `refuses_a_negative_break`, which **cannot be stated**:
the fork's field is a `u32` and this one is a `Nat`, so there is no negative break to refuse
and a theorem of that name would be a precondition nothing can satisfy (AGENTS §5.2, §9.2's
disguised-gap list).  The real bound is the host's width, the fork's `u32` (D81, gap 3902). -/
theorem mkBreak?_refuses_a_break_past_the_width (now : Cal.Instant) (b : BreakState)
    (h : Look.maxPlanMinutes < b.plannedMin) : mkBreak? now b = none := by
  unfold mkBreak? BreakState.wf
  rw [dif_neg (by simp; omega)]

/-- **D81 (gap 3902): a break planned past the day is read** — `tm break 25h` stores 1,500 minutes and the fork plans
it.  mkBreak?_refuses_a_break_longer_than_a_day said the day refused it until W-41; this refutes it. -/
theorem mkBreak?_reads_a_break_past_the_day :
    (mkBreak? ⟨0, 0⟩ ⟨none, Look.maxDayMin + 60, none⟩).map Subtype.val = some ⟨none, 1500, none⟩ := by decide

/-- **A running break's start after `now` stays REFUSED by name** (`badBreak wf`), and D78 does not reach it: the log
holds no line for a running break, so the host reads its start off `.tm/state.json`'s `HH:MM` as the LATEST instant at
or before `now` with that clock (D81, README gap 3820) and no request the binary builds carries one after `now`.  One
that arrives is a host that did not read it so, and the refusal says so rather than plan a break that has not begun. -/
theorem mkBreak?_refuses_a_start_after_now (now : Cal.Instant) (b : BreakState)
    (t : Cal.Instant) (hs : b.started = some t) (h : now.sec < t.sec) :
    mkBreak? now b = none := by
  unfold mkBreak? BreakState.wf
  rw [dif_neg (by rw [hs]; simp; omega)]

theorem mkBreak?_accepts (now : Cal.Instant) (b : BreakState)
    (h : BreakState.wf now b = true) : (mkBreak? now b).map Subtype.val = some b := by
  unfold mkBreak?
  rw [dif_pos h]
  rfl

/-- **Fork `store::InterruptState`** — the running interruption, which §8.2 choice 1 places as an ad-hoc wall from
`t_i` to `now` and which does **not** extend the window.  **No smart constructor since W-41**: its `wf` bounded the
start by `now` and nothing else, and the owner's D78 reads a start after `now` as fork 4748911 does — `collect_walls`
pushes the wall only `if self.now > start`, which `interruptRows` already is — so it draws and pauses nothing, and the
bound went with its refusal.  Both fields keep their readers' bounds (`PlanWire.instantWithin`, `EmitWire.idWithin`). -/
structure InterruptState where
  started : Option Cal.Instant
  id      : Option Id
deriving DecidableEq, Repr

/-- **mkActive?_refuses_a_start_after_now is REFUTED** (D78, README gap 2874's input 1): the constructor builds a block
whose start is after a `now`, so a running block's logged start ahead of the clock is no longer refused. -/
theorem mkActive?_refuses_a_start_after_now_is_refuted :
    ¬ ∀ (now : Cal.Instant) (a : ActiveBlock), now.sec < a.started.sec → mkActive? a = none :=
  fun h => absurd (h ⟨0, 0⟩ ⟨['m','1'], ⟨10, 0⟩, 60, false⟩ (by decide))
    (by decide)

/-- `state.priorities_yesterday`, decoded (§7.4).  Each stored `p` goes through
`yesterdayOf?` — the kernel's one reader of a stored priority — and the length is refused
**before** the map runs, so a wire-sized list is measured once and never walked twice.
D9-21: the only recursion is core's `List.length` and `List.mapM`. -/
def mkYesterday? (ps : List (Id × Nat)) : Option (Capped (Id × Fin 8)) :=
  if ps.length ≤ maxCands then
    (ps.mapM (fun p => (yesterdayOf? p.2).map (fun v => (p.1, v)))).bind Capped.ofList?
  else none

theorem mkYesterday?_refuses_a_priority_past_seven (ps : List (Id × Nat)) (i : Id) (n : Nat)
    (hmem : (i, n) ∈ ps) (h : 8 ≤ n) : mkYesterday? ps = none := by
  unfold mkYesterday?
  have hm : ps.mapM (fun p => (yesterdayOf? p.2).map (fun v => (p.1, v))) = none := by
    induction ps with
    | nil => cases hmem
    | cons a as ih =>
      rcases List.mem_cons.mp hmem with rfl | hmem'
      · simp [List.mapM_cons, yesterdayOf?_refuses_eight n h]
      · cases ha : (yesterdayOf? a.2).map (fun v => (a.1, v)) with
        | none => simp [List.mapM_cons, ha]
        | some _ => simp [List.mapM_cons, ha, ih hmem']
  split
  · rw [hm]; rfl
  · rfl

theorem mkYesterday?_refuses_too_many (ps : List (Id × Nat)) (h : maxCands < ps.length) :
    mkYesterday? ps = none := by
  unfold mkYesterday?
  rw [if_neg (by omega)]

/-- **§9's five remaining rows**, decoded.  The other seven are `Look.Today`'s and are read
through `PlanReq.look` (see this section's opening comment). -/
structure RuntimeIn where
  active    : Option ActiveBlock
  brk       : Option BreakState
  interrupt : Option InterruptState
  lastHash  : Option PlanHash
  yesterday : Capped (Id × Fin 8)
  worked    : Option (Fin (Look.maxPlanMinutes + 1))  -- the host's worked minutes (W-36, gap 2920; W-41's width)
/-- Nothing running, nothing planned yet. -/
def RuntimeIn.empty : RuntimeIn := ⟨none, none, none, none, Capped.nil, none⟩

/-- The item the running block holds, if any — the exception five of §8.3's laws are restated
around (design §6.3, D29). -/
def RuntimeIn.activeId (s : RuntimeIn) : Option Id := s.active.map (·.id)

theorem RuntimeIn.activeId_empty : RuntimeIn.empty.activeId = none := rfl

/-! ## §9.1's what-if overrides -/

/-- **Fork `planner::PlanOverrides`** — the est / extra-block / drop overrides behind §9.1's
overtime prompt.  Nothing is written anywhere: they live for one call. -/
structure PlanOverrides where
  estMin   : Capped (Id × Nat)
  extraMin : Capped (Id × Nat)
  drop     : IdList

def PlanOverrides.empty : PlanOverrides := ⟨Capped.nil, Capped.nil, Capped.nil⟩

/-- Fork `PlanOverrides::is_empty`. -/
def PlanOverrides.isEmpty (o : PlanOverrides) : Bool :=
  o.estMin.val.isEmpty && o.extraMin.val.isEmpty && o.drop.val.isEmpty

theorem PlanOverrides.isEmpty_empty : PlanOverrides.empty.isEmpty = true := rfl

/-- The decoder (R10).  Each list is bounded by the candidate cap. -/
def mkOverrides? (est extra : List (Id × Nat)) (drop : List Id) : Option PlanOverrides := do
  let e ← Capped.ofList? est
  let x ← Capped.ofList? extra
  let d ← Capped.ofList? drop
  return ⟨e, x, d⟩

theorem mkOverrides?_refuses_too_many_estimates (est extra : List (Id × Nat)) (drop : List Id)
    (h : maxCands < est.length) : mkOverrides? est extra drop = none := by
  unfold mkOverrides?
  rw [Capped.ofList?_refuses_past_the_cap est h]
  rfl

theorem mkOverrides?_refuses_too_many_drops (est extra : List (Id × Nat)) (drop : List Id)
    (h : maxCands < drop.length) : mkOverrides? est extra drop = none := by
  unfold mkOverrides?
  cases he : Capped.ofList? est with
  | none => rfl
  | some e =>
    cases hx : Capped.ofList? extra with
    | none => simp
    | some x => simp [Capped.ofList?_refuses_past_the_cap drop h]

/-! ## §8.2 step 2's input, declared here because the request carries it -/

/-- **Fork `priority::Candidate`'s routine half** — the per-instance facts `collect_routines`
reads and the kernel cannot yet derive: which item, which instance, the occurrence's own window
in absolute seconds, the minutes it still needs, and §5.2's mandatory flag.

`pref:` and the daily `win:` hours are **not** here: they are the item's, the item is in the
request, and taking them from the host would be a second reading of the plan (AGENTS §5.3). -/
structure RoutineIn where
  id        : Id
  inst      : Option Id
  winLo     : Nat
  winHi     : Nat
  durMin    : Nat
  mandatory : Bool
deriving DecidableEq, Repr

/-! ## `DayPlan` — the whole day, past and future -/

/-- **Fork `planner::DayPlan`.**  `window` is the pair of absolute seconds the plan used;
`priorities` is §7's answer for the Queue and `--explain`; `planHash` is the identity
`state.last_plan_hash` compares against.

The provisional form dropped `diagnostics`, `priorities` and the hash on the grounds that "no
§8.3 invariant is about them".  True of §8.3 and false of the stage: `diagnostics` **is** §8.2
step 8, one of the eight steps this stage owns, and the hash decides whether a log line is
written. -/
structure DayPlan where
  day          : Day
  window       : Nat × Nat
  blockMin     : Nat
  budgetBlocks : Nat
  segments     : List WfSeg
  diagnostics  : Diagnostics
  priorities   : Capped (Id × Fin 8)
  planHash     : PlanHash

/-- **Fork `DayPlan::empty`** — a day with its window and its budget and nothing placed. -/
def DayPlan.empty (day : Day) (window : Nat × Nat) (blockMin budgetBlocks : Nat) : DayPlan :=
  ⟨day, window, blockMin, budgetBlocks, [], Diagnostics.empty, Capped.nil, PlanHash.zero⟩

/-- Every item the day assigns, in row order.  (Was `Goals.segItems`.) -/
def segItems (s : WfSeg) : List Id := s.val.items

/-- Every item the day **assigns** — fork `DayPlan::assigned`, which filters
`s.kind.is_work()` (`planner.rs:634`).

**Corrected in step P1** (README gap 345).  P0 wrote this as the flatMap over *every* segment,
which was harmless while the day had no segments and is wrong the moment one is placed: a Wall
row carries the item it is written on, so the P0 form would have reported a meeting as an
assigned task and every goal that reads `assignedOf` — four of the thirteen — would have been
about the wrong set. -/
def assignedOf (d : DayPlan) : List Id :=
  (d.segments.filter (fun s => s.val.kind.isWork)).flatMap segItems

theorem mem_assignedOf (d : DayPlan) (i : Id) :
    i ∈ assignedOf d ↔ ∃ s ∈ d.segments, s.val.kind.isWork = true ∧ i ∈ segItems s := by
  simp [assignedOf, List.mem_flatMap, List.mem_filter, and_assoc]

/-- **A wall is not work**, so no wall row can put its item into `assignedOf` — fork
`SegKind::is_work`, which answers `true` for `Block` and `Batch` and for nothing else. -/
theorem a_wall_is_not_work : SegKind.wall.isWork = false := rfl

/-- The **seconds** the day spends on blocks — §8.3's overbooking law counts these.

**Seconds and not `Seg.minutes`** (W-14 repair, gap 392).  P0 ported `Goals.blockMinutes`
from minutes-since-midnight to absolute seconds and folded `Seg.minutes`, which *floors*:
`Σ ⌊(stop − start)/60⌋ ≤ budget × blockMin` tolerates up to 59 s of unbudgeted work **per
Block row**, where the minutes-since-midnight form it replaced could not express a sub-minute
overrun at all.  That was a silent weakening of plan_does_not_overbook and of
`plan_reserves_one_block_at_a_time`.  Summing seconds and comparing against `budget × blockMin
× 60` is the faithful port: identical on minute-aligned rows, and strictly stronger on the
rows `pastRows` can actually produce, which are clipped at `min stop now` — an arbitrary
second.  `Seg.minutes` stays, because the fork's `Segment::minutes` is what the renderer and
the diagnostics print; it is just not what a budget law is stated over (AGENTS §2545: where
you floor is load-bearing). -/
def blockSeconds (d : DayPlan) : Nat :=
  (d.segments.filter (fun s => decide (s.val.kind = SegKind.block))).foldl
    (fun a s => a + (s.val.stop - s.val.start)) 0

theorem assignedOf_empty (day : Day) (w : Nat × Nat) (bm bb : Nat) :
    assignedOf (DayPlan.empty day w bm bb) = [] := rfl

theorem blockSeconds_empty (day : Day) (w : Nat × Nat) (bm bb : Nat) :
    blockSeconds (DayPlan.empty day w bm bb) = 0 := rfl

/-- **§7's configuration, as one value** — fork `priority::compute`'s `cfg` half: §7.1's bin
ladder, R1's safety factor, `default_priority`, and §7.4's hysteresis switch.  These are
`CapReq.bins`, `CapReq.safety`, `CapReq.dflt` and `CandReq.hysteresis`, which the capacity
section already decodes; each carries its own smart constructor (`binsOf?`, `safetyOf?`,
`defaultPrioOf?`), so **nothing is re-bounded here** — this record only puts the four in one
place so a request carries them once. -/
structure PrioCfg where
  bins   : Bins
  safety : Arith.Pos
  dflt   : Fin 4
  hyst   : Bool
  /-- §16 `[priority] batch_max_min` (default `20`): the largest `remaining` §7.5 will gather
  into another item's block.  It is a **configured count of minutes**, not a wire value: there
  is no `plan` request section yet (`Boundary.lean` names no `PlanReq`), so nothing decodes it
  and R10's bound on it lands with P0's wire half, which is not this step's.  Its R10 statement
  is written down beside the step that will owe it — README gap 801. -/
  batchMaxMin : Nat

/-! ## `PlanReq` — what §9 and the seam make necessary

**What is NOT a field, and why.**  `now`, `tz`, the `[day]` configuration, the curves, the
home cap, the location and `--allow-home` are all already inside `Look.Input` (stage 5 L5/L9),
and the window and the budget are *computed* from it by `Look.day0Window` and `Look.budgetOf`.
Carrying any of them here would be a second copy of a value the kernel already has one reader
of (AGENTS §5.3).  They are reachable as views below, so `r.now` still reads as the design
wrote it while there is exactly one place the value lives. -/
structure PlanReq where
  /-- The plan value, whole-tree loaded. -/
  plan      : WfPlan
  /-- **The seam** (D24, K1): this call's own replay, so the day's past half is reachable
  without a second read of the log (D9). -/
  run       : Seal.Run
  /-- Stage 5's decoded lookahead input: tz, `[day]`, curves, home cap, walls, and today's
  runtime facts in `today0`. -/
  look      : Look.Input
  /-- §9's five rows `Look.Today` does not carry. -/
  state     : RuntimeIn
  /-- **§8.2 step 4's candidates, host-collected** (stage 6 P4), each with §7.3's floor —
  exactly the pair `capacity.candidates.items` already carries (`Boundary.readCandFloor`).
  Which items are candidates is D27's, and D27 is **not** this step (D34): these arrive on the
  wire as they do today, and the step ranks them.  Bounded by `Capped` at `maxCands`, which is
  the wire's own guard (`Boundary.maxCandidates`) — **reused rather than re-bounded** (R10).-/
  cands     : Capped (Look.Cand × Option Look.Floor)
  /-- **§7's configuration**, the four values the capacity section already decodes
  (`CapReq.bins`/`safety`/`dflt` and `CandReq.hysteresis`).  Each is stage 5's own bounded
  type with its own smart constructor; none is re-bounded here. -/
  prio      : PrioCfg
  /-- **§8.2 step 2's window instances, host-collected** (stage 6 P2).  Which occurrences are
  due today is F2's recurrence expansion — track **K3**, not built — so until the owner's D27
  lands these arrive with the request, refused one at a time by `mkRoutines?`.  Bounded at the
  candidate cap (R10). -/
  routines  : Capped RoutineIn
  /-- §9.1's what-if overrides, on a consequence replan. -/
  overrides : Option PlanOverrides

/-- The day being planned. -/
def PlanReq.today (r : PlanReq) : Day := r.look.today
/-- The instant the plan is made at.  One storage site: `Look.Today.now`. -/
def PlanReq.now (r : PlanReq) : Cal.Instant := r.look.today0.now
def PlanReq.tz (r : PlanReq) : Cal.Tz := r.look.tz
def PlanReq.day (r : PlanReq) : Look.DayCfg := r.look.day
def PlanReq.blockMin (r : PlanReq) : Nat := r.look.day.cut.blockMin
def PlanReq.curves (r : PlanReq) : Look.Curves := r.look.curves
def PlanReq.homeMax (r : PlanReq) : Nat := r.look.homeMax
def PlanReq.loc (r : PlanReq) : List Char := r.look.today0.loc
def PlanReq.allowHome (r : PlanReq) : Bool := r.look.today0.allowHome

/-- Today's record inside **this call's own replay** (D24's seam, `PlanReq.run`): the past half, `blocks_done` and
the planner's logged arrival all come from here, never from a second read of the log (D9). -/
def PlanReq.todayRecord (r : PlanReq) : Option Replay.DayAcc :=
  (r.run.answer.days.find? (fun d => decide (d.day = r.today))).bind (·.record)
/-- **The day's first logged `arrive`**, off `todayRecord` — fork `Planner::new`'s fall-back to the replay's day record
when the state stores no arrival, read by `PlanReq.window` through `Look.Today.planArrivalSec` (README gap 3390). -/
def PlanReq.loggedArrival (r : PlanReq) : Option Cal.Instant := (r.todayRecord.bind (·.arrival)).map (·.1)

/-- §8.1's window as the fork's PLANNER reads it (`Planner::window_and_budget`, README gaps 320 and 3341): the window stored for
`plan_date`'s day (`Look.Today.planWindow`: a state naming no day is today's, and no budget is needed beside it), its end 24 HOURS
later when earlier than its start (fork `end += Duration::days(1)`; until W-40 the NEXT day's clock, README gap 3782); else §8.1's formula from `Planner::new`'s arrival (`Look.Today.planArrivalSec` over `loggedArrival`, gap 3390), extended by the day's walls CLIPPED to it (`Look.wallsClippedOn`, fork `collect_walls`; gap 3556). -/
def PlanReq.window (r : PlanReq) : Nat × Nat := match r.look.today0.planWindow r.look.today with
  | some w => ((Cal.instantOf r.look.tz r.look.today w.1).sec, (Cal.instantOf r.look.tz r.look.today w.2).sec + (if w.2 < w.1 then 86400 else 0)) | none => Look.windowFrom r.look.tz (r.look.today0.planArrivalSec r.look.today r.look.tz r.loggedArrival) (Look.windowMinOf r.look.day.windowHours) r.look.day.windowCap (Look.wallsClippedOn (Cal.instantOf r.look.tz r.look.today 0).sec (Cal.instantOf r.look.tz (r.look.today + 1) 0).sec r.look.walls r.look.today)

/-- §8.1's budget as the fork's planner reads it: the one stored for `plan_date`'s day, with or without a window
(`Look.Today.planBudget`, gap 320), else the formula (`Look.budgetOf`, stage 5 L2).  Never recomputed here. -/
def PlanReq.budgetBlocks (r : PlanReq) : Nat :=
  match r.look.today0.planBudget r.look.today with
  | some b => b
  | none => Look.budgetOf r.look.day.windowHours r.look.day.cut.blockMin r.look.day.budgetRatio

-- The view law that equated this with day 0's capacity window is false on a window crossing midnight (gap 3341), on a
-- state naming no day and on a window with no budget beside it (gap 320); the end of this file states where it holds.

theorem PlanReq.budget_is_the_stored_one_when_there_is_one (r : PlanReq) (b : Nat)
    (h : r.look.today0.planBudget r.look.today = some b) : r.budgetBlocks = b := by
  unfold PlanReq.budgetBlocks
  rw [h]

theorem PlanReq.budget_is_the_formula_without_a_budget_on_its_day (r : PlanReq)
    (h : r.look.today0.planBudget r.look.today = none) :
    r.budgetBlocks =
      Look.budgetOf r.look.day.windowHours r.look.day.cut.blockMin r.look.day.budgetRatio := by
  unfold PlanReq.budgetBlocks
  rw [h]

/-- §8.4's lookahead, in the exact units §7.3's pass reserves over — **`Look.lookahead` of this
request's own input, and never a field** (step P4, AGENTS §5.3).

P0 carried it as `caps : Lookahead`, on design §5.4's row, and nothing read it for four steps.
The moment step 4 does, a carried lookahead is a **second answer** to a question `Look.Input`
already settles: a host could send a `caps` that is not `Look.lookahead r.look`, the ranking
would be computed over it, and `tm plan`'s order would disagree with the `lookahead.grants` of
the very same call — the class this kernel exists to remove.  The field is gone and this view
is in its place, which is exactly what the section header above says about `window` and
`budgetBlocks`.  `Look.lookahead_is_a_lookahead` (stage 5) is what makes the view total: the
days it produces ascend and `capDen` is positive, so `lookaheadOf?` cannot answer `none`. -/
def PlanReq.edfDays (r : PlanReq) : List DayCapacity := Look.lookahead r.look

/-- The same list under the EDF pass's own subtype, with the denominator §7.3 reserves over. -/
def PlanReq.caps (r : PlanReq) : Lookahead :=
  (lookaheadOf? Look.capDen (Look.lookahead r.look)).get (Look.lookahead_is_a_lookahead r.look)

theorem PlanReq.edfDays_is_the_lookaheads (r : PlanReq) : r.edfDays = Look.lookahead r.look := rfl

/-- What an accepted `lookaheadOf?` carries: the days it was given, over the denominator it was
given.  Stage 5 states the *refusals* (`lookaheadOf?_refuses_a_zero_denominator`,
`…_refuses_unsorted_days`) and the length of an acceptance; this is the acceptance's own
identity, which is what makes `PlanReq.caps` a view rather than a value of its own. -/
theorem lookaheadOf?_is_what_it_was_given {den : Nat} {days : List DayCapacity} {la : Lookahead}
    (h : lookaheadOf? den days = some la) : la.val.2 = days ∧ la.val.1.val = den := by
  unfold lookaheadOf? at h
  split at h
  · rename_i d hd
    split at h
    · cases h
      refine ⟨rfl, ?_⟩
      unfold denOf? at hd
      split at hd
      · cases hd; rfl
      · exact absurd hd (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The view's days **are** `edfDays`: there is one list, not two. -/
theorem PlanReq.caps_days (r : PlanReq) : r.caps.val.2 = r.edfDays :=
  (lookaheadOf?_is_what_it_was_given
    (Option.some_get (Look.lookahead_is_a_lookahead r.look)).symm).1

/-- And its denominator is `capDen` — the one `Look.prioritiesWithFloors` reserves over.  Without
this the pass could be handed a lookahead built over a different unit and would silently use
`capDen` anyway (`Look.passLeft`), which is a wrong *value*, not a missing one. -/
theorem PlanReq.caps_den (r : PlanReq) : r.caps.val.1.val = Look.capDen :=
  (lookaheadOf?_is_what_it_was_given
    (Option.some_get (Look.lookahead_is_a_lookahead r.look)).symm).2

/-! ### The pass, declared ahead of §8.2 step 2 (W-37 track R, README gap 2870)

**Moved here from §8.2 step 4's section, body unchanged**, because §8.2 step 2's routine rows now
read it: fork `emit_segments` marks a scheduled window task's Routine row `⚠` at `prios[i].p == 0`
(`planner.rs:1493`), and `PlanReq.routineHot` is that reading of this pass.  A definition cannot be
called above the line that declares it, and a second copy of the pass nearer the routines would be
AGENTS §5.3's defect; so the pass moved and the section below it (step 4) still calls it by name. -/

/-- **§8.2 step 4.**  The answers to this request's candidates: `Look.prioritiesWithFloors`
over this request's own lookahead, in request order, one per candidate. -/
def PlanReq.candAnswers (r : PlanReq) : List Look.FloorOut :=
  Look.prioritiesWithFloors r.prio.bins r.prio.safety r.prio.dflt r.prio.hyst r.edfDays
    r.cands.val

/-- **The pass is stage 5's, called and not copied.** -/
theorem PlanReq.candAnswers_is_the_lookaheads (r : PlanReq) :
    r.candAnswers = Look.prioritiesWithFloors r.prio.bins r.prio.safety r.prio.dflt r.prio.hyst
      (Look.lookahead r.look) r.cands.val := rfl

/-- **And it is the same expression the capacity op answers `lookahead.grants` with**
(`Boundary.grantsOf c la q = Look.prioritiesWithFloors c.bins c.safety c.dflt q.hysteresis la
q.items`, at `la = Look.lookahead c.look`).  Stated as the equation a reader can check against
`Boundary.lean` by eye: same four configuration values, same lookahead, same items.  A day whose
ranking disagreed with the `grants` of the very same call is the defect this kernel exists to
remove, and there is now no way to write it — the lookahead is a view (`PlanReq.caps`), not a
field, and the pass is one function. -/
theorem PlanReq.candAnswers_is_the_capacity_ops_own_grants (r : PlanReq) (bins : Bins)
    (s : Arith.Pos) (dflt : Fin 4) (hy : Bool) (la : List DayCapacity)
    (items : List (Look.Cand × Option Look.Floor))
    (hb : bins = r.prio.bins) (hs : s = r.prio.safety) (hd : dflt = r.prio.dflt)
    (hh : hy = r.prio.hyst) (hl : la = Look.lookahead r.look) (hi : items = r.cands.val) :
    Look.prioritiesWithFloors bins s dflt hy la items = r.candAnswers := by
  subst hb; subst hs; subst hd; subst hh; subst hl; subst hi; rfl

/-- One answer per candidate, in request order. -/
theorem PlanReq.candAnswers_length (r : PlanReq) :
    r.candAnswers.length = r.cands.val.length :=
  Look.prioritiesWithFloors_length _ _ _ _ _ _

/-- The answers are as bounded as the candidates: `maxCands` is `Capped`'s and the pass is
length-preserving, so nothing here needs a second bound (R10). -/
theorem PlanReq.candAnswers_capped (r : PlanReq) : r.candAnswers.length ≤ maxCands := by
  rw [r.candAnswers_length]; exact r.cands.property

/-- The answer for an id, if the request sent one.  **First by id**, which is the shape
`PlannerWit.plan_never_drops_an_impossible_item_as_stage_6_wrote_it_is_refuted` states its
hypothesis in (the goal it was written for left `Goals.lean` at W-32); §5.3's carried instance
and today's fresh one share an id, and the fork pairs by *index* (`priority::prio_at`) for
exactly that reason, so an id that names two is answered here by the first. -/
def PlanReq.answerFor (r : PlanReq) (i : Id) : Option Look.FloorOut :=
  r.candAnswers.find? (fun o => o.out.cand.id == i)

/-- Why a plan request is refused, by name (AGENTS §5.7, design §10.3).  **There is no
`planCheckFailed`**: D28 proves the eleven single-run laws rather than gating on them, and a
gate a proved lift makes unreachable is §9.2's "check no input can fail". -/
inductive PlanErr
  | badState
  | badBudget
  | badActive
  | badBreak
  | badInterrupt
  | badHash
  | badOverride
  | badSegment (e : SegErr)
  | tooManyCands
deriving DecidableEq, Repr

/-! ############################################################################
## §8.2 step 1 — the walls (stage 6, step P1)

APPENDED 2026-09-17 (stage 6, track P, step P1; design §14.2's P1 row).

**Nothing here computes a wall.**  `Look.wallOfEntity` ran once, at the boundary, inside
`Look.wallIndex` — `readCapacity_ok` proves the request's index *is* the loaded plan's — and
this step selects today's from it with `Look.wallIxOn`, which is `Look.wallsOn`'s own
selection with the projection left off (`Look.wallsOn_eq_map_wallIxOn`).  §8.1's window and
L3's cut read the same list through `wallsOn`, so the day's window, the day's slots and the
day's *rows* cannot disagree about which walls are today's.  A second `wallOfEntity` would be
AGENTS §5.3's defect with a calendar behind it.

**What step 1 is**, from fork `planner.rs`: `collect_walls` (clip to the day, the ad-hoc
interruption wall, the sort), `wall_conflicts` (each overlapping pair once, unresolved),
the `travel-day` zeroing of the remaining budget, and `emit_segments`' wall loop (the
`buffer:` row in front of the event's own row).  `past_segments` comes with it, because the
fork's day is the replay's past joined to the plan's future and P1 is the step that first
produces a row at all.
-/

/-! **The horizon is `LogStamp.yearEnd` and nothing else** (AGENTS §5.3, W-14 repair, gap 391).
P0 wrote the bound as a bare literal in `mkSeg?_refuses_past_the_horizon` and P1 then added a
third spelling, `Planner.horizonSec`, beside it — while stage 5 had already named the same
number once, in `LogStamp.yearEnd`, with the same doc comment.  Both stage-6 copies are gone;
this module consumes stage 5's name, and the two theorems below pin it to the bound it claims
to be, so a change to `Cal.Instant.wf`'s own literal cannot pass silently. -/

theorem instant_wf_of_sec (n : Nat) (h : n < LogStamp.yearEnd) :
    Cal.Instant.wf ⟨n, 0⟩ = true := by
  simp only [Cal.Instant.wf, LogStamp.yearEnd] at *
  simp [h]

/-- The other side of the same pin: the horizon itself is **not** representable, so
`LogStamp.yearEnd` is exactly `Cal.Instant.wf`'s bound and not merely below it. -/
theorem the_horizon_is_cal_instants_own_bound :
    Cal.Instant.wf ⟨LogStamp.yearEnd, 0⟩ = false := by
  simp [Cal.Instant.wf, LogStamp.yearEnd]

/-- **Every row the day holds ends inside the calendar** — the `Seg.wf` bit read back, which is
what lets a comparison against a `clampSec`ed instant be decided rather than assumed. -/
theorem WfSeg.stop_lt_yearEnd (s : WfSeg) : s.val.stop < LogStamp.yearEnd := by
  have h := s.property
  unfold Seg.wf at h
  simp only [Bool.and_eq_true] at h
  have h2 := h.2
  simp only [Cal.Instant.wf, Bool.and_eq_true, decide_eq_true_eq] at h2
  simp only [LogStamp.yearEnd]
  omega

/-- **And it runs forwards**, the other half of the same bit. -/
theorem WfSeg.start_le_stop (s : WfSeg) : s.val.start ≤ s.val.stop := by
  have h := s.property
  unfold Seg.wf at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem Seg.wf_of (s : Seg) (h1 : s.start ≤ s.stop) (h2 : s.stop < LogStamp.yearEnd) :
    Seg.wf s = true := by
  simp [Seg.wf, instant_wf_of_sec _ h2, h1]

/-- A second inside the calendar. -/
def clampSec (n : Nat) : Nat := min n (LogStamp.yearEnd - 1)

theorem clampSec_lt (n : Nat) : clampSec n < LogStamp.yearEnd := by
  simp only [clampSec, LogStamp.yearEnd]; omega

theorem clampSec_id (n : Nat) (h : n < LogStamp.yearEnd) : clampSec n = n := by
  simp only [clampSec, LogStamp.yearEnd] at *; omega

/-- **The total constructor the placement steps use** (D28: `dayPlan` is total, so no step of
it may fail).  A row is forced forwards and into the calendar; `segOf_is_the_row_inside_the
_calendar` says the forcing is the identity on every row a day the boundary accepts can
produce, so this is a bound and not a rewrite. -/
def segOf (s : Seg) : WfSeg :=
  ⟨{ s with start := clampSec s.start, stop := max (clampSec s.start) (clampSec s.stop) },
    Seg.wf_of _ (Nat.le_max_left _ _) (Nat.max_lt.2 ⟨clampSec_lt _, clampSec_lt _⟩)⟩

theorem segOf_is_the_row_inside_the_calendar (s : Seg) (h1 : s.start ≤ s.stop)
    (h2 : s.stop < LogStamp.yearEnd) : (segOf s).val = s := by
  have h3 : s.start < LogStamp.yearEnd := by omega
  simp only [segOf, clampSec_id _ h2, clampSec_id _ h3, Nat.max_eq_right h1]

theorem segOf_kind (s : Seg) : (segOf s).val.kind = s.kind := rfl
theorem segOf_item (s : Seg) : (segOf s).val.item = s.item := rfl

/-- **And its items**, which is `kind` and `item` together and so is forced too — the lemma
that lets a law about the ids a *placed* row names be read off the row the planner wrote. -/
theorem segOf_items (s : Seg) : (segOf s).val.items = s.items := rfl

/-- **The forcing only ever shrinks a row**, so every second the placed row covers is a second
the written row covered.  This is what lets a law about `[t.start, t.stop)` be read off the
`WfSeg` the day actually holds. -/
theorem segOf_units (t : Seg) {u : Nat} (h1 : (segOf t).val.start ≤ u)
    (h2 : u < (segOf t).val.stop) : t.start ≤ u ∧ u < t.stop := by
  have e1 : (segOf t).val.start = clampSec t.start := rfl
  have e2 : (segOf t).val.stop = max (clampSec t.start) (clampSec t.stop) := rfl
  rw [e1] at h1
  rw [e2] at h2
  simp only [clampSec, LogStamp.yearEnd] at h1 h2
  omega

/-! ### The day's own bounds, and the one place the request's walls are checked -/

/-- Fork `Planner::day_start`: local midnight. -/
def PlanReq.dayStart (r : PlanReq) : Nat := (Cal.instantOf r.tz r.today 0).sec

/-- Fork `Planner::day_end`: the next local midnight. -/
def PlanReq.dayEnd (r : PlanReq) : Nat := (Cal.instantOf r.tz (r.today + 1) 0).sec

/-- **The request's wall index is the request's own plan's.**

`PlanReq` carries the plan *and* the lookahead input, and the lookahead input carries the
wall index; nothing in the type says the two agree, so a request could name a wall no item
in its plan writes.  The boundary already establishes exactly this for the capacity request
(`Boundary.readCapacity_ok`'s `c.input.walls = wallIndex …`), and `PlanReq` has no decoder
yet (README gap 346), so the laws that cross from a wall row back to the item it is written
on take it as a hypothesis rather than assume it. -/
def PlanReq.wallsAgree (r : PlanReq) : Bool :=
  decide (r.look.walls = Look.wallIndex r.tz r.blockMin r.plan.val)

/-! ### `collect_walls` -/

-- Fork `collect_walls`' clip — `Look.clipWall` since the W-39 repair (README gap 3556): ONE clip, which
-- step 1 places the day's walls through (`wallsOfDay`, below) and §8.1's window reads (`Look.wallsClippedOn`),
-- so the walls the day places and the walls its window flows around cannot part.  It was defined here until
-- then; it moved to `Lookahead.lean` because the window is defined above this section and reads it.  Every
-- mention of `clipWall` below is `Look.clipWall`; the laws about it keep their names
-- (`clipWall_within`, `clipWall_id`, `clipWall_id_inside`).

/-- Fork `collect_walls`' sort: by blocked start, then by id. -/
def wallLe (a b : Look.WallIx) : Bool :=
  decide (a.lo < b.lo) || (decide (a.lo = b.lo) && Log.charsLe a.id b.id)

theorem wallLe_trans (a b c : Look.WallIx) (h₁ : wallLe a b) (h₂ : wallLe b c) : wallLe a c := by
  simp only [wallLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂ ⊢
  rcases h₁ with h₁ | ⟨h₁, hid₁⟩ <;> rcases h₂ with h₂ | ⟨h₂, hid₂⟩
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inl (by omega)
  · exact Or.inr ⟨by omega, Log.charsLe_trans _ _ _ hid₁ hid₂⟩

theorem wallLe_total (a b : Look.WallIx) : wallLe a b || wallLe b a := by
  simp only [wallLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rcases Nat.lt_trichotomy a.lo b.lo with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases Bool.or_eq_true _ _ |>.mp (Log.charsLe_total a.id b.id) with hid | hid
    · exact Or.inl (Or.inr ⟨h, hid⟩)
    · exact Or.inr (Or.inr ⟨h.symm, hid⟩)
  · exact Or.inr (Or.inl h)

/-- A day's walls in the fork's order.  `Replay.insSort` is the **specification** sort —
quadratic and not tail-recursive, kept because it reduces under `decide` — and `sortWallsFast`
is its compiled twin.

**This is gap 394's second half, closed by the W-16 repair step.** The twin was owed from
W-14 and could not be written, because `insSort_eq_mergeSort` needs the order transitive and
total and `wallLe` breaks ties on `Log.charsLe`, which had neither law. The repair proved
`Log.charsLe_trans`, `Log.charsLe_total` and `Log.charsLe_antisymm` **on `Log.charsLe`
itself** — the move AGENTS §5.3 asks for, rather than the second `charsLe` W-16's track A and
K3b each wrote — so the two laws are now available at every call site at once
(README gaps 394 and 581). -/
def sortWalls (l : List Look.WallIx) : List Look.WallIx := Replay.insSort wallLe l

def sortWallsFast (l : List Look.WallIx) : List Look.WallIx := l.mergeSort wallLe

@[csimp] theorem sortWalls_eq_sortWallsFast : @sortWalls = @sortWallsFast := by
  funext l
  exact Replay.insSort_eq_mergeSort wallLe wallLe_trans wallLe_total l

theorem mem_sortWalls {l : List Look.WallIx} {x : Look.WallIx} : x ∈ sortWalls l ↔ x ∈ l :=
  (Replay.insSort_perm wallLe l).mem_iff

/-- **§8.2 step 1's selection, with the request's three numbers as arguments.**  Stage 5's
index, selected for a day (`Look.wallIxOn`), clipped to it, in the fork's order; an empty clip
is dropped (`if e <= s { continue }`).  The request is not a parameter because the rule does
not depend on it — which is also what lets the rule be *run* and checked by `decide`
(`the_spec_days_walls_are_placed_where_they_are_written`; AGENTS §5.2, non-vacuity is a
separate check from correctness). -/
def wallsOfDay (dayLo dayHi d : Nat) (ix : List Look.WallIx) : List Look.WallIx :=
  sortWalls
    ((Look.wallIxOn ix d).filterMap fun x =>
      if (Look.clipWall dayLo dayHi x).lo < (Look.clipWall dayLo dayHi x).hi
      then some (Look.clipWall dayLo dayHi x) else none)

/-- **§8.2 step 1: today's walls.** -/
def wallsToday (r : PlanReq) : List Look.WallIx :=
  wallsOfDay r.dayStart r.dayEnd r.today r.look.walls

theorem wallsToday_is_wallsOfDay (r : PlanReq) :
    wallsToday r = wallsOfDay r.dayStart r.dayEnd r.today r.look.walls := rfl

/-- **The walls the planner places are the walls the window and the cut flowed around.**  Both
sides read `Look.wallIxOn`; this says so as a membership, so a row can always be traced back
to the index entry it came from. -/
theorem mem_wallsToday {r : PlanReq} {c : Look.WallIx} (h : c ∈ wallsToday r) :
    ∃ x ∈ r.look.walls, x.fromDay ≤ r.today ∧ r.today ≤ x.toDay ∧
      c = Look.clipWall r.dayStart r.dayEnd x ∧ c.lo < c.hi := by
  have hm := (Replay.insSort_perm wallLe _).mem_iff.1 h
  simp only [wallsToday, wallsOfDay, List.mem_filterMap] at hm
  obtain ⟨x, hx, hc⟩ := hm
  obtain ⟨hmem, h1, h2⟩ := Look.mem_wallIxOn.1 hx
  by_cases hlt : (Look.clipWall r.dayStart r.dayEnd x).lo < (Look.clipWall r.dayStart r.dayEnd x).hi
  · rw [if_pos hlt] at hc
    have he : Look.clipWall r.dayStart r.dayEnd x = c := Option.some.inj hc
    exact ⟨x, hmem, h1, h2, he.symm, he ▸ hlt⟩
  · rw [if_neg hlt] at hc; exact absurd hc (by simp)

/-- **A clipped wall keeps its id** — the row can name the item it is written on. -/
theorem clipWall_id (lo hi : Nat) (x : Look.WallIx) : (Look.clipWall lo hi x).id = x.id := rfl

/-- **The clip never widens a wall.** -/
theorem clipWall_within (lo hi : Nat) (x : Look.WallIx) :
    x.lo ≤ (Look.clipWall lo hi x).lo ∧ (Look.clipWall lo hi x).hi ≤ max x.hi (max x.lo lo) := by
  cases x
  simp only [Look.clipWall]
  omega

/-- **A wall wholly inside its day is not moved at all** — the hypothesis the restated
`plan_never_moves_a_wall` runs on. -/
theorem clipWall_id_inside (lo hi : Nat) (x : Look.WallIx) (h1 : lo ≤ x.lo) (h2 : x.hi ≤ hi)
    (h3 : x.lo ≤ x.evLo) (h4 : x.lo ≤ x.hi) : Look.clipWall lo hi x = x := by
  have e1 : max x.lo lo = x.lo := by omega
  have e2 : max x.evLo (max x.lo lo) = x.evLo := by omega
  have e3 : max (min x.hi hi) (max x.lo lo) = x.hi := by omega
  unfold Look.clipWall
  rw [e2, e3, e1]

/-! ### The rule, run: §4.3's Monday with a `buffer:` and a clash

AGENTS §5.2: non-vacuity is a **separate** check from correctness, and a theorem whose
hypotheses nothing satisfies is the failure this kernel has already had once.  Every law above
is a ∀ over a request; the two witnesses below are `decide` over the rule itself, so what step
1 does to a real day is *run* and not argued. -/

/-- The §4.3 meeting on the Monday, 12:50-13:50 in Chicago, with `buffer:1h` in front of it, as
`Look.wallIndex` lists it.  (`Look.mondayWall` is the same meeting with no buffer.) -/
def bufferedMondayWall : Look.WallIx :=
  ⟨['g','1'], 739865, 739865, (Cal.instantOf Cal.chicago 739865 710).sec,
   (Cal.instantOf Cal.chicago 739865 770).sec, (Cal.instantOf Cal.chicago 739865 830).sec⟩

/-- A second meeting on the same Monday, 13:30-14:30, which runs into the first. -/
def secondMondayWall : Look.WallIx :=
  ⟨['g','2'], 739865, 739865, (Cal.instantOf Cal.chicago 739865 810).sec,
   (Cal.instantOf Cal.chicago 739865 810).sec, (Cal.instantOf Cal.chicago 739865 870).sec⟩

/-! ### `wall_conflicts` -/

/-- Fork `wall_conflicts` (`planner.rs:2238`): every overlapping pair once, named at the later
one, **compared on the events' own spans** and not on the blocked ones.  §8.2 step 1: the
planner does not resolve them.

D9-21: the recursion is structural over the list the previous definition produced, and its
answer is bounded at the diagnostic cap by `Capped.ofListTake`. -/
def wallConflicts : List Look.WallIx → List (Id × Id)
  | [] => []
  | a :: l =>
    (l.filterMap fun b => if b.evLo < a.hi ∧ a.evLo < b.hi then some (a.id, b.id) else none)
      ++ wallConflicts l

theorem wallConflicts_nil : wallConflicts [] = [] := rfl

/-- **Each pair is named once, and both walls are named** — the planner reports the overlap it
refuses to resolve. -/
theorem mem_wallConflicts {l : List Look.WallIx} {p : Id × Id} (h : p ∈ wallConflicts l) :
    ∃ a ∈ l, ∃ b ∈ l, p = (a.id, b.id) ∧ b.evLo < a.hi ∧ a.evLo < b.hi := by
  induction l with
  | nil => cases h
  | cons a t ih =>
    rw [wallConflicts, List.mem_append] at h
    rcases h with h | h
    · simp only [List.mem_filterMap] at h
      obtain ⟨b, hb, hp⟩ := h
      by_cases hc : b.evLo < a.hi ∧ a.evLo < b.hi
      · rw [if_pos hc] at hp
        exact ⟨a, List.mem_cons_self .., b, List.mem_cons_of_mem _ hb,
          (Option.some.inj hp).symm, hc.1, hc.2⟩
      · rw [if_neg hc] at hp; exact absurd hp (by simp)
    · obtain ⟨x, hx, y, hy, he⟩ := ih h
      exact ⟨x, List.mem_cons_of_mem _ hx, y, List.mem_cons_of_mem _ hy, he⟩

/-- **The clash is named once and nothing is moved.**  The two Monday meetings overlap
13:30-13:50; step 1 reports the pair at the later one and leaves both rows exactly where
`the_spec_days_walls_are_placed_where_they_are_written` puts them — §8.2 step 1's "the planner
does not resolve them", run. -/
theorem the_spec_days_clash_is_named_once :
    wallConflicts (wallsOfDay (Cal.instantOf Cal.chicago 739865 0).sec
        (Cal.instantOf Cal.chicago 739866 0).sec 739865
        [secondMondayWall, bufferedMondayWall])
      = [(['g','1'], ['g','2'])] := by
  decide

/-! ### The travel day, and the budget it zeroes -/

/-- Fork `Item::is_travel_day()` on the wall's own item, read from the same store
`wallIndex` keyed. -/
def PlanReq.isTravelDay (r : PlanReq) (i : Id) : Bool :=
  match r.plan.val.store.get i with
  | some e => decide (Field.Flag.travelDay ∈ e.val.flags)
  | none => false

/-- Fork `walls.iter().any(|w| w.travel_day)`. -/
def travelDay (r : PlanReq) : Bool := (wallsToday r).any (fun x => r.isTravelDay x.id)

-- `PlanReq.todayRecord` — today's record in this call's own replay — sits above `PlanReq.window` since W-39,
-- because the window reads the day's first logged `arrive` off it (`PlanReq.loggedArrival`, README gap 3390);
-- `blocksDone` below reads its closed blocks.  Moved, not copied: the day record has one reader (AGENTS §5.3),
-- and the move is line-neutral so every check-9 pin site below it stays where `kernel/mutations.txt` has it.

/-- **Fork `self.blocks_done`** (`planner.rs:884`): today's closed blocks, off this call's own
replay.  It was inline inside `remainingBudget` until §8.2 step 7, which needs the same number
for `Note.budgetSpent` — fork `diagnose`'s `self.blocks_done > 0` (`planner.rs:2216`) — and a
second reading of the day record is the defect this kernel exists to remove (AGENTS §5.3). -/
def PlanReq.blocksDone (r : PlanReq) : Nat := (r.todayRecord.map (·.blocksDone)).getD 0

/-- Fork `capacity::remaining_budget(budget, blocks_done)` — `Nat` subtraction *is* the fork's
`saturating_sub` — with §8.2 step 1's travel-day zeroing in front of it. -/
def remainingBudget (r : PlanReq) : Nat :=
  if travelDay r then 0 else r.budgetBlocks - r.blocksDone

/-- **A travel day plans no blocks** (§8.2 step 1: "a `travel-day` wall today zeroes the
remaining budget"). -/
theorem a_travel_day_has_no_budget (r : PlanReq) (h : travelDay r = true) :
    remainingBudget r = 0 := by simp [remainingBudget, h]

theorem remainingBudget_le_budget (r : PlanReq) : remainingBudget r ≤ r.budgetBlocks := by
  unfold remainingBudget; split
  · exact Nat.zero_le _
  · omega

/-! ### `emit_segments`' wall loop -/

/-- The rows one wall places (fork `emit_segments`, `planner.rs:1772-1797`): the `buffer:`
run-up as its own Wall row when there is one, then the event's own Wall row.  Both carry the
item; the run-up carries the note that says which it is. -/
def wallRows (travel : Bool) (x : Look.WallIx) : List Seg :=
  (if x.lo < x.evLo then
     [{ start := x.lo, stop := x.evLo, kind := .wall, energy := none, item := some x.id,
        inst := none, flags := SegFlags.none, planned := none, mult := none,
        note := some (.bufferBefore x.id) }]
   else []) ++
  [{ start := x.evLo, stop := x.hi, kind := .wall, energy := none, item := some x.id,
     inst := none, flags := SegFlags.none, planned := none, mult := none,
     note := if travel then some .travelDayWall else none }]

/-- **Every row a wall places is a Wall row of that wall's own item.** -/
theorem wallRows_are_walls_of_the_item (travel : Bool) (x : Look.WallIx) (s : Seg)
    (h : s ∈ wallRows travel x) : s.kind = SegKind.wall ∧ s.item = some x.id := by
  simp only [wallRows, List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨rfl, rfl⟩
    · cases h
  · simp only [List.mem_singleton] at h; subst h; exact ⟨rfl, rfl⟩

/-- **The event's own row runs from the event's own start to its own end.**  This is the
equation `plan_never_moves_a_wall`'s restatement turns on: the planner contributes neither
endpoint. -/
theorem the_event_row_is_the_event (travel : Bool) (x : Look.WallIx) :
    { start := x.evLo, stop := x.hi, kind := .wall, energy := none, item := some x.id,
      inst := none, flags := SegFlags.none, planned := none, mult := none,
      note := if travel then some Note.travelDayWall else none : Seg }
      ∈ wallRows travel x := by
  simp [wallRows]

/-- **A wall with no `buffer:` places exactly one row.** -/
theorem wallRows_without_a_buffer (travel : Bool) (x : Look.WallIx) (h : x.evLo ≤ x.lo) :
    (wallRows travel x).length = 1 := by
  simp only [wallRows, List.length_append]
  rw [if_neg (by omega)]
  rfl

/-- **§8.2 step 1, run on the §4.3 Monday.**  Handed the two meetings in the wrong order, step 1
answers them in blocked-start order; the buffered one places **two** rows — the run-up
11:50-12:50 and the event 12:50-13:50 — and the second places one, 13:30-14:30; every endpoint
is one the index wrote and none is one the planner chose.  Nothing here is an argument: it is
the rule evaluated. -/
theorem the_spec_days_walls_are_placed_where_they_are_written :
    wallsOfDay (Cal.instantOf Cal.chicago 739865 0).sec (Cal.instantOf Cal.chicago 739866 0).sec
        739865 [secondMondayWall, bufferedMondayWall]
      = [bufferedMondayWall, secondMondayWall] ∧
    ((wallsOfDay (Cal.instantOf Cal.chicago 739865 0).sec
        (Cal.instantOf Cal.chicago 739866 0).sec 739865
        [secondMondayWall, bufferedMondayWall]).flatMap (fun x => wallRows false x)).map
        (fun s => (s.start, s.stop, s.kind, s.item))
      = [((Cal.instantOf Cal.chicago 739865 710).sec, (Cal.instantOf Cal.chicago 739865 770).sec,
          SegKind.wall, some ['g','1']),
         ((Cal.instantOf Cal.chicago 739865 770).sec, (Cal.instantOf Cal.chicago 739865 830).sec,
          SegKind.wall, some ['g','1']),
         ((Cal.instantOf Cal.chicago 739865 810).sec, (Cal.instantOf Cal.chicago 739865 870).sec,
          SegKind.wall, some ['g','2'])] := by
  decide

/-! ### §9's running interruption, as an ad-hoc wall -/

/-- Fork `collect_walls`' §9 tail: an interruption that has not been resumed blocks from where
it started to `now`.  It is **not** in `wallsToday` — it is not a calendar wall, it takes no
part in `wall_conflicts`, and §8.1's window does not extend for it. -/
def interruptRows (r : PlanReq) : List Seg :=
  match r.state.interrupt with
  | none => []
  | some x =>
    match x.started with
    | none => []
    | some t =>
      if r.now.sec ≤ max t.sec r.dayStart then []
      else [{ start := max t.sec r.dayStart, stop := r.now.sec, kind := .lost, energy := none,
              item := x.id, inst := none, flags := { SegFlags.none with isOpen := true },
              planned := none, mult := none, note := some .interruption }]

/-- **The running interruption is Lost time, open, and ends at `now`** (fork
`planner.rs:1755-1770`: `SegKind::Lost`, `open: w.end >= self.now`). -/
theorem interruptRows_are_open_lost_time (r : PlanReq) (s : Seg) (h : s ∈ interruptRows r) :
    s.kind = SegKind.lost ∧ s.flags.isOpen = true ∧ s.stop = r.now.sec := by
  unfold interruptRows at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  · simp only [List.mem_singleton] at h; subst h; exact ⟨rfl, rfl, rfl⟩

/-- **An interruption is never a wall row**, so it can never satisfy a wall law: §8.1's window
does not extend for it and `wall_conflicts` skips it (`a.adhoc || b.adhoc → continue`). -/
theorem interruptRows_are_not_walls (r : PlanReq) (s : Seg) (h : s ∈ interruptRows r) :
    s.kind ≠ SegKind.wall := by
  rw [(interruptRows_are_open_lost_time r s h).1]; intro hc; cases hc

/-- **§9's running break** (W-35, owner D57 (1), parity **P45**): a Break row from where it started
to its planned end, or to `now`, open, once overrun.  Its laws and its reason close the module. -/
def breakRows (r : PlanReq) : List Seg :=
  match r.state.brk.bind (fun b => b.started.map (b, ·)) with
  | none => []
  | some (b, t) =>
    let e := max (min (t.sec + 60 * b.plannedMin) r.dayEnd) r.now.sec
    if e ≤ max t.sec r.dayStart then [] else
      [{ start := max t.sec r.dayStart, stop := e, kind := .brk, energy := none, item := none,
         inst := none, planned := none, mult := none, note := b.place.map (·.word |> .breakWhere),
         flags := { SegFlags.none with isOpen := decide (t.sec + 60 * b.plannedMin ≤ r.now.sec) } }]

/-! ### `past_segments` — the half that comes from the log, through the seam -/

/-- Fork `past_segments`' kind map (`planner.rs:2044-2076`): the replay's segment kinds as the
day's rows, with the note each one carries. -/
def pastKind : Replay.SegKind → SegKind × Option Id × Option Note
  | .block i => (.block, some i, none)
  | .pause i => (.lost, some i, some .paused)
  | .interrupt i => (.lost, i, some .interruption)
  | .brk w => (.brk, none, w.map Note.breakWhere)
  | .routine item _ => (.routine, some item, none)
  | .idle a => (.lost, none, some (.idleAttributed a))

/-- The instance key a replayed routine row carries (`Replay.Facts.instances`' own key). -/
def pastInst : Replay.SegKind → Option (Id × Id)
  | .routine item inst => some (item, inst)
  | _ => none

/-- **D65** (parity P56): the day's walls as the spans they block — step 1's rows, run-up included. -/
def wallSpans (r : PlanReq) : List (Nat × Nat) := (wallsToday r).map (fun w => (w.lo, w.hi))
/-- A replayed segment's spans: its clip to `[day_start, now]`, a Pause's with the walls cut out. -/
def pastSpans (r : PlanReq) (g : Replay.Segment) : List (Nat × Nat) :=
  clipCut (max g.start.1.sec r.dayStart) (min g.stop.1.sec r.now.sec)
    (match g.kind with | .pause _ => wallSpans r | _ => [])
/-- One replayed row over one span: `pastKind`'s kind, item and note, done when closed today. -/
def pastRowOf (d : Replay.DayAcc) (g : Replay.Segment) (q : Nat × Nat) : Seg :=
  { start := q.1, stop := q.2, kind := (pastKind g.kind).1, energy := none,
    item := (pastKind g.kind).2.1, inst := pastInst g.kind,
    flags := { SegFlags.none with
      done := ((pastKind g.kind).1 == SegKind.routine) ||
        (((pastKind g.kind).2.1).map (fun i => decide (i ∈ d.done))).getD false },
    planned := none, mult := none, note := (pastKind g.kind).2.2 }
/-- **§8.3's stability half** (fork `past_segments`): everything that ended before `now` comes
from the log, clipped to `[day_start, now]`, so a replan cannot move it.  The log is read
**once**, through D24's seam (`PlanReq.run`), and never a second time (D9).  Since the owner's
D65 a Pause is drawn only where no wall of the day is (`a_paused_row_lies_under_no_wall`). -/
def pastRows (r : PlanReq) : List Seg :=
  match r.todayRecord with
  | none => []
  | some d => d.segments.flatMap fun g => (pastSpans r g).map (pastRowOf d g)

/-- **What `pastRows` holds**: one row per span `pastSpans` answers for a segment of today's record. -/
theorem mem_pastRows {r : PlanReq} {t : Seg} : t ∈ pastRows r ↔ ∃ d, r.todayRecord = some d ∧
    ∃ g ∈ d.segments, ∃ q ∈ pastSpans r g, t = pastRowOf d g q := by
  unfold pastRows
  cases r.todayRecord with
  | none => simp
  | some d =>
    simp only [List.mem_flatMap, List.mem_map, Option.some.injEq]
    exact ⟨fun ⟨g, hg, q, hq, he⟩ => ⟨d, rfl, g, hg, q, hq, he.symm⟩,
      fun ⟨_, hd, g, hg, q, hq, he⟩ => hd ▸ ⟨g, hg, q, hq, he.symm⟩⟩

/-- **The past half ends at `now`** — nothing it holds is in the future, which is the half of
L25 that makes a replan able to leave it alone (design §7.2 item 1). -/
theorem pastRows_end_at_now (r : PlanReq) (s : Seg) (h : s ∈ pastRows r) :
    r.dayStart ≤ s.start ∧ s.start < s.stop ∧ s.stop ≤ r.now.sec := by
  obtain ⟨d, -, g, -, q, hq, rfl⟩ := mem_pastRows.1 h
  have := clipCut_within hq
  exact ⟨by simp only [pastRowOf]; omega, this.2.1, by simp only [pastRowOf]; omega⟩

/-- **The past half is never a wall row.**  A wall is placed from the plan; the past is
replayed from the log, and the two never meet in one row. -/
theorem pastRows_are_not_walls (r : PlanReq) (s : Seg) (h : s ∈ pastRows r) :
    s.kind ≠ SegKind.wall := by
  obtain ⟨d, -, g, -, q, -, rfl⟩ := mem_pastRows.1 h
  cases hg : g.kind <;> simp [pastRowOf, pastKind, hg]

/-! ### The day, assembled -/

/-- Fork `day.segments.sort_by(|a, b| a.start.cmp(&b.start).then(a.end.cmp(&b.end)))`. -/
def rowLe (a b : WfSeg) : Bool :=
  decide (a.val.start < b.val.start) ||
    (decide (a.val.start = b.val.start) && decide (a.val.stop ≤ b.val.stop))

/-- The day's rows in the fork's order.  `Replay.insSort` is the **specification** sort —
quadratic and not tail-recursive, kept because it reduces under `decide` — and `sortRowsFast`
is its compiled twin (D9-21, W-14 repair, gap 394).  Every stage-5 sort of this shape ships
one (`Replay.sortSegs`/`sortSegsFast`, `Look.windowEnd`/`windowEndFast`); P1 took the half
that reduces and not the half that runs, and this list is the whole day's, under D30 Q8's
5 ms trigger. -/
def sortRows (l : List WfSeg) : List WfSeg := Replay.insSort rowLe l

def sortRowsFast (l : List WfSeg) : List WfSeg := l.mergeSort rowLe

@[csimp] theorem sortRows_eq_sortRowsFast : @sortRows = @sortRowsFast := by
  funext l
  exact Replay.insSort_eq_mergeSort rowLe
    (fun a b c h₁ h₂ => by
      simp only [rowLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *; omega)
    (fun a b => by
      simp only [rowLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega) l

theorem mem_sortRows {l : List WfSeg} {s : WfSeg} : s ∈ sortRows l ↔ s ∈ l :=
  (Replay.insSort_perm rowLe l).mem_iff

theorem rowLe_trans (a b c : WfSeg) (h₁ : rowLe a b = true) (h₂ : rowLe b c = true) :
    rowLe a c = true := by
  simp only [rowLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *; omega

theorem rowLe_total (a b : WfSeg) : rowLe a b = true ∨ rowLe b a = true := by
  simp only [rowLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]; omega

/-- **The sort may be taken after a filter** — `Seal.insSort_filter` at the day's own order,
which is what makes "these rows cannot reach the assigned set" a statement about the rows and
not about where the sort happens to put them. -/
theorem sortRows_filter (p : WfSeg → Bool) (l : List WfSeg) :
    (sortRows l).filter p = sortRows (l.filter p) :=
  Seal.insSort_filter rowLe rowLe_trans rowLe_total p l

/-! ############################################################################
## §8.2 step 2 — the routines (stage 6, step P2)

APPENDED 2026-09-17 (stage 6, run W-15, track P, step P2; design §14.2's P2 row).

**What step 2 is**, from fork `planner.rs`: `collect_routines` (today's window instances, their
spans, and the one that is sleep), `place_mandatory_and_pref` (the earliest feasible position
for a mandatory instance, a free `pref:` anchor for the rest, deferral otherwise), `night()`
(everything from `wind_down` on is closed to the day), and `emit_segments`' routine, wind-down
and sleep rows.  Choices 2 and 3 of design §2.

**Nothing here computes a free interval.**  `earliestFree` is `Look.freeIntervals` — L3's own —
with the first stretch wide enough taken off the front, which is exactly what fork
`earliest_free` does (`planner.rs:2258`: `free_intervals(from, to, walls).find(|(a, b)| b - a >=
dur).map(|(a, _)| a)`).  A second walk over the blocked list would be AGENTS §5.3's defect with
the day's placement behind it, and §8.2 step 3 reads the same function through `cutSlots`, so
the day's slots and the day's routines cannot disagree about what is free.

**`[day]`'s evening keys were WIDENED into `Look.DayCfg`, not forked** (AGENTS §5.3, and the
pattern W-14's P1 set with `Look.wallIxOn`).  §16's `[day]` has `wind_down` and `bed`; the
kernel reads `[day]` in one record and now reads all of it.  `Look.the_evening_keys_do_not_move
_the_window`, `…_the_cut` and `…_the_budget` are the projections that say the old readers are
unchanged.

**`Core.pref` was declared in `State.lean`**, beside the other twenty-six field views, for the
same reason: §3.1's rule is one function per field, and a `viewPref` call in `Planner.lean`
would have been the second reader.

**The `loc:` filter is NOT applied to routines** (design §2 choice 2, fork `collect_routines`,
which never calls `loc_ok`).  A routine is furniture: it happens where you are.

### What step 2 does NOT do, by name

* **The Active reservation** (choice 5b) is not in `blocked` yet.  Fork `run()` pushes
  `active_run` before `place_mandatory_and_pref`, and every input it reads exists today — the
  walls, the wind-down this step landed, `Replay.OpenBlock`'s worked minutes through the seam,
  and `current_block_end`.  **What stops it is not a missing input**: the reservation is a
  `SegKind.block` row, and the day's first Block makes four of `PlanCheck`'s six block-side
  checks non-vacuous — `noDemandingAfterWindDown` among them, and that one has **no Active
  exception** and needs one (README gap **437**).  Landing it therefore drags in the
  restatement `PlanCheck.dayPlan_ok_core_given_the_budget`'s own comment assigns to **P5**.  Until it lands a
  routine may be placed over the running block (README gap 434).
* **`diagnostics.notes`' un-placed note** (`planner.rs:1055`) is **P6**'s: a deferred routine is
  only *finally* un-placed once step 6 has tried the lowest-energy position.  `Note.noPosition`
  exists and nothing constructs it yet.
* **A routine row's `hot` mark** is §7.2's `p = 0`, which is **P4**'s pass; the rows carry
  `hot := false` and the flag becomes real there (README gap 435).  *Set since W-37: P4 landed
  without setting it, and W-35 found it an R3 prerequisite (gap 2870); `PlanReq.routineHot` is
  the reading.*
* **The deferred routines themselves** are step 6 and are **P6**'s: they carry `deferred := true`
  and no position, which is exactly the state `place_deferred` receives.
-/

/-! ### The evening, from `[day]` -/

/-- **Fork `Planner::new`'s `wind_down`**: `[day] wind_down` on the day being planned. -/
def PlanReq.windDownSec (r : PlanReq) : Nat :=
  (Cal.instantOf r.tz r.today r.look.day.windDown).sec

/-- **Fork `Planner::new`'s `bed`**, with the fork's own fixup: a `bed` at or before the
wind-down is pushed to half an hour after it, never past the day's end
(`planner.rs:868-871`). -/
def PlanReq.bedSec (r : PlanReq) : Nat :=
  if (Cal.instantOf r.tz r.today r.look.day.bed).sec ≤ r.windDownSec
  then max (min r.dayEnd (r.windDownSec + 1800)) r.windDownSec
  else (Cal.instantOf r.tz r.today r.look.day.bed).sec

/-- **Bed is never before the wind-down**, whatever `[day]` says — the fixup, stated. -/
theorem the_night_is_in_order (r : PlanReq) : r.windDownSec ≤ r.bedSec := by
  unfold PlanReq.bedSec
  split
  · exact Nat.le_max_right _ _
  · omega

/-- **Fork `Planner::night()`**: the evening the day is over — from the wind-down (or the day's
end, whichever comes first) to the end of *tomorrow*.  It runs past midnight on purpose: §8.1's
wall extension can push the window past it, and the small hours are not a second evening. -/
def PlanReq.night (r : PlanReq) : Nat × Nat :=
  (min r.windDownSec r.dayEnd, r.dayEnd + 86400)

/-! ### `earliest_free` and `overlaps_any`, on L3's own free intervals -/

/-- **Fork `overlaps_any`** (`planner.rs:2253`): a half-open `[lo, hi)` meets one of `ws`. -/
def overlapsAny (lo hi : Nat) (ws : List (Nat × Nat)) : Bool :=
  ws.any (fun w => decide (lo < w.2 ∧ w.1 < hi))

/-- **Fork `earliest_free`** (`planner.rs:2258`): the earliest `t ≥ lo` with `[t, t + dur)`
inside `[lo, hi)` and free of `ws`.

`Look.freeIntervals` **is** the fork's `capacity::free_intervals` and is step L3's; this is its
first stretch wide enough, and not a second walk (AGENTS §5.3, design §1.2). -/
def earliestFree (lo hi durSec : Nat) (ws : List (Nat × Nat)) : Option Nat :=
  ((Look.freeIntervals lo hi ws).find? (fun iv => decide (durSec ≤ iv.2 - iv.1))).map Prod.fst

/-- **What a free stretch wide enough gives**: a position inside the range that was searched,
every second of which is off the blocked list.

Both of `earliestFree`'s laws and both of `PlanReq.lowestFree`'s (step P6) are this lemma at a
different choice of stretch — the two searches differ in **which** stretch of
`Look.freeIntervals` they take and in nothing else, so the reasoning is written once
(AGENTS §5.3). -/
theorem freeStretch_gives_a_position {lo hi d : Nat} {ws : List (Nat × Nat)} {iv : Nat × Nat}
    (hm : iv ∈ Look.freeIntervals lo hi ws) (hd : d ≤ iv.2 - iv.1) :
    lo ≤ iv.1 ∧ iv.1 + d ≤ hi ∧ ∀ u, iv.1 ≤ u → u < iv.1 + d → Look.covered ws u = false := by
  obtain ⟨hlo, hlt, hhi⟩ := Look.freeIntervals_inside_the_window hm
  refine ⟨hlo, by omega, fun u hu1 hu2 => ?_⟩
  have hin : ∃ w ∈ Look.freeIntervals lo hi ws, w.1 ≤ u ∧ u < w.2 := ⟨iv, hm, hu1, by omega⟩
  have hfree := (Look.freeIntervals_are_the_free_units lo hi ws u).1 hin
  cases hc : Look.covered ws u with
  | false => rfl
  | true =>
    obtain ⟨w, hw, hw1, hw2⟩ := Look.covered_eq_true.1 hc
    exact absurd ⟨hw1, hw2⟩ (hfree.2.2 w hw)

/-- The stretch `earliestFree` took: the first one wide enough. -/
theorem earliestFree_from_a_stretch {lo hi d : Nat} {ws : List (Nat × Nat)} {s : Nat}
    (h : earliestFree lo hi d ws = some s) :
    ∃ iv ∈ Look.freeIntervals lo hi ws, iv.1 = s ∧ d ≤ iv.2 - iv.1 := by
  unfold earliestFree at h
  cases hf : (Look.freeIntervals lo hi ws).find? (fun iv => decide (d ≤ iv.2 - iv.1)) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some iv =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    refine ⟨iv, List.mem_of_find?_eq_some hf, h, ?_⟩
    have := List.find?_some hf
    simpa using this

/-- **What `earliestFree` answers is inside the range it was asked about.** -/
theorem earliestFree_inside {lo hi d : Nat} {ws : List (Nat × Nat)} {s : Nat}
    (h : earliestFree lo hi d ws = some s) : lo ≤ s ∧ s + d ≤ hi := by
  obtain ⟨iv, hm, hs, hd⟩ := earliestFree_from_a_stretch h
  subst hs
  obtain ⟨h1, h2, -⟩ := freeStretch_gives_a_position hm hd
  exact ⟨h1, h2⟩

/-- **And every second of it is free.**  This is the half that makes the placement laws mean
something: a routine placed at `earliestFree` overlaps nothing that was blocked. -/
theorem earliestFree_is_free {lo hi d : Nat} {ws : List (Nat × Nat)} {s u : Nat}
    (h : earliestFree lo hi d ws = some s) (h1 : s ≤ u) (h2 : u < s + d) :
    Look.covered ws u = false := by
  obtain ⟨iv, hm, hs, hd⟩ := earliestFree_from_a_stretch h
  subst hs
  exact (freeStretch_gives_a_position hm hd).2.2 u h1 h2

/-- **`overlapsAny` is `covered`, pointwise** — the two readings of "this stretch is taken" are
one reading (AGENTS §5.3).  `false` means every second of `[lo, hi)` is uncovered, which is what
the `pref:` branch of the placement needs and what the fork's own `!overlaps_any(...)` test
means. -/
theorem overlapsAny_false_covers_nothing {lo hi : Nat} {ws : List (Nat × Nat)}
    (h : overlapsAny lo hi ws = false) {u : Nat} (h1 : lo ≤ u) (h2 : u < hi) :
    Look.covered ws u = false := by
  cases hc : Look.covered ws u with
  | false => rfl
  | true =>
    obtain ⟨w, hw, hw1, hw2⟩ := Look.covered_eq_true.1 hc
    have hany : overlapsAny lo hi ws = true := by
      simp only [overlapsAny, List.any_eq_true, decide_eq_true_eq]
      exact ⟨w, hw, by omega, by omega⟩
    rw [hany] at h; cases h

/-- **And it refuses a stretch that is taken** (AGENTS §5.2: the test is not vacuous). -/
theorem overlapsAny_true_of_covered {lo hi : Nat} {ws : List (Nat × Nat)} {w : Nat × Nat}
    (hw : w ∈ ws) (h1 : lo < w.2) (h2 : w.1 < hi) : overlapsAny lo hi ws = true := by
  simp only [overlapsAny, List.any_eq_true, decide_eq_true_eq]
  exact ⟨w, hw, h1, h2⟩

/-! ### `collect_routines` — what the host hands in, and what the kernel refuses

**D27 has not landed** (the owner's decision, W-14's finding), so a routine instance still
arrives as a host-collected candidate: which occurrences are due today is F2's recurrence
expansion, which is track **K3**'s and is not built.  What the kernel does *not* take on trust is
the item behind the instance — the plan is in the request, and `routines.md`'s own rule
(`routine_lines_have_a_window_or_after_done`, `Plan.lean`) is already proved. -/

/-! `RoutineIn` is declared above `PlanReq` (§8.2 step 2's input); `mkRoutine?` and its
refusals are here, beside the rule they enforce. -/

/-- Why a routine instance is refused, by name (AGENTS §5.7, R10). -/
inductive RoutineErr
  /-- The request names an item its own plan does not hold. -/
  | unknownItem (id : Id)
  /-- **README gap 285.**  The instance claims a window and the item declares none. -/
  | undeclaredWindow (id : Id)
  /-- The occurrence's window ends at or before it opens. -/
  | emptyWindow (id : Id)
  /-- It ends outside the calendar. -/
  | pastTheHorizon (id : Id)
  /-- It asks for no minutes at all. -/
  | noMinutes (id : Id)
  /-- More instances than the candidate cap (R10). -/
  | tooManyRoutines
deriving DecidableEq, Repr

/-- **The item declares a window** — §4.3's `routines.md` rule read at the planner: a
`Shape.window`, or an `after-done` recurrence whose tolerance is the window (§5.1).  This is
the disjunction `Plan.routine_lines_have_a_window_or_after_done` already proves of every
`routines.md` line, evaluated for one id.

**`shapeOf`, not `effectiveShape`** — fork `Planner::daily_window` reads `item.shape`, and
`shapeOf` is the kernel's reader of exactly that.  `effectiveShape` is built on it and only ever
*replaces* a `Shape.none` with §3.2's prep `Point`, which is never a window, so the two cannot
disagree here; both are `Plan.lean`'s and neither is a second copy (AGENTS §5.3). -/
def declaresAWindow (p : PlanCore) (i : Id) : Bool :=
  match p.store.get i with
  | none => false
  | some e =>
    (match shapeOf p i with | .window _ _ => true | _ => false) ||
    (match e.val.recur with | .afterDone _ => true | _ => false)

/-- **A routine the kernel may place** (R10).  Every clause is a refusal with a name. -/
def RoutineIn.wf (p : PlanCore) (x : RoutineIn) : Bool :=
  (p.store.get x.id).isSome && declaresAWindow p x.id &&
    decide (x.winLo < x.winHi) && decide (x.winHi < LogStamp.yearEnd) && decide (0 < x.durMin)

/-- **The smart constructor** (R10), and **README gap 285's rule**: `tm plan` schedules a routine
whose declared window is malformed rather than refusing it, and here it is refused **by name**.

The reproducing line is §4.1's `- lunch  win:25:99-13:30 dur:30m  every:day`.  `25:99` is not a
clock, so `Field.parseWindow` answers `none`, so `viewShape` falls through to `Shape.none`
(`Line.lean`; `shape_win_needs_dur` is the same fall-through for a `win:` with no `dur:`), and
the item declares **no** window while its instance carries one.  The fork drops the window and
plans the routine anyway (`collect_routines`' `let Some((ws, we)) = c.window else continue` never
fires, because the *candidate* still has one); the kernel answers `undeclaredWindow` and the verb
refuses.  It is a refusal and not a repair: R10 never adjusts a value it will not take. -/
def mkRoutine? (p : PlanCore) (x : RoutineIn) : Except RoutineErr RoutineIn :=
  if (p.store.get x.id).isNone then .error (.unknownItem x.id)
  else if declaresAWindow p x.id = false then .error (.undeclaredWindow x.id)
  else if x.winHi ≤ x.winLo then .error (.emptyWindow x.id)
  else if LogStamp.yearEnd ≤ x.winHi then .error (.pastTheHorizon x.id)
  else if x.durMin = 0 then .error (.noMinutes x.id)
  else .ok x

theorem mkRoutine?_refuses_an_unknown_item (p : PlanCore) (x : RoutineIn)
    (h : p.store.get x.id = none) : mkRoutine? p x = .error (.unknownItem x.id) := by
  unfold mkRoutine?; rw [if_pos (by simp [h])]

/-- **Gap 285, as a theorem.** -/
theorem mkRoutine?_refuses_a_window_the_item_does_not_declare (p : PlanCore) (x : RoutineIn)
    (e : Entity) (h : p.store.get x.id = some e) (hd : declaresAWindow p x.id = false) :
    mkRoutine? p x = .error (.undeclaredWindow x.id) := by
  unfold mkRoutine?; rw [if_neg (by simp [h]), if_pos hd]

theorem mkRoutine?_refuses_an_empty_window (p : PlanCore) (x : RoutineIn) (e : Entity)
    (h : p.store.get x.id = some e) (hd : declaresAWindow p x.id = true)
    (hw : x.winHi ≤ x.winLo) : mkRoutine? p x = .error (.emptyWindow x.id) := by
  unfold mkRoutine?; rw [if_neg (by simp [h]), if_neg (by simp [hd]), if_pos hw]

theorem mkRoutine?_refuses_past_the_horizon (p : PlanCore) (x : RoutineIn) (e : Entity)
    (h : p.store.get x.id = some e) (hd : declaresAWindow p x.id = true)
    (hw : x.winLo < x.winHi) (hh : LogStamp.yearEnd ≤ x.winHi) :
    mkRoutine? p x = .error (.pastTheHorizon x.id) := by
  unfold mkRoutine?
  rw [if_neg (by simp [h]), if_neg (by simp [hd]), if_neg (by omega), if_pos hh]

theorem mkRoutine?_refuses_an_instance_with_no_minutes (p : PlanCore) (x : RoutineIn) (e : Entity)
    (h : p.store.get x.id = some e) (hd : declaresAWindow p x.id = true)
    (hw : x.winLo < x.winHi) (hh : x.winHi < LogStamp.yearEnd) (hz : x.durMin = 0) :
    mkRoutine? p x = .error (.noMinutes x.id) := by
  unfold mkRoutine?
  rw [if_neg (by simp [h]), if_neg (by simp [hd]), if_neg (by omega), if_neg (by omega),
    if_pos hz]

/-- **Both directions**: what it accepts is exactly `RoutineIn.wf`. -/
theorem mkRoutine?_accepts (p : PlanCore) (x : RoutineIn) (h : RoutineIn.wf p x = true) :
    mkRoutine? p x = .ok x := by
  simp only [RoutineIn.wf, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  unfold mkRoutine?
  rw [if_neg (by simp [Option.isNone_iff_eq_none]; exact Option.ne_none_iff_isSome.2 h1),
    if_neg (by simp [h2]), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem mkRoutine?_ok_is_wf (p : PlanCore) (x y : RoutineIn) (h : mkRoutine? p x = .ok y) :
    RoutineIn.wf p x = true ∧ y = x := by
  unfold mkRoutine? at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  · rename_i h1 h2 h3 h4 h5
    cases h
    simp only [Option.isNone_iff_eq_none] at h1
    simp only [Bool.not_eq_false] at h2
    refine ⟨?_, rfl⟩
    simp only [RoutineIn.wf, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨Option.ne_none_iff_isSome.1 h1, h2⟩, by omega⟩, by omega⟩, by omega⟩

/-- The whole list off the wire, bounded (R10): the first refusal is returned, with the id it is
about. -/
def mkRoutines? (p : PlanCore) (xs : List RoutineIn) : Except RoutineErr (Capped RoutineIn) :=
  if maxCands < xs.length then .error .tooManyRoutines
  else match xs.mapM (mkRoutine? p) with
    | .error e => .error e
    | .ok l => match Capped.ofList? l with
      | some c => .ok c
      | none => .error .tooManyRoutines

theorem mkRoutines?_refuses_too_many (p : PlanCore) (xs : List RoutineIn)
    (h : maxCands < xs.length) : mkRoutines? p xs = .error .tooManyRoutines := by
  unfold mkRoutines?; rw [if_pos h]

/-- **A host that sends no window instance is accepted, and gets the empty cap.**  The
positive end of `mkRoutines?`' rejection theorems (AGENTS §5.8: both directions get a
theorem), and what lets a caller that has no routines to send rewrite the decoder away
instead of carrying its `match` (W-15's land step, `PlannerWit.witBuilds`). -/
theorem mkRoutines?_of_none (p : PlanCore) : mkRoutines? p [] = .ok Capped.nil := by
  unfold mkRoutines?
  rw [if_neg (by simp [maxCands])]
  rfl

/-- **A refused instance refuses the list** — gap 285 reaches the boundary and is not dropped
on the way. -/
theorem mkRoutines?_refuses_when_one_is_refused (p : PlanCore) (x : RoutineIn) (e : RoutineErr)
    (h : mkRoutine? p x = .error e) (h2 : ¬ (maxCands < [x].length)) :
    mkRoutines? p [x] = .error e := by
  have hm : [x].mapM (mkRoutine? p) = Except.error e := by rw [List.mapM_cons, h]; rfl
  unfold mkRoutines?
  rw [if_neg h2, hm]

/-! ### `collect_routines`' span, and the one instance that is sleep -/

/-- **Fork `Planner::daily_window`** (`planner.rs:1259`): the item's `win:` *daily* hours placed
on the day being planned; an overnight range (`to ≤ from`) runs into the next day.

The fork adds `Duration::days(1)` — 86,400 absolute seconds, not "the same clock time
tomorrow" — and so does this. -/
def PlanReq.dailyWindow (r : PlanReq) (i : Id) : Option (Nat × Nat) :=
  match shapeOf r.plan.val i with
  | .window (.daily f t) _ =>
    let a := (Cal.instantOf r.tz r.today f).sec
    let b := (Cal.instantOf r.tz r.today t).sec
    some (a, if b ≤ a then b + 86400 else b)
  | _ => none

/-- **Fork `collect_routines`' span** (`planner.rs:1295-1313`).  A carried instance whose window
has closed may go anywhere left in the day — but a `win:` with a daily range keeps its hours, and
so does an occurrence spanning several days, because clipping a weekly `09:00-21:00` chore to
today alone would leave `00:00-24:00` and let steps 2 and 6 place it outside its stated hours. -/
def PlanReq.routineSpan (r : PlanReq) (x : RoutineIn) : Nat × Nat :=
  if x.winHi ≤ r.now.sec then
    match r.dailyWindow x.id with
    | some (a, b) => (max (max a r.now.sec) r.dayStart, max b r.now.sec)
    | none => (max r.dayStart r.now.sec, max r.dayEnd r.now.sec)
  else
    match r.dailyWindow x.id with
    | some (ha, hb) => (max (max x.winLo r.dayStart) ha, min (min x.winHi r.dayEnd) hb)
    | none => (max x.winLo r.dayStart, min x.winHi r.dayEnd)

/-- ASCII lower case, the fold fork `str::eq_ignore_ascii_case` uses.  **The kernel has no other
case-folder** (`grep -rn 'toLower\|ofNat (.*+ 32)' TmKernel/*.lean` finds none), so this is the
first and only one, and it is ASCII on purpose: an item id is §4.1's `[a-z0-9-]` word and a
Unicode fold would be a different function with the same name. -/
def asciiLower (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- Fork `c.id.as_str().eq_ignore_ascii_case("sleep")`. -/
def isSleepId (i : Id) : Bool := i.map asciiLower == ['s', 'l', 'e', 'e', 'p']

theorem isSleepId_accepts_the_written_spellings :
    isSleepId ['s', 'l', 'e', 'e', 'p'] = true ∧ isSleepId ['S', 'l', 'e', 'e', 'p'] = true ∧
      isSleepId ['s', 'l', 'e', 'e', 'p', 'y'] = false := by decide

/-- Fork `SLEEP_MIN_MINUTES` (`planner.rs:177`). -/
def sleepMinMinutes : Nat := 360

/-- **Fork `collect_routines`' sleep test**: the instance called `sleep`, or an overnight
occurrence of at least six hours. -/
def PlanReq.isSleepInstance (r : PlanReq) (x : RoutineIn) : Bool :=
  isSleepId x.id ||
    (decide (Cal.localDate r.tz ⟨x.winLo, 0⟩ < Cal.localDate r.tz ⟨x.winHi, 0⟩) &&
      decide (sleepMinMinutes ≤ x.durMin))

/-! ### One instance, with its span and where step 2 put it -/

/-- **Fork `planner::RoutineInst`.**  `placedAt` is `Some` exactly when steps 2 placed it;
`deferred` is the mark step 6 (P6) reads. -/
structure Placed where
  inst     : RoutineIn
  span     : Nat × Nat
  placedAt : Option (Nat × Nat)
  deferred : Bool
deriving DecidableEq, Repr

/-- Fork `collect_routines`' loop body, for one candidate that reached the kernel.  The two
`continue`s are here: an instance with no minutes left, and — the kernel's own, because
`dayPlan` is total (D28) and a degenerate row must be unrepresentable rather than merely
unlikely — one whose window is empty.  `mkRoutine?` refuses both **by name** at the boundary;
this is what the total function does if one arrives anyway. -/
def PlanReq.instanceOf? (r : PlanReq) (x : RoutineIn) : Option Placed :=
  if x.winHi ≤ x.winLo then none
  else if x.durMin = 0 then none
  else some ⟨x, r.routineSpan x, none, false⟩

/-- The instances the request carries, spanned.  D9-21: `List.filterMap` over a list the
`Capped` bound holds at `maxCands`. -/
def PlanReq.routineInstances (r : PlanReq) : List Placed :=
  r.routines.val.filterMap r.instanceOf?

/-- **Fork `collect_routines`' `sleep` slot**: the *first* instance that is sleep is taken out of
the list and the rest stay.  D9-21: structural over `routineInstances`, which `Capped` bounds at
`maxCands`. -/
def splitSleep (r : PlanReq) : List Placed → Option Placed × List Placed
  | [] => (none, [])
  | q :: t =>
    if r.isSleepInstance q.inst then (some q, t)
    else
      let s := splitSleep r t
      (s.1, q :: s.2)

/-- **`splitSleep` reads the request only through `isSleepInstance`.**  It is the ONE step-two
definition that takes the whole `PlanReq` and recurses, so it is the one place where two
requests that agree on every field a step-two row can see are still not *definitionally* equal
— every other link in the chain (`routineInstances`, `bedSec`, `blockedByWalls`, `night`,
`placeStep`, `routineRow`) reduces on its own.  Found at W-15's land step, which needed
the busy day's budget witness re-proved over P2's day (D5; refuted at W-38 as
`PlannerWit.the_budget_does_not_move_the_assigned_set_at_the_busy_request_is_refuted`). -/
theorem splitSleep_congr {r r' : PlanReq}
    (h : PlanReq.isSleepInstance r' = PlanReq.isSleepInstance r) :
    ∀ l : List Placed, splitSleep r' l = splitSleep r l
  | [] => rfl
  | q :: t => by
    simp only [splitSleep, h, splitSleep_congr h t]

theorem splitSleep_keeps_the_rest (r : PlanReq) :
    ∀ l : List Placed, ∀ q ∈ (splitSleep r l).2, q ∈ l
  | [], q, hq => by cases hq
  | a :: t, q, hq => by
    simp only [splitSleep] at hq
    split at hq
    · exact List.mem_cons_of_mem _ hq
    · simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (splitSleep_keeps_the_rest r t q hq)

/-- **Fork `collect_routines`' sort**: mandatory first, then the moment the window closes — the
tightest window claims its position first — then the id.

`Replay.insSort` is the **specification** sort, as `wallsOfDay`'s is, and since W-16's repair
step both have their compiled twins: `Log.charsLe` now carries its transitivity and totality
laws (**gap 394, closed**), so `insSort_eq_mergeSort` applies at both call sites. -/
def routineLe (a b : Placed) : Bool :=
  (decide (a.inst.mandatory = true) && decide (b.inst.mandatory = false)) ||
    (decide (a.inst.mandatory = b.inst.mandatory) &&
      (decide (a.span.2 < b.span.2) ||
        (decide (a.span.2 = b.span.2) && Log.charsLe a.inst.id b.inst.id)))

theorem routineLe_trans (a b c : Placed) (h₁ : routineLe a b) (h₂ : routineLe b c) :
    routineLe a c := by
  simp only [routineLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂ ⊢
  rcases h₁ with ⟨ha, hb⟩ | ⟨hab, h₁⟩
  · rcases h₂ with ⟨hb', _⟩ | ⟨hbc, _⟩
    · exact absurd (hb'.symm.trans hb) (by simp)
    · exact Or.inl ⟨ha, hbc ▸ hb⟩
  · rcases h₂ with ⟨hb', hc⟩ | ⟨hbc, h₂⟩
    · exact Or.inl ⟨hab.trans hb', hc⟩
    · refine Or.inr ⟨hab.trans hbc, ?_⟩
      rcases h₁ with h₁ | ⟨h₁, hid₁⟩ <;> rcases h₂ with h₂ | ⟨h₂, hid₂⟩
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, Log.charsLe_trans _ _ _ hid₁ hid₂⟩

/-- The tie-break below `mandatory`: the window's close, then the id.  Total, because
`Log.charsLe` is (`Log.charsLe_total`). -/
theorem routine_span_total (a b : Placed) :
    (a.span.2 < b.span.2 ∨ a.span.2 = b.span.2 ∧ Log.charsLe a.inst.id b.inst.id = true) ∨
      (b.span.2 < a.span.2 ∨ b.span.2 = a.span.2 ∧ Log.charsLe b.inst.id a.inst.id = true) := by
  rcases Nat.lt_trichotomy a.span.2 b.span.2 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases Bool.or_eq_true _ _ |>.mp (Log.charsLe_total a.inst.id b.inst.id) with hid | hid
    · exact Or.inl (Or.inr ⟨h, hid⟩)
    · exact Or.inr (Or.inr ⟨h.symm, hid⟩)
  · exact Or.inr (Or.inl h)

theorem routineLe_total (a b : Placed) : routineLe a b || routineLe b a := by
  simp only [routineLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  cases ha : a.inst.mandatory <;> cases hb : b.inst.mandatory
  · rcases routine_span_total a b with h | h
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inr ⟨rfl, h⟩)
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inl (Or.inl ⟨rfl, rfl⟩)
  · rcases routine_span_total a b with h | h
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inr ⟨rfl, h⟩)

def sortRoutines (l : List Placed) : List Placed := Replay.insSort routineLe l

def sortRoutinesFast (l : List Placed) : List Placed := l.mergeSort routineLe

@[csimp] theorem sortRoutines_eq_sortRoutinesFast : @sortRoutines = @sortRoutinesFast := by
  funext l
  exact Replay.insSort_eq_mergeSort routineLe routineLe_trans routineLe_total l

theorem mem_sortRoutines {l : List Placed} {q : Placed} : q ∈ sortRoutines l ↔ q ∈ l :=
  (Replay.insSort_perm routineLe l).mem_iff

/-! ### `place_mandatory_and_pref` -/

/-- **Fork `place_mandatory_and_pref`'s anchor**: `pref:wake+<dur>` off the day's own wake
(`Look.wakeOn`, step L9 — the kernel has one wake and this is it), or `pref:<clock>` on the day.
`Dur.minutes` takes the block length because `pref:2b` is two blocks. -/
def PlanReq.anchorOf (r : PlanReq) (i : Id) : Option Nat :=
  match (r.plan.val.store.get i).bind (fun e => e.val.pref) with
  | some (.wakePlus d) => some ((Look.wakeOn r.look r.today).sec + 60 * Field.Dur.minutes r.blockMin d)
  | some (.clock t)    => some (Cal.instantOf r.tz r.today t).sec
  | none               => none

/-- **Everything step 2 must flow around before it places anything**: the walls' blocked spans
(the `buffer:` run-up included, which is why this reads `x.lo` and not `x.evLo`) and §9's running
interruption.

**The Active reservation is NOT here** — it joins in `PlanReq.blockedBeforeRoutines`, which is
what step 2's fold and step 3's cut actually start from (§8.2 choice 5b, step P3).

**The span is `max x.evLo x.hi` and not `x.hi` — a repair, step P3** (README gap **552**).  Fork
`run()` blocks `(w.blocked_start, w.end)` where `WallSeg`'s three instants satisfy
`blocked_start ≤ start ≤ end` by construction; `Look.WallIx` carries no such bound, and
`Look.wallOfEntity` builds `evLo`/`hi` straight out of `at:<s>/<f>`, which the grammar accepts
inverted.  On a wall written `at:…T13:50/12:50` **with** a `buffer:`, `wallRows` still emits the
run-up row `[lo, evLo)` while `(x.lo, x.hi)` stops at `hi < evLo`, so step 2 could place a
routine inside a wall's own buffer and step 3 could cut slots there.  `max` only ever widens —
it is the identity on every wall whose interval runs forwards — and it is what makes
`a_wall_row_sits_in_a_blocked_span` true without a hypothesis.  (That sentence named
`a_wall_row_is_covered_by_the_blocked_list` until W-16's repair step — a constant that has
never existed in this repository; the theorem is `a_wall_row_sits_in_a_blocked_span`, below.
Check 3 counts theorems and cannot read doc comments: gap 582.) -/
def blockedByWalls (r : PlanReq) : List (Nat × Nat) :=
  (wallsToday r).map (fun x => (x.lo, max x.evLo x.hi)) ++
    (interruptRows r ++ breakRows r).map (fun s => (s.start, s.stop))

/-! ############################################################################
## §8.2 choice 5b — the running block is RESERVED, not assigned (stage 6, step P3)

Fork `Planner::active_run` (`planner.rs:1497`) and `run()`'s §9 paragraph: the block that is
running takes its remaining minutes **before** the routines are placed and **before** the slots
are cut, so nothing is scheduled on top of a block that is running.  It is a reservation and not
a slot, so it carries no slot energy (`emit_segments`, `planner.rs:1741`: `energy: None`).

**This is the first `SegKind.block` row the planner itself places**, and that is what makes it
the step it is: six of `PlanCheck`'s seven eligibility-free checks quantify over a Block row,
and until now every one of them was about a row `Planner.pastRows` replayed from the log.
README gaps **433** and **434** are what this section closes.

*The fork's six refusals, five kept by name* — a paused timer, what pauses the block at `now`
(`PlanReq.pauseRows`, wider since W-35), §9.1's `d done` what-if, a day whose limit has passed,
a wall sitting on `now`; overtime is not one since W-35 (P46).  `end <= now` is arithmetic's.
############################################################################ -/

/-- **Fork `ActiveRun`** (`planner.rs:1477`) — the reservation, in absolute seconds.  Fork
`ActiveRun` also carries the candidate's `multiplier`; this record does not, because the row
reads it off the request's own candidates where it is drawn (`PlanReq.candMult`, W-37, README gap
550 closed).  *(This comment said until W-37 that `PlanReq.activeRow` emitted no multiplier and
that D34 forbade deriving one here; D34 still forbids deriving it, and it is read, not derived.)* -/
structure ActiveRes where
  id      : Id
  start   : Nat
  stop    : Nat
  leftMin : Nat
deriving DecidableEq, Repr

/-- **The request agrees with `mkActive?`.**  `RuntimeIn.active` is a plain `Option
ActiveBlock`, so nothing in the type stops a decoder handing in an estimate past the host's
width; `ActiveBlock.wf` is the bound and `mkActive?` is its smart constructor (R10, step P0),
in exactly the shape `PlanReq.wallsAgree` has (README gap **346**).  Until W-41 it also bounded
the START by `now`, and E1 carried it for that; D78 plans a start after `now` as the fork does,
so E1 reads the block's lead past `now` instead and no lift needs this clause any more. -/
def PlanReq.activeAgrees (r : PlanReq) : Bool :=
  match r.state.active with
  | none => true
  | some a => ActiveBlock.wf a

/-- **The `[day]` the request carries is one `mkDayCfg?` would have built** (R10;
`Look.mkDayCfg?_wf` is what establishes it).  The one clause this step needs of it is
`1 ≤ block_min`: the fork's `current_block_end` puts **no** bound on the run when `block_min` is
zero (`planner.rs:1578`, "a zero `block_min` … puts no bound on the run at all") and
`Look.cutSlots` answers the empty cut there, so E1 is genuinely false on a hand-edited config
and this is the hypothesis that says so rather than a weakening that hides it. -/
def PlanReq.dayAgrees (r : PlanReq) : Bool := r.look.day.wf

/-- A `[day]` the decoder accepted has a block length. -/
theorem PlanReq.blockMin_pos (r : PlanReq) (h : r.dayAgrees = true) : r.blockMin ≠ 0 := by
  unfold PlanReq.dayAgrees Look.DayCfg.wf at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold PlanReq.blockMin
  omega

/-- **What pauses the running block** (§9): the running interruption — the fork's one — and, since
W-35, the running break (D57 (1), P45) and every row of a wall whose blocked span covers `now`
(D57 (3), P47: §9's Interruption row, *"ad-hoc Wall … Active block paused"*, campaign's call). -/
def PlanReq.pauseRows (r : PlanReq) : List Seg := interruptRows r ++ breakRows r ++
  ((wallsToday r).filter (fun x => decide (x.lo ≤ r.now.sec ∧ r.now.sec < max x.evLo x.hi))).flatMap
    (fun x => wallRows (r.isTravelDay x.id) x)

/-- §9: something pauses the block at `now` — fork `walls.iter().any(|w| w.adhoc && w.end >=
self.now)` over `pauseRows`, read by `active_run` and by `open_block_segment` alike (W-34). -/
def PlanReq.interrupted (r : PlanReq) : Bool :=
  r.pauseRows.any (fun s => decide (r.now.sec ≤ s.stop))

/-- **Fork `OpenBlock::worked_min_at(now)`** (`log.rs:1016`): the banked minutes plus the stretch
since the last resume, through `Look.spanMinutes`, the kernel's one such arithmetic (AGENTS §5.3,
README gap 390).  One reading for `active_run`'s `worked` and `open_block_segment`'s note. -/
def openWorkedMin (nowSec : Nat) (b : Replay.OpenBlock) : Nat :=
  b.workedMin + (b.since.map (fun s => Look.spanMinutes s.1.sec nowSec)).getD 0

/-- **ONE reading of worked minutes** (W-36, gap 2920, P55): the HOST's (`RuntimeIn.worked`) for the item the runtime says runs, else `logs`. -/
def PlanReq.workedOf (r : PlanReq) (id : Id) (logs : Nat) : Nat :=
  match r.state.active, r.state.worked with | some a, some w => if a.id = id then w.val else logs | _, _ => logs
/-- **Fork `active_run`'s `worked`**, through `workedOf`: the log's open block for this item, else the clock (the W-36 note at the end). -/
def PlanReq.activeWorked (r : PlanReq) (a : ActiveBlock) : Nat := r.workedOf a.id (match r.run.answer.openBlock with
  | some b => if b.id = a.id then openWorkedMin r.now.sec b else Look.spanMinutes a.started.sec r.now.sec
  | none => Look.spanMinutes a.started.sec r.now.sec)

/-- Fork `active_run`'s `left`: `est_min.saturating_sub(worked)` — `Nat` subtraction *is* the
fork's saturating one. -/
def PlanReq.activeLeft (r : PlanReq) (a : ActiveBlock) : Nat := a.estMin - r.activeWorked a

/-- **Fork `Planner::current_block_end`** (`planner.rs:1572`): the end of the `block_min` block
that started at `started` and is still running at `now`.  A block that has overrun its length is
still the block you are in, so the boundary rolls forward a whole block at a time; a hand-edited
`block_min = 0` puts no bound on the run at all (§10.2: saturate, never panic).

**The request is not a parameter**, for the reason `wallsOfDay`'s is not (step P1): the rule does
not depend on it, and a request-free rule can be *run* by `decide` — `the_block_boundary_is_run`
below, and `Negative.lean`'s cheat 180 from the other side (AGENTS §5.2). -/
def blockBoundary (blockMin nowSec startedSec dayEndSec : Nat) : Nat :=
  if blockMin = 0 then dayEndSec
  else startedSec + (Look.spanMinutes startedSec nowSec / blockMin + 1) * (60 * blockMin)

/-- **The rule, run** (AGENTS §5.2): a block started at 13:40 and still going at 14:00 belongs to
the hour that ends at **14:40**, whatever estimate is left on it — and a `[day]` with no block
length puts no boundary on it at all. -/
theorem the_block_boundary_is_run :
    blockBoundary 60 50400 49200 86400 = 52800 ∧ blockBoundary 0 50400 49200 86400 = 86400 := by
  decide

def PlanReq.currentBlockEnd (r : PlanReq) (startedSec : Nat) : Nat :=
  blockBoundary r.blockMin r.now.sec startedSec r.dayEnd

/-- **A block boundary is at most one block past `now`** — the arithmetic choice 5b's half of
`plan_reserves_one_block_at_a_time` turns on.  It needs the block to have *started*: for
`now < startedSec` the fork's own formula answers `startedSec + block_min`, further than a block
from `now` — since W-41 (D78) the fork's reading, kept: the reservation carries that lead. -/
theorem PlanReq.currentBlockEnd_within_a_block (r : PlanReq) (startedSec : Nat)
    (hst : startedSec ≤ r.now.sec) (hb : r.blockMin ≠ 0) :
    r.currentBlockEnd startedSec ≤ r.now.sec + 60 * r.blockMin := by
  unfold PlanReq.currentBlockEnd blockBoundary
  rw [if_neg hb]
  have h1 : Look.spanMinutes startedSec r.now.sec / r.blockMin * r.blockMin
      ≤ Look.spanMinutes startedSec r.now.sec := Nat.div_mul_le_self _ _
  have h2 : Look.spanMinutes startedSec r.now.sec * 60 ≤ r.now.sec - startedSec := by
    show (r.now.sec - startedSec) / 60 * 60 ≤ r.now.sec - startedSec
    exact Nat.div_mul_le_self _ _
  have h3 : Look.spanMinutes startedSec r.now.sec / r.blockMin * r.blockMin * 60
      ≤ Look.spanMinutes startedSec r.now.sec * 60 := Nat.mul_le_mul_right 60 h1
  have hexp : (Look.spanMinutes startedSec r.now.sec / r.blockMin + 1) * (60 * r.blockMin)
      = Look.spanMinutes startedSec r.now.sec / r.blockMin * r.blockMin * 60 + 60 * r.blockMin := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm 60 r.blockMin, ← Nat.mul_assoc]
  omega

/-- **Fork `active_run`'s `limit`** (`planner.rs:1531`): never past the wind-down while the
wind-down is still ahead, never past the day's end.  The `if` is the fork's and it is
load-bearing — see `the_reservation_never_runs_under_a_wind_down_row`, which is why README gap
**437** does not reproduce. -/
def PlanReq.activeLimit (r : PlanReq) : Nat :=
  if r.now.sec < r.windDownSec then min r.windDownSec r.dayEnd else r.dayEnd

/-- Fork `active_run`'s last line: the estimate, the free stretch's end or the block boundary,
first — and in OVERTIME (W-35, D57 (2), P46) the block the item is in, which the fork refuses. -/
def PlanReq.activeStop (r : PlanReq) (a : ActiveBlock) (ivStop : Nat) : Nat :=
  min (if r.activeLeft a = 0 then ivStop else min (r.now.sec + 60 * r.activeLeft a) ivStop)
    (r.currentBlockEnd a.started.sec)

/-- **Fork `active_run`** (`planner.rs:1497`), with five of its six refusals in the fork's order.
The free stretch it may run in is **L3's own `Look.freeIntervals`** and not a second walk over
the walls (AGENTS §5.3, design §1.2). -/
def PlanReq.activeRun (r : PlanReq) : Option ActiveRes :=
  match r.state.active with
  | none => none
  | some a =>
    -- the timer is stopped; the block is not running
    if a.paused then none
    -- §9: an interruption pauses the Active block — so, since W-35, do a break and a wall
    else if r.interrupted then none
    -- §9.1's `d done` what-if: the block is finished in that plan
    else if (r.overrides.map (fun o => decide (a.id ∈ o.drop.val))).getD false then none
    -- overtime is NOT refused since W-35 (D57 (2), P46): the block keeps its block
    else if r.activeLimit ≤ r.now.sec then none
    else
      match Look.freeIntervals r.now.sec r.activeLimit (blockedByWalls r) with
      | [] => none
      -- a wall covers `now`
      | iv :: _ =>
        if r.now.sec < iv.1 then none
        else if r.activeStop a iv.2 ≤ r.now.sec then none
        else some ⟨a.id, r.now.sec, r.activeStop a iv.2, r.activeLeft a⟩

/-- **Everything a reservation satisfies**, read off the one branch that builds it: it is the
running item's, it starts at `now`, it is not empty, it ends inside the first free stretch of
`[now, limit)`, and it ends no later than the block boundary. -/
theorem PlanReq.activeRun_spec (r : PlanReq) (q : ActiveRes) (h : r.activeRun = some q) :
    ∃ a iv, r.state.active = some a ∧ q.id = a.id ∧ q.start = r.now.sec ∧ r.now.sec < q.stop ∧
      q.stop ≤ r.currentBlockEnd a.started.sec ∧ q.stop ≤ iv.2 ∧ iv.1 ≤ r.now.sec ∧
      iv ∈ Look.freeIntervals r.now.sec r.activeLimit (blockedByWalls r) ∧
      q.stop ≤ r.activeLimit := by
  unfold PlanReq.activeRun at h
  split at h
  · exact absurd h (by simp)
  · rename_i a ha
    split at h
    · exact absurd h (by simp)
    split at h
    · exact absurd h (by simp)
    split at h
    · exact absurd h (by simp)
    split at h
    · exact absurd h (by simp)
    -- (the fork's overtime refusal was split here until W-35, D57 (2), P46)
    split at h
    · exact absurd h (by simp)
    · rename_i iv rest hfree
      split at h
      · exact absurd h (by simp)
      · rename_i hge
        split at h
        · exact absurd h (by simp)
        · rename_i hgt
          have he := Option.some.inj h
          subst he
          have hiv : iv ∈ Look.freeIntervals r.now.sec r.activeLimit (blockedByWalls r) := by
            rw [hfree]; simp
          refine ⟨a, iv, ha, rfl, rfl, Nat.lt_of_not_le hgt, ?_, ?_, Nat.le_of_not_lt hge, hiv, ?_⟩
          · show r.activeStop a iv.2 ≤ _; unfold PlanReq.activeStop; split <;> omega
          · show r.activeStop a iv.2 ≤ _; unfold PlanReq.activeStop; split <;> omega
          · have := (Look.freeIntervals_inside_the_window hiv).2.2
            show r.activeStop a iv.2 ≤ _; unfold PlanReq.activeStop; split <;> omega

/-- **The reservation reaches at most one block past the later of `now` and its block's start** (§8.3's E1 over the row
choice 5b places, restated at W-41 for D78: a start after `now` is planned from `now`, its block ending `block_min` after
the START as fork `current_block_end` ends it, so the row is a block plus the (r.state.active.map (fun a => a.started.sec - r.now.sec)).getD 0 — the running block's logged start
less `now`, zero unless the clock is behind the log; written out, because a definition only proofs read would be code
the export never reaches, check 12's class).  `hb` is R10's: a `[day]` with a block length. -/
theorem PlanReq.the_reservation_reaches_at_most_one_block_past_its_start (r : PlanReq) (q : ActiveRes)
    (hb : r.blockMin ≠ 0) (h : r.activeRun = some q) : q.stop - q.start ≤ r.blockMin * 60 + (r.state.active.map (fun a => a.started.sec - r.now.sec)).getD 0 := by
  obtain ⟨a, iv, ha, -, hs, -, hcbe, -⟩ := r.activeRun_spec q h
  have hl : (r.state.active.map (fun a => a.started.sec - r.now.sec)).getD 0 = a.started.sec - r.now.sec := by rw [ha]; rfl
  by_cases hst : a.started.sec ≤ r.now.sec
  · have hcb := r.currentBlockEnd_within_a_block a.started.sec hst hb
    omega
  · have hz : Look.spanMinutes a.started.sec r.now.sec = 0 := by unfold Look.spanMinutes; rw [Nat.sub_eq_zero_of_le (by omega)]
    have hcb : r.currentBlockEnd a.started.sec = a.started.sec + 60 * r.blockMin := by
      unfold PlanReq.currentBlockEnd blockBoundary; rw [if_neg hb, hz, Nat.zero_div, Nat.zero_add, Nat.one_mul]
    omega

/-- **The reservation is free of every wall** — it is placed inside the *first* free stretch
`Look.freeIntervals` reports, and the fork refuses outright when that stretch does not start at
`now`.  No second walk over the walls is written here (AGENTS §5.3). -/
theorem PlanReq.the_reservation_is_free_of_every_wall (r : PlanReq) (q : ActiveRes)
    (h : r.activeRun = some q) {w : Nat × Nat} (hw : w ∈ blockedByWalls r) {t : Nat}
    (h1 : q.start ≤ t) (h2 : t < q.stop) : ¬ (w.1 ≤ t ∧ t < w.2) := by
  obtain ⟨a, iv, -, -, hstart, -, -, hle, hge, hiv, -⟩ := r.activeRun_spec q h
  refine ((Look.freeIntervals_are_the_free_units r.now.sec r.activeLimit
    (blockedByWalls r) t).1 ⟨iv, hiv, ?_, ?_⟩).2.2 w hw
  · omega
  · omega

/-- **The reservation never runs past `active_run`'s limit** — the wind-down when the wind-down
is still ahead, the day's end otherwise. -/
theorem PlanReq.the_reservation_stops_at_the_limit (r : PlanReq) (q : ActiveRes)
    (h : r.activeRun = some q) : q.stop ≤ r.activeLimit :=
  let ⟨_, _, _, _, _, _, _, _, _, _, hx⟩ := r.activeRun_spec q h
  hx

/-- **The span the reservation blocks**, in the order fork `run()` pushes it: onto `blocked`
before `place_mandatory_and_pref` and before the cut. -/
def PlanReq.reservedSpan (r : PlanReq) : List (Nat × Nat) :=
  match r.activeRun with
  | none => []
  | some q => [(q.start, q.stop)]

/-- **Fork `run()`'s `blocked` at the moment step 2 starts** (`planner.rs:936`): the walls, the
running interruption, **and the reservation**.  README gap **434** — *"choice 5b's Active
reservation is not in `blockedByWalls`, so step 2 can place a routine over the running block"* —
is closed here, and `a_routine_is_never_placed_over_the_running_block` is the law. -/
def PlanReq.blockedBeforeRoutines (r : PlanReq) : List (Nat × Nat) :=
  blockedByWalls r ++ r.reservedSpan

/-- **Fork `active_run`'s `multiplier`** (`planner.rs:1234-1237`): `cands.iter().find(|c| c.id ==
active.id).map(|c| c.multiplier)` — the §8.5 multiplier of the first candidate the request carries
under the running item's id, `none` when none does.  It is `Look.PlanFacts.multiplier` as the wire
decoded it (`CapWire.multiplierOfWire`), the field every assigned row's `mult` already reads
(`Planner.groupOf`): a candidate fact read, not derived (D34).  README gap **550**, closed at W-37. -/
def PlanReq.candMult (r : PlanReq) (i : Id) : Option Arith.Pos :=
  (r.cands.val.find? (fun cf => cf.1.id == i)).map (fun cf => cf.1.plan.val.multiplier)

/-- **`emit_segments`' reservation row** (`planner.rs:1741`): a Block that carries **no slot
energy**, marked `▶`, with the minutes it still needs, and the running candidate's multiplier
(`PlanReq.candMult`, fork `multiplier: run.multiplier`).  The multiplier was `none` from P3 to
W-36 — README gap 550, which named P4 and then P8 and was cleared by neither. -/
def PlanReq.activeRow (r : PlanReq) : List Seg :=
  match r.activeRun with
  | none => []
  | some q =>
    [{ start := q.start, stop := q.stop, kind := .block, energy := none, item := some q.id,
       inst := none, flags := { SegFlags.none with current := true },
       planned := some q.leftMin, mult := r.candMult q.id, note := some (.runningLeft q.leftMin) }]

/-- A row of `activeRow` is the reservation's, with its own endpoints. -/
theorem PlanReq.mem_activeRow (r : PlanReq) (t : Seg) (h : t ∈ r.activeRow) :
    ∃ q, r.activeRun = some q ∧ t.start = q.start ∧ t.stop = q.stop ∧ t.kind = SegKind.block ∧
      t.energy = none ∧ t.flags.current = true ∧ t.item = some q.id := by
  unfold PlanReq.activeRow at h
  split at h
  · exact absurd h (by simp)
  · rename_i q hq
    simp only [List.mem_singleton] at h
    subst h
    exact ⟨q, hq, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The reservation carries no slot energy** (§8.2 choice 5b: "it is a reservation, not a
slot"), and it is the running item's Block row.  This is what makes `PlanCheck.energyFilterOk`
true of it without an exception — the `energy = none` branch, not `isActive`'s escape. -/
theorem PlanReq.activeRow_is_an_energyless_block (r : PlanReq) (s : Seg) (h : s ∈ r.activeRow) :
    s.kind = SegKind.block ∧ s.energy = none ∧ s.flags.current = true ∧
      s.item = r.state.activeId ∧ s.start = r.now.sec := by
  obtain ⟨q, hq, hst, -, hk, he, hc, hi⟩ := r.mem_activeRow s h
  obtain ⟨a, -, ha, hid, hs0, -⟩ := r.activeRun_spec q hq
  refine ⟨hk, he, hc, ?_, by rw [hst, hs0]⟩
  rw [hi, hid]
  unfold RuntimeIn.activeId
  rw [ha]
  rfl

/-- **Fork `place_mandatory_and_pref`'s loop body** (`planner.rs:1362`).  A mandatory instance
takes the earliest feasible position before the wind-down, and reaches into the evening only when
its window leaves no other choice; anything else is placed at a free `pref:` anchor or deferred to
step 6.  Each placement joins the blocked list, so two routines cannot take one stretch.

The deferred branch writes `placedAt := none` rather than leaving the field alone.  The fork
never *assigns* `r.placed` there and the field starts `None`, so it is the same value on every
input the fork can build; writing it makes the total function say so instead of relying on the
caller (AGENTS §5.2). -/
def placeStep (r : PlanReq) (acc : List Placed × List (Nat × Nat)) (q : Placed) :
    List Placed × List (Nat × Nat) :=
  let dur := 60 * q.inst.durMin
  let lo := max q.span.1 r.now.sec
  let dayOnly := r.night :: acc.2
  if q.inst.mandatory then
    match earliestFree lo q.span.2 dur dayOnly with
    | some t => ({ q with placedAt := some (t, t + dur) } :: acc.1, (t, t + dur) :: acc.2)
    | none =>
      match earliestFree lo q.span.2 dur acc.2 with
      | some t => ({ q with placedAt := some (t, t + dur) } :: acc.1, (t, t + dur) :: acc.2)
      | none => ({ q with placedAt := none, deferred := true } :: acc.1, acc.2)
  else
    match r.anchorOf q.inst.id with
    | some a =>
      if lo ≤ a ∧ a + dur ≤ q.span.2 ∧ overlapsAny a (a + dur) dayOnly = false then
        ({ q with placedAt := some (a, a + dur) } :: acc.1, (a, a + dur) :: acc.2)
      else ({ q with placedAt := none, deferred := true } :: acc.1, acc.2)
    | none => ({ q with placedAt := none, deferred := true } :: acc.1, acc.2)

/-- The instance that is sleep (fork `collect_routines`' second return). -/
def PlanReq.sleepInstance (r : PlanReq) : Option Placed := (splitSleep r r.routineInstances).1

/-- **Fork `run()`'s placement fold** — the whole of `place_mandatory_and_pref`, carrying both
halves: the instances it placed and the `blocked` list it grew.  Step 3 needs the second half
(`planner.rs:940`: `let mut slot_blocked = blocked.clone()`), which `placedRoutines` throws
away, so the fold is named once and projected twice rather than run twice. -/
def PlanReq.placementFold (r : PlanReq) : List Placed × List (Nat × Nat) :=
  (sortRoutines (splitSleep r r.routineInstances).2).foldl (placeStep r)
    ([], r.blockedBeforeRoutines)

/-- **§8.2 step 2, run**: today's window instances, sorted, each placed or deferred.  D9-21: a
`List.foldl` over a list `Capped` bounds at `maxCands`.

**Since step P3 the fold starts from `blockedBeforeRoutines`**, which is `blockedByWalls` plus
§8.2 choice 5b's reservation — fork `run()` pushes the running block onto `blocked` *before*
this call (`planner.rs:934`).  README gap **434** closed. -/
def PlanReq.placedRoutines (r : PlanReq) : List Placed := r.placementFold.1.reverse

/-! ### What a placement satisfies

These are the laws the placement rule owes, and they are what makes `Negative.lean`'s "a routine
placed outside its window" a cheat that does not close. -/

/-- **What a placed routine satisfies**: it sits inside its own span, starts at or after `now`,
and takes exactly the minutes the instance asked for. -/
def PlacedOk (r : PlanReq) (p : Placed) : Prop :=
  ∀ a b, p.placedAt = some (a, b) →
    max p.span.1 r.now.sec ≤ a ∧ b ≤ p.span.2 ∧ b = a + 60 * p.inst.durMin

/-- One step keeps it. -/
theorem placeStep_keeps_PlacedOk (r : PlanReq) (acc : List Placed × List (Nat × Nat))
    (q : Placed) (h : ∀ z ∈ acc.1, PlacedOk r z) :
    ∀ z ∈ (placeStep r acc q).1, PlacedOk r z := by
  have hdef : ∀ z : Placed, z.placedAt = none → PlacedOk r z := by
    intro z hz a b hab; rw [hz] at hab; exact absurd hab (by simp)
  have hnew : ∀ t : Nat,
      max q.span.1 r.now.sec ≤ t → t + 60 * q.inst.durMin ≤ q.span.2 →
      PlacedOk r { q with placedAt := some (t, t + 60 * q.inst.durMin) } := by
    intro t h1 h2 a b hab
    simp only [Option.some.injEq, Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    exact ⟨h1, h2, rfl⟩
  unfold placeStep
  simp only
  split
  · split
    · next t ht =>
      obtain ⟨g1, g2⟩ := earliestFree_inside ht
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hnew t g1 g2
      · exact h z hz
    · split
      · next t ht =>
        obtain ⟨g1, g2⟩ := earliestFree_inside ht
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hnew t g1 g2
        · exact h z hz
      · intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hdef _ rfl
        · exact h z hz
  · split
    · next anc _ =>
      split
      · next hok =>
        intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hnew anc hok.1 hok.2.1
        · exact h z hz
      · intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hdef _ rfl
        · exact h z hz
    · intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hdef _ rfl
      · exact h z hz

theorem foldl_placeStep_keeps_PlacedOk (r : PlanReq) :
    ∀ (l : List Placed) (acc : List Placed × List (Nat × Nat)),
      (∀ z ∈ acc.1, PlacedOk r z) → ∀ z ∈ (l.foldl (placeStep r) acc).1, PlacedOk r z
  | [], acc, h => by simpa using h
  | q :: t, acc, h => by
    simp only [List.foldl_cons]
    exact foldl_placeStep_keeps_PlacedOk r t _ (placeStep_keeps_PlacedOk r acc q h)

/-- **§8.2 step 2's own law: a placed routine is inside its window.**  This is the sentence the
step is written to make true, and `Negative.lean`'s "a routine placed outside its window" is the
claim it refuses. -/
theorem a_placed_routine_is_inside_its_window (r : PlanReq) (p : Placed)
    (hp : p ∈ r.placedRoutines) (a b : Nat) (hab : p.placedAt = some (a, b)) :
    max p.span.1 r.now.sec ≤ a ∧ b ≤ p.span.2 ∧ b = a + 60 * p.inst.durMin := by
  unfold PlanReq.placedRoutines PlanReq.placementFold at hp
  rw [List.mem_reverse] at hp
  exact foldl_placeStep_keeps_PlacedOk r _ _ (by simp) p hp a b hab

/-! ### A placement never lands on something already blocked

The half of the fold `PlacedOk` does not state, and the half README gap **434** is about: every
stretch the placement reads as free is free of the list it started from, and since step P3 that
list holds §8.2 choice 5b's reservation. -/

/-- **A placement is off every span the fold started blocked.** -/
def PlacedOffThe (ws : List (Nat × Nat)) (p : Placed) : Prop :=
  ∀ a b, p.placedAt = some (a, b) → ∀ u, a ≤ u → u < b → Look.covered ws u = false

/-- One step only ever conses onto the blocked list, so it keeps everything already there. -/
theorem placeStep_grows_the_blocked (r : PlanReq) (W : List (Nat × Nat))
    (acc : List Placed × List (Nat × Nat)) (q : Placed) (hsub : ∀ w ∈ W, w ∈ acc.2) :
    ∀ w ∈ W, w ∈ (placeStep r acc q).2 := by
  unfold placeStep
  simp only
  split
  · split
    · exact fun w hw => List.mem_cons_of_mem _ (hsub w hw)
    · split
      · exact fun w hw => List.mem_cons_of_mem _ (hsub w hw)
      · exact hsub
  · split
    · split
      · exact fun w hw => List.mem_cons_of_mem _ (hsub w hw)
      · exact hsub
    · exact hsub

/-- One step keeps it, and keeps the initial list inside the accumulator. -/
theorem placeStep_keeps_PlacedOffThe (r : PlanReq) (W : List (Nat × Nat))
    (acc : List Placed × List (Nat × Nat)) (q : Placed)
    (hsub : ∀ w ∈ W, w ∈ acc.2) (h : ∀ z ∈ acc.1, PlacedOffThe W z) :
    (∀ w ∈ W, w ∈ (placeStep r acc q).2) ∧ ∀ z ∈ (placeStep r acc q).1, PlacedOffThe W z := by
  have hcov : ∀ (vs : List (Nat × Nat)) (u : Nat), (∀ w ∈ W, w ∈ vs) →
      Look.covered vs u = false → Look.covered W u = false := by
    intro vs u hv hc
    cases hw : Look.covered W u with
    | false => rfl
    | true =>
      obtain ⟨w, hwm, h1, h2⟩ := Look.covered_eq_true.1 hw
      exact absurd hc (by simp [Look.covered_eq_true.2 ⟨w, hv w hwm, h1, h2⟩])
  have hdef : ∀ z : Placed, z.placedAt = none → PlacedOffThe W z := by
    intro z hz a b hab; rw [hz] at hab; exact absurd hab (by simp)
  unfold placeStep
  simp only
  split
  · split
    · next t ht =>
      refine ⟨fun w hw => List.mem_cons_of_mem _ (hsub w hw), fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · intro a b hab u h1 h2
        simp only [Option.some.injEq, Prod.mk.injEq] at hab
        obtain ⟨rfl, rfl⟩ := hab
        exact hcov _ u (fun w hw => List.mem_cons_of_mem _ (hsub w hw))
          (earliestFree_is_free ht h1 h2)
      · exact h z hz
    · split
      · next t ht =>
        refine ⟨fun w hw => List.mem_cons_of_mem _ (hsub w hw), fun z hz => ?_⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · intro a b hab u h1 h2
          simp only [Option.some.injEq, Prod.mk.injEq] at hab
          obtain ⟨rfl, rfl⟩ := hab
          exact hcov _ u hsub (earliestFree_is_free ht h1 h2)
        · exact h z hz
      · refine ⟨hsub, fun z hz => ?_⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hdef _ rfl
        · exact h z hz
  · split
    · next anc _ =>
      split
      · next hok =>
        refine ⟨fun w hw => List.mem_cons_of_mem _ (hsub w hw), fun z hz => ?_⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · intro a b hab u h1 h2
          simp only [Option.some.injEq, Prod.mk.injEq] at hab
          obtain ⟨rfl, rfl⟩ := hab
          exact hcov _ u (fun w hw => List.mem_cons_of_mem _ (hsub w hw))
            (overlapsAny_false_covers_nothing hok.2.2 h1 h2)
        · exact h z hz
      · refine ⟨hsub, fun z hz => ?_⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hdef _ rfl
        · exact h z hz
    · refine ⟨hsub, fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact hdef _ rfl
      · exact h z hz

/-- The fold only grows the blocked list, so everything it started with is still there when
step 3 reads it. -/
theorem foldl_placeStep_grows_the_blocked (r : PlanReq) (W : List (Nat × Nat)) :
    ∀ (l : List Placed) (acc : List Placed × List (Nat × Nat)),
      (∀ w ∈ W, w ∈ acc.2) → ∀ w ∈ W, w ∈ (l.foldl (placeStep r) acc).2
  | [], acc, h => by simpa using h
  | q :: t, acc, hs => by
    simp only [List.foldl_cons]
    exact foldl_placeStep_grows_the_blocked r W t _ (placeStep_grows_the_blocked r W acc q hs)

theorem foldl_placeStep_keeps_PlacedOffThe (r : PlanReq) (W : List (Nat × Nat)) :
    ∀ (l : List Placed) (acc : List Placed × List (Nat × Nat)),
      (∀ w ∈ W, w ∈ acc.2) → (∀ z ∈ acc.1, PlacedOffThe W z) →
      ∀ z ∈ (l.foldl (placeStep r) acc).1, PlacedOffThe W z
  | [], acc, _, h => by simpa using h
  | q :: t, acc, hs, h => by
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := placeStep_keeps_PlacedOffThe r W acc q hs h
    exact foldl_placeStep_keeps_PlacedOffThe r W t _ h1 h2

/-- **§8.2 choice 5b, from step 2's side: a routine is never placed over the running block.**
README gap **434** — *"on a day with a block running, a mandatory routine may be placed on top
of it"* — closed, and stated over the reservation itself rather than over the list it sits in. -/
theorem a_routine_is_never_placed_over_the_running_block (r : PlanReq) (p : Placed)
    (hp : p ∈ r.placedRoutines) (a b : Nat) (hab : p.placedAt = some (a, b))
    (q : ActiveRes) (hq : r.activeRun = some q) {u : Nat} (h1 : a ≤ u) (h2 : u < b) :
    ¬ (q.start ≤ u ∧ u < q.stop) := by
  have hmem : (q.start, q.stop) ∈ r.blockedBeforeRoutines := by
    unfold PlanReq.blockedBeforeRoutines PlanReq.reservedSpan
    rw [hq]
    simp
  unfold PlanReq.placedRoutines PlanReq.placementFold at hp
  rw [List.mem_reverse] at hp
  have := foldl_placeStep_keeps_PlacedOffThe r r.blockedBeforeRoutines _ _
    (fun w hw => hw) (by simp) p hp a b hab u h1 h2
  intro hc
  exact absurd this (by simp [Look.covered_eq_true.2 ⟨(q.start, q.stop), hmem, hc.1, hc.2⟩])

/-! ### The rows step 2 places -/

/-- Fork `emit_segments`' `scheduled` test (`planner.rs:1811`): a `routines.md` or `optional.md`
line is the day's furniture and carries no `ci`; a backlog item with a `win:` keeps §7's scale.
The fork asks `item.horizon`; the kernel asks which file the live line is in, which is the same
question (`docKindAt`, `Plan.lean`). -/
def PlanReq.isFurniture (r : PlanReq) (i : Id) : Bool :=
  match r.plan.val.store.get i with
  | none => false
  | some e =>
    (docKindAt r.plan.val e.val.live.doc == DocKind.routines) ||
      (docKindAt r.plan.val e.val.live.doc == DocKind.optional)

/-- The energy a routine row carries: none for furniture, the item's `ci` otherwise.
`effectiveCi` is `Plan.lean`'s §3.2 walk and is not re-derived here (AGENTS §5.3). -/
def PlanReq.routineEnergy (r : PlanReq) (i : Id) : Option (Fin 6) :=
  if r.isFurniture i then none else some (effectiveCi r.plan.val i)

/-- **Fork `emit_segments`' routine-row `⚠`** (`planner.rs:1493-1497`): `scheduled &&
cands.iter().position(|c| c.id == r.id).is_some_and(|i| prios[i].p == 0)`.  A Routine row is
marked hot only when it is a **scheduled** window task — not `routines.md`/`optional.md`
furniture, `PlanReq.isFurniture`, the test the row's energy already reads — and the first
candidate carrying its id was answered `p = 0` by §8.2 step 4's pass (`PlanReq.answerFor`, first
by id, as the fork's `position` is).  The `p` is the pass's answer and nothing here derives a
candidate fact (D34); it is the reading every assigned row's `⚠` already makes
(`assignedSeg`: `m.key.p == 0`, and `key.p` is `p.getD 7`, so the two agree on every answer).
README gaps **2870** and **435**, closed at W-37. -/
def PlanReq.routineHot (r : PlanReq) (i : Id) : Bool :=
  !r.isFurniture i && (r.answerFor i).any (fun o => o.out.p == some 0)

/-- **Fork `emit_segments`' routine loop** (`planner.rs:1802-1836`): one Routine row per *placed*
instance; a deferred one has no row until step 6 places it (P6).

The `hot` mark is §7.2's `p = 0` (`PlanReq.routineHot`).  It was `false` on every row from P2 to
W-36 — README gap 435, which named P4 as the step to set it, and gap 2870, which found it an R3
prerequisite on the fixture days (`^a3`'s row) — and is the pass's answer since W-37. -/
def PlanReq.routineRow (r : PlanReq) (q : Placed) : List Seg :=
  match q.placedAt with
  | none => []
  | some (a, b) =>
    [{ start := a, stop := b, kind := .routine, energy := r.routineEnergy q.inst.id,
       item := some q.inst.id, inst := q.inst.inst.map (fun k => (q.inst.id, k)),
       flags := { SegFlags.none with mandatory := q.inst.mandatory, deferred := q.deferred,
                                     hot := r.routineHot q.inst.id },
       planned := some q.inst.durMin, mult := none, note := none }]

/-- **Fork `emit_segments`' close of the day** (`planner.rs:1962-1988`): the wind-down runs from
`[day] wind_down` to `bed`.  §8.2 step 3 will find the evening closed to cutting, because
`night()` is in the blocked list. -/
def PlanReq.windDownSeg (r : PlanReq) : Seg :=
  { start := r.windDownSec, stop := min r.bedSec r.dayEnd, kind := .windDown, energy := none,
    item := none, inst := none, flags := SegFlags.none, planned := none, mult := none,
    note := none }

/-- Fork `emit_segments`' Sleep row: from `bed` (never before `now`) to midnight, carrying the
sleep instance the collection took out. -/
def PlanReq.sleepSeg (r : PlanReq) : Seg :=
  { start := min (max r.bedSec r.now.sec) r.dayEnd, stop := r.dayEnd, kind := .sleep,
    energy := none, item := r.sleepInstance.map (fun q => q.inst.id),
    inst := r.sleepInstance.bind (fun q => q.inst.inst.map (fun k => (q.inst.id, k))),
    flags := SegFlags.none, planned := r.sleepInstance.map (fun q => q.inst.durMin),
    mult := none, note := none }

def PlanReq.eveningRows (r : PlanReq) : List Seg :=
  (if r.now.sec < r.windDownSec ∧ r.windDownSec < r.dayEnd then [r.windDownSeg] else []) ++
    (if min (max r.bedSec r.now.sec) r.dayEnd < r.dayEnd then [r.sleepSeg] else [])

/-- **The rows a routine list and the evening make**, over the list rather than over one
particular list (AGENTS §5.3's widen-and-project).  Fork `emit_segments` renders the routine
instances **once**, from the array `place_deferred` has finished with, so this is the one
renderer and `stepTwoSegs` and `dayRoutineSegs` (step P6) are its two arguments: what step 2
had, and what the day really carries. -/
def routineRows (r : PlanReq) (qs : List Placed) : List Seg :=
  qs.flatMap r.routineRow ++ r.eveningRows

/-- **§8.2 step 2's rows.** -/
def stepTwoSegs (r : PlanReq) : List Seg := routineRows r r.placedRoutines

/-- **Three kinds of row and no other, whichever routine list it is given.** -/
theorem routineRows_kinds (r : PlanReq) (qs : List Placed) (t : Seg) (h : t ∈ routineRows r qs) :
    t.kind = SegKind.routine ∨ t.kind = SegKind.windDown ∨ t.kind = SegKind.sleep := by
  simp only [routineRows, List.mem_append] at h
  rcases h with h | h
  · simp only [List.mem_flatMap] at h
    obtain ⟨q, _, hq⟩ := h
    unfold PlanReq.routineRow at hq
    split at hq
    · cases hq
    · simp only [List.mem_singleton] at hq; subst hq; exact Or.inl rfl
  · unfold PlanReq.eveningRows at h
    simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton] at h; subst h; exact Or.inr (Or.inl rfl)
      · cases h
    · split at h
      · simp only [List.mem_singleton] at h; subst h; exact Or.inr (Or.inr rfl)
      · cases h

/-- **Step 2 places three kinds of row and no other.** -/
theorem stepTwoSegs_kinds (r : PlanReq) (t : Seg) (h : t ∈ stepTwoSegs r) :
    t.kind = SegKind.routine ∨ t.kind = SegKind.windDown ∨ t.kind = SegKind.sleep :=
  routineRows_kinds r _ t h

/-- **No routine row is a Wall**, so the two wall laws are untouched by them. -/
theorem routineRows_are_not_walls (r : PlanReq) (qs : List Placed) (t : Seg)
    (h : t ∈ routineRows r qs) : t.kind ≠ SegKind.wall := by
  rcases routineRows_kinds r qs t h with h1 | h1 | h1 <;> rw [h1] <;> intro hc <;> cases hc

/-- **No row of step 2 is a Wall**, so the two wall laws are untouched by it. -/
theorem stepTwoSegs_are_not_walls (r : PlanReq) (t : Seg) (h : t ∈ stepTwoSegs r) :
    t.kind ≠ SegKind.wall := routineRows_are_not_walls r _ t h

/-- **No routine row is a Block**, so every block-side check of the battery is about the
replayed past and §8.2 choice 5b's reservation and nothing else
(`PlanCheck.dayPlan_block_rows_are_replayed_reserved_or_assigned`). -/
theorem routineRows_are_not_blocks (r : PlanReq) (qs : List Placed) (t : Seg)
    (h : t ∈ routineRows r qs) : t.kind ≠ SegKind.block := by
  rcases routineRows_kinds r qs t h with h1 | h1 | h1 <;> rw [h1] <;> intro hc <;> cases hc

/-- **No row of step 2 is a Block.** -/
theorem stepTwoSegs_are_not_blocks (r : PlanReq) (t : Seg) (h : t ∈ stepTwoSegs r) :
    t.kind ≠ SegKind.block := routineRows_are_not_blocks r _ t h

/-- **And none of them is work**, so §8.3's assigned set is still empty after `now`
(`SegKind.isWork`: `Block` and `Batch`, and nothing else). -/
theorem routineRows_are_not_work (r : PlanReq) (qs : List Placed) (t : Seg)
    (h : t ∈ routineRows r qs) : t.kind.isWork = false := by
  rcases routineRows_kinds r qs t h with h1 | h1 | h1 <;> rw [h1] <;> rfl

/-- **And no row of step 2 is work.** -/
theorem stepTwoSegs_are_not_work (r : PlanReq) (t : Seg) (h : t ∈ stepTwoSegs r) :
    t.kind.isWork = false := routineRows_are_not_work r _ t h

/-- **A Routine row is exactly where the placement put it**, carrying the item and the instance
key.  With `a_placed_routine_is_inside_its_window` this is §8.2 step 2's promise end to end: the
row a reader sees is inside the window the instance declared. -/
theorem a_routine_row_is_where_the_placement_put_it (r : PlanReq) (q : Placed) (t : Seg)
    (h : t ∈ r.routineRow q) :
    ∃ a b, q.placedAt = some (a, b) ∧ t.start = a ∧ t.stop = b ∧
      t.kind = SegKind.routine ∧ t.item = some q.inst.id := by
  unfold PlanReq.routineRow at h
  split at h
  · cases h
  · next a b hq =>
    simp only [List.mem_singleton] at h
    subst h
    exact ⟨a, b, hq, rfl, rfl, rfl, rfl⟩

/-! ############################################################################
## §8.2 step 3 — the slots (stage 6, step P3)

Fork `run()`'s step-3 paragraph (`planner.rs:938-955`), choice 4: *"`cut_slots_around` with the
placed routines as **rests**, continuing the break counter from the log"*.

**This section computes nothing.**  Every line of it is an argument list for a stage-5
definition: the cut is `Look.cutSlots` (L3), the energies are `Look.energizeToday` (L4, widened
here rather than forked), the free stretches inside it are `Look.freeIntervals`, and the window
is `Look.day0Window` through `PlanReq.window`.  AGENTS §5.3 and design §1.2-§1.3 name these by
hand precisely so that a second `cutSlots`, a second `energize` or a second `windowEnd` is a
defect rather than a style question, and the grep that proves there is none is in this step's
README block.

*The slots are not rows.*  A slot is where §8.2 step 5 may put a Block and step 7 may put Rest;
neither step exists yet, so `dayPlan` gains exactly **one** row here — choice 5b's reservation
— and the Break rows the cut produces stayed out of the day, because fork `emit_segments` keeps
a break only when work touches it (`kept_breaks(breaks, slots, assign)`) and `assign` was P5's.
README gap **551** recorded that (closed at W-37: `PlanReq.keptBreakRows`), and it is why
`plan_places_no_block_over_a_break` was **not** discharged by this step.
############################################################################ -/

/-- **Fork `blocks_since_last_break`** (`planner.rs:2229`): today's `start`s after the last break, counted, off this call's own
run (D24's seam, D9).  Since W-40 the RUNNING break's start is a break here too, at the instant the `break` line `tm break` appends
will carry (owner D77, parity P67, README gaps 3480 and 3666): a running break resets the counter as the same break once logged. -/
def PlanReq.sinceBreak (r : PlanReq) : Nat :=
  match r.todayRecord with
  | none => 0
  | some d =>
    let starts := d.breaks.map (·.t.1.sec) ++ (r.state.brk.bind (·.started)).toList.map (·.sec)
    let lastBreak : Option Nat := if starts.isEmpty then none else some (starts.foldl max 0)
    (d.starts.filter (fun s =>
      match lastBreak with | none => true | some t => decide (t < s.t.1.sec))).length

/-- **Fork `run()`'s `rests`** (`planner.rs:939`): the stretches step 2 placed, which the cut treats as rests — one of at least
`break_min` ending where a stretch does resets the break counter (`Look.restfulEnd`).  The running break was one from W-35 (P45)
until W-40 (D77): `PlanReq.sinceBreak` counts it now, and `blockedByWalls` keeps its span blocked. -/
def PlanReq.restsToday (r : PlanReq) : List (Nat × Nat) :=
  r.placedRoutines.filterMap (·.placedAt)

/-- **Fork `run()`'s `slot_blocked`** (`planner.rs:940-942`): everything blocked when step 2
finishes, plus `night()` — so nothing is cut in the evening. -/
def PlanReq.slotBlocked (r : PlanReq) : List (Nat × Nat) := r.night :: r.placementFold.2

/-- **Fork `run()`'s `from`** (`planner.rs:943`): `now`, never before the window opens and
never past where it closes. -/
def PlanReq.cutFrom (r : PlanReq) : Nat := min (max r.now.sec r.window.1) r.window.2

/-- **§8.2 step 3's cut**, which is `Look.cutSlots` and nothing else (design §1.2). -/
def PlanReq.todayCut (r : PlanReq) : Look.Cut :=
  Look.cutSlots r.look.day.cut r.cutFrom r.window.2 r.slotBlocked r.restsToday r.sinceBreak

/-- The slots step 5 will assign into. -/
def PlanReq.todaySlots (r : PlanReq) : List Look.Slot := r.todayCut.slots

/-- The cut's breaks; the day keeps the ones work touches (`PlanReq.keptBreakRows`, W-37). -/
def PlanReq.todayBreaks (r : PlanReq) : List (Nat × Nat) := r.todayCut.breaks

/-- **Fork `run()`'s `slots`** (`planner.rs:952`): `capacity::energize(&cut.slots, &ectx)` with
today's `EnergyCtx` — the prediction at the hours since wake, less the sleep-debt shift,
corrected by today's posterior, then the home cap, in that order (cheat 158's order).  It is
`Look.energizeToday`, the widening of step L9's `day0Slots`; **no level is computed here**. -/
def PlanReq.energisedSlots (r : PlanReq) : List (Fin 6 × Look.Slot) :=
  Look.energizeToday r.look r.todaySlots

/-! ### What the cut is, said as projections rather than re-derived -/

/-- **The cut is L3's**, at step 3's arguments.  A `rfl`, and it is the point of the section:
there is no second `cutSlots` for this one to disagree with. -/
theorem PlanReq.todayCut_is_the_lookaheads (r : PlanReq) :
    r.todayCut =
      Look.cutSlots r.look.day.cut r.cutFrom r.window.2 r.slotBlocked r.restsToday r.sinceBreak :=
  rfl

/-- **The energies are L4's**, at step 3's slots. -/
theorem PlanReq.energisedSlots_are_the_lookaheads (r : PlanReq) :
    r.energisedSlots = Look.energizeToday r.look r.todaySlots := rfl

/-- **A slot's level is today's, through the one posterior** (`Look.todayEnergy`, cheat 158). -/
theorem PlanReq.a_slots_level_is_todays_energy (r : PlanReq) (e : Fin 6) (s : Look.Slot)
    (h : (e, s) ∈ r.energisedSlots) : e = Look.todayEnergy r.look ⟨s.start, 0⟩ := by
  unfold PlanReq.energisedSlots Look.energizeToday at h
  simp only [List.mem_map, Prod.mk.injEq] at h
  obtain ⟨t, _, h1, h2⟩ := h
  subst h2; exact h1.symm

/-- **Every slot lies inside the window, at or after `now`** — L3's
`cutSlots_inside_the_window` at these arguments. -/
theorem PlanReq.a_slot_is_inside_the_window (r : PlanReq) (s : Look.Slot)
    (h : s ∈ r.todaySlots) : r.cutFrom ≤ s.start ∧ s.start < s.stop ∧ s.stop ≤ r.window.2 := by
  unfold PlanReq.todaySlots PlanReq.todayCut at h
  exact Look.cutSlots_inside_the_window _ _ _ _ _ _ h

/-- **No slot is cut on top of a wall, the running interruption, the running block or a placed
routine** — L3's `cutSlots_avoid_the_walls`, over the list step 3 hands it. -/
theorem PlanReq.a_slot_touches_nothing_blocked (r : PlanReq) (s : Look.Slot)
    (h : s ∈ r.todaySlots) {w : Nat × Nat} (hw : w ∈ r.slotBlocked ++ r.restsToday) {t : Nat}
    (h1 : s.start ≤ t) (h2 : t < s.stop) : ¬ (w.1 ≤ t ∧ t < w.2) := by
  unfold PlanReq.todaySlots PlanReq.todayCut at h
  exact Look.cutSlots_avoid_the_walls _ _ _ _ _ _ h hw h1 h2

/-- **The running block is not cut into slots** (§8.2 choice 5b: it is a reservation, not a
slot).  The reservation reaches the cut because step 2's fold started from
`blockedBeforeRoutines` and only ever grows its list. -/
theorem PlanReq.no_slot_touches_the_running_block (r : PlanReq) (q : ActiveRes)
    (hq : r.activeRun = some q) (s : Look.Slot) (h : s ∈ r.todaySlots) {t : Nat}
    (h1 : s.start ≤ t) (h2 : t < s.stop) : ¬ (q.start ≤ t ∧ t < q.stop) := by
  have hmem : (q.start, q.stop) ∈ r.slotBlocked ++ r.restsToday := by
    refine List.mem_append_left _ ?_
    unfold PlanReq.slotBlocked
    refine List.mem_cons_of_mem _ ?_
    refine foldl_placeStep_grows_the_blocked r r.blockedBeforeRoutines _ _ (fun w hw => hw) _ ?_
    unfold PlanReq.blockedBeforeRoutines PlanReq.reservedSpan
    rw [hq]; simp
  exact r.a_slot_touches_nothing_blocked s h hmem h1 h2

/-- **A slot is never empty** — `Look.SlotShape`'s own first conjunct, read off L3's spec at
the planner's arguments.  It is what makes "the slot is free of every wall" an argument about a
real instant: an empty span touches nothing and would say nothing. -/
theorem PlanReq.a_slot_is_not_empty (r : PlanReq) (s : Look.Slot) (h : s ∈ r.todaySlots) :
    s.start < s.stop := by
  unfold PlanReq.todaySlots PlanReq.todayCut at h
  obtain ⟨-, -, -, h4, -, -, -, -⟩ :=
    Look.cutSlots_spec r.look.day.cut r.cutFrom r.window.2 r.slotBlocked r.restsToday r.sinceBreak
  exact (h4 s h).1.1

/-- **No slot is cut under a wall.**  `blockedByWalls` is inside `blockedBeforeRoutines`, which
is where step 2's fold starts and which it only ever grows
(`foldl_placeStep_grows_the_blocked`) — the same three lines
`no_slot_touches_the_running_block` takes for the reservation.  It is the half §8.2 step 5's
Block rows need: a row that spans a slot cannot overlap a Wall row, because the slot does not. -/
theorem PlanReq.no_slot_touches_a_wall (r : PlanReq) {v : Nat × Nat}
    (hv : v ∈ blockedByWalls r) (s : Look.Slot) (h : s ∈ r.todaySlots) {t : Nat}
    (h1 : s.start ≤ t) (h2 : t < s.stop) : ¬ (v.1 ≤ t ∧ t < v.2) := by
  have hmem : v ∈ r.slotBlocked ++ r.restsToday := by
    refine List.mem_append_left _ ?_
    unfold PlanReq.slotBlocked
    refine List.mem_cons_of_mem _ ?_
    refine foldl_placeStep_grows_the_blocked r r.blockedBeforeRoutines _ _ (fun w hw => hw) _ ?_
    unfold PlanReq.blockedBeforeRoutines
    exact List.mem_append_left _ hv
  exact r.a_slot_touches_nothing_blocked s h hmem h1 h2

/-- **The evening is not cut** — `night()` is in the blocked list, so no slot reaches the
wind-down.  §8.2 step 3's own sentence, and the reason `PlanCheck.noDemandingAfterWindDown`
will still hold when P5 puts a Block in a slot. -/
theorem PlanReq.no_slot_reaches_the_evening (r : PlanReq) (s : Look.Slot) (h : s ∈ r.todaySlots)
    {t : Nat} (h1 : s.start ≤ t) (h2 : t < s.stop) : ¬ (r.night.1 ≤ t ∧ t < r.night.2) :=
  r.a_slot_touches_nothing_blocked s h
    (List.mem_append_left _ (by unfold PlanReq.slotBlocked; simp)) h1 h2

/-- **The reservation never sits under a WindDown row** — README gap **437**, refuted.

The gap reads: *"`PlanCheck.noDemandingAfterWindDown` has no Active exception and needs one …
on a day replanned *after* the wind-down the reservation runs in the evening, and its item may
carry `ci ≥ 4`"*.  The premise is right and the conclusion does not follow, because the two
halves are **mutually exclusive by construction**: `active_run`'s limit is the wind-down
exactly when `now < wind_down` (`planner.rs:1531`), and `emit_segments` places a WindDown row
exactly when `wind_down > now` (`planner.rs:1962`, `PlanReq.eveningRows`).  A day whose
reservation may reach the evening therefore has **no WindDown row** for the check to compare it
with, and a day that has one caps the reservation at the wind-down.  So the check needs **no**
Active exception and none was added: `PlanCheck`'s eleven are still exactly as track G wrote
them, and README gap 437 is closed as **not a defect**. -/
theorem PlanReq.the_reservation_never_runs_under_a_wind_down_row (r : PlanReq) (q : ActiveRes)
    (h : r.activeRun = some q) (hrow : r.windDownSeg ∈ r.eveningRows) :
    q.stop ≤ r.windDownSeg.start := by
  have hnow : r.now.sec < r.windDownSec := by
    by_cases hc : r.now.sec < r.windDownSec ∧ r.windDownSec < r.dayEnd
    · exact hc.1
    · exfalso
      unfold PlanReq.eveningRows at hrow
      rw [if_neg hc] at hrow
      simp only [List.nil_append] at hrow
      by_cases hd : min (max r.bedSec r.now.sec) r.dayEnd < r.dayEnd
      · rw [if_pos hd] at hrow
        simp only [List.mem_singleton] at hrow
        have hkk : SegKind.windDown = SegKind.sleep := congrArg Seg.kind hrow
        cases hkk
      · rw [if_neg hd] at hrow; simp at hrow
  have hlim : r.activeLimit ≤ r.windDownSec := by
    unfold PlanReq.activeLimit; rw [if_pos hnow]; omega
  have hstop := r.the_reservation_stops_at_the_limit q h
  show q.stop ≤ r.windDownSec
  omega

/-- **No slot overlaps a break of the same cut** — L3's `cutSlots_no_slot_overlaps_a_break`,
which is the half of `plan_places_no_block_over_a_break` the cut owes.  The other half is
drawn since W-37: a Break row reaches the day only when work touches it (gap 551, closed).

(W-18: the goal itself no longer sits in `Goals.lean` waiting on both halves — as written it
is **false**, because the day's Break rows and Block rows alike include `pastRows`' replayed
ones, and it left the file as a §3.1-item-3 discharge.  What this theorem is a half of is now
`PlanCheck.plan_places_no_block_over_a_break`, the restatement over the Block rows that start
at or after `now`; gap 551 closed at W-37, `Planner.a_block_row_clears_a_kept_break`.) -/
theorem PlanReq.no_slot_overlaps_a_break (r : PlanReq) (s : Look.Slot) (hs : s ∈ r.todaySlots)
    (b : Nat × Nat) (hb : b ∈ r.todayBreaks) : s.stop ≤ b.1 ∨ b.2 ≤ s.start := by
  unfold PlanReq.todaySlots PlanReq.todayCut at hs
  unfold PlanReq.todayBreaks PlanReq.todayCut at hb
  exact Look.cutSlots_no_slot_overlaps_a_break _ _ _ _ _ _ hs hb

/-- **A full slot is exactly one block long**, and a short last slot is shorter — L3's, and the
half of E1 that will make P5's assigned Blocks fit inside `block_min` without a second
argument. -/
theorem PlanReq.a_slot_is_at_most_one_block (r : PlanReq) (s : Look.Slot)
    (h : s ∈ r.todaySlots) : s.stop - s.start ≤ 60 * r.blockMin := by
  show s.stop - s.start ≤ 60 * r.look.day.cut.blockMin
  unfold PlanReq.todaySlots PlanReq.todayCut at h
  cases hk : s.kind with
  | block =>
    have := (Look.cutSlots_block_is_block_min _ _ _ _ _ _ h hk).1
    omega
  | short =>
    have := (Look.cutSlots_short_block_is_at_least_min_last _ _ _ _ _ _ h hk).2.1
    omega


/-- **The past half never closes the day**: `pastKind` answers Block, Lost, Break or Routine
and never the evening's two kinds, so a WindDown row is step 2's and nobody else's. -/
theorem pastRows_are_not_wind_down (r : PlanReq) (s : Seg) (h : s ∈ pastRows r) :
    s.kind ≠ SegKind.windDown := by
  -- Since the owner's D65 (W-37 track T, parity P56) `pastRows` draws each replayed segment
  -- over the spans `pastSpans` answers — a Pause's with the day's walls cut out of it — so a
  -- row is read through `mem_pastRows` and not by unfolding a `filterMap`.  Its kind is
  -- `pastKind`'s either way, and `pastKind` never answers the evening's two kinds.  (Shorter
  -- than the proof it replaces; these lines keep every check-9 pin site below it where
  -- `kernel/mutations.txt` recorded it — `PastCut.lean`'s header says why.)
  --
  --
  obtain ⟨d, -, g, -, q, -, rfl⟩ := mem_pastRows.1 h
  cases hg : g.kind <;> simp [pastRowOf, pastKind, hg]

/-- **A WindDown row is `eveningRows`' own, and it exists only while the wind-down is ahead.**
This is what makes `PlanCheck.noDemandingAfterWindDown` true of §8.2 choice 5b's reservation
with no exception (README gap 437, and `the_reservation_never_runs_under_a_wind_down_row`). -/
theorem a_wind_down_row_is_the_evenings (r : PlanReq) (qs : List Placed) (t : Seg)
    (ht : t ∈ routineRows r qs) (hk : t.kind = SegKind.windDown) :
    r.now.sec < r.windDownSec ∧ r.windDownSec < r.dayEnd ∧ t = r.windDownSeg := by
  simp only [routineRows, List.mem_append] at ht
  rcases ht with h | h
  · simp only [List.mem_flatMap] at h
    obtain ⟨q, -, hq⟩ := h
    unfold PlanReq.routineRow at hq
    split at hq
    · exact absurd hq (by simp)
    · simp only [List.mem_singleton] at hq; subst hq; exact absurd hk (by simp)
  · unfold PlanReq.eveningRows at h
    simp only [List.mem_append] at h
    rcases h with h | h
    · by_cases hc : r.now.sec < r.windDownSec ∧ r.windDownSec < r.dayEnd
      · rw [if_pos hc] at h; simp only [List.mem_singleton] at h; exact ⟨hc.1, hc.2, h⟩
      · rw [if_neg hc] at h; exact absurd h (by simp)
    · by_cases hd : min (max r.bedSec r.now.sec) r.dayEnd < r.dayEnd
      · rw [if_pos hd] at h
        simp only [List.mem_singleton] at h; subst h
        exact absurd hk (by simp [PlanReq.sleepSeg])
      · rw [if_neg hd] at h; exact absurd h (by simp)

/-! ### The day, assembled -/

/-- **A deferred instance has no row until step 6 places it** — fork `emit_segments`' routine
loop skips an instance with no `placed`, and `place_deferred` (**P6**) is what gives it one. -/
theorem a_deferred_routine_has_no_row (r : PlanReq) (q : Placed) (h : q.placedAt = none) :
    r.routineRow q = [] := by
  unfold PlanReq.routineRow; rw [h]

/-- **§8.2 choice 5b's row** — the only row step P3 adds to the day.  The cut's slots are not
rows: a slot becomes a Block at step 5 or Rest at step 7, and a Break reaches the day only when
work touches it (`kept_breaks`; `PlanReq.keptBreakRows` since W-37, README gap **551**). -/
def reservationSegs (r : PlanReq) : List Seg := r.activeRow

/-- Every row §8.2 choice 5b places is a Block, so none of them is a Wall. -/
theorem reservationSegs_are_blocks (r : PlanReq) (t : Seg) (h : t ∈ reservationSegs r) :
    t.kind = SegKind.block := (r.activeRow_is_an_energyless_block t h).1

theorem reservationSegs_are_not_walls (r : PlanReq) (t : Seg) (h : t ∈ reservationSegs r) :
    t.kind ≠ SegKind.wall := by
  rw [reservationSegs_are_blocks r t h]; intro hc; cases hc

/-- The reservation row is the one `PlanCheck.isActive` names. -/
theorem the_reservation_row_names_the_running_item (r : PlanReq) (t : Seg)
    (h : t ∈ reservationSegs r) : ∃ a, r.state.activeId = some a ∧ t.item = some a := by
  obtain ⟨-, -, -, hit, -⟩ := r.activeRow_is_an_energyless_block t h
  obtain ⟨q, hq, -, -, -, -, -, hi⟩ := r.mem_activeRow t h
  obtain ⟨a, -, ha, hid, -⟩ := r.activeRun_spec q hq
  exact ⟨a.id, by unfold RuntimeIn.activeId; rw [ha]; rfl, by rw [hi, hid]⟩

/-- **The reservation row, unclamped**: on a day whose `now` is inside the calendar the forcing
is the identity on its start, and its stop is never past the reservation's own. -/
theorem the_reservation_row_is_exact (r : PlanReq) (q : ActiveRes) (hq : r.activeRun = some q)
    (hcal : r.now.sec + 1 < LogStamp.yearEnd) (t : Seg) (ht : t ∈ reservationSegs r) :
    (segOf t).val.start = r.now.sec ∧ r.now.sec < (segOf t).val.stop ∧
      (segOf t).val.stop ≤ q.stop ∧ (segOf t).val.stop < LogStamp.yearEnd := by
  obtain ⟨q', hq', hst, hsp, -, -, -, -⟩ := r.mem_activeRow t ht
  rw [hq] at hq'
  have he : q = q' := Option.some.inj hq'
  subst he
  obtain ⟨-, -, -, -, hs0, hlt, -⟩ := r.activeRun_spec q hq
  have e1 : (segOf t).val.start = clampSec t.start := rfl
  have e2 : (segOf t).val.stop = max (clampSec t.start) (clampSec t.stop) := rfl
  rw [e1, e2, hst, hsp]
  rw [hs0]
  simp only [clampSec, LogStamp.yearEnd] at *
  omega

/-! ############################################################################
## §8.2 step 4 — PRIORITY (stage 6, step P4)

`priorities = priority::compute(candidates, capacity_lookahead, log, cfg)` — spec §8.2 step 4,
one line, and the fork's `planner.rs:960-997` is the same: when the caller hands a ranking in
(and the shipped binary always does, `PlanInput::with_ranking`) step 4 *is* that ranking,
restricted to the candidates §9.1's overrides keep.  **That ranking is stage 5's**: the whole
of `Look.prioritiesWithFloors` — the EDF pass, §7.1's bin, §7.2's row table and §7.4's
hysteresis — was built at step L8 and has had exactly one caller since, the capacity op's
`Boundary.grantsOf`.  This step gives it its second, and **defines it as the same expression**
so the two cannot drift: `candAnswers_is_the_capacity_ops_own_grants`.

**What this step does NOT do, and D34 says so.**  It does not collect the candidates.  The
twelve facts of a `Look.Cand` are still the host's (`priority::collect_candidates`, README
gaps 113 and 577), they arrive on the wire as they do today, and D27 is a wire change that
changes *where they come from, not what they are*.  So this step ranks what it is given.

**What it does derive, because the kernel already holds it.**  §7.4's sort key is
`(p, root line order, own line order)` and the two line orders are `Tree::order` — `(file,
line)` of the item and of its root.  Those are not candidate facts on the wire and they are not
D27's either: they are the **plan's**, and `PlanCore.store` and `Plan.rootOf` hold them.  Taking
them from the host would have been a second reading of the plan (AGENTS §5.3), so `keyOf` reads
them off `r.plan`.

### AGENTS §5.3 — what is consumed here

`Look.prioritiesWithFloors`, `Look.priorities`, `Look.Cand`, `Look.Cand.enters`,
`Look.servedOrder`, `Look.servedGrants`, `Look.CandOut`, `Look.FloorOut`, `Look.Floor`,
`Look.lookahead`, `Look.lookahead_is_a_lookahead`, `Cap.lookaheadOf?`, `Cap.Grant`,
`Cap.Deadline`, `Cap.grantOf`, `Prio.finalPrio`, `Prio.rawPrio`, `Prio.prio`,
`Prio.hysteresis`/`applyHysteresis`, `Prio.rowOf`/`rowTable`, `Arith.isImpossible`,
`Plan.rootOf`, `Replay.insSort`/`insSort_perm`/`insSort_eq_mergeSort`, `Capped`.
**Nothing of the pass is re-implemented**: `candAnswers` is one call.

One genuinely new function: `natsLe`, the lexicographic order of a tuple of `Nat`s, which the
nine-deep sort key needs.  `Log.charsLe` is the `List Char` order and `Seal.lexLt` the *strict*
pair combinator; neither is an order on `List Nat`, and a nine-level nested `Bool` in
`routineLe`'s shape is the same function written unreadably.

### D9-21, the recursion rule

`candAnswers` is `Look.prioritiesWithFloors`, whose recursion (`entering`, `sortDueIx`,
`edfGrantsGo`) is stage 5's and already has its `foldl` twin.  `sortRanked` is `Replay.insSort`
over a list the wire caps at `maxCands`, with the `@[csimp]` twin `sortRankedFast` below —
the `wallsOfDay` shape, and the reason gap 394 had to close first.  `natsLe` recurses over a
nine-element literal list, not over anything the wire sizes.
############################################################################ -/

/-! ### The pass — `PlanReq.candAnswers` and `PlanReq.answerFor` are declared above §8.2 step 2
since W-37 (README gap 2870: step 2's Routine rows read the `p` they answer), bodies unchanged. -/

/-! ### §7.3's two numbers for one item — `edfNumbers`, which was a `sorry` in `Goals.lean` -/

/-- Its grant, if it entered §7.3's pass (`Look.Cand.enters`). -/
def PlanReq.grantFor (r : PlanReq) (i : Id) : Option Grant :=
  (r.answerFor i).bind (fun o => o.out.grant)

/-- **§7.3's two numbers of one candidate**, design §5.5 — the need it reserves for and the
capacity available to it by its due date after earlier deadlines have reserved.

**Both over `capDen`, and design §5.5's `(g.deadline.need, g.avail)` is WRONG in one of them.**
`Grant.avail` is a *numerator over the pass's denominator* (`Grant.availQ g den = avail/den`),
while `Deadline.need` is whole minutes; `Arith.isImpossible need avail = decide (avail < need)`
compares them directly, so the design's pair asks whether a numerator over 10^18 is smaller
than a count of minutes and answers `false` for every candidate that has any capacity at all.
The kernel's own test is `Grant.impossible den g = decide (g.avail < g.deadline.need * den.val)`
— the need scaled into the pass's units — and `edfNumbers_is_the_grants_own_impossibility` is
the theorem that the pair below makes `Arith.isImpossible` say exactly that.  Recorded as a
finding against design §5.5. -/
def edfNumbers (r : PlanReq) (i : Id) : Nat × Nat :=
  match r.grantFor i with
  | some g => (g.deadline.need * Look.capDen, g.avail)
  | none   => (0, 0)

/-- **The pair is the grant's own impossibility test, not a second opinion on it.** -/
theorem edfNumbers_is_the_grants_own_impossibility (r : PlanReq) (i : Id) (g : Grant)
    (h : r.grantFor i = some g) :
    Arith.isImpossible (edfNumbers r i).1 (edfNumbers r i).2 = g.impossible Look.capDenD := by
  unfold edfNumbers Grant.impossible Arith.isImpossible
  rw [h]
  rfl

/-- **An item that did not enter the pass is never impossible.**  §7.3's IMPOSSIBLE is a
statement about *capacity*, and a candidate with no due date reserves none — fork
`priority::compute` gives it no grant and `PrioClass::Rank`.  Without this the `(0, 0)` fallback
would be a silent `isImpossible 0 0 = false` nobody had checked. -/
theorem edfNumbers_without_a_grant (r : PlanReq) (i : Id) (h : r.grantFor i = none) :
    Arith.isImpossible (edfNumbers r i).1 (edfNumbers r i).2 = false := by
  unfold edfNumbers Arith.isImpossible
  rw [h]
  rfl

/-- And the numbers are the grant's, unscaled, for a reader that wants the fork's `need_min`. -/
theorem edfNumbers_is_the_grant (r : PlanReq) (i : Id) (g : Grant) (h : r.grantFor i = some g) :
    edfNumbers r i = (g.deadline.need * Look.capDen, g.avail) := by
  unfold edfNumbers; rw [h]

/-! ### §7.4's key and the assignment order -/

/-- The lexicographic order of a tuple of `Nat`s, shortest-first.  `Log.charsLe` is the one
order on `List Char` and `Seal.lexLt` the strict pair combinator; neither orders `List Nat`. -/
def natsLe : List Nat → List Nat → Bool
  | [],      _       => true
  | _ :: _,  []      => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else natsLe as bs

theorem natsLe_trans : ∀ a b c : List Nat, natsLe a b → natsLe b c → natsLe a c
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h₁, _ => absurd h₁ (by simp [natsLe])
  | _ :: _, _ :: _, [], _, h₂ => absurd h₂ (by simp [natsLe])
  | x :: xs, y :: ys, z :: zs, h₁, h₂ => by
    simp only [natsLe] at h₁ h₂ ⊢
    split at h₁
    · rename_i hxy
      split at h₂
      · rename_i hyz; rw [if_pos (by omega)]
      · split at h₂
        · rename_i hzy; exact absurd h₂ (by simp)
        · rename_i hzy; rw [if_pos (by omega)]
    · rename_i hxy
      split at h₁
      · exact absurd h₁ (by simp)
      · rename_i hyx
        have hxy' : x = y := by omega
        subst hxy'
        split at h₂
        · rename_i hyz; rw [if_pos hyz]
        · split at h₂
          · exact absurd h₂ (by simp)
          · rename_i h1 h2
            rw [if_neg h1, if_neg h2]
            exact natsLe_trans xs ys zs h₁ h₂

theorem natsLe_cons (x y : Nat) (xs ys : List Nat) :
    natsLe (x :: xs) (y :: ys) =
      if x < y then true else if y < x then false else natsLe xs ys := rfl

theorem natsLe_total : ∀ a b : List Nat, natsLe a b || natsLe b a
  | [], _ => by simp [natsLe]
  | _ :: _, [] => by simp [natsLe]
  | x :: xs, y :: ys => by
    rw [natsLe_cons, natsLe_cons]
    rcases Nat.lt_trichotomy x y with h | h | h
    · rw [if_pos h]; simp
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact natsLe_total xs ys
    · rw [if_neg (by omega), if_pos h]; simp [h]

/-- What one step of the order gives back: the heads are ordered, and the tails decide a tie. -/
theorem natsLe_cons_le {a b : Nat} {as bs : List Nat} (h : natsLe (a :: as) (b :: bs) = true) :
    a ≤ b ∧ (a = b → natsLe as bs = true) := by
  rw [natsLe_cons] at h
  by_cases h1 : a < b
  · exact ⟨Nat.le_of_lt h1, fun he => absurd he (by omega)⟩
  · rw [if_neg h1] at h
    by_cases h2 : b < a
    · rw [if_pos h2] at h; exact absurd h (by simp)
    · rw [if_neg h2] at h
      exact ⟨by omega, fun _ => h⟩

/-- **§7.4's sort key**, fork `priority::sorted_candidates`'s tuple: walls first (`u8::from
(!c.is_wall)`), then `p` — with a candidate that has none read as `7`, as the fork's
`map_or(7, …)` and its `if c.is_wall { 7 }` both do — then the root's line order, then the
item's own, then the request position, which is the fork's `keyed.sort()` tie-break and the
only thing that separates two instances of one id. -/
structure CandKey where
  notWall : Bool
  p       : Nat
  root    : Option Site
  own     : Option Site
  ix      : Nat
deriving DecidableEq, Repr

/-- A site as two numbers, with a **missing** one last: fork `order` answers
`(usize::MAX, usize::MAX)` for an id the tree does not hold, and `Nat` has no maximum, so the
marker is a leading digit rather than a number nothing can exceed. -/
def siteNums : Option Site → List Nat
  | none   => [1, 0, 0]
  | some s => [0, s.doc, s.rank]

/-- The key as the nine numbers the fork's tuple sort compares, in its order. -/
def CandKey.nums (k : CandKey) : List Nat :=
  (if k.notWall then 1 else 0) :: k.p :: (siteNums k.root ++ siteNums k.own ++ [k.ix])

def candKeyLe (a b : CandKey) : Bool := natsLe a.nums b.nums

theorem candKeyLe_trans (a b c : CandKey) (h₁ : candKeyLe a b) (h₂ : candKeyLe b c) :
    candKeyLe a c := natsLe_trans _ _ _ h₁ h₂

theorem candKeyLe_total (a b : CandKey) : candKeyLe a b || candKeyLe b a := natsLe_total _ _

/-- **Walls first.**  The key's leading digit is `0` for a wall and `1` for everything else, so
an ordered pair cannot put a task in front of a wall. -/
theorem candKeyLe_notWall {a b : CandKey} (h : candKeyLe a b = true) :
    (if a.notWall then 1 else 0) ≤ (if b.notWall then (1 : Nat) else 0) :=
  (natsLe_cons_le h).1

/-- **Then `p`.**  Between two keys of the same kind the order is `p`'s. -/
theorem candKeyLe_p {a b : CandKey} (h : candKeyLe a b = true) (hw : a.notWall = b.notWall) :
    a.p ≤ b.p :=
  (natsLe_cons_le ((natsLe_cons_le h).2 (by rw [hw]))).1

/-- One ranked candidate: its answer and the key §7.4 sorts it by. -/
structure Ranked where
  key : CandKey
  out : Look.FloorOut

/-- **The date an answer's availability is read until**: a floor answer's last day, else its
grant's due date, and none for an answer with neither.  The one reader of it (AGENTS §5.3):
`PlanReq.dayImpossibleUntil`'s `until` calls it, and so does D60's key below. -/
def answerUntil (o : Look.FloorOut) : Option Nat :=
  match o.floor, o.out.grant with
  | some g, _ => some g.floor.last
  | none, some g => some g.deadline.due
  | none, none => none

/-- **D60's component of the key** (README gap 2801, parity P51): a `p = 0` answer with a positive
shortfall — IMPOSSIBLE, as `PlanReq.dayImpossible` names it — carries its `until` and its request
position, which is §7.3's served order among such answers (`Look.sortDueIx`: by due, ties by
position); every other answer carries none. -/
def Ranked.imp (x : Ranked) : Option (Nat × Nat) :=
  if x.key.p = 0 ∧ 0 < x.out.shortfall then (answerUntil x.out).map (fun u => (u, x.key.ix))
  else none

/-- The component as numbers: an impossible answer before every other, by its date and then its
position; every other answer one value, so the fork's order among them is untouched. -/
def impNums : Option (Nat × Nat) → List Nat
  | some (u, ix) => [0, u, ix]
  | none         => [1, 0, 0]

/-- **§7.4's key as step 5 sorts by it**: the fork's tuple (`CandKey.nums`) with D60's component after
`p` (owner D60).  Local, not a definition: `sortRankedFast` hands `rankedLe` to `List.mergeSort` as a
static closure check 12's call graph does not read, so a key function would be one more unreached. -/
def rankedLe (a b : Ranked) : Bool :=
  let nums := fun (x : Ranked) => (if x.key.notWall then 1 else 0) :: x.key.p ::
    (impNums x.imp ++ siteNums x.key.root ++ siteNums x.key.own ++ [x.key.ix])
  natsLe (nums a) (nums b)

theorem rankedLe_trans (a b c : Ranked) (h₁ : rankedLe a b) (h₂ : rankedLe b c) : rankedLe a c :=
  natsLe_trans _ _ _ h₁ h₂

theorem rankedLe_total (a b : Ranked) : rankedLe a b || rankedLe b a := natsLe_total _ _

/-- The assignment order.  `Replay.insSort` is the **specification** sort — quadratic, kept
because it reduces under `decide` — and `sortRankedFast` its compiled twin, the shape
`sortWalls`/`sortRoutines` take since gap 394 closed. -/
def sortRanked (l : List Ranked) : List Ranked := Replay.insSort rankedLe l

def sortRankedFast (l : List Ranked) : List Ranked := l.mergeSort rankedLe

@[csimp] theorem sortRanked_eq_sortRankedFast : @sortRanked = @sortRankedFast := by
  funext l
  unfold sortRanked sortRankedFast
  exact Replay.insSort_eq_mergeSort rankedLe rankedLe_trans rankedLe_total l

theorem mem_sortRanked {l : List Ranked} {x : Ranked} : x ∈ sortRanked l ↔ x ∈ l :=
  (Replay.insSort_perm rankedLe l).mem_iff

theorem sortRanked_length (l : List Ranked) : (sortRanked l).length = l.length :=
  (Replay.insSort_perm rankedLe l).length_eq

/-- **Sorted, and this is the half that makes the order a claim rather than a name.** -/
theorem sortRanked_sorted (l : List Ranked) :
    (sortRanked l).Pairwise (fun a b => rankedLe a b = true) := by
  unfold sortRanked
  rw [Replay.insSort_eq_mergeSort rankedLe rankedLe_trans rankedLe_total l]
  exact List.pairwise_mergeSort (fun a b c h₁ h₂ => rankedLe_trans a b c h₁ h₂)
    (fun a b => rankedLe_total a b) l

/-! ### The key of a request's candidate -/

/-- `Tree::order(id)` — the item's `(file, line)`, `none` when the plan does not hold it. -/
def PlanReq.ownSite (r : PlanReq) (i : Id) : Option Site :=
  (r.plan.val.store.get i).map (fun e => e.val.live)

/-- `Tree::order(root(id))` — §3.2's root walk is `Plan.rootOf`, already proved total. -/
def PlanReq.rootSite (r : PlanReq) (i : Id) : Option Site :=
  r.ownSite (rootOf r.plan.val i)

/-- §7.4's key of the answer at request position `ix`. -/
def PlanReq.keyOf (r : PlanReq) (ix : Nat) (o : Look.FloorOut) : CandKey :=
  ⟨!o.out.cand.wall, o.out.p.getD 7, r.rootSite o.out.cand.id, r.ownSite o.out.cand.id, ix⟩

/-- **Fork `priority::sorted_candidates`' own filter** (README gap 602, closed here on P5a's
wire).

Two clauses, both the fork's:

* `Candidate::eligible()` — not `[?]`, an open state, no unsatisfied `after:`, and a `max:`
  with minutes left.  `Look.PlanFacts.eligible` is that predicate, over the facts P5a put on
  the wire; an ineligible candidate is left out of the **assignment order** and
  `diagnostics.blocked` keeps it with its reason (§5.5), which is P8's.
* `!c.is_wall || c.wall_today` — an Interval whose span does not cover today is another day's
  wall, and nothing about it can be placed in this one.

Both read only wire facts: nothing here derives a candidate fact inside the kernel, which
would be doing D27 early and is what **D34** forbids. -/
def entersTheOrder (o : Look.FloorOut) : Bool :=
  o.out.cand.plan.val.eligible && (!o.out.cand.wall || o.out.cand.plan.val.wallToday)

/-- **§8.2 step 4's answer, in §7.4's order** — fork `priority::sorted_candidates` over
`priority::compute`'s output, **filter and all** since P5a put its facts on the wire.

The filter runs **before** the sort, as the fork's does; filtering a sorted list by any
predicate leaves the survivors in the same order, so the two orders agree and the sortedness
laws below are unchanged by it. -/
def PlanReq.rankedCands (r : PlanReq) : List Ranked :=
  sortRanked ((r.candAnswers.zipIdx.filter (fun x => entersTheOrder x.1)).map
    (fun x => ⟨r.keyOf x.2 x.1, x.1⟩))

/-- The order is **at most** the request's candidates — an equality until P5a's filter, and a
bound after it.  The `Capped` bound every list in `DayPlan` needs still follows. -/
theorem PlanReq.rankedCands_length (r : PlanReq) :
    r.rankedCands.length ≤ r.cands.val.length := by
  unfold PlanReq.rankedCands
  rw [sortRanked_length, List.length_map]
  exact Nat.le_trans (List.length_filter_le _ _)
    (Nat.le_of_eq (by rw [List.length_zipIdx, r.candAnswers_length]))

/-- **Nothing is invented and nothing but the filter is dropped**: every entry of the ranking
is an answer of this request that passes `entersTheOrder`, at the position it arrived at. -/
theorem PlanReq.mem_rankedCands {r : PlanReq} {x : Ranked} :
    x ∈ r.rankedCands ↔
      ∃ p ∈ r.candAnswers.zipIdx, entersTheOrder p.1 = true ∧ x = ⟨r.keyOf p.2 p.1, p.1⟩ := by
  unfold PlanReq.rankedCands
  rw [mem_sortRanked]
  simp only [List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨p, ⟨hp, he⟩, rfl⟩; exact ⟨p, hp, he, rfl⟩
  · rintro ⟨p, hp, he, rfl⟩; exact ⟨p, ⟨hp, he⟩, rfl⟩

/-- **Every entry of the order passes the filter** — the direction §8.2 step 5's fold reads:
a group built from this list never contains a Waiting, closed, dep-blocked or `max:`-exhausted
item, nor another day's wall. -/
theorem PlanReq.a_ranked_entry_enters_the_order {r : PlanReq} {x : Ranked}
    (h : x ∈ r.rankedCands) : entersTheOrder x.out = true := by
  obtain ⟨p, _hp, he, rfl⟩ := PlanReq.mem_rankedCands.1 h
  exact he

/-- **An ineligible candidate is not in the order** — the fork's `!c.eligible()` drop, stated
as the contrapositive so the fold can use it directly. -/
theorem PlanReq.an_ineligible_candidate_is_not_ranked {r : PlanReq} {x : Ranked}
    (h : x ∈ r.rankedCands) : x.out.out.cand.plan.val.eligible = true := by
  have he := PlanReq.a_ranked_entry_enters_the_order h
  unfold entersTheOrder at he
  simp only [Bool.and_eq_true] at he
  exact he.1

/-- **Another day's wall is not in the order.**  An exam six weeks out is a wall and is not
today's; §8.2 step 1 places today's and step 5 never sees either. -/
theorem PlanReq.another_days_wall_is_not_ranked {r : PlanReq} {x : Ranked}
    (h : x ∈ r.rankedCands) (hw : x.out.out.cand.wall = true) :
    x.out.out.cand.plan.val.wallToday = true := by
  have he := PlanReq.a_ranked_entry_enters_the_order h
  unfold entersTheOrder at he
  simp only [Bool.and_eq_true, hw, Bool.not_true, Bool.false_or] at he
  exact he.2

/-- Every ranked entry is an answer of this request, at the position it arrived at. -/
theorem PlanReq.a_ranked_entry_is_an_answer {r : PlanReq} {x : Ranked} (h : x ∈ r.rankedCands) :
    r.candAnswers[x.key.ix]? = some x.out := by
  obtain ⟨p, hp, -, rfl⟩ := PlanReq.mem_rankedCands.1 h
  exact List.mem_zipIdx_iff_getElem?.mp hp

/-- **And its key is that answer's own four facts** — not a label attached beside it.  This is
the half that makes the order laws below claims about the candidate rather than about the key:
a key whose `p` did not come from `finalPrio` would satisfy every sortedness theorem. -/
theorem PlanReq.a_ranked_entry_carries_its_answers_facts {r : PlanReq} {x : Ranked}
    (h : x ∈ r.rankedCands) :
    x.key.notWall = !x.out.out.cand.wall ∧ x.key.p = x.out.out.p.getD 7 ∧
      x.key.root = r.rootSite x.out.out.cand.id ∧ x.key.own = r.ownSite x.out.out.cand.id := by
  obtain ⟨p, -, -, rfl⟩ := PlanReq.mem_rankedCands.1 h
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem PlanReq.rankedCands_sorted (r : PlanReq) :
    r.rankedCands.Pairwise (fun a b => rankedLe a b = true) := sortRanked_sorted _

/-- **Step 5's served order, as the plan response carries it** (W-38, README gap 3343): each ranked answer's request
position, its id and the `ci` step 5 reads, in the order the walk serves them — `diagnostics.served`. -/
def PlanReq.dayServed (r : PlanReq) : List (Nat × Id × Fin 6) :=
  r.rankedCands.map (fun x => (x.key.ix, x.out.out.cand.id, x.out.out.cand.ci))

/-! ### The day's `priorities` -/

/-- One `(id, p)` row of `DayPlan.priorities`, when the candidate has a `p` at all.  A wall has
none — §7.2's first row is off the scale (`rawPrio_of_a_wall`), and fork `sorted_candidates`
reads walls as `7` only to sort them, never to report them. -/
def prioRow (o : Look.FloorOut) : Option (Id × Fin 8) :=
  match o.out.p with
  | none   => none
  | some n =>
    if hn : n < 8 then some (o.out.cand.id, ⟨n, hn⟩) else none

/-- §8.2 step 8's `priorities`, fork `planner.rs:1066`: one row per candidate **in request
order**, id and `p`.  Bounded by the candidates' own `Capped`; `filterMap` cannot grow a list. -/
def dayPriorities (r : PlanReq) : Capped (Id × Fin 8) :=
  ⟨r.candAnswers.filterMap prioRow, by
    refine Nat.le_trans (Nat.le_trans (List.length_filterMap_le _ _) ?_) r.cands.property
    exact Nat.le_of_eq r.candAnswers_length⟩

theorem dayPriorities_val (r : PlanReq) :
    (dayPriorities r).val = r.candAnswers.filterMap prioRow := rfl

/-- **A wall contributes no priority row.** -/
theorem a_wall_has_no_priority_row (o : Look.FloorOut) (h : o.out.p = none) :
    prioRow o = none := by unfold prioRow; rw [h]

/-- **The `dif` in `prioRow` is never the branch taken.**  A `p` the pass produces is on §7.2's
scale (`Look.prioritiesWithFloors_p_is_on_the_scale`), so no candidate loses its row at the
bound of a type — which would be a refusal nothing names, §9.2's disguised gap. -/
theorem an_answer_with_a_p_gets_a_row (r : PlanReq) (o : Look.FloorOut) (n : Nat)
    (ho : o ∈ r.candAnswers) (h : o.out.p = some n) :
    (prioRow o).map (fun q => (q.1, q.2.val)) = some (o.out.cand.id, n) := by
  have hn : n ≤ 7 := Look.prioritiesWithFloors_p_is_on_the_scale ho h
  unfold prioRow
  rw [h]
  show Option.map _ (dite (n < 8) _ _) = _
  rw [dif_pos (show n < 8 by omega)]
  rfl

/-- **And an answer with no `p` is the only thing that loses one** — the two directions
together say the row list is exactly the answers on the scale. -/
theorem a_row_is_lost_only_off_the_scale (o : Look.FloorOut) (h : prioRow o = none) :
    o.out.p = none ∨ ∃ n, o.out.p = some n ∧ 8 ≤ n := by
  unfold prioRow at h
  split at h
  · rename_i hp; exact Or.inl hp
  · rename_i n hp
    split at h
    · exact absurd h (by simp)
    · exact Or.inr ⟨n, hp, by omega⟩

/-- **And a row's `p` is the answer's own `p`** — the value, not a placeholder. -/
theorem a_priority_row_carries_the_answers_p (o : Look.FloorOut) (i : Id) (q : Fin 8)
    (h : prioRow o = some (i, q)) : o.out.cand.id = i ∧ o.out.p = some q.val := by
  unfold prioRow at h
  split at h
  · cases h
  · rename_i n hn
    split at h
    · cases h; exact ⟨rfl, hn⟩
    · cases h

/-! ############################################################################
## §8.2 step 5, the first half: the groups the fold walks

**Fork `Planner::build_groups`** (`planner.rs:1406`), over **fork `priority::batches`** (`priority.rs:1214`) and **fork
`split_by_filters`** (`planner.rs:2354`).  Step 5's cursor is the other half and is below; this half turns the ranked order
into the list of *things a slot may be given to*.

**This is not an EDF pass** (README gap 701).  §7.3's deadline pass already ran — it is `Cap.edf`/`Cap.edfGrants`, it has six
call sites, and its result reaches this step only as the `p` inside `CandKey`.  Fork `build_groups`/`pick` is a **greedy
cursor in §7.4's key order with no deadline anywhere**, and a step that reused the EDF pass here would build a second scheduler.

**Nothing here derives a candidate fact** (D34): every fact read below — `remaining`, `wall`, `optional`, `window`, `ci`, and
the nine of `PlanFacts` — arrives on the wire, host-collected, and `Look.PlanFacts` is P5a's single reader of the nine.

**`left_min` is carried as `commitMin` and `spent`, and that is stronger than the fork's `i64`** (AGENTS §5.3, and the one place
this module deviates in *representation* rather than in behaviour).  Fork `Group::left_min` is a signed counter the assign
loop decrements by a whole slot's minutes and **step 6 increments back** when a mandatory routine displaces an assigned block,
so a saturating `Nat` would not invert: `left 10 − slot 60 = −50`, restored `+60`, is `10` in the fork and `60` under
saturation.  Both of `left_min`'s readers are order comparisons — `pick`'s `g.left_min <= 0` and `contiguous_fits`' `need`,
which is reached only when it is positive — so `commitMin ≤ spent` and `commitMin − spent` say exactly what the fork says, in
`Nat`, and P6's restore is `spent − minutes`, which is exact.
############################################################################ -/

/-! ### The ranked entry's own facts -/

/-- The candidate one ranked entry is about. -/
def Ranked.cand (x : Ranked) : Look.Cand := x.out.out.cand

/-- Its §8.2 step 5 facts — P5a's nine, off the wire (`Look.PlanFacts`). -/
def Ranked.facts (x : Ranked) : Look.PlanFacts := x.out.out.cand.plan.val

/-- **Fork `batches`' `small`** (`priority.rs:1219`): a candidate small enough to share a block,
and none of the three kinds that never share one — a wall is an interval, an optional only
fills rest, and a window instance is placed inside its own window. -/
def Ranked.gatherable (maxSmall : Nat) (x : Ranked) : Bool :=
  decide (0 < x.cand.remaining) && decide (x.cand.remaining ≤ maxSmall) &&
    !x.cand.wall && !x.cand.optional && !x.cand.window

/-! ### §7.5's batching -/

/-- **Fork `batches`' inner loop** (`priority.rs:1242-1256`), as a walk over the rest of the
order rather than over a `used` array: a member of a different `ci` is *passed over and kept*
(the fork's `continue`), and the first member of the **same** `ci` that cannot join stops the
walk and everything from there is kept (the fork's `break`, which is §8.3's monotone-rank rule).
The two halves come back as `(gathered, kept)`, and `kept` is what the next leader walks.

`room` is the kernel's own stop and is **not** the fork's: `BatchIds` is bounded at `maxBatch`
(R10) and the fork's loop is not bounded at all — `planned_min` is `round(est × multiplier)`
(`energy::planned_minutes`) and is `0` for a small enough multiplier, so `total_min + 0 ≤
block_min` never fires and a fork batch may hold any number of members.  Gathering stops at
`maxBatch` here; a member not gathered is a **group of its own** and is still assigned, so the
deviation loses no candidate.  README gap 800. -/
def gatherBatch (maxSmall blockMin : Nat) (ci : Fin 6) (room tot : Nat) :
    List Ranked → List Ranked × List Ranked
  | [] => ([], [])
  | x :: xs =>
    if x.cand.ci = ci then
      if room == 0 || !x.gatherable maxSmall ||
          decide (blockMin < tot + x.facts.plannedMin) then ([], x :: xs)
      else
        let p := gatherBatch maxSmall blockMin ci (room - 1) (tot + x.facts.plannedMin) xs
        (x :: p.1, p.2)
    else
      let p := gatherBatch maxSmall blockMin ci room tot xs
      (p.1, x :: p.2)

/-- **Nothing is invented and nothing is lost**: the gathered members and the kept rest are the
walk's input, rearranged. -/
theorem gatherBatch_perm (ms bm : Nat) (ci : Fin 6) : ∀ (l : List Ranked) (room tot : Nat),
    ((gatherBatch ms bm ci room tot l).1 ++ (gatherBatch ms bm ci room tot l).2).Perm l
  | [], _, _ => by simp [gatherBatch]
  | x :: xs, room, tot => by
    unfold gatherBatch
    by_cases hci : x.cand.ci = ci
    · rw [if_pos hci]
      by_cases hstop : (room == 0 || !x.gatherable ms ||
          decide (bm < tot + x.facts.plannedMin)) = true
      · rw [if_pos hstop]; simp
      · rw [if_neg hstop]
        exact List.Perm.cons x (gatherBatch_perm ms bm ci xs (room - 1) (tot + x.facts.plannedMin))
    · rw [if_neg hci]
      exact ((List.perm_middle).trans
        (List.Perm.cons x (gatherBatch_perm ms bm ci xs room tot)))

/-- The kept rest is no longer than the walk's input — what makes the outer loop's fuel enough. -/
theorem gatherBatch_snd_length (ms bm : Nat) (ci : Fin 6) (room tot : Nat) (l : List Ranked) :
    (gatherBatch ms bm ci room tot l).2.length ≤ l.length := by
  have h := (gatherBatch_perm ms bm ci l room tot).length_eq
  rw [List.length_append] at h
  omega

/-- **The gathered members are a prefix of the same-`ci` entries of the order** — §8.3's
monotone-rank rule, stated as the thing the `break` buys: gathering cannot reach *past* an
equal-`ci` candidate it left behind.  This is the half `plan_never_batches_past_an_equal_ci_
candidate` rests on. -/
theorem gatherBatch_fst_is_a_prefix_of_its_ci (ms bm : Nat) (ci : Fin 6) :
    ∀ (l : List Ranked) (room tot : Nat),
      (gatherBatch ms bm ci room tot l).1 <+: l.filter (fun y => decide (y.cand.ci = ci))
  | [], _, _ => by simp [gatherBatch]
  | x :: xs, room, tot => by
    unfold gatherBatch
    by_cases hci : x.cand.ci = ci
    · rw [if_pos hci]
      by_cases hstop : (room == 0 || !x.gatherable ms ||
          decide (bm < tot + x.facts.plannedMin)) = true
      · rw [if_pos hstop]; exact List.nil_prefix
      · rw [if_neg hstop]
        simp only [List.filter_cons, hci, decide_true, if_pos]
        obtain ⟨t, ht⟩ :=
          gatherBatch_fst_is_a_prefix_of_its_ci ms bm ci xs (room - 1) (tot + x.facts.plannedMin)
        exact ⟨t, by rw [List.cons_append, ht]⟩
    · rw [if_neg hci]
      simp only [List.filter_cons, hci, decide_false, Bool.false_eq_true, if_neg, not_false_iff]
      exact gatherBatch_fst_is_a_prefix_of_its_ci ms bm ci xs room tot

/-- Every gathered member carries the leader's `ci` — the fork's `other.ci != c.ci` skip. -/
theorem gatherBatch_fst_ci (ms bm : Nat) (ci : Fin 6) (room tot : Nat) (l : List Ranked)
    (y : Ranked) (h : y ∈ (gatherBatch ms bm ci room tot l).1) : y.cand.ci = ci := by
  have hp := (gatherBatch_fst_is_a_prefix_of_its_ci ms bm ci l room tot).subset h
  simpa using (List.mem_filter.1 hp).2

/-- And the gather takes at most `room` of them: `BatchIds`' bound, established rather than
assumed (R10). -/
theorem gatherBatch_fst_length (ms bm : Nat) (ci : Fin 6) :
    ∀ (l : List Ranked) (room tot : Nat), (gatherBatch ms bm ci room tot l).1.length ≤ room
  | [], _, _ => by simp [gatherBatch]
  | x :: xs, room, tot => by
    unfold gatherBatch
    by_cases hci : x.cand.ci = ci
    · rw [if_pos hci]
      by_cases hstop : (room == 0 || !x.gatherable ms ||
          decide (bm < tot + x.facts.plannedMin)) = true
      · rw [if_pos hstop]; simp
      · rw [if_neg hstop]
        have hr : room ≠ 0 := by
          intro h0; rw [h0] at hstop; simp at hstop
        have := gatherBatch_fst_length ms bm ci xs (room - 1) (tot + x.facts.plannedMin)
        simp only [List.length_cons]
        omega
    · rw [if_neg hci]
      exact gatherBatch_fst_length ms bm ci xs room tot

/-- **Fork `batches`' outer loop**, on structural fuel — `Look.cutStretch`'s own shape.  Each
turn takes the first entry of what is left as a leader and gathers behind it. -/
def batchLoop (ms bm : Nat) : Nat → List Ranked → List (List Ranked)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, x :: xs =>
    let p := if x.gatherable ms then
        gatherBatch ms bm x.cand.ci (maxBatch - 1) x.facts.plannedMin xs
      else ([], xs)
    (x :: p.1) :: batchLoop ms bm fuel p.2

/-- **§7.5's groups**, fork `priority::batches`: the order walked once, each leader carrying
what it gathered.  The fuel is the order's own length, which the theorem below shows is
enough. -/
def batches (ms bm : Nat) (l : List Ranked) : List (List Ranked) := batchLoop ms bm l.length l

/-- **Every batch is non-empty** — it holds at least its leader. -/
theorem batchLoop_ne_nil (ms bm : Nat) : ∀ (fuel : Nat) (l : List Ranked),
    ∀ b ∈ batchLoop ms bm fuel l, b ≠ []
  | 0, _, _, h => by simp [batchLoop] at h
  | _ + 1, [], _, h => by simp [batchLoop] at h
  | fuel + 1, x :: xs, b, h => by
    unfold batchLoop at h
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · exact batchLoop_ne_nil ms bm fuel _ b h

/-- **And no batch is longer than `maxBatch`**, so `mkBatch?` cannot refuse one (R10). -/
theorem batchLoop_length (ms bm : Nat) : ∀ (fuel : Nat) (l : List Ranked),
    ∀ b ∈ batchLoop ms bm fuel l, b.length ≤ maxBatch
  | 0, _, _, h => by simp [batchLoop] at h
  | _ + 1, [], _, h => by simp [batchLoop] at h
  | fuel + 1, x :: xs, b, h => by
    unfold batchLoop at h
    rcases List.mem_cons.1 h with rfl | h
    · simp only [List.length_cons]
      by_cases hg : x.gatherable ms = true
      · simp only [hg, if_pos]
        have := gatherBatch_fst_length ms bm x.cand.ci xs (maxBatch - 1) x.facts.plannedMin
        simp only [maxBatch] at this ⊢
        omega
      · simp only [hg, Bool.false_eq_true, if_neg, not_false_iff]
        simp [maxBatch]
    · exact batchLoop_length ms bm fuel _ b h

/-- **The batches are the order, rearranged** — given fuel enough, nothing entered and nothing
left.  This is the law §8.3's "never drops" goals read: a candidate in the assignment order is
in exactly one group of it. -/
theorem batchLoop_flatten_perm (ms bm : Nat) : ∀ (fuel : Nat) (l : List Ranked),
    l.length ≤ fuel → ((batchLoop ms bm fuel l).flatten).Perm l
  | 0, l, h => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [batchLoop]
  | fuel + 1, [], _ => by simp [batchLoop]
  | fuel + 1, x :: xs, h => by
    unfold batchLoop
    simp only [List.flatten_cons, List.cons_append]
    refine List.Perm.cons x ?_
    by_cases hg : x.gatherable ms = true
    · simp only [hg, if_pos]
      have hlen := gatherBatch_snd_length ms bm x.cand.ci (maxBatch - 1) x.facts.plannedMin xs
      have hrec := batchLoop_flatten_perm ms bm fuel
        (gatherBatch ms bm x.cand.ci (maxBatch - 1) x.facts.plannedMin xs).2
        (by simp only [List.length_cons] at h; omega)
      exact (hrec.append_left _).trans
        (gatherBatch_perm ms bm x.cand.ci xs (maxBatch - 1) x.facts.plannedMin)
    · simp only [hg, Bool.false_eq_true, if_neg, not_false_iff]
      simpa using batchLoop_flatten_perm ms bm fuel xs (by simp only [List.length_cons] at h; omega)

theorem batches_flatten_perm (ms bm : Nat) (l : List Ranked) :
    ((batches ms bm l).flatten).Perm l := batchLoop_flatten_perm ms bm l.length l (Nat.le_refl _)

/-- Every member of every batch came from the order. -/
theorem mem_of_mem_batches {ms bm : Nat} {l b : List Ranked} {y : Ranked}
    (hb : b ∈ batches ms bm l) (hy : y ∈ b) : y ∈ l :=
  (batches_flatten_perm ms bm l).subset (List.mem_flatten.2 ⟨b, hb, hy⟩)

/-- **And every entry of the order is in a batch** — the direction that says the batching drops
nothing. -/
theorem batches_cover {ms bm : Nat} {l : List Ranked} {y : Ranked} (hy : y ∈ l) :
    ∃ b ∈ batches ms bm l, y ∈ b :=
  List.mem_flatten.1 ((batches_flatten_perm ms bm l).mem_iff.2 hy)

theorem batches_ne_nil (ms bm : Nat) (l : List Ranked) : ∀ b ∈ batches ms bm l, b ≠ [] :=
  batchLoop_ne_nil ms bm l.length l

theorem batches_length (ms bm : Nat) (l : List Ranked) : ∀ b ∈ batches ms bm l, b.length ≤ maxBatch :=
  batchLoop_length ms bm l.length l

/-- **A batch is one `ci`** — §7.5 gathers by `ci` alone, and this is the law that makes a
group's energy filter a statement about every member of it. -/
theorem batchLoop_ci (ms bm : Nat) : ∀ (fuel : Nat) (l : List Ranked),
    ∀ b ∈ batchLoop ms bm fuel l, ∀ y ∈ b, ∀ z ∈ b, y.cand.ci = z.cand.ci
  | 0, _, _, h, _, _, _, _ => by simp [batchLoop] at h
  | _ + 1, [], _, h, _, _, _, _ => by simp [batchLoop] at h
  | fuel + 1, x :: xs, b, h, y, hy, z, hz => by
    unfold batchLoop at h
    rcases List.mem_cons.1 h with rfl | h
    · have key : ∀ w ∈ x :: (if x.gatherable ms then
          gatherBatch ms bm x.cand.ci (maxBatch - 1) x.facts.plannedMin xs
        else ([], xs)).1, w.cand.ci = x.cand.ci := by
        intro w hw
        rcases List.mem_cons.1 hw with rfl | hw
        · rfl
        · by_cases hgb : x.gatherable ms = true
          · rw [if_pos hgb] at hw
            exact gatherBatch_fst_ci ms bm x.cand.ci (maxBatch - 1) x.facts.plannedMin xs w hw
          · rw [if_neg (by simpa using hgb)] at hw; simp at hw
      rw [key y hy, key z hz]
    · exact batchLoop_ci ms bm fuel _ b h y hy z hz

theorem batches_ci {ms bm : Nat} {l b : List Ranked} (hb : b ∈ batches ms bm l) :
    ∀ y ∈ b, ∀ z ∈ b, y.cand.ci = z.cand.ci := batchLoop_ci ms bm l.length l b hb

/-! ### The batch split (fork `split_by_filters`) — RUNS, since the owner's D74 (parity P64)

**A bucket closes where the next member cannot join it** — another `loc:`, an atomic item, the
running block — so every bucket is a run of CONSECUTIVE members of its batch, in §7.4's order,
and the split never serves a lower-ranked sibling ahead of a higher-ranked one (README gap 3546).
The fork's own doc comment says "runs" and its code is a group-by: `out.iter_mut().find(|(k, _)|
*k == key)` puts a member into the FIRST bucket with its key wherever it sits, so `[^t3, ^t1,
^t2]` with `^t1` atomic was split `{^t3, ^t2}`, `{^t1}`, the pair keyed by `^t3` and served first.
That group-by is fork 4748911's and is the divergence P64 records; the runs are the kernel's. -/

/-- The key `split_by_filters` groups by (`planner.rs:2360`): the two halves of §8.2 step 5's
filter that are written about the *item* — its `loc:` and whether `atomic` cleared its
`splittable` — plus the block that is already running (§9), whose remaining minutes are its own
and not its batch's. -/
structure SplitKey where
  loc        : Field.Loc
  splittable : Bool
  running    : Bool
deriving DecidableEq, Repr

def splitKeyOf (act : Option Id) (x : Ranked) : SplitKey :=
  ⟨x.facts.loc, x.facts.splittable, act == some x.cand.id⟩

/-- One member onto the LAST bucket when it carries that bucket's key, else into a new bucket
after it (D74): the bucket before it is closed for good, and a bucket keeps §7.4's order. -/
def splitPush (k : SplitKey) (x : Ranked) :
    List (SplitKey × List Ranked) → List (SplitKey × List Ranked)
  | [] => [(k, [x])]
  | [e] => if e.1 = k then [(e.1, e.2 ++ [x])] else [e, (k, [x])]
  | e :: f :: rest => e :: splitPush k x (f :: rest)

/-- **§8.2 step 5's split of one batch** — its RUNS of equal key, in order (D74; fork
`split_by_filters` is the group-by P64 departs from). -/
def splitGroups (act : Option Id) (members : List Ranked) : List (SplitKey × List Ranked) :=
  members.foldl (fun acc x => splitPush (splitKeyOf act x) x acc) []

/-- The flattened buckets are the members, rearranged — in order: `PlanFold.splitGroups_flatten_eq`. -/
theorem splitPush_flatten (k : SplitKey) (x : Ranked) :
    ∀ acc : List (SplitKey × List Ranked),
      (((splitPush k x acc).map Prod.snd).flatten).Perm (((acc.map Prod.snd).flatten) ++ [x])
  | [] => by simp [splitPush]
  | [e] => by
    simp only [splitPush]
    by_cases hk : e.1 = k
    · rw [if_pos hk]; simp
    · rw [if_neg hk]; simp
  | e :: f :: rest => by
    simp only [splitPush, List.map_cons, List.flatten_cons, List.append_assoc]
    exact List.Perm.append_left _ (by simpa using splitPush_flatten k x (f :: rest))

theorem splitFold_flatten (act : Option Id) :
    ∀ (members : List Ranked) (acc : List (SplitKey × List Ranked)),
      (((members.foldl (fun a x => splitPush (splitKeyOf act x) x a) acc).map Prod.snd).flatten).Perm
        ((acc.map Prod.snd).flatten ++ members)
  | [], acc => by simp
  | x :: xs, acc => by
    simp only [List.foldl_cons]
    refine (splitFold_flatten act xs (splitPush (splitKeyOf act x) x acc)).trans ?_
    refine ((splitPush_flatten (splitKeyOf act x) x acc).append_right xs).trans ?_
    simp only [List.append_assoc, List.singleton_append]
    exact List.Perm.refl _

theorem splitGroups_flatten (act : Option Id) (members : List Ranked) :
    (((splitGroups act members).map Prod.snd).flatten).Perm members := by
  unfold splitGroups
  simpa using splitFold_flatten act members []

/-- Every member of a bucket came from the batch. -/
theorem mem_of_mem_splitGroups {act : Option Id} {members : List Ranked}
    {e : SplitKey × List Ranked} {y : Ranked} (he : e ∈ splitGroups act members) (hy : y ∈ e.2) :
    y ∈ members :=
  (splitGroups_flatten act members).subset
    (List.mem_flatten.2 ⟨e.2, List.mem_map.2 ⟨e, he, rfl⟩, hy⟩)

/-- And every member is in a bucket. -/
theorem splitGroups_cover {act : Option Id} {members : List Ranked} {y : Ranked}
    (hy : y ∈ members) : ∃ e ∈ splitGroups act members, y ∈ e.2 := by
  obtain ⟨g, hg, hyg⟩ := List.mem_flatten.1 ((splitGroups_flatten act members).mem_iff.2 hy)
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hg
  exact ⟨e, he, hyg⟩

/-- A bucket is no longer than the batch it came from. -/
theorem splitGroups_length {act : Option Id} {members : List Ranked}
    {e : SplitKey × List Ranked} (he : e ∈ splitGroups act members) :
    e.2.length ≤ members.length := by
  have hperm := (splitGroups_flatten act members).length_eq
  have hmem : e.2 ∈ (splitGroups act members).map Prod.snd := List.mem_map.2 ⟨e, he, rfl⟩
  have := List.Sublist.length_le (List.sublist_flatten_of_mem hmem)
  omega

/-- **Every member of a bucket carries that bucket's key** — the half that makes `Group.loc` and
`Group.splittable` statements about the members and not labels beside them. -/
def SplitOk (act : Option Id) (acc : List (SplitKey × List Ranked)) : Prop :=
  ∀ e ∈ acc, ∀ y ∈ e.2, splitKeyOf act y = e.1

/-- **What a push leaves**: the buckets it had, the LAST one grown by `x` under its own key, or a
new bucket holding `x` alone under `k`. -/
theorem mem_splitPush {k : SplitKey} {x : Ranked} :
    ∀ {acc : List (SplitKey × List Ranked)} {f : SplitKey × List Ranked}, f ∈ splitPush k x acc →
      f ∈ acc ∨ (∃ e ∈ acc, e.1 = k ∧ f = (e.1, e.2 ++ [x])) ∨ f = (k, [x])
  | [], f, h => by simp only [splitPush, List.mem_singleton] at h; exact Or.inr (Or.inr h)
  | [e], f, h => by
    simp only [splitPush] at h
    split at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    · next hk => exact Or.inr (Or.inl ⟨e, List.mem_singleton_self _, hk, h⟩)
    · rcases h with rfl | rfl
      · exact Or.inl (List.mem_singleton_self _)
      · exact Or.inr (Or.inr rfl)
  | e :: g :: rest, f, h => by
    simp only [splitPush, List.mem_cons] at h
    rcases h with rfl | h
    · exact Or.inl (List.mem_cons_self ..)
    · rcases mem_splitPush (acc := g :: rest) h with h | ⟨e', he', hk, rfl⟩ | rfl
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr (Or.inl ⟨e', List.mem_cons_of_mem _ he', hk, rfl⟩)
      · exact Or.inr (Or.inr rfl)

theorem splitPush_keeps_SplitOk {act : Option Id} {x : Ranked} :
    ∀ {acc : List (SplitKey × List Ranked)}, SplitOk act acc →
      SplitOk act (splitPush (splitKeyOf act x) x acc) := by
  intro acc h f hf y hy
  rcases mem_splitPush hf with hf | ⟨e, he, hk, rfl⟩ | rfl
  · exact h f hf y hy
  · rcases List.mem_append.1 hy with hy | hy
    · exact h e he y hy
    · simp only [List.mem_singleton] at hy; subst hy; exact hk.symm
  · simp only [List.mem_singleton] at hy; subst hy; rfl

theorem splitFold_SplitOk (act : Option Id) :
    ∀ (members : List Ranked) (acc : List (SplitKey × List Ranked)), SplitOk act acc →
      SplitOk act (members.foldl (fun a x => splitPush (splitKeyOf act x) x a) acc)
  | [], _, h => h
  | x :: xs, acc, h => by
    simp only [List.foldl_cons]
    exact splitFold_SplitOk act xs _ (splitPush_keeps_SplitOk h)

theorem splitGroups_keys (act : Option Id) (members : List Ranked) :
    SplitOk act (splitGroups act members) :=
  splitFold_SplitOk act members [] (by intro e he; simp at he)

/-- No bucket is empty. -/
def SplitNe (acc : List (SplitKey × List Ranked)) : Prop := ∀ e ∈ acc, e.2 ≠ []

theorem splitPush_keeps_SplitNe {k : SplitKey} {x : Ranked} :
    ∀ {acc : List (SplitKey × List Ranked)}, SplitNe acc → SplitNe (splitPush k x acc) := by
  intro acc h f hf
  rcases mem_splitPush hf with hf | ⟨e, -, -, rfl⟩ | rfl
  · exact h f hf
  · simp
  · simp

theorem splitFold_SplitNe (act : Option Id) :
    ∀ (members : List Ranked) (acc : List (SplitKey × List Ranked)), SplitNe acc →
      SplitNe (members.foldl (fun a x => splitPush (splitKeyOf act x) x a) acc)
  | [], _, h => h
  | x :: xs, acc, h => by
    simp only [List.foldl_cons]
    exact splitFold_SplitNe act xs _ (splitPush_keeps_SplitNe h)

theorem splitGroups_ne_nil (act : Option Id) (members : List Ranked) :
    ∀ e ∈ splitGroups act members, e.2 ≠ [] :=
  splitFold_SplitNe act members [] (by intro e he; simp at he)

/-! ### The group, and the `max:` commit -/

/-- **Fork `priority::sort_key`** (`priority.rs:1103`): `(prio.p, root_order, own_order)` — the
key `build_groups` takes the **minimum** of over a group's members and then sorts the groups by —
with D60's component after `p` (`Ranked.imp`; owner D60, parity P51), so a group holding a `p = 0`
IMPOSSIBLE member is walked by that member's date and position, §7.3's served order.  The fork's
`out.sort_by` is **stable**, so two groups that agree on every part keep the order the batching
gave them.  `siteNums`, `impNums` and `natsLe` are §7.4's own, called and not copied (AGENTS §5.3). -/
structure GroupKey where
  p    : Nat
  imp  : Option (Nat × Nat)
  root : Option Site
  own  : Option Site
deriving DecidableEq, Repr

def GroupKey.nums (k : GroupKey) : List Nat := k.p :: (impNums k.imp ++ siteNums k.root ++ siteNums k.own)

def groupKeyLe (a b : GroupKey) : Bool := natsLe a.nums b.nums

theorem groupKeyLe_trans (a b c : GroupKey) (h₁ : groupKeyLe a b) (h₂ : groupKeyLe b c) :
    groupKeyLe a c := natsLe_trans _ _ _ h₁ h₂

theorem groupKeyLe_total (a b : GroupKey) : groupKeyLe a b || groupKeyLe b a := natsLe_total _ _

/-- A ranked entry's key parts, read off the key §7.4 already gave it, D60's component with them. -/
def groupKeyOf (x : Ranked) : GroupKey := ⟨x.key.p, x.imp, x.key.root, x.key.own⟩

/-- Fork `members.iter().map(sort_key).min()`, which answers the **first** minimum. -/
def minGroupKey (k : GroupKey) : List Ranked → GroupKey
  | [] => k
  | x :: xs => minGroupKey (if groupKeyLe (groupKeyOf x) k then groupKeyOf x else k) xs

/-- The minimum is no greater than the seed. -/
theorem minGroupKey_le_seed : ∀ (l : List Ranked) (k : GroupKey), groupKeyLe (minGroupKey k l) k
  | [], k => by
    show groupKeyLe k k = true
    have := groupKeyLe_total k k
    simpa using this
  | x :: xs, k => by
    unfold minGroupKey
    by_cases h : groupKeyLe (groupKeyOf x) k = true
    · rw [if_pos h]
      exact groupKeyLe_trans _ _ _ (minGroupKey_le_seed xs _) h
    · rw [if_neg h]
      exact minGroupKey_le_seed xs k

/-- **And no greater than any member's** — the half that makes `Group.key` the group's own
minimum rather than a number beside it. -/
theorem minGroupKey_le_mem : ∀ (l : List Ranked) (k : GroupKey) (y : Ranked), y ∈ l →
    groupKeyLe (minGroupKey k l) (groupKeyOf y)
  | [], _, _, h => by simp at h
  | x :: xs, k, y, h => by
    unfold minGroupKey
    rcases List.mem_cons.1 h with rfl | h
    · by_cases hk : groupKeyLe (groupKeyOf y) k = true
      · rw [if_pos hk]; exact minGroupKey_le_seed xs _
      · rw [if_neg hk]
        refine groupKeyLe_trans _ _ _ (minGroupKey_le_seed xs k) ?_
        have := groupKeyLe_total (groupKeyOf y) k
        simp only [hk, Bool.false_or] at this
        exact this
    · exact minGroupKey_le_mem xs _ y h

/-- Fork `cap_left.min()`: the tightest `max:` any member is still under, `none` when no member
has one (the fork's `unwrap_or(u32::MAX)`, which is "no constraint").

The combining step is **`Seal.minOpt`**, stage 5's own `Option Nat` minimum, not a second copy
of it (AGENTS §5.3).  A byte-for-byte duplicate of it under a different name shipped here at
P5b and is **deleted** by W-19's repair step; `Seal.minOpt_assoc` is the law it never had.
README gap 886. -/
def capLeftOf (l : List Ranked) : Option Nat :=
  l.foldl (fun a x => Seal.minOpt a x.facts.capLeftMin) none

theorem capFold_some : ∀ (l : List Ranked) (e : Nat),
    ∃ c, l.foldl (fun a x => Seal.minOpt a x.facts.capLeftMin) (some e) = some c ∧ c ≤ e
  | [], e => ⟨e, rfl, Nat.le_refl e⟩
  | x :: xs, e => by
    simp only [List.foldl_cons]
    cases hc : x.facts.capLeftMin with
    | none =>
      obtain ⟨c, h1, h2⟩ := capFold_some xs e
      exact ⟨c, by simpa [Seal.minOpt, hc] using h1, h2⟩
    | some d =>
      obtain ⟨c, h1, h2⟩ := capFold_some xs (min e d)
      exact ⟨c, by simpa [Seal.minOpt, hc] using h1, Nat.le_trans h2 (Nat.min_le_left e d)⟩

theorem capFold_le_member : ∀ (l : List Ranked) (acc : Option Nat) (y : Ranked), y ∈ l →
    ∀ d, y.facts.capLeftMin = some d →
      ∃ c, l.foldl (fun a x => Seal.minOpt a x.facts.capLeftMin) acc = some c ∧ c ≤ d
  | [], _, _, h, _, _ => by simp at h
  | x :: xs, acc, y, hy, d, hd => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hy with rfl | hy
    · have hstep : Seal.minOpt acc y.facts.capLeftMin = some (min (acc.getD d) d) := by
        cases acc <;> simp [Seal.minOpt, hd]
      rw [hstep]
      obtain ⟨c, h1, h2⟩ := capFold_some xs (min (acc.getD d) d)
      exact ⟨c, h1, Nat.le_trans h2 (Nat.min_le_right _ _)⟩
    · exact capFold_le_member xs _ y hy d hd

/-- **A member's `max:` binds the group's commitment**: if any member has minutes left under a
`max:`, the group's cap is at most that member's. -/
theorem capLeftOf_le_member (l : List Ranked) (y : Ranked) (hy : y ∈ l) (d : Nat)
    (hd : y.facts.capLeftMin = some d) : ∃ c, capLeftOf l = some c ∧ c ≤ d :=
  capFold_le_member l none y hy d hd

/-- Σ `planned_min` over a group (fork `members.iter().map(planned_min).sum()`). -/
def plannedSum (l : List Ranked) : Nat := l.foldl (fun a x => a + x.facts.plannedMin) 0

/-- **Fork `build_groups`' `commit`** (`planner.rs:1451`): `planned.min(cap_left)` — what the
group asks the cursor for, capped by the tightest `max:` a member is still under. -/
def commitOf (l : List Ranked) : Nat :=
  match capLeftOf l with
  | none => plannedSum l
  | some c => min (plannedSum l) c

theorem commitOf_le_planned (l : List Ranked) : commitOf l ≤ plannedSum l := by
  unfold commitOf
  cases capLeftOf l with
  | none => exact Nat.le_refl _
  | some c => exact Nat.min_le_left _ _

theorem commitOf_le_cap (l : List Ranked) (y : Ranked) (hy : y ∈ l) (d : Nat)
    (hd : y.facts.capLeftMin = some d) : commitOf l ≤ d := by
  obtain ⟨c, hc, hcd⟩ := capLeftOf_le_member l y hy d hd
  unfold commitOf
  rw [hc]
  exact Nat.le_trans (Nat.min_le_right _ _) hcd

/-- **Fork `planner::Group`** (`planner.rs:1440`), with `left_min` carried as the pair
`commitMin`/`spent` (see this section's header). -/
structure Group where
  key        : GroupKey
  members    : List Ranked
  ci         : Fin 6
  loc        : Field.Loc
  splittable : Bool
  mult       : Arith.Pos
  /-- Fork `commit_min` = `planned.min(cap_left)`: the §8.5 minutes the group asks for, capped
  by the tightest `max:` a member is still under. -/
  commitMin  : Nat
  /-- The slot minutes already given to this group — the fork's `commit_min − left_min`. -/
  spent      : Nat

/-- Fork `g.left_min`, whenever the fork's is positive. -/
def Group.leftMin (g : Group) : Nat := g.commitMin - g.spent

/-- Fork `pick`'s first clause, `g.left_min > 0`. -/
def Group.live (g : Group) : Bool := decide (g.spent < g.commitMin)

theorem Group.live_iff (g : Group) : g.live = true ↔ 0 < g.leftMin := by
  unfold Group.live Group.leftMin
  simp only [decide_eq_true_eq]
  omega

/-- Fork `build_groups`' body for one split bucket.  `none` only for an empty bucket, which
`splitGroups_ne_nil` says cannot arise. -/
def groupOf (k : SplitKey) : List Ranked → Option Group
  | [] => none
  | x :: xs =>
    some ⟨minGroupKey (groupKeyOf x) xs, x :: xs, x.cand.ci, k.loc, k.splittable,
      x.facts.multiplier, commitOf (x :: xs), 0⟩

theorem groupOf_members {k : SplitKey} {l : List Ranked} {g : Group} (h : groupOf k l = some g) :
    g.members = l ∧ g.loc = k.loc ∧ g.splittable = k.splittable := by
  cases l with
  | nil => exact absurd h (by simp [groupOf])
  | cons x xs =>
    unfold groupOf at h
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl⟩

/-- **The commitment never exceeds what the estimates ask for.** -/
theorem groupOf_commit_le_planned {k : SplitKey} {l : List Ranked} {g : Group}
    (h : groupOf k l = some g) : g.commitMin ≤ plannedSum g.members := by
  cases l with
  | nil => exact absurd h (by simp [groupOf])
  | cons x xs =>
    unfold groupOf at h
    simp only [Option.some.injEq] at h
    subst h
    exact commitOf_le_planned (x :: xs)

/-- **And never exceeds a member's `max:`** — §6.2's ceiling, honoured by the commitment and
not merely reported.  This is the `max:` half of §8.2 step 5. -/
theorem groupOf_commit_le_cap {k : SplitKey} {l : List Ranked} {g : Group} (h : groupOf k l = some g)
    (y : Ranked) (hy : y ∈ g.members) (d : Nat) (hd : y.facts.capLeftMin = some d) :
    g.commitMin ≤ d := by
  cases l with
  | nil => exact absurd h (by simp [groupOf])
  | cons x xs =>
    have hm := (groupOf_members h).1
    unfold groupOf at h
    simp only [Option.some.injEq] at h
    subst h
    rw [hm] at hy
    exact commitOf_le_cap (x :: xs) y hy d hd

/-! ### The groups of a request -/

def groupLe (a b : Group) : Bool := groupKeyLe a.key b.key

theorem groupLe_trans (a b c : Group) (h₁ : groupLe a b) (h₂ : groupLe b c) : groupLe a c :=
  groupKeyLe_trans _ _ _ h₁ h₂

theorem groupLe_total (a b : Group) : groupLe a b || groupLe b a := groupKeyLe_total _ _

/-- Fork `out.sort_by(|a, b| a.key.cmp(&b.key))`, a **stable** sort: `Replay.insSort` is the
specification (`decide` evaluates it) and core's `mergeSort` the compiled twin. -/
def sortGroups (l : List Group) : List Group := Replay.insSort groupLe l

def sortGroupsFast (l : List Group) : List Group := l.mergeSort groupLe

@[csimp] theorem sortGroups_eq_sortGroupsFast : @sortGroups = @sortGroupsFast := by
  funext l
  unfold sortGroups sortGroupsFast
  exact Replay.insSort_eq_mergeSort groupLe groupLe_trans groupLe_total l

theorem mem_sortGroups {l : List Group} {x : Group} : x ∈ sortGroups l ↔ x ∈ l :=
  (Replay.insSort_perm groupLe l).mem_iff

theorem sortGroups_sorted (l : List Group) :
    (sortGroups l).Pairwise (fun a b => groupLe a b = true) := by
  unfold sortGroups
  rw [Replay.insSort_eq_mergeSort groupLe groupLe_trans groupLe_total l]
  exact List.pairwise_mergeSort (fun a b c h₁ h₂ => groupLe_trans a b c h₁ h₂)
    (fun a b => groupLe_total a b) l

/-- **Fork `build_groups`' `members` filter** (`planner.rs:1420`): a wall is placed by step 1, an
optional only fills Rest in step 7, and a window instance is placed inside its own window by
step 2, so none of the three is ever given a slot here. -/
def batchMembers (b : List Ranked) : List Ranked :=
  b.filter (fun x => !x.cand.wall && !x.cand.optional && !x.cand.window)

theorem mem_batchMembers {b : List Ranked} {y : Ranked} (h : y ∈ batchMembers b) :
    y ∈ b ∧ y.cand.wall = false ∧ y.cand.optional = false ∧ y.cand.window = false := by
  simp only [batchMembers, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1, h.2.1.1, h.2.1.2, h.2.2⟩

theorem mem_batchMembers_of {b : List Ranked} {y : Ranked} (hy : y ∈ b)
    (hw : y.cand.wall = false) (ho : y.cand.optional = false) (hn : y.cand.window = false) :
    y ∈ batchMembers b := by
  simp [batchMembers, List.mem_filter, hy, hw, ho, hn]

/-- **§7.5's groups of this request** — the one call `build_groups` walks, so a witness that
reads the batching and the step that consumes it cannot drift apart (AGENTS §5.3). -/
def PlanReq.dayBatches (r : PlanReq) : List (List Ranked) :=
  batches r.prio.batchMaxMin r.blockMin r.rankedCands

/-- **§8.2 step 5's groups, unsorted** — the batching, the split and one `Group` per bucket. -/
def PlanReq.rawGroups (r : PlanReq) : List Group :=
  r.dayBatches.flatMap (fun b =>
    (splitGroups (r.activeRun.map (·.id)) (batchMembers b)).filterMap (fun e => groupOf e.1 e.2))

/-- **Fork `build_groups`**: §7.4's key order, restored after the batching gathered forward. -/
def PlanReq.buildGroups (r : PlanReq) : List Group := sortGroups r.rawGroups

theorem PlanReq.mem_rawGroups {r : PlanReq} {g : Group} (h : g ∈ r.rawGroups) :
    ∃ b ∈ r.dayBatches,
      ∃ e ∈ splitGroups (r.activeRun.map (·.id)) (batchMembers b), groupOf e.1 e.2 = some g := by
  simp only [PlanReq.rawGroups, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨b, hb, e, he, hg⟩ := h
  exact ⟨b, hb, e, he, hg⟩

theorem PlanReq.mem_buildGroups {r : PlanReq} {g : Group} :
    g ∈ r.buildGroups ↔ g ∈ r.rawGroups := mem_sortGroups

/-- **Every member of every group is a candidate this request ranked** — nothing is invented. -/
theorem PlanReq.a_group_member_is_ranked {r : PlanReq} {g : Group} {y : Ranked}
    (hg : g ∈ r.buildGroups) (hy : y ∈ g.members) : y ∈ r.rankedCands := by
  obtain ⟨b, hb, e, he, hgo⟩ := PlanReq.mem_rawGroups (PlanReq.mem_buildGroups.1 hg)
  rw [(groupOf_members hgo).1] at hy
  exact mem_of_mem_batches hb (mem_batchMembers (mem_of_mem_splitGroups he hy)).1

/-- **And every ranked candidate a slot could take is in one** — the direction the "never
drops" goals read.  A wall, an optional and a window instance are placed by other steps and are
deliberately not here. -/
theorem PlanReq.a_ranked_candidate_has_a_group {r : PlanReq} {y : Ranked}
    (hy : y ∈ r.rankedCands) (hw : y.cand.wall = false) (ho : y.cand.optional = false)
    (hn : y.cand.window = false) : ∃ g ∈ r.buildGroups, y ∈ g.members := by
  obtain ⟨b, hb, hyb⟩ := batches_cover (ms := r.prio.batchMaxMin) (bm := r.blockMin) hy
  obtain ⟨e, he, hye⟩ := splitGroups_cover (act := r.activeRun.map (·.id))
    (mem_batchMembers_of hyb hw ho hn)
  have hne : e.2 ≠ [] := splitGroups_ne_nil _ _ e he
  cases hgo : groupOf e.1 e.2 with
  | none =>
    cases hl : e.2 with
    | nil => exact absurd hl hne
    | cons z zs => rw [hl] at hgo; simp [groupOf] at hgo
  | some g =>
    refine ⟨g, PlanReq.mem_buildGroups.2 ?_, ?_⟩
    · simp only [PlanReq.rawGroups, List.mem_flatMap, List.mem_filterMap]
      exact ⟨b, hb, e, he, hgo⟩
    · rw [(groupOf_members hgo).1]; exact hye

/-- **A group's `loc:` and `splittable` are its members'**, by the key they were bucketed on. -/
theorem PlanReq.a_group_member_carries_the_groups_filters {r : PlanReq} {g : Group} {y : Ranked}
    (hg : g ∈ r.buildGroups) (hy : y ∈ g.members) :
    y.facts.loc = g.loc ∧ y.facts.splittable = g.splittable := by
  obtain ⟨b, hb, e, he, hgo⟩ := PlanReq.mem_rawGroups (PlanReq.mem_buildGroups.1 hg)
  obtain ⟨hm, hl, hs⟩ := groupOf_members hgo
  rw [hm] at hy
  have hk := splitGroups_keys (r.activeRun.map (·.id)) (batchMembers b) e he y hy
  unfold splitKeyOf at hk
  rw [hl, hs, ← hk]
  exact ⟨rfl, rfl⟩

/-- **And its `ci` is its members'** — §7.5 gathers by `ci` alone, so a group is one level, and
that is what `pick`'s energy filter needs to be a statement about every member. -/
theorem PlanReq.a_group_member_carries_the_groups_ci {r : PlanReq} {g : Group} {y : Ranked}
    (hg : g ∈ r.buildGroups) (hy : y ∈ g.members) : y.cand.ci = g.ci := by
  obtain ⟨b, hb, e, he, hgo⟩ := PlanReq.mem_rawGroups (PlanReq.mem_buildGroups.1 hg)
  have hm := (groupOf_members hgo).1
  rw [hm] at hy
  cases hl : e.2 with
  | nil => rw [hl] at hgo; simp [groupOf] at hgo
  | cons z zs =>
    have hci : g.ci = z.cand.ci := by rw [hl] at hgo; simp only [groupOf, Option.some.injEq] at hgo;
                                      rw [← hgo]
    rw [hl] at hy
    have h1 := mem_of_mem_splitGroups (e := e) he (by rw [hl]; exact hy)
    have h2 := mem_of_mem_splitGroups (e := e) he (by rw [hl]; exact List.mem_cons_self ..)
    rw [hci]
    exact batches_ci hb _ (mem_batchMembers h1).1 _ (mem_batchMembers h2).1

/-- **No group is empty and none is longer than `maxBatch`** — so `mkBatch?` cannot refuse the
row a group's slot emits (R10). -/
theorem PlanReq.a_group_is_a_bounded_batch {r : PlanReq} {g : Group} (hg : g ∈ r.buildGroups) :
    g.members ≠ [] ∧ g.members.length ≤ maxBatch := by
  obtain ⟨b, hb, e, he, hgo⟩ := PlanReq.mem_rawGroups (PlanReq.mem_buildGroups.1 hg)
  have hm := (groupOf_members hgo).1
  refine ⟨by rw [hm]; exact splitGroups_ne_nil _ _ e he, ?_⟩
  rw [hm]
  refine Nat.le_trans (splitGroups_length he) (Nat.le_trans ?_ (batches_length _ _ _ b hb))
  exact List.Sublist.length_le List.filter_sublist

/-- **Sorted in §7.4's key order.** -/
theorem PlanReq.buildGroups_sorted (r : PlanReq) :
    r.buildGroups.Pairwise (fun a b => groupLe a b = true) := sortGroups_sorted _

/-- **And a group's key is the minimum of its members'** — fork `members.iter().map(sort_key)
.min()`, stated over the value rather than assumed of it. -/
theorem PlanReq.a_group_key_is_its_minimum {r : PlanReq} {g : Group} {y : Ranked}
    (hg : g ∈ r.buildGroups) (hy : y ∈ g.members) : groupKeyLe g.key (groupKeyOf y) := by
  obtain ⟨b, hb, e, he, hgo⟩ := PlanReq.mem_rawGroups (PlanReq.mem_buildGroups.1 hg)
  have hm := (groupOf_members hgo).1
  rw [hm] at hy
  cases hl : e.2 with
  | nil => rw [hl] at hgo; simp [groupOf] at hgo
  | cons z zs =>
    have hk : g.key = minGroupKey (groupKeyOf z) zs := by
      rw [hl] at hgo; simp only [groupOf, Option.some.injEq] at hgo; rw [← hgo]
    rw [hl] at hy
    rw [hk]
    rcases List.mem_cons.1 hy with rfl | hy
    · exact minGroupKey_le_seed zs _
    · exact minGroupKey_le_mem zs _ y hy

/-! ### §9's running block, against its own group

Fork `plan()` (`planner.rs:1008-1015`): the block running at `now` has already spent part of
the work its group was owed, so its group starts the cursor with those minutes taken.  It costs
exactly **one** block against the budget however long it runs, which is the cursor's `used`
seed and is P5b's other half. -/

/-- The first group holding `id` starts with `mins` of its commitment spent (fork `groups[gi]
.left_min -= run.minutes()`). -/
def spendActive (id : Id) (mins : Nat) : List Group → List Group
  | [] => []
  | g :: rest =>
    if g.members.any (fun x => x.cand.id == id) then { g with spent := g.spent + mins } :: rest
    else g :: spendActive id mins rest

/-- **§8.2 step 5's groups, as the cursor receives them.** -/
def PlanReq.startGroups (r : PlanReq) : List Group :=
  match r.activeRun with
  | none => r.buildGroups
  | some q => spendActive q.id (Look.spanMinutes q.start q.stop) r.buildGroups

/-- `spendActive` touches nothing but one group's `spent`. -/
theorem spendActive_keys (id : Id) (mins : Nat) : ∀ (l : List Group) (g : Group),
    g ∈ spendActive id mins l →
      ∃ g₀ ∈ l, g.key = g₀.key ∧ g.members = g₀.members ∧ g.ci = g₀.ci ∧ g.loc = g₀.loc ∧
        g.splittable = g₀.splittable ∧ g.commitMin = g₀.commitMin
  | [], _, h => by simp [spendActive] at h
  | g₀ :: rest, g, h => by
    unfold spendActive at h
    by_cases hb : (g₀.members.any (fun x => x.cand.id == id)) = true
    · rw [if_pos hb] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨g₀, List.mem_cons_self .., rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨g, List.mem_cons_of_mem _ h, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [if_neg hb] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨g, List.mem_cons_self .., rfl, rfl, rfl, rfl, rfl, rfl⟩
      · obtain ⟨g₁, h₁, hrest⟩ := spendActive_keys id mins rest g h
        exact ⟨g₁, List.mem_cons_of_mem _ h₁, hrest⟩

theorem spendActive_length (id : Id) (mins : Nat) : ∀ l : List Group,
    (spendActive id mins l).length = l.length
  | [] => rfl
  | g :: rest => by
    unfold spendActive
    by_cases hb : (g.members.any (fun x => x.cand.id == id)) = true
    · rw [if_pos hb]; simp
    · rw [if_neg hb]; simp [spendActive_length id mins rest]

/-- **A group the cursor receives is a group `build_groups` built**, with at most one of them
holding a different `spent` — so every law above about `buildGroups` is a law about the
cursor's input. -/
theorem PlanReq.a_started_group_is_a_built_group {r : PlanReq} {g : Group}
    (hg : g ∈ r.startGroups) :
    ∃ g₀ ∈ r.buildGroups, g.key = g₀.key ∧ g.members = g₀.members ∧ g.ci = g₀.ci ∧
      g.loc = g₀.loc ∧ g.splittable = g₀.splittable ∧ g.commitMin = g₀.commitMin := by
  unfold PlanReq.startGroups at hg
  cases hq : r.activeRun with
  | none => rw [hq] at hg; exact ⟨g, hg, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | some q => rw [hq] at hg; exact spendActive_keys _ _ _ g hg

/-! ############################################################################
## §8.2 step 5, the second half: the cursor

**Fork `plan()`'s assign loop** (`planner.rs:1017-1026`) over **fork `Planner::pick`**
(`planner.rs:1582`) and **fork `contiguous_fits`** (`planner.rs:2303`).  One walk over the
energised slots in time order; at each free slot the **first** group in §7.4's key order that
passes the filter takes it, and the budget stops the walk.

**This is eligibleAt's SLOT half** (README gap 365).  The *item* half —
`Candidate::eligible()` and `!is_wall || wall_today` — is `entersTheOrder`'s and was applied
before the sort at P5b-i.  The two halves are written once each and in different places for the
reason the fork puts them in different places: the item half decides who is in the order at all,
the slot half decides whether *this* slot may hold them.

**Nothing here reaches `dayPlan`.**  The rows an assignment emits are the step after this one;
`dayRows` is unchanged and `PlanCheck`'s four emptiness theorems still hold.  README gap 803.
############################################################################ -/

/-- An index a `getElem?` answered at is in range.  Core states this as an existential inside
`List.getElem?_eq_some_iff`, which `omega` cannot destructure. -/
theorem lt_of_getElem?_some {α : Type} {l : List α} {n : Nat} {a : α} (h : l[n]? = some a) :
    n < l.length := by
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.1 h
  exact hlt

/-- **One energised entry per slot**, in the cut's own order — `Look.energizeToday` is a `map`,
so the cursor's slot vector and the slot list are indexed alike. -/
theorem PlanReq.energisedSlots_length (r : PlanReq) :
    r.energisedSlots.length = r.todaySlots.length := by
  unfold PlanReq.energisedSlots Look.energizeToday
  exact List.length_map _

/-- **Fork `Planner::loc_ok`** (`planner.rs:1609`): an item with no constraint fits anywhere,
and an unknown current location constrains nothing.

**Named `groupLocOk` and not `locOk`** — `Cmd.locOk` is a different predicate (well-formedness
of a location *word*), and check 8 resolves a prose citation on its **last dotted segment**, so
two `locOk`s would make a citation of either resolve against the other and no gate could tell a
stale one from a live one (W-19's reuse critic; README gap 878). -/
def groupLocOk (cur item : Field.Loc) : Bool :=
  match item with
  | .any => true
  | other => (cur == Field.Loc.any) || (other == cur)

/-- The request's current location as the grammar's own value.  `state.loc` is a word and
`Field.parseLoc` is the kernel's single reader of it (AGENTS §5.3); a word the grammar does not
accept — the empty one — constrains nothing, which is fork `Loc::Any`. -/
def PlanReq.curLoc (r : PlanReq) : Field.Loc := (Field.parseLoc r.loc).getD .any

/-- **Fork `contiguous_fits`' walk** (`planner.rs:2313-2327`): from the slot the cursor is at,
forwards, while the run is unbroken — an assigned slot ends it, and so does a gap that is not
one of step 3's own breaks.  "Sitting through the break the planner itself inserted is not a
context switch", which is why `breaks` is consulted and not merely the clock.

The test is over **free slots** and never over what the budget can pay for: bounding the run by
the budget would break §8.3's tail-drop, because shrinking the budget by one block would make a
non-splittable item skip its slot and a *different* candidate take it — a re-shuffle, not the
removal of a suffix.  The fork's comment says exactly that and it is carried here because L24 is
stated against this function. -/
def fitsRun (breaks : List (Nat × Nat)) (prev : Option Nat) (need : Nat) :
    List (Look.Slot × Option Nat) → Bool
  | [] => false
  | (s, a) :: rest =>
    if a.isSome then false
    else if (match prev with
             | Option.none => false
             | some p => decide (s.start ≠ p) && !breaks.any (fun b => decide (b = (p, s.start))))
      then false
    else if need ≤ s.minutes then true
    else fitsRun breaks (some s.stop) (need - s.minutes) rest

/-- **Fork `contiguous_fits`**, at the cursor's position. -/
def contiguousFits (slots : List Look.Slot) (slotOf : List (Option Nat))
    (breaks : List (Nat × Nat)) (i need : Nat) : Bool :=
  fitsRun breaks Option.none need ((slots.zip slotOf).drop i)

/-- **Fork `Planner::pick`'s per-group test** — §8.2 step 5's filter at one slot, and the whole
of eligibleAt's slot half.  Five clauses, the fork's, in the fork's order: the group still
owes minutes; its `ci` is within the slot's energy; its `loc:` fits where we are; nothing
demanding runs after the wind-down (step 3's rule again, defensively); and a non-`splittable`
group needs an unbroken run long enough for what it still owes. -/
def PlanReq.groupFitsSlot (r : PlanReq) (slots : List Look.Slot) (slotOf : List (Option Nat))
    (breaks : List (Nat × Nat)) (i : Nat) (e : Fin 6) (s : Look.Slot) (g : Group) : Bool :=
  g.live && decide (g.ci.val ≤ e.val) && groupLocOk r.curLoc g.loc &&
    !(decide (r.windDownSec ≤ s.start) && decide (4 ≤ g.ci.val)) &&
    (g.splittable || contiguousFits slots slotOf breaks i g.leftMin)

/-- **Fork `pick`'s `for (gi, g) in groups.iter().enumerate()`**: the **first** group in §7.4's
order that passes, by index — and that walk is **`List.findIdx?`**, which the cursor calls
rather than carrying a third copy of it (AGENTS §5.3; W-19's reuse critic, README gap 877).
Lean 4.33.1's `List.findIdx?` is `go l 0`, an accumulator walk of exactly the shape the
hand-written definition deleted here had, so it reduces under `decide` as that one did.

This is **stronger** than the hand-written soundness lemma it replaces, and deliberately so:
`List.findIdx?_eq_some_iff_getElem` also gives that every group *before* the answer **fails**
the test, which is the whole of what the fork's `for` loop means by "first" and which the
deleted lemma never stated.

**The second conjunct has a subject and no consumer**, and both halves are said here rather
than left for an auditor.  Its subject is computed:
`PlannerWit.the_cursor_fills_the_day_in_key_order` gives the second slot of §4.3's Wednesday to
group **3**, so groups 0, 1 and 2 are refused there — `^c2` for its `loc:` and `^c3` for its
`ci` — and the quantifier is not empty.  Its consumer is nobody: `PlanReq.assignStep_cases`
destructures this theorem as `⟨⟨g₀, hg₀, hpg⟩, -⟩` and discards it.  It is kept because it is
free from the core lemma and because it is the claim the fork's `for` loop actually makes;
README gap 877.

**GENERALISED AT §8.2 STEP 7, over the element type and nothing else.**  Step 7's optionals
take the **first free stretch wide enough** (`Planner.placeOptional`, fork
`free.iter().position(…)`), which is this walk at `List (Nat × Nat)`, and a second copy of an
eight-line `findIdx?` inversion is the class §5.3 names.  The statement is the same
conjunction at `α = Group`, so every consumer of the old form is unchanged and D5's
"re-proved over the new shape, never weakened" is satisfied by construction.  The name is
still step 5's; it is the one caller that named it. -/
theorem pickedGroup_is_the_first_that_fits {α : Type} (P : α → Bool) (l : List α) (n : Nat)
    (h : l.findIdx? P = some n) :
    (∃ g, l[n]? = some g ∧ P g = true) ∧
      ∀ j, j < n → ∀ g, l[j]? = some g → P g = false := by
  obtain ⟨hlt, hp, hbefore⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  refine ⟨⟨l[n], List.getElem?_eq_getElem hlt, hp⟩, ?_⟩
  intro j hj g hg
  have hjl : j < l.length := Nat.lt_trans hj hlt
  rw [List.getElem?_eq_getElem hjl] at hg
  have hje : l[j] = g := Option.some.inj hg
  have hb := hbefore j hj
  rw [hje] at hb
  simpa using hb

/-- What the cursor carries: which group each slot went to, the groups with what they have
spent, and the blocks the day has committed. -/
structure Assign where
  /-- One entry per slot, in the cut's own order — fork `assign : Vec<Option<usize>>`. -/
  slotOf : List (Option Nat)
  groups : List Group
  /-- Fork `used`, seeded at `u32::from(active.is_some())`: the running block costs exactly one
  block against the budget however long it runs. -/
  used   : Nat

/-- Fork `plan()`'s loop body (`planner.rs:1017-1026`).  A slot already taken is passed over,
and a spent budget passes over the slot without ending the walk — the fork `continue`s rather
than breaking, because `place_deferred` may free a slot later and re-place into it.

**The slot-taken guard is structurally unreachable here, and it is unreachable in the fork
too.**  `assignStart` seeds `slotOf` with one `Option.none` per slot and `assignFold` folds
over `r.energisedSlots.zipIdx`, so each index is visited exactly **once** and the only entry a
step ever `set`s is `x.2`'s: no step can observe an occupied slot.  The fork's step-5 loop has
the same shape — `let mut assign = vec![None; slots.len()]` then `for i in 0..slots.len() { if
assign[i].is_some() || … { continue } }` — and only `place_deferred` (step 6) writes `assign`
out of order.  So **dropping `(a.slotOf[x.2]?).join.isSome ||` leaves the whole build green**
(W-19's audit, inversion I2), and the guard stays anyway because the port is faithful and step
6 is the caller that will reach it.  It is the **sixth** clause of this fold that no
∀-theorem pins, beside the two README gap 806 names — and unlike those two, nothing can pin
it until P6 exists.  README gap 876. -/
def PlanReq.assignStep (r : PlanReq) (slots : List Look.Slot) (breaks : List (Nat × Nat))
    (budget : Nat) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat) : Assign :=
  if (a.slotOf[x.2]?).join.isSome || decide (budget ≤ a.used) then a
  else
    match a.groups.findIdx? (r.groupFitsSlot slots a.slotOf breaks x.2 x.1.1 x.1.2) with
    | Option.none => a
    | some gi =>
      match a.groups[gi]? with
      | Option.none => a
      | some g =>
        ⟨a.slotOf.set x.2 (some gi),
         a.groups.set gi { g with spent := g.spent + x.1.2.minutes }, a.used + 1⟩

/-- Fork `used`'s seed. -/
def PlanReq.activeSeed (r : PlanReq) : Nat := if r.activeRun.isSome then 1 else 0

/-- Nothing assigned yet: one `none` per slot, the groups as `build_groups` left them with the
running block's minutes already charged, and one block of the budget already gone if it runs. -/
def PlanReq.assignStart (r : PlanReq) : Assign :=
  ⟨List.replicate r.todaySlots.length Option.none, r.startGroups, r.activeSeed⟩

/-- **§8.2 step 5's assignment.** -/
def PlanReq.assignFold (r : PlanReq) : Assign :=
  r.energisedSlots.zipIdx.foldl
    (r.assignStep r.todaySlots r.todayBreaks (remainingBudget r)) r.assignStart

/-! ### What the cursor guarantees

Every law below is proved by the same case split, taken once: a step either **changes nothing**
or fills exactly one slot with a group the filter passed.  `assignStep_cases` is that split, and
nothing else in this section unfolds `assignStep`. -/

/-- The two shapes a step can have. -/
theorem PlanReq.assignStep_cases (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat) :
    r.assignStep slots breaks budget a x = a ∨
      ∃ gi g, a.groups[gi]? = some g ∧
        r.groupFitsSlot slots a.slotOf breaks x.2 x.1.1 x.1.2 g = true ∧
        a.used < budget ∧
        r.assignStep slots breaks budget a x =
          ⟨a.slotOf.set x.2 (some gi),
           a.groups.set gi { g with spent := g.spent + x.1.2.minutes }, a.used + 1⟩ := by
  unfold PlanReq.assignStep
  split
  · exact Or.inl rfl
  · rename_i hguard
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true] at hguard
    split
    · exact Or.inl rfl
    · rename_i gi hp
      split
      · exact Or.inl rfl
      · rename_i g hg
        refine Or.inr ⟨gi, g, hg, ?_, by omega, rfl⟩
        obtain ⟨⟨g₀, hg₀, hpg⟩, -⟩ := pickedGroup_is_the_first_that_fits _ a.groups gi hp
        rw [hg] at hg₀
        rwa [(Option.some.inj hg₀.symm : g₀ = g)] at hpg

/-- The slot vector keeps one entry per slot, and the group list its length. -/
theorem PlanReq.assignStep_lengths (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat) :
    (r.assignStep slots breaks budget a x).slotOf.length = a.slotOf.length ∧
      (r.assignStep slots breaks budget a x).groups.length = a.groups.length := by
  rcases PlanReq.assignStep_cases r slots breaks budget a x with heq | ⟨gi, g, -, -, -, heq⟩ <;>
    rw [heq] <;> simp

/-- **The cursor moves nothing but `spent`** — a group's key, members, `ci`, `loc:`,
`splittable` and commitment are what `build_groups` made them, at every point of the walk. -/
theorem PlanReq.assignStep_keeps_the_group (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat)
    (n : Nat) (g' : Group) (h : (r.assignStep slots breaks budget a x).groups[n]? = some g') :
    ∃ g, a.groups[n]? = some g ∧ g.key = g'.key ∧ g.members = g'.members ∧ g.ci = g'.ci ∧
      g.loc = g'.loc ∧ g.splittable = g'.splittable ∧ g.commitMin = g'.commitMin := by
  rcases PlanReq.assignStep_cases r slots breaks budget a x with heq | ⟨gi, g, hg, -, -, heq⟩
  · rw [heq] at h; exact ⟨g', h, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [heq] at h
    simp only at h
    by_cases hn : n = gi
    · subst hn
      rw [List.getElem?_set_self (lt_of_getElem?_some hg)] at h
      simp only [Option.some.injEq] at h
      exact ⟨g, hg, by rw [← h], by rw [← h], by rw [← h], by rw [← h], by rw [← h], by rw [← h]⟩
    · rw [List.getElem?_set_ne (by omega)] at h
      exact ⟨g', h, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **§8.2 step 5's filter, as a property of the assignment it produced**: a slot that went to a
group went to one whose `ci` the slot's energy covers, whose `loc:` fits where the day is being
lived, and which is not demanding work after the wind-down.  Those three read only fields the
cursor never touches, which is what makes them survive the rest of the walk — the other two
clauses (`g.live` and the atomic run) are about values the walk *does* move, and are
plan_does_not_overbook's and E1's business at the step that emits rows. -/
def PlanReq.AssignOk (r : PlanReq) (a : Assign) : Prop :=
  a.slotOf.length = r.energisedSlots.length ∧
  ∀ (i gi : Nat), a.slotOf[i]? = some (some gi) →
    ∃ (e : Fin 6) (s : Look.Slot) (g : Group),
      r.energisedSlots[i]? = some (e, s) ∧ a.groups[gi]? = some g ∧
        g.ci.val ≤ e.val ∧ groupLocOk r.curLoc g.loc = true ∧
        ¬ (r.windDownSec ≤ s.start ∧ 4 ≤ g.ci.val)

theorem PlanReq.assignStart_ok (r : PlanReq) : r.AssignOk r.assignStart := by
  unfold PlanReq.AssignOk PlanReq.assignStart
  refine ⟨by simp [PlanReq.energisedSlots_length], ?_⟩
  intro i gi h
  simp only [List.getElem?_replicate] at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem PlanReq.assignStep_ok (r : PlanReq) (breaks : List (Nat × Nat)) (budget : Nat)
    (a : Assign) (x : (Fin 6 × Look.Slot) × Nat) (hx : r.energisedSlots[x.2]? = some x.1)
    (h : r.AssignOk a) : r.AssignOk (r.assignStep r.todaySlots breaks budget a x) := by
  unfold PlanReq.AssignOk at h ⊢
  obtain ⟨hlen, h⟩ := h
  have hxlt : x.2 < a.slotOf.length := by
    rw [hlen]; exact lt_of_getElem?_some hx
  rcases PlanReq.assignStep_cases r r.todaySlots breaks budget a x with
    heq | ⟨gj, g, hg, hpg, -, heq⟩
  · rw [heq]; exact ⟨hlen, h⟩
  · rw [heq]
    refine ⟨by simpa using hlen, ?_⟩
    intro i gi hi
    simp only at hi ⊢
    unfold PlanReq.groupFitsSlot at hpg
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, Bool.and_eq_false_iff,
      decide_eq_false_iff_not] at hpg
    by_cases hix : i = x.2
    · subst hix
      rw [List.getElem?_set_self hxlt] at hi
      simp only [Option.some.injEq] at hi
      subst hi
      refine ⟨x.1.1, x.1.2, { g with spent := g.spent + x.1.2.minutes }, hx,
        by rw [List.getElem?_set_self (lt_of_getElem?_some hg)], hpg.1.1.1.2, hpg.1.1.2, ?_⟩
      rintro ⟨h1, h2⟩
      rcases hpg.1.2 with hw | hc
      · exact hw h1
      · exact hc h2
    · rw [List.getElem?_set_ne (by omega)] at hi
      obtain ⟨e, s, g₀, he, hg₀, h1, h2, h3⟩ := h i gi hi
      by_cases hgi : gi = gj
      · subst hgi
        rw [hg] at hg₀
        have hgg : g₀ = g := Option.some.inj hg₀.symm
        subst hgg
        exact ⟨e, s, { g₀ with spent := g₀.spent + x.1.2.minutes }, he,
          by rw [List.getElem?_set_self (lt_of_getElem?_some hg)], h1, h2, h3⟩
      · exact ⟨e, s, g₀, he, by rw [List.getElem?_set_ne (by omega)]; exact hg₀, h1, h2, h3⟩

theorem PlanReq.foldl_assignStep_ok (r : PlanReq) (breaks : List (Nat × Nat)) (budget : Nat) :
    ∀ (l : List ((Fin 6 × Look.Slot) × Nat)),
      (∀ x ∈ l, r.energisedSlots[x.2]? = some x.1) →
      ∀ a, r.AssignOk a → r.AssignOk (l.foldl (r.assignStep r.todaySlots breaks budget) a)
  | [], _, a, ha => ha
  | x :: xs, hl, a, ha => by
    simp only [List.foldl_cons]
    exact PlanReq.foldl_assignStep_ok r breaks budget xs
      (fun y hy => hl y (List.mem_cons_of_mem _ hy)) _
      (PlanReq.assignStep_ok r breaks budget a x (hl x (List.mem_cons_self ..)) ha)

/-- **The energy filter, the `loc:` filter and the wind-down rule hold of the produced
assignment** — the three of §8.2 step 5's five that are about fields the walk cannot move.  This
is what `plan_respects_the_energy_filter` and `plan_places_no_demanding_block_after_wind_down`
will read once a slot emits a row. -/
theorem PlanReq.assignFold_ok (r : PlanReq) : r.AssignOk r.assignFold := by
  unfold PlanReq.assignFold
  exact PlanReq.foldl_assignStep_ok r _ _ _
    (fun x hx => List.mem_zipIdx_iff_getElem?.mp hx) _ (PlanReq.assignStart_ok r)

/-- **The walk never spends more than the remaining budget** — fork `used >= remaining_budget`,
with the running block's one block already counted by the seed. -/
theorem PlanReq.assignStep_used (r : PlanReq) (slots : List Look.Slot)
    (breaks : List (Nat × Nat)) (budget : Nat) (a : Assign) (x : (Fin 6 × Look.Slot) × Nat)
    (h : a.used ≤ max r.activeSeed budget) :
    (r.assignStep slots breaks budget a x).used ≤ max r.activeSeed budget := by
  rcases PlanReq.assignStep_cases r slots breaks budget a x with heq | ⟨gi, g, -, -, hlt, heq⟩ <;>
    rw [heq]
  · exact h
  · simp only
    omega

theorem PlanReq.foldl_assignStep_used (r : PlanReq) (breaks : List (Nat × Nat)) (budget : Nat) :
    ∀ (l : List ((Fin 6 × Look.Slot) × Nat)) (a : Assign), a.used ≤ max r.activeSeed budget →
      (l.foldl (r.assignStep r.todaySlots breaks budget) a).used ≤ max r.activeSeed budget
  | [], a, h => h
  | x :: xs, a, h => by
    simp only [List.foldl_cons]
    exact PlanReq.foldl_assignStep_used r breaks budget xs _
      (PlanReq.assignStep_used r _ breaks budget a x h)

theorem PlanReq.assignFold_used (r : PlanReq) :
    r.assignFold.used ≤ max r.activeSeed (remainingBudget r) :=
  PlanReq.foldl_assignStep_used r _ _ _ _ (Nat.le_max_left _ _)

/-- **A day with no budget left and nothing running assigns nothing** — the travel-day case, and
the case of a day whose blocks are all done.  Fork `used >= remaining_budget` is the whole of it,
and this is the half of §9's "→ drops" the budget owns. -/
theorem PlanReq.a_spent_budget_assigns_nothing (r : PlanReq) (hb : remainingBudget r = 0)
    (ha : r.activeRun = none) : r.assignFold = r.assignStart := by
  have hseed : r.assignStart.used = 0 := by
    unfold PlanReq.assignStart PlanReq.activeSeed; rw [ha]; rfl
  unfold PlanReq.assignFold
  have key : ∀ (l : List ((Fin 6 × Look.Slot) × Nat)) (a : Assign), a.used = 0 →
      l.foldl (r.assignStep r.todaySlots r.todayBreaks (remainingBudget r)) a = a := by
    intro l
    induction l with
    | nil => intro a _; rfl
    | cons x xs ih =>
      intro a h
      simp only [List.foldl_cons]
      have hstep : r.assignStep r.todaySlots r.todayBreaks (remainingBudget r) a x = a := by
        unfold PlanReq.assignStep
        rw [if_pos (by simp [hb, h])]
      rw [hstep]
      exact ih a h
  exact key _ r.assignStart hseed

/-- **Every slot the cursor filled names a group `build_groups` built** — the index is real, and
the group it names carries the key, the members, the `ci`, the `loc:`, the `splittable` and the
commitment that step 5's first half gave it. -/
theorem PlanReq.an_assigned_slot_names_a_group (r : PlanReq) (i gi : Nat)
    (h : r.assignFold.slotOf[i]? = some (some gi)) :
    ∃ g, r.assignFold.groups[gi]? = some g ∧
      ∃ g₀ ∈ r.startGroups, g₀.key = g.key ∧ g₀.members = g.members ∧ g₀.ci = g.ci ∧
        g₀.loc = g.loc ∧ g₀.splittable = g.splittable ∧ g₀.commitMin = g.commitMin := by
  have hok := PlanReq.assignFold_ok r
  unfold PlanReq.AssignOk at hok
  obtain ⟨e, s, g, -, hg, -, -, -⟩ := hok.2 i gi h
  refine ⟨g, hg, ?_⟩
  have key : ∀ (l : List ((Fin 6 × Look.Slot) × Nat)) (a : Assign) (n : Nat) (g' : Group),
      (l.foldl (r.assignStep r.todaySlots r.todayBreaks (remainingBudget r)) a).groups[n]?
        = some g' →
      ∃ g₀, a.groups[n]? = some g₀ ∧ g₀.key = g'.key ∧ g₀.members = g'.members ∧
        g₀.ci = g'.ci ∧ g₀.loc = g'.loc ∧ g₀.splittable = g'.splittable ∧
        g₀.commitMin = g'.commitMin := by
    intro l
    induction l with
    | nil => intro a n g' h; exact ⟨g', h, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | cons x xs ih =>
      intro a n g' h
      simp only [List.foldl_cons] at h
      obtain ⟨g₁, h1, e1, e2, e3, e4, e5, e6⟩ := ih _ n g' h
      obtain ⟨g₂, h2, f1, f2, f3, f4, f5, f6⟩ :=
        PlanReq.assignStep_keeps_the_group r r.todaySlots r.todayBreaks (remainingBudget r)
          a x n g₁ h1
      exact ⟨g₂, h2, f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4, f5.trans e5,
        f6.trans e6⟩
  obtain ⟨g₀, h0, k1, k2, k3, k4, k5, k6⟩ := key _ r.assignStart gi g (by
    unfold PlanReq.assignFold at hg; exact hg)
  exact ⟨g₀, List.mem_of_getElem? h0, k1, k2, k3, k4, k5, k6⟩

/-! ############################################################################
## §8.2 step 6 — the routines that missed their window (stage 6, step P6)

**Fork `Planner::place_deferred`** (`planner.rs:1622`), over **fork `occupied_now`**
(`planner.rs:2271`) and **fork `kept_breaks`** (`planner.rs:2333`), called from `run()` at
`planner.rs:1032` with the assignment §8.2 step 5 ended with.  Design §2's choice 6:

> *deferred routines take the **lowest predicted energy** free position (ties: earliest); a
> mandatory one may reach into the wind-down and then displace the lowest-energy assigned
> block; an instance with no position is named in `diagnostics.notes`.*

**Nothing here computes a free stretch, a slot energy or a slot.**  The search is
`Look.freeIntervals` — step L3's own, the same function step 2's `earliestFree` and step 3's
`Look.cutSlots` call; the energy is `Look.todayEnergy`, step L4's, at the instant the fork
asks about (`ectx.energy_at(a, blocks_done, 0)`, whose other two arguments reach `Features`
and cannot move a level — `Look.energizeToday`'s own doc comment says so); the re-placement of
a displaced group is `PlanReq.assignStep`, §8.2 step 5's own body, stopped at its first
success.  The **only** new search is "the lowest of these", and that is `Replay.lastMax?`
with its replacing relation turned round (`leastBy`).

**What step 6 may do that step 2 may not.**  Step 2 takes the *earliest* feasible position and
never touches anything already placed; step 6 takes the *lowest-energy* one, may reach into the
evening when the instance is mandatory, and may take a slot away from the group step 5 gave it
to.  The three are different rules over the same free time, which is why the fork runs them in
this order and why `PlanReq.deferOne_keeps_a_placed_routine` is stated below: step 6 only
ever fills a position step 2 left empty.

**README gap 285's family is not re-admitted here.**  A routine whose declared window is
malformed is refused **by name** at the boundary (`mkRoutine?`, `undeclaredWindow`), and an
occurrence whose remaining span has closed is passed over by the fork's own
`if span_to <= from { continue }` — §5.3's expiry, not a placement failure.
`PlanReq.deferOne_places_nothing_in_a_closed_window` is that guard as a theorem, and
`a_deferred_routine_is_inside_its_window` is step 2's own law restated over step 6's output:
every position step 6 gives is inside the instance's own span, at or after `now`, and exactly
the minutes the instance asked for.

**D9-21.**  `deferWalk` and `rePlaceWalk` are structural recursions over lists `Capped` bounds
at `maxCands` and at the day's own slot count — the shape `splitSleep` already has, and
neither carries an accumulator core's `foldl` could carry instead, because each step reads the
list it is walking (`occupied_now` is recomputed from every instance's current position).

**What does NOT reach `dayPlan` here** — README gap 803 is still open and this step does not
close it: `assignFold` emits no rows, so the slots step 6 frees and re-fills change no row of
the day.  What *does* reach the day is this step's own half: a routine step 6 places gets its
Routine row, and one it cannot place gets `Note.noPosition`.
############################################################################ -/

/-! ### The first minimum of a list, once -/

/-- **The first minimum of a list under a strict order.**  `Replay.lastMax?` is the running
*maximum* under a *replacing* relation — "`x` replaces `a` when `r a x`" — so the minimum is
that same fold with the relation turned round, and not a second walk (AGENTS §5.3).  Because
the relation is strict, a later element equal on every key does **not** replace an earlier one,
which is Rust's own rule for the minimum of an iterator, by key or not: the first of the
minima wins.

*(`Replay.minDay?` and `Seal.minInstant?` are minima too, each folding `Nat.min` / `if` over
its own element type.  Neither is a call of this one and this is not a call of them: widening
either into this shape would restate its laws, which is D5's price and not this step's.
README gap 900.)* -/
def leastBy {α : Type} (lt : α → α → Bool) (l : List α) : Option α :=
  Replay.lastMax? (fun a x => lt x a) l

/-- The turned-round relation is transitive when the order is. -/
theorem flip_trans {α : Type} {lt : α → α → Bool} (h : Seal.StrictTotal lt) (a b c : α)
    (h₁ : lt b a = true) (h₂ : lt c b = true) : lt c a = true := h.trans _ _ _ h₂ h₁

/-- And a candidate it does not replace is replaced by whatever replaces that one — the
`skip` side condition `Replay.lastMax?_spec` asks for. -/
theorem flip_skip {α : Type} {lt : α → α → Bool} (h : Seal.StrictTotal lt) (a b c : α)
    (h₁ : lt b a = false) (h₂ : lt c a = true) : lt c b = true := by
  by_cases hab : lt a b = true
  · exact h.trans _ _ _ h₂ hab
  · have hba : a = b := h.eq_of_not (by simpa using hab) h₁
    rw [← hba]; exact h₂

/-- **What the minimum is**: an element of the list, and no element of the list is below it. -/
theorem leastBy_spec {α : Type} {lt : α → α → Bool} (h : Seal.StrictTotal lt)
    (l : List α) (b : α) (hb : leastBy lt l = some b) :
    b ∈ l ∧ ∀ x ∈ l, lt x b = false := by
  obtain ⟨l₁, l₂, hsp, h1, h2⟩ :=
    Replay.lastMax?_spec (fun a x => lt x a) (flip_trans h) (flip_skip h) l b hb
  refine ⟨by rw [hsp]; simp, fun x hx => ?_⟩
  rw [hsp] at hx
  simp only [List.mem_append, List.mem_cons] at hx
  rcases hx with hx | rfl | hx
  · -- an element before the minimum: the minimum replaced it, so it is not below
    have hbx : lt b x = true := h1 x hx
    cases hxb : lt x b with
    | false => rfl
    | true => exact absurd (h.trans _ _ _ hbx hxb) (by simp [h.irrefl])
  · exact h.irrefl x
  · exact h2 x hx

/-! ### The two orders step 6 takes a minimum in -/

/-- **Fork `place_deferred`'s `(energy_at(a), a)`** (`planner.rs:1653`): the free positions are
compared on their predicted energy first and on their start second, so the lowest energy wins
and the earlier start breaks the tie — design §2's choice 6, in the fork's own key order.
`Seal.lexLt` and `Seal.natLt` are the kernel's strict pair order and its strict `Nat` order and
are called, not copied. -/
abbrev posLt : Nat × Nat → Nat × Nat → Bool := Seal.lexLt Seal.natLt Seal.natLt

theorem posLt_strictTotal : Seal.StrictTotal posLt :=
  Seal.lexLt_strictTotal Seal.natLt_strictTotal Seal.natLt_strictTotal

/-- **Fork `place_deferred`'s victim comparator** (`planner.rs:1682`): the lowest slot energy,
and among equals the **later** slot — the fork writes the second key as `bi.cmp(ai)`, which is
the index descending.

The fork's *third* key, the slot's start ascending, is unreachable and is not ported: the
candidates come from an enumeration, so two of them never share an index, and a key after a
key that always decides is a clause no input can reach (AGENTS §5.2, and the class README gap
876 records for the cursor's own slot-taken guard). -/
abbrev victimLt : Nat × Nat → Nat × Nat → Bool :=
  Seal.lexLt Seal.natLt (fun a b => Seal.natLt b a)

theorem victimLt_strictTotal : Seal.StrictTotal victimLt :=
  Seal.lexLt_strictTotal Seal.natLt_strictTotal
    ⟨fun a => by simp [Seal.natLt], fun a b c h₁ h₂ => by
      simp only [Seal.natLt, decide_eq_true_eq] at *; omega,
     fun a b hne => by
      simp only [Seal.natLt, decide_eq_true_eq]
      rcases Nat.lt_trichotomy a b with h | h | h
      · exact Or.inr h
      · exact absurd h hne
      · exact Or.inl h⟩

/-! ### The search, and what it guarantees -/

/-- **Fork `place_deferred`'s search** (`planner.rs:1651-1655`): every free position inside
what is left of the instance's window that is wide enough for it, at that position's own
predicted energy, and the least of them in `posLt`.

`Look.freeIntervals` is step L3's and `Look.todayEnergy` step L4's; neither is re-derived
(design §1.2, §1.3). -/
def PlanReq.lowestFree (r : PlanReq) (occ : List (Nat × Nat)) (lo hi durSec : Nat) :
    Option Nat :=
  (leastBy posLt
    (((Look.freeIntervals lo hi occ).filter (fun iv => decide (durSec ≤ iv.2 - iv.1))).map
      (fun iv => ((Look.todayEnergy r.look ⟨iv.1, 0⟩).val, iv.1)))).map Prod.snd

/-- The position the search answers with comes from a free stretch of the range it searched,
wide enough for the instance. -/
theorem PlanReq.lowestFree_from_a_stretch {r : PlanReq} {occ : List (Nat × Nat)}
    {lo hi durSec t : Nat} (h : r.lowestFree occ lo hi durSec = some t) :
    ∃ iv ∈ Look.freeIntervals lo hi occ, iv.1 = t ∧ durSec ≤ iv.2 - iv.1 := by
  unfold PlanReq.lowestFree at h
  cases hl : leastBy posLt
      (((Look.freeIntervals lo hi occ).filter (fun iv => decide (durSec ≤ iv.2 - iv.1))).map
        (fun iv => ((Look.todayEnergy r.look ⟨iv.1, 0⟩).val, iv.1))) with
  | none => rw [hl] at h; exact absurd h (by simp)
  | some b =>
    rw [hl] at h
    simp only [Option.map_some, Option.some.injEq] at h
    obtain ⟨hmem, -⟩ := leastBy_spec posLt_strictTotal _ b hl
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq] at hmem
    obtain ⟨iv, ⟨hiv, hd⟩, hb⟩ := hmem
    exact ⟨iv, hiv, by rw [← h, ← hb], hd⟩

/-- **It is inside the range it was asked about, and every second of it is free** — the search
half of `PlacedOk`, and the half that makes a placement mean something. -/
theorem PlanReq.lowestFree_inside {r : PlanReq} {occ : List (Nat × Nat)} {lo hi durSec t : Nat}
    (h : r.lowestFree occ lo hi durSec = some t) :
    lo ≤ t ∧ t + durSec ≤ hi ∧ ∀ u, t ≤ u → u < t + durSec → Look.covered occ u = false := by
  obtain ⟨iv, hiv, ht, hd⟩ := PlanReq.lowestFree_from_a_stretch h
  subst ht
  exact freeStretch_gives_a_position hiv hd

/-! ### What is occupied at the moment step 6 looks -/

/-- **Fork `occupied_now`'s third list** (`planner.rs:2278-2285`): the slots the cursor filled.
The day's slots and the cursor's vector are indexed alike (`energisedSlots_length`), so the
`zip` loses neither. -/
def PlanReq.assignedSpans (r : PlanReq) (a : Assign) : List (Nat × Nat) :=
  (r.todaySlots.zip a.slotOf).filterMap
    (fun p => if p.2.isSome then some (p.1.start, p.1.stop) else none)

/-- **Fork `occupied_now`** (`planner.rs:2271`): everything a deferred routine must flow
around — the blocked list step 2 finished with (the walls with their `buffer:` run-ups, §9's
running interruption, §8.2 choice 5b's reservation and every routine step 2 placed), every
position given since, and the slots step 5 filled. -/
def PlanReq.occupiedNow (r : PlanReq) (qs : List Placed) (a : Assign) : List (Nat × Nat) :=
  r.placementFold.2 ++ qs.filterMap (·.placedAt) ++ r.assignedSpans a

/-- **Fork `kept_breaks`** (`planner.rs:2333`): a break belongs to the day only when work
touches it — the slot that ends where it starts, or the slot that starts where it ends, went to
a group.  Its row half is `PlanReq.keptBreakRows` (W-37, README gap **551**); what step 6 needs
is that a break the day really keeps is not free time a routine may be dropped into. -/
def PlanReq.keptBreaks (r : PlanReq) (a : Assign) : List (Nat × Nat) :=
  r.todayBreaks.filter (fun b =>
    (r.todaySlots.zip a.slotOf).any
      (fun p => p.2.isSome && (decide (p.1.stop = b.1) || decide (p.1.start = b.2))))

/-- **Fork `run()`'s `kept_breaks(&cut.breaks, &slots, &assign)`** (`planner.rs:1031`), taken
**once**, on the assignment step 5 ended with — the fork does not recompute it as step 6
frees and re-fills slots, and neither does this. -/
def PlanReq.keptBreaksToday (r : PlanReq) : List (Nat × Nat) := r.keptBreaks r.assignFold

/-! ### The displacement -/

/-- **Fork's `groups[gi].left_min += slots[vi].minutes()`** (`planner.rs:1688`): the group whose
slot was taken gets its minutes back.  `left_min` is carried here as `commitMin`/`spent`
(§8.2 step 5's first half), so giving minutes back is lowering `spent` — and it is **exact**,
because `assignStep` raised `spent` by the same number when the group took that very slot. -/
def unspend (gi mins : Nat) (gs : List Group) : List Group :=
  match gs[gi]? with
  | none => gs
  | some g => gs.set gi { g with spent := g.spent - mins }

/-- **The restore moves nothing but `spent`**, and only downwards. -/
theorem unspend_keeps_the_group (gi mins : Nat) (gs : List Group) (n : Nat) (g' : Group)
    (h : (unspend gi mins gs)[n]? = some g') :
    ∃ g, gs[n]? = some g ∧ g.key = g'.key ∧ g.members = g'.members ∧ g.ci = g'.ci ∧
      g.loc = g'.loc ∧ g.splittable = g'.splittable ∧ g.commitMin = g'.commitMin ∧
      g'.spent ≤ g.spent := by
  unfold unspend at h
  cases hg : gs[gi]? with
  | none => rw [hg] at h; exact ⟨g', h, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _⟩
  | some g =>
    rw [hg] at h
    by_cases hn : n = gi
    · subst hn
      rw [List.getElem?_set_self (lt_of_getElem?_some hg)] at h
      simp only [Option.some.injEq] at h
      exact ⟨g, hg, by rw [← h], by rw [← h], by rw [← h], by rw [← h], by rw [← h], by rw [← h],
        by rw [← h]; exact Nat.sub_le _ _⟩
    · rw [List.getElem?_set_ne (by omega)] at h
      exact ⟨g', h, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _⟩

theorem unspend_length (gi mins : Nat) (gs : List Group) : (unspend gi mins gs).length = gs.length := by
  unfold unspend
  cases gs[gi]? <;> simp

/-- **Fork `place_deferred`'s victim** (`planner.rs:1672-1683`): among the slots inside what is
left of the instance's window that a group holds and that are long enough for it, the one with
the lowest energy, latest first. -/
def PlanReq.victimSlot (r : PlanReq) (a : Assign) (lo hi durSec : Nat) : Option Nat :=
  (leastBy victimLt
    ((r.energisedSlots.zipIdx.filter (fun x =>
        (a.slotOf[x.2]?).join.isSome && decide (lo ≤ x.1.2.start) &&
          decide (x.1.2.stop ≤ hi) && decide (durSec ≤ x.1.2.stop - x.1.2.start))).map
      (fun x => (x.1.1.val, x.2)))).map Prod.snd

/-- What the victim satisfies: it is an energised slot of this day, a group holds it, and it is
inside the window and long enough. -/
theorem PlanReq.victimSlot_spec {r : PlanReq} {a : Assign} {lo hi durSec vi : Nat}
    (h : r.victimSlot a lo hi durSec = some vi) :
    ∃ e s, r.energisedSlots[vi]? = some (e, s) ∧ (a.slotOf[vi]?).join.isSome = true ∧
      lo ≤ s.start ∧ s.stop ≤ hi ∧ durSec ≤ s.stop - s.start := by
  unfold PlanReq.victimSlot at h
  cases hl : leastBy victimLt
      ((r.energisedSlots.zipIdx.filter (fun x =>
          (a.slotOf[x.2]?).join.isSome && decide (lo ≤ x.1.2.start) &&
            decide (x.1.2.stop ≤ hi) && decide (durSec ≤ x.1.2.stop - x.1.2.start))).map
        (fun x => (x.1.1.val, x.2))) with
  | none => rw [hl] at h; exact absurd h (by simp)
  | some b =>
    rw [hl] at h
    simp only [Option.map_some, Option.some.injEq] at h
    obtain ⟨hmem, -⟩ := leastBy_spec victimLt_strictTotal _ b hl
    simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hmem
    obtain ⟨x, ⟨hx, ⟨⟨⟨hass, h1⟩, h2⟩, h3⟩⟩, hb⟩ := hmem
    have hidx : r.energisedSlots[x.2]? = some x.1 := List.mem_zipIdx_iff_getElem?.mp hx
    have hvi : x.2 = vi := by rw [← h, ← hb]
    subst hvi
    exact ⟨x.1.1, x.1.2, hidx, hass, h1, h2, h3⟩

/-! ### The loop body, and the walk -/

/-- **Fork `place_deferred`'s re-placement** (`planner.rs:1693-1704`): the group that lost its
slot is offered the slots after it, and the **first** one that takes a group ends the walk.

It is `PlanReq.assignStep` — §8.2 step 5's own loop body — stopped at its first success, and
not a second picker: the fork calls the same `self.pick` here that step 5 calls, with the same
budget guard and the same slot-taken guard, and **this** is the caller that makes that guard
reachable (README gap 876). -/
def PlanReq.rePlaceWalk (r : PlanReq) (budget : Nat) :
    Assign → List ((Fin 6 × Look.Slot) × Nat) → Assign
  | a, [] => a
  | a, x :: rest =>
    let a' := r.assignStep r.todaySlots r.todayBreaks budget a x
    if a'.used = a.used then r.rePlaceWalk budget a' rest else a'

/-- The position step 6 gives: the instance's own minutes from `t`, marked `deferred` because
it is step 6 and not step 2 that placed it (fork `routines[ri].deferred = true`). -/
def placeAt (q : Placed) (t : Nat) : Placed :=
  { q with placedAt := some (t, t + 60 * q.inst.durMin), deferred := true }

/-- **Fork `place_deferred`'s displacement** (`planner.rs:1684-1704`): the slot goes back to
being free, the group that held it gets its minutes back, the day gives a block back, the
instance takes the slot's start, and the displaced group is offered the slots after it. -/
def PlanReq.displaceInto (r : PlanReq) (budget : Nat) (a : Assign) (q : Placed) (vi : Nat)
    (s : Look.Slot) : Placed × Assign :=
  (placeAt q s.start,
   r.rePlaceWalk budget
     ⟨a.slotOf.set vi Option.none,
      (match (a.slotOf[vi]?).join with
       | none => a.groups
       | some gi => unspend gi s.minutes a.groups),
      a.used - 1⟩
     (r.energisedSlots.zipIdx.drop (vi + 1)))

/-- **Fork `place_deferred`'s loop body** (`planner.rs:1633-1705`), for one instance.

The five outcomes are the fork's five, in the fork's order: an instance step 2 already placed
is passed over; one whose remaining span has closed is passed over (§5.3's expiry, not a
failure); otherwise the lowest-energy free position inside the window that is not in the
evening; failing that, and only when the instance is **mandatory**, the same search with the
evening opened; and failing that, the lowest-energy assigned slot inside the window, taken
from the group that held it. -/
def PlanReq.deferOne (r : PlanReq) (budget : Nat) (qs : List Placed) (a : Assign) (q : Placed) :
    Placed × Assign :=
  if q.placedAt.isSome then (q, a)
  else if q.span.2 ≤ max q.span.1 r.now.sec then (q, a)
  else
    match r.lowestFree (r.occupiedNow qs a ++ r.keptBreaksToday ++ [r.night])
            (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin) with
    | some t => (placeAt q t, a)
    | none =>
      if q.inst.mandatory = false then (q, a)
      else
        match r.lowestFree (r.occupiedNow qs a ++ r.keptBreaksToday)
                (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin) with
        | some t => (placeAt q t, a)
        | none =>
          match r.victimSlot a (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin) with
          | none => (q, a)
          | some vi =>
            -- structurally unreachable: `victimSlot`'s candidates come from `zipIdx`
            match r.energisedSlots[vi]? with
            | none => (q, a)
            | some es => r.displaceInto budget a q vi es.2

/-- **Fork `place_deferred`'s loop** (`planner.rs:1633`), over the instances step 2 left, with
the ones already visited in front: `occupied_now` reads every instance's *current* position, so
the walk carries the whole list and not only what is left of it. -/
def PlanReq.deferWalk (r : PlanReq) (budget : Nat) :
    List Placed → Assign → List Placed → List Placed × Assign
  | pre, a, [] => (pre.reverse, a)
  | pre, a, q :: post =>
    let e := r.deferOne budget (pre.reverse ++ q :: post) a q
    r.deferWalk budget (e.1 :: pre) e.2 post

/-- **§8.2 step 6, run.** -/
def PlanReq.deferFold (r : PlanReq) : List Placed × Assign :=
  r.deferWalk (remainingBudget r) [] r.assignFold r.placedRoutines

/-- The day's routine instances after step 6 — the list fork `emit_segments` is handed. -/
def PlanReq.finalRoutines (r : PlanReq) : List Placed := r.deferFold.1

/-- The assignment after step 6, with any displacement and its re-placement in it. -/
def PlanReq.finalAssign (r : PlanReq) : Assign := r.deferFold.2

/-- **Fork `run()`'s un-placed note** (`planner.rs:1046-1060`): an instance with no position and
a window still open is named, because *"a day that quietly loses lunch is a day no monitor can
see"*.  An instance whose window has **closed** is §5.3's expiry and is not reported — the
fork's `if r.span.1 <= from { continue }`, the same guard `deferOne` takes. -/
def PlanReq.noPositionNotes (r : PlanReq) : List Note :=
  r.finalRoutines.filterMap (fun q =>
    if q.placedAt.isSome then none
    else if q.span.2 ≤ max q.span.1 r.now.sec then none
    else some (Note.noPosition q.inst.id q.inst.durMin (max q.span.1 r.now.sec) q.span.2))

/-! ### What step 6 guarantees

Every law below is about one of two things: what the loop may do to an **instance** (it fills a
position step 2 left empty, inside that instance's own window, and never moves one step 2
placed), and what it may do to the **assignment** (it frees at most the one slot it displaces,
re-fills at most one, and keeps both vectors the length step 5 left them).

`PlanReq.deferOne_cases` is the one case split this section takes, in the shape
`PlanReq.assignStep_cases` set at §8.2 step 5: **nothing else below unfolds the loop body.** -/

/-- An energised entry's slot is a slot of this day — `Look.energizeToday` is a `map`. -/
theorem PlanReq.energised_slot_is_a_slot (r : PlanReq) {e : Fin 6} {s : Look.Slot}
    (h : (e, s) ∈ r.energisedSlots) : s ∈ r.todaySlots := by
  unfold PlanReq.energisedSlots Look.energizeToday at h
  simp only [List.mem_map, Prod.mk.injEq] at h
  obtain ⟨t, ht, -, h2⟩ := h
  exact h2 ▸ ht

/-- **The three shapes one step of the loop can have**: it leaves the instance and the
assignment exactly as they were; it gives the instance a position a search found, inside the
instance's own span and — when the instance is not mandatory — outside the evening, and leaves
the assignment alone; or it displaces an assigned slot into the instance.

This lemma does the unfolding once and carries out what the searches guarantee, so that
**nothing below unfolds `PlanReq.deferOne` again** (the shape `PlanReq.assignStep_cases` set at
§8.2 step 5). -/
theorem PlanReq.deferOne_cases (r : PlanReq) (budget : Nat) (qs : List Placed) (a : Assign)
    (q : Placed) :
    r.deferOne budget qs a q = (q, a) ∨
      (∃ t, q.placedAt = none ∧ max q.span.1 r.now.sec ≤ t ∧
        t + 60 * q.inst.durMin ≤ q.span.2 ∧
        (q.inst.mandatory = false → ∀ u, t ≤ u → u < t + 60 * q.inst.durMin →
          ¬ (r.night.1 ≤ u ∧ u < r.night.2)) ∧
        r.deferOne budget qs a q = (placeAt q t, a)) ∨
      (∃ vi s, q.placedAt = none ∧ q.inst.mandatory = true ∧
        max q.span.1 r.now.sec ≤ s.start ∧ s.start + 60 * q.inst.durMin ≤ q.span.2 ∧
        r.deferOne budget qs a q = r.displaceInto budget a q vi s) := by
  unfold PlanReq.deferOne
  by_cases hp : q.placedAt.isSome = true
  · exact Or.inl (by rw [if_pos hp])
  have hnone : q.placedAt = none := by
    cases hq : q.placedAt with
    | none => rfl
    | some _ => rw [hq] at hp; exact absurd rfl hp
  rw [if_neg hp]
  by_cases hs : q.span.2 ≤ max q.span.1 r.now.sec
  · exact Or.inl (by rw [if_pos hs])
  rw [if_neg hs]
  cases ht1 : r.lowestFree (r.occupiedNow qs a ++ r.keptBreaksToday ++ [r.night])
      (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin) with
  | some t =>
    obtain ⟨g1, g2, gfree⟩ := PlanReq.lowestFree_inside ht1
    refine Or.inr (Or.inl ⟨t, hnone, g1, g2, fun _ u hu1 hu2 hnight => ?_, by rfl⟩)
    have hc := gfree u hu1 hu2
    rw [Look.covered_eq_true.2 ⟨r.night, by simp, hnight.1, hnight.2⟩] at hc
    exact absurd hc (by simp)
  | none =>
    by_cases hm : q.inst.mandatory = false
    · exact Or.inl (by rw [if_pos hm])
    have hmt : q.inst.mandatory = true := by
      cases hq : q.inst.mandatory with
      | false => exact absurd hq hm
      | true => rfl
    rw [if_neg hm]
    cases ht2 : r.lowestFree (r.occupiedNow qs a ++ r.keptBreaksToday)
        (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin) with
    | some t =>
      obtain ⟨g1, g2, -⟩ := PlanReq.lowestFree_inside ht2
      exact Or.inr (Or.inl
        ⟨t, hnone, g1, g2, fun hf => absurd (hmt.symm.trans hf) (by simp), by rfl⟩)
    | none =>
      cases hv : r.victimSlot a (max q.span.1 r.now.sec) q.span.2 (60 * q.inst.durMin) with
      | none => exact Or.inl (by rfl)
      | some vi =>
        -- iota-reduce the outer match so the inner discriminant names this `vi`
        dsimp only
        cases he : r.energisedSlots[vi]? with
        | none => exact Or.inl (by rfl)
        | some es =>
          obtain ⟨ee, ss⟩ := es
          obtain ⟨e, s, hslot, -, h1, h2, h3⟩ := PlanReq.victimSlot_spec hv
          have hpair : (ee, ss) = (e, s) := by rw [he] at hslot; exact Option.some.inj hslot
          have hss : ss = s := congrArg Prod.snd hpair
          subst hss
          have hlt := (r.a_slot_is_inside_the_window ss
            (r.energised_slot_is_a_slot (List.mem_of_getElem? he))).2.1
          exact Or.inr (Or.inr ⟨vi, ss, hnone, hmt, h1, by omega, by rfl⟩)

/-- **Step 6 never moves a routine step 2 placed** — the fork's first `continue`
(`planner.rs:1634`), and the sentence that makes every step-2 law survive this step. -/
theorem PlanReq.deferOne_keeps_a_placed_routine (r : PlanReq) (budget : Nat) (qs : List Placed)
    (a : Assign) (q : Placed) (h : q.placedAt.isSome = true) :
    r.deferOne budget qs a q = (q, a) := by
  unfold PlanReq.deferOne; rw [if_pos h]

/-- **README gap 285's family, as a theorem**: an occurrence whose remaining span has closed is
passed over, not squeezed in — the fork's `if span_to <= from { continue }`.  §5.3's expiry
owns that instance, and a placement rule that quietly re-admitted one would be putting a
routine outside the window its own line declares. -/
theorem PlanReq.deferOne_places_nothing_in_a_closed_window (r : PlanReq) (budget : Nat)
    (qs : List Placed) (a : Assign) (q : Placed) (h : q.span.2 ≤ max q.span.1 r.now.sec) :
    r.deferOne budget qs a q = (q, a) := by
  unfold PlanReq.deferOne
  by_cases hp : q.placedAt.isSome = true
  · rw [if_pos hp]
  · rw [if_neg hp, if_pos h]

/-- A position `placeAt` gives satisfies `PlacedOk` as soon as it is inside the span. -/
theorem placeAt_PlacedOk (r : PlanReq) (q : Placed) (t : Nat)
    (h1 : max q.span.1 r.now.sec ≤ t) (h2 : t + 60 * q.inst.durMin ≤ q.span.2) :
    PlacedOk r (placeAt q t) := by
  intro x y hxy
  simp only [placeAt, Option.some.injEq, Prod.mk.injEq] at hxy
  obtain ⟨rfl, rfl⟩ := hxy
  exact ⟨h1, h2, rfl⟩

/-- **One step keeps `PlacedOk`** — every position step 6 gives is inside the instance's own
span, at or after `now`, and exactly the minutes it asked for.  The displacement is the
interesting case: the slot it takes lies inside the window by `PlanReq.victimSlot_spec`'s
filter, and is long enough for the instance because the cut never makes an empty slot
(`PlanReq.a_slot_is_inside_the_window`). -/
theorem PlanReq.deferOne_keeps_PlacedOk (r : PlanReq) (budget : Nat) (qs : List Placed)
    (a : Assign) (q : Placed) (h : PlacedOk r q) : PlacedOk r (r.deferOne budget qs a q).1 := by
  rcases r.deferOne_cases budget qs a q with heq | ⟨t, -, g1, g2, -, heq⟩ |
    ⟨vi, s, -, -, g1, g2, heq⟩ <;> rw [heq]
  · exact h
  · exact placeAt_PlacedOk r q t g1 g2
  · exact placeAt_PlacedOk r q s.start g1 g2

/-- **Nothing a light instance takes is in the evening** — design §2's choice 6: only a
mandatory instance may reach into the wind-down, because only the mandatory branch searches
with `night()` taken out of the occupied list, and the displacement is behind that same
branch. -/
theorem PlanReq.a_light_deferred_instance_stays_out_of_the_evening (r : PlanReq) (budget : Nat)
    (qs : List Placed) (a : Assign) (q : Placed) (hq : q.placedAt = none)
    (hm : q.inst.mandatory = false) (x y : Nat)
    (h : (r.deferOne budget qs a q).1.placedAt = some (x, y)) (u : Nat)
    (h1 : x ≤ u) (h2 : u < y) : ¬ (r.night.1 ≤ u ∧ u < r.night.2) := by
  rcases r.deferOne_cases budget qs a q with heq | ⟨t, -, -, -, hev, heq⟩ |
    ⟨-, -, -, hmt, -, -, -⟩
  · rw [heq] at h; simp only at h; rw [hq] at h; exact absurd h (by simp)
  · rw [heq] at h
    simp only [placeAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hev hm u h1 h2
  · rw [hmt] at hm; exact absurd hm (by simp)

/-! #### The assignment: the lengths and the budget -/

theorem PlanReq.rePlaceWalk_lengths (r : PlanReq) (budget : Nat) :
    ∀ (a : Assign) (l : List ((Fin 6 × Look.Slot) × Nat)),
      (r.rePlaceWalk budget a l).slotOf.length = a.slotOf.length ∧
        (r.rePlaceWalk budget a l).groups.length = a.groups.length
  | _, [] => ⟨rfl, rfl⟩
  | a, x :: rest => by
    unfold PlanReq.rePlaceWalk
    obtain ⟨e1, e2⟩ := r.assignStep_lengths r.todaySlots r.todayBreaks budget a x
    simp only
    split
    · obtain ⟨f1, f2⟩ := PlanReq.rePlaceWalk_lengths r budget
        (r.assignStep r.todaySlots r.todayBreaks budget a x) rest
      exact ⟨f1.trans e1, f2.trans e2⟩
    · exact ⟨e1, e2⟩

theorem PlanReq.rePlaceWalk_used (r : PlanReq) (budget : Nat) :
    ∀ (a : Assign) (l : List ((Fin 6 × Look.Slot) × Nat)), a.used ≤ max r.activeSeed budget →
      (r.rePlaceWalk budget a l).used ≤ max r.activeSeed budget
  | _, [], h => h
  | a, x :: rest, h => by
    unfold PlanReq.rePlaceWalk
    have hstep := r.assignStep_used r.todaySlots r.todayBreaks budget a x h
    simp only
    split
    · exact PlanReq.rePlaceWalk_used r budget _ rest hstep
    · exact hstep

theorem PlanReq.displaceInto_lengths (r : PlanReq) (budget : Nat) (a : Assign) (q : Placed)
    (vi : Nat) (s : Look.Slot) :
    (r.displaceInto budget a q vi s).2.slotOf.length = a.slotOf.length ∧
      (r.displaceInto budget a q vi s).2.groups.length = a.groups.length := by
  unfold PlanReq.displaceInto
  obtain ⟨h1, h2⟩ := PlanReq.rePlaceWalk_lengths r budget
    ⟨a.slotOf.set vi Option.none,
     (match (a.slotOf[vi]?).join with
      | none => a.groups
      | some gi => unspend gi s.minutes a.groups), a.used - 1⟩
    (r.energisedSlots.zipIdx.drop (vi + 1))
  refine ⟨h1.trans (by simp), h2.trans ?_⟩
  show (match (a.slotOf[vi]?).join with
        | none => a.groups
        | some gi => unspend gi s.minutes a.groups).length = a.groups.length
  cases (a.slotOf[vi]?).join with
  | none => rfl
  | some gi => exact unspend_length _ _ _

theorem PlanReq.displaceInto_used (r : PlanReq) (budget : Nat) (a : Assign) (q : Placed)
    (vi : Nat) (s : Look.Slot) (h : a.used ≤ max r.activeSeed budget) :
    (r.displaceInto budget a q vi s).2.used ≤ max r.activeSeed budget := by
  unfold PlanReq.displaceInto
  exact PlanReq.rePlaceWalk_used r budget _ _ (by simp only; omega)

theorem PlanReq.deferOne_lengths (r : PlanReq) (budget : Nat) (qs : List Placed) (a : Assign)
    (q : Placed) :
    (r.deferOne budget qs a q).2.slotOf.length = a.slotOf.length ∧
      (r.deferOne budget qs a q).2.groups.length = a.groups.length := by
  rcases r.deferOne_cases budget qs a q with heq | ⟨t, -, -, -, -, heq⟩ |
    ⟨vi, s, -, -, -, -, heq⟩ <;> rw [heq]
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact r.displaceInto_lengths budget a q vi s

theorem PlanReq.deferOne_used (r : PlanReq) (budget : Nat) (qs : List Placed) (a : Assign)
    (q : Placed) (h : a.used ≤ max r.activeSeed budget) :
    (r.deferOne budget qs a q).2.used ≤ max r.activeSeed budget := by
  rcases r.deferOne_cases budget qs a q with heq | ⟨t, -, -, -, -, heq⟩ |
    ⟨vi, s, -, -, -, -, heq⟩ <;> rw [heq]
  · exact h
  · exact h
  · exact r.displaceInto_used budget a q vi s h

/-! #### The walk -/

theorem PlanReq.deferWalk_keeps_PlacedOk (r : PlanReq) (budget : Nat) :
    ∀ (post : List Placed) (pre : List Placed) (a : Assign),
      (∀ z ∈ pre, PlacedOk r z) → (∀ z ∈ post, PlacedOk r z) →
      ∀ z ∈ (r.deferWalk budget pre a post).1, PlacedOk r z
  | [], pre, a, hpre, _ => by
    intro z hz
    exact hpre z (List.mem_reverse.1 hz)
  | q :: post, pre, a, hpre, hpost => by
    unfold PlanReq.deferWalk
    refine PlanReq.deferWalk_keeps_PlacedOk r budget post _ _ (fun z hz => ?_)
      (fun z hz => hpost z (List.mem_cons_of_mem _ hz))
    rcases List.mem_cons.1 hz with rfl | hz
    · exact r.deferOne_keeps_PlacedOk budget _ a q (hpost q (List.mem_cons_self ..))
    · exact hpre z hz

theorem PlanReq.deferWalk_lengths (r : PlanReq) (budget : Nat) :
    ∀ (post : List Placed) (pre : List Placed) (a : Assign),
      (r.deferWalk budget pre a post).2.slotOf.length = a.slotOf.length ∧
        (r.deferWalk budget pre a post).2.groups.length = a.groups.length
  | [], _, _ => ⟨rfl, rfl⟩
  | q :: post, pre, a => by
    unfold PlanReq.deferWalk
    obtain ⟨e1, e2⟩ := r.deferOne_lengths budget (pre.reverse ++ q :: post) a q
    obtain ⟨f1, f2⟩ := PlanReq.deferWalk_lengths r budget post
      ((r.deferOne budget (pre.reverse ++ q :: post) a q).1 :: pre)
      (r.deferOne budget (pre.reverse ++ q :: post) a q).2
    exact ⟨f1.trans e1, f2.trans e2⟩

theorem PlanReq.deferWalk_used (r : PlanReq) (budget : Nat) :
    ∀ (post : List Placed) (pre : List Placed) (a : Assign),
      a.used ≤ max r.activeSeed budget →
      (r.deferWalk budget pre a post).2.used ≤ max r.activeSeed budget
  | [], _, _, h => h
  | q :: post, pre, a, h => by
    unfold PlanReq.deferWalk
    exact PlanReq.deferWalk_used r budget post _ _
      (r.deferOne_used budget (pre.reverse ++ q :: post) a q h)

/-! #### What the day gets -/

/-- **§8.2 step 6's own law: a routine step 6 places is inside its window.**  The same sentence
step 2's `a_placed_routine_is_inside_its_window` makes true of the earliest-feasible rule, now
of the lowest-energy rule and of the displacement — which is what keeps `Negative.lean`'s "a
routine placed outside its window" a cheat that does not close once a second rule can place
one. -/
theorem a_deferred_routine_is_inside_its_window (r : PlanReq) (p : Placed)
    (hp : p ∈ r.finalRoutines) (a b : Nat) (hab : p.placedAt = some (a, b)) :
    max p.span.1 r.now.sec ≤ a ∧ b ≤ p.span.2 ∧ b = a + 60 * p.inst.durMin :=
  PlanReq.deferWalk_keeps_PlacedOk r _ _ [] _ (by simp)
    (fun z hz x y hxy => a_placed_routine_is_inside_its_window r z hz x y hxy) p hp a b hab

/-- **Step 6 keeps the cursor's two vectors the length step 5 left them** — one entry per slot
and one group per group, so every law of §8.2 step 5 that is about those lengths survives the
displacement and the re-placement. -/
theorem the_deferred_pass_keeps_the_assignments_shape (r : PlanReq) :
    r.finalAssign.slotOf.length = r.assignFold.slotOf.length ∧
      r.finalAssign.groups.length = r.assignFold.groups.length :=
  PlanReq.deferWalk_lengths r _ _ [] _

/-- **And it never spends more of the budget than step 5 could** — the displacement gives a
block back and the re-placement takes at most that one back, under `PlanReq.assignStep`'s own
guard. -/
theorem the_deferred_pass_stays_inside_the_budget (r : PlanReq) :
    r.finalAssign.used ≤ max r.activeSeed (remainingBudget r) :=
  PlanReq.deferWalk_used r _ _ [] _ (PlanReq.assignFold_used r)

/-! ############################################################################
## §8.2 step 7 — rest and optionals

Spec §8.2 step 7: *"leftover slots after the budget → Rest; optionals (`p = 5`) fill Rest and
the evening before wind-down, within `max:`."*  Fork `emit_segments` does both, in that order,
at `planner.rs:1900-1957`, after step 6 has finished with the routines and the assignment.

**The rest rule and the cut already have a relationship, and this section does not build a
second one.**  `Look.cutSlots` takes the placed routines as `rests` (AGENTS §8.4, design §1.2)
— which is `PlanReq.restsToday`, step 3's argument — so a slot never overlaps a routine **step
2** placed, and the break counter resets after one.  What step 7 adds is the routines **step
6** placed, which the cut could not know about because step 6 runs after it, and the optionals
step 7 has just placed.  `PlanReq.restTaken` is exactly that difference; `Look.freeIntervals`,
L3's own walk, carves each unfilled slot around it.  Nothing here cuts, energises, or computes
a free stretch a second time.

**And the breaks are step 6's list, widened, not a new rule.**  P6 landed `PlanReq.keptBreaks`
— a break belongs to the day only when work touches it — and `PlanReq.keptBreaksToday` at the
assignment step 5 ended with.  Fork `emit_segments` takes the *same function* at the assignment
**step 6** left and drops the breaks a placed routine has taken over; `PlanReq.emitKeptBreaks`
is that one extra filter over `keptBreaks`, and the filter's test is `Planner.overlapsAny`,
step 2's own.  There is no second break rule and no second overlap test.

**What step 7 does NOT emit, and why.**  The Block and Batch rows of §8.2 step 5 are still
owed (README gap **803** item 4): they are the switch-shaped change (D19) that makes four
`PlanCheck` emptiness theorems false on one commit and takes `PlanCheck.dayPlan_ok_core_given_the_budget`'s
`hblk` — *"every Block row of this day is the reservation"* — with them, which is **G1**'s
lift.  Rest, Optional and Break rows are none of those kinds, so they land without touching it.
The **Break rows** themselves were gap **551**'s until W-37: their spans are read here (the
optionals flow around them), and since W-37 they are drawn as well, `PlanReq.keptBreakRows`
below, composed into `dayRows` between the Block rows they sit beside and the optionals —
fork `emit_segments`' own order (README gap 551, closed at W-37 track R).

### D9-21, the recursion rule

`optionalFold` is a `foldl` over `optionalCands`, which the wire caps at `maxCands`
(`PlanReq.cands` is `Capped`); `foldl` is already the compiled form, as `assignFold`'s is.
`restRows` is a `List.flatMap` over the slot list and `Look.freeIntervals` inside it, both
core's.  Nothing here recurses by hand.
############################################################################ -/

/-! ### The breaks the day keeps -/

/-- **Fork `emit_segments`' own `kept_breaks`** (`planner.rs:1876-1885`): §8.2 step 6's list at
the assignment step 6 **left** (`PlanReq.finalAssign`, not `assignFold` — the fork recomputes
it here, and gap **906** is the record of the one it did not), less every break a routine has
taken over.  `Planner.overlapsAny` is the test, called and not copied. -/
def PlanReq.emitKeptBreaks (r : PlanReq) : List (Nat × Nat) :=
  (r.keptBreaks r.finalAssign).filter
    (fun b => !overlapsAny b.1 b.2 (r.finalRoutines.filterMap (·.placedAt)))

/-- **Every break the day keeps is one the cut made and work touches** — `emitKeptBreaks`
adds nothing to `keptBreaks`, it only removes. -/
theorem PlanReq.emitKeptBreaks_is_a_kept_break (r : PlanReq) (b : Nat × Nat)
    (h : b ∈ r.emitKeptBreaks) : b ∈ r.keptBreaks r.finalAssign :=
  (List.mem_filter.1 h).1

/-- **And no break the day keeps is under a routine** — the second half of the fork's filter,
as a disjointness rather than as a `Bool`. -/
theorem PlanReq.an_emitted_break_is_clear_of_the_routines (r : PlanReq) (b : Nat × Nat)
    (hb : b ∈ r.emitKeptBreaks) (p : Placed) (hp : p ∈ r.finalRoutines) (x y : Nat)
    (hxy : p.placedAt = some (x, y)) : b.2 ≤ x ∨ y ≤ b.1 := by
  have h2 : overlapsAny b.1 b.2 (r.finalRoutines.filterMap (·.placedAt)) = false := by
    have := (List.mem_filter.1 hb).2
    simpa using this
  have hmem : (x, y) ∈ r.finalRoutines.filterMap (·.placedAt) :=
    List.mem_filterMap.2 ⟨p, hp, hxy⟩
  have h3 : ¬ (b.1 < y ∧ x < b.2) := by
    have := (List.any_eq_false.1 h2) (x, y) hmem
    simpa using this
  omega

/-- **The Break rows the day keeps** (W-37 track R, README gap **551** closed): one per break
`emitKeptBreaks` names — the cut's, touched by work, clear of every routine — drawn as fork
`emit_segments` draws it (`planner.rs:1886-1898`): `SegKind::Break`, no slot energy, no item, no
instance, no marks, and `planned_min: Some(b.minutes())`, fork `Break::minutes` = `(end −
start).num_minutes()`, which is `Look.spanMinutes`, the kernel's one such arithmetic (AGENTS
§5.3).  Until W-37 the optionals flowed around these breaks and no row said they were there. -/
def PlanReq.keptBreakRows (r : PlanReq) : List Seg :=
  r.emitKeptBreaks.map (fun b =>
    { start := b.1, stop := b.2, kind := .brk, energy := none, item := none, inst := none,
      flags := SegFlags.none, planned := some (Look.spanMinutes b.1 b.2), mult := none,
      note := none })

/-- **A kept Break row is exactly the fork's row for a break the day keeps** — every field
`emit_segments` writes, read off the one map that builds it (the shape of `mem_openBlockRows`). -/
theorem PlanReq.mem_keptBreakRows (r : PlanReq) (t : Seg) (h : t ∈ r.keptBreakRows) :
    ∃ b ∈ r.emitKeptBreaks, t.start = b.1 ∧ t.stop = b.2 ∧ t.kind = SegKind.brk ∧
      t.energy = none ∧ t.item = none ∧ t.inst = none ∧ t.flags = SegFlags.none ∧
      t.planned = some (Look.spanMinutes b.1 b.2) ∧ t.mult = none ∧ t.note = none := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 h
  exact ⟨b, hb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Every kept Break row is a Break** — one kind, so none of them is work, a Block, a Wall or
the wind-down (the corollaries below, in `optionalRows_are_not_work`'s shape). -/
theorem PlanReq.keptBreakRows_kinds (r : PlanReq) (t : Seg) (h : t ∈ r.keptBreakRows) :
    t.kind = SegKind.brk :=
  let ⟨_, _, _, _, hk, _⟩ := r.mem_keptBreakRows t h
  hk

theorem PlanReq.keptBreakRows_are_not_work (r : PlanReq) (t : Seg) (h : t ∈ r.keptBreakRows) :
    t.kind.isWork = false := by rw [r.keptBreakRows_kinds t h]; rfl

theorem PlanReq.keptBreakRows_are_not_blocks (r : PlanReq) (t : Seg) (h : t ∈ r.keptBreakRows) :
    t.kind ≠ SegKind.block := by rw [r.keptBreakRows_kinds t h]; intro hc; cases hc

theorem PlanReq.keptBreakRows_are_not_walls (r : PlanReq) (t : Seg) (h : t ∈ r.keptBreakRows) :
    t.kind ≠ SegKind.wall := by rw [r.keptBreakRows_kinds t h]; intro hc; cases hc

theorem PlanReq.keptBreakRows_are_not_wind_down (r : PlanReq) (t : Seg)
    (h : t ∈ r.keptBreakRows) : t.kind ≠ SegKind.windDown := by
  rw [r.keptBreakRows_kinds t h]; intro hc; cases hc

/-- **A break the day keeps is one of today's cut** — `emitKeptBreaks` filters `keptBreaks`, which
filters `todayBreaks`, and neither adds a break. -/
theorem PlanReq.a_kept_break_is_a_break_of_the_cut (r : PlanReq) (b : Nat × Nat)
    (h : b ∈ r.emitKeptBreaks) : b ∈ r.todayBreaks :=
  (List.mem_filter.1 (r.emitKeptBreaks_is_a_kept_break b h)).1

/-- **A break the day keeps starts at or after `now`, is not empty, and ends inside the window**
— L3's `cutSlots_breaks_inside_the_window` at step 3's `from`, which is `now` whenever the cut
holds anything at all (`PlanReq.cutFrom`: a window already closed at `now` cuts nothing). -/
theorem PlanReq.a_kept_break_is_after_now (r : PlanReq) (b : Nat × Nat) (h : b ∈ r.emitKeptBreaks) :
    r.now.sec ≤ b.1 ∧ b.1 < b.2 ∧ b.2 ≤ r.window.2 := by
  have hc := r.a_kept_break_is_a_break_of_the_cut b h
  unfold PlanReq.todayBreaks PlanReq.todayCut at hc
  obtain ⟨h1, h2, h3⟩ := Look.cutSlots_breaks_inside_the_window _ _ _ _ _ _ hc
  unfold PlanReq.cutFrom at h1
  exact ⟨by omega, h2, h3⟩

/-- **No unit of a kept break is blocked** — L3's `cutSlots_breaks_avoid_the_walls` over the list
step 3 handed the cut, which is the walls, the running interruption and break, §8.2 choice 5b's
reservation, every routine step 2 placed, and the night. -/
theorem PlanReq.a_kept_break_touches_nothing_blocked (r : PlanReq) (b : Nat × Nat)
    (hb : b ∈ r.emitKeptBreaks) {w : Nat × Nat} (hw : w ∈ r.slotBlocked ++ r.restsToday) {t : Nat}
    (h1 : b.1 ≤ t) (h2 : t < b.2) : ¬ (w.1 ≤ t ∧ t < w.2) := by
  have hc := r.a_kept_break_is_a_break_of_the_cut b hb
  unfold PlanReq.todayBreaks PlanReq.todayCut at hc
  exact Look.cutSlots_breaks_avoid_the_walls _ _ _ _ _ _ hc hw h1 h2

/-- **The reservation clears every break the day keeps** — its span is on the list the cut flows
around (the argument `PlanReq.no_slot_touches_the_running_block` takes for a slot), so no unit of
a kept break is inside it. -/
theorem PlanReq.a_kept_break_clears_the_reservation (r : PlanReq) (q : ActiveRes)
    (hq : r.activeRun = some q) (b : Nat × Nat) (hb : b ∈ r.emitKeptBreaks) :
    q.stop ≤ b.1 ∨ b.2 ≤ q.start := by
  have hmem : (q.start, q.stop) ∈ r.slotBlocked ++ r.restsToday := by
    refine List.mem_append_left _ ?_
    unfold PlanReq.slotBlocked
    refine List.mem_cons_of_mem _ ?_
    refine foldl_placeStep_grows_the_blocked r r.blockedBeforeRoutines _ _ (fun w hw => hw) _ ?_
    unfold PlanReq.blockedBeforeRoutines PlanReq.reservedSpan
    rw [hq]; simp
  have hbne := (r.a_kept_break_is_after_now b hb).2.1
  obtain ⟨-, -, -, -, hs0, hlt, -⟩ := r.activeRun_spec q hq
  rcases Nat.lt_or_ge b.1 q.stop with h1 | h1
  · rcases Nat.lt_or_ge q.start b.2 with h2 | h2
    · exact absurd (⟨Nat.le_max_right _ _, by omega⟩ : q.start ≤ max b.1 q.start ∧ max b.1 q.start < q.stop)
        (r.a_kept_break_touches_nothing_blocked b hb hmem (Nat.le_max_left _ _) (by omega))
    · exact Or.inr h2
  · exact Or.inl h1

/-- **No slot overlaps a break the day keeps** — `PlanReq.no_slot_overlaps_a_break`, at a kept
break: the Block and Batch rows step 5 fills sit *beside* the breaks the day draws. -/
theorem PlanReq.a_slot_clears_a_kept_break (r : PlanReq) (s : Look.Slot) (hs : s ∈ r.todaySlots)
    (b : Nat × Nat) (hb : b ∈ r.emitKeptBreaks) : s.stop ≤ b.1 ∨ b.2 ≤ s.start :=
  r.no_slot_overlaps_a_break s hs b (r.a_kept_break_is_a_break_of_the_cut b hb)

/-! ### The optionals -/

/-- **Fork `emit_segments`' `occupied`** (`planner.rs:1901-1911`): everything step 6 had to
flow around, at step 6's own answer, and the breaks the day keeps.  `PlanReq.occupiedNow` is
step 6's list and is called here with step 6's output, which is exactly the fork's three
`extend`s. -/
def PlanReq.optionalOccupied (r : PlanReq) : List (Nat × Nat) :=
  r.occupiedNow r.finalRoutines r.finalAssign ++ r.emitKeptBreaks

/-- **Fork's `free`** (`planner.rs:1912-1913`): `free_intervals(now.max(day_start),
wind_down, occupied)`.  The optionals fill the day **before** the wind-down and never the
evening — which is the half of §8.2 step 7 that is not about the budget at all. -/
def PlanReq.optionalFree (r : PlanReq) : List (Nat × Nat) :=
  Look.freeIntervals (max r.now.sec r.dayStart) r.windDownSec r.optionalOccupied

/-- **Fork `c.cap_left_min().map_or(c.remaining_min, |l| c.remaining_min.min(l))`**
(`planner.rs:1915`): what an optional asks the day for, within what is left of its `max:`.
`Seal.minOpt` is the kernel's own `Option Nat` minimum — the function a byte-for-byte copy of
which shipped at P5b and was deleted by W-19's repair (README gap 886). -/
def optionalWant (c : Look.Cand) : Nat :=
  (Seal.minOpt (some c.remaining) c.plan.val.capLeftMin).getD 0

/-- Without a `max:` an optional asks for everything it has left. -/
theorem optionalWant_without_a_cap (c : Look.Cand) (h : c.plan.val.capLeftMin = none) :
    optionalWant c = c.remaining := by
  unfold optionalWant; rw [h]; rfl

/-- **With one, it asks for no more than the cap allows** — §8.2 step 7's "within `max:`". -/
theorem optionalWant_is_within_the_cap (c : Look.Cand) (l : Nat)
    (h : c.plan.val.capLeftMin = some l) : optionalWant c = min c.remaining l := by
  unfold optionalWant; rw [h]; rfl

theorem optionalWant_le_remaining (c : Look.Cand) : optionalWant c ≤ c.remaining := by
  unfold optionalWant Seal.minOpt
  cases h : c.plan.val.capLeftMin with
  | none => simp
  | some l => simp [Nat.min_le_left]

/-- **Fork `cands.iter().filter(|c| c.is_optional && c.eligible())`** (`planner.rs:1914`): the
`optional.md` lines, in **request order**.  §7's ranking is not consulted and cannot be: an
optional never enters a group (fork `build_groups`' own `c.is_optional` guard,
`planner.rs:1281`), so it has no key to be sorted by.  Both facts are the wire's
(`Look.Cand.optional`, `Look.PlanFacts.eligible`); nothing is derived here, which would be
doing D27 early (**D34**). -/
def PlanReq.optionalCands (r : PlanReq) : List Look.Cand :=
  (r.cands.val.map Prod.fst).filter (fun c => c.optional && c.plan.val.eligible)

/-- Every candidate step 7 considers is an optional the wire called eligible. -/
theorem PlanReq.an_optional_candidate_is_optional_and_eligible (r : PlanReq) (c : Look.Cand)
    (h : c ∈ r.optionalCands) : c.optional = true ∧ c.plan.val.eligible = true := by
  have h2 := (List.mem_filter.1 h).2
  simp only [Bool.and_eq_true] at h2
  exact h2

/-- **Fork `free.iter().position(|(a, b)| *b - *a >= dur)` and the shrink after it**
(`planner.rs:1919-1941`): the **first** free stretch wide enough, the position at its start,
and that stretch left shorter — or dropped, when the optional took all of it.

The `findIdx?`-then-`getElem?` shape is §8.2 step 5's own (`PlanReq.assignStep`), and
`pickedGroup_is_the_first_that_fits` — generalised over the element type for this caller — is
the inversion both use. -/
def placeOptional (durSec : Nat) (free : List (Nat × Nat)) : Option (Nat × List (Nat × Nat)) :=
  match free.findIdx? (fun iv => decide (durSec ≤ iv.2 - iv.1)) with
  | Option.none => Option.none
  | some k =>
    match free[k]? with
    | Option.none => Option.none
    | some iv =>
      some (iv.1,
        if iv.1 + durSec < iv.2 then free.set k (iv.1 + durSec, iv.2) else free.eraseIdx k)

/-- **The stretch it took, and that every earlier one was too narrow.**  The second half is
the whole of what "first fit" means, and it is the clause a search that merely found *a*
stretch would not satisfy. -/
theorem placeOptional_spec {d t : Nat} {free free' : List (Nat × Nat)}
    (h : placeOptional d free = some (t, free')) :
    ∃ k iv, free[k]? = some iv ∧ iv.1 = t ∧ d ≤ iv.2 - iv.1 ∧
      (∀ j, j < k → ∀ w, free[j]? = some w → w.2 - w.1 < d) ∧
      free' = (if iv.1 + d < iv.2 then free.set k (iv.1 + d, iv.2) else free.eraseIdx k) := by
  unfold placeOptional at h
  cases hf : free.findIdx? (fun iv => decide (d ≤ iv.2 - iv.1)) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some k =>
    rw [hf] at h
    simp only at h
    cases hg : free[k]? with
    | none => rw [hg] at h; exact absurd h (by simp)
    | some iv =>
      rw [hg] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, hbefore⟩ := pickedGroup_is_the_first_that_fits _ free k hf
      have hwide : d ≤ iv.2 - iv.1 := by
        obtain ⟨w, hw, hpw⟩ := (pickedGroup_is_the_first_that_fits _ free k hf).1
        rw [hg] at hw
        rw [(Option.some.inj hw : iv = w)]
        simpa using hpw
      refine ⟨k, iv, hg, h.1, hwide, fun j hj w hw => ?_, h.2.symm⟩
      have := hbefore j hj w hw
      simpa using this

/-- One placed optional, before it is a row: fork's `Segment` fields at `planner.rs:1926-1937`
without the text, which is `Emit.lean`'s (D30 Q6). -/
structure OptPlaced where
  id    : Id
  start : Nat
  stop  : Nat
  /-- Fork `SegFlags::planned_min` — the minutes it asked for, within its `max:`. -/
  want  : Nat
deriving DecidableEq, Repr

/-- One turn of fork's optional loop (`planner.rs:1914-1942`): an optional with nothing left
to ask for is passed over (`if want == 0 { continue }`), and so is one no free stretch can
hold. -/
def optionalStep (acc : List (Nat × Nat) × List OptPlaced) (c : Look.Cand) :
    List (Nat × Nat) × List OptPlaced :=
  if optionalWant c = 0 then acc
  else
    match placeOptional (60 * optionalWant c) acc.1 with
    | Option.none => acc
    | some (t, free) => (free, ⟨c.id, t, t + 60 * optionalWant c, optionalWant c⟩ :: acc.2)

/-- **§8.2 step 7's optionals**, in request order, each in the earliest free stretch that
could hold it. -/
def PlanReq.optionalFold (r : PlanReq) : List OptPlaced :=
  (r.optionalCands.foldl optionalStep (r.optionalFree, [])).2.reverse

/-- **The invariant the loop carries**: every stretch still on the working list lies inside
the day before the wind-down and is free of everything steps 1–6 occupied.  It is what makes
an optional's position a claim about the *day* and not only about a list.

Stated as a `Prop` in the shape `PlanReq.AssignOk` and `Planner.PlacedOk` set: the fold's law
is that the start satisfies it and each step preserves it. -/
def FreeOk (lo hi : Nat) (occ : List (Nat × Nat)) (free : List (Nat × Nat)) : Prop :=
  ∀ iv ∈ free, lo ≤ iv.1 ∧ iv.1 < iv.2 ∧ iv.2 ≤ hi ∧
    ∀ u, iv.1 ≤ u → u < iv.2 → Look.covered occ u = false

/-- `Look.freeIntervals` answers a list that satisfies it — which is `freeIntervals_spec`'s
two halves at one stretch, and is `freeStretch_gives_a_position` widened from a position to
the whole stretch. -/
theorem freeIntervals_FreeOk (lo hi : Nat) (occ : List (Nat × Nat)) :
    FreeOk lo hi occ (Look.freeIntervals lo hi occ) := by
  intro iv hiv
  obtain ⟨h1, h2, h3⟩ := Look.freeIntervals_inside_the_window hiv
  refine ⟨h1, h2, h3, fun u hu1 hu2 => ?_⟩
  obtain ⟨-, -, hfree⟩ := freeStretch_gives_a_position hiv (Nat.le_refl (iv.2 - iv.1))
  exact hfree u hu1 (by omega)

/-- Shrinking a stretch from the left, or dropping it, keeps the invariant. -/
theorem placeOptional_FreeOk {lo hi d t : Nat} {occ free free' : List (Nat × Nat)}
    (hok : FreeOk lo hi occ free) (h : placeOptional d free = some (t, free')) :
    FreeOk lo hi occ free' := by
  obtain ⟨k, iv, hk, ht, hd, -, hf⟩ := placeOptional_spec h
  subst hf
  intro w hw
  split at hw
  · rcases List.mem_or_eq_of_mem_set hw with hw | rfl
    · exact hok w hw
    · obtain ⟨g1, g2, g3, g4⟩ := hok iv (List.mem_of_getElem? hk)
      exact ⟨by simp only; omega, by simp only; omega, g3,
        fun u hu1 hu2 => g4 u (by simp only at hu1; omega) (by simp only at hu2; omega)⟩
  · exact hok w (List.eraseIdx_subset hw)

/-- **What an optional's position is a claim about**: it starts inside the day and at or after
`now`, it ends at or before the wind-down, it is exactly the minutes it asked for, and every
second of it is free of the walls, the routines, the slots the cursor filled and the breaks
the day keeps.

The proof is one induction over the fold, carrying `FreeOk`; `optionalStep` is unfolded here
and **nowhere else**, which is the shape `PlanReq.assignStep_cases` and
`PlanReq.deferOne_cases` set. -/
theorem optionalFold_ok (lo hi : Nat) (occ : List (Nat × Nat)) :
    ∀ (cs : List Look.Cand) (free : List (Nat × Nat)) (acc : List OptPlaced),
      FreeOk lo hi occ free →
      (∀ o ∈ acc, lo ≤ o.start ∧ o.stop ≤ hi ∧ o.stop = o.start + 60 * o.want ∧
        ∀ u, o.start ≤ u → u < o.stop → Look.covered occ u = false) →
      ∀ o ∈ (cs.foldl optionalStep (free, acc)).2,
        lo ≤ o.start ∧ o.stop ≤ hi ∧ o.stop = o.start + 60 * o.want ∧
          ∀ u, o.start ≤ u → u < o.stop → Look.covered occ u = false
  | [], _, _, _, hacc => hacc
  | c :: cs, free, acc, hfree, hacc => by
    simp only [List.foldl_cons]
    unfold optionalStep
    split
    · exact optionalFold_ok lo hi occ cs free acc hfree hacc
    · rename_i hw
      cases hp : placeOptional (60 * optionalWant c) free with
      | none =>
        simp only [hp]
        exact optionalFold_ok lo hi occ cs free acc hfree hacc
      | some p =>
        obtain ⟨t, free'⟩ := p
        simp only [hp]
        refine optionalFold_ok lo hi occ cs free' _
          (placeOptional_FreeOk hfree hp) (fun o ho => ?_)
        rcases List.mem_cons.1 ho with rfl | ho
        · obtain ⟨k, iv, hk, hti, hd, -, -⟩ := placeOptional_spec hp
          obtain ⟨g1, g2, g3, g4⟩ := hfree iv (List.mem_of_getElem? hk)
          subst hti
          exact ⟨by simp only; omega, by simp only; omega, rfl,
            fun u hu1 hu2 => g4 u (by simp only at hu1; omega) (by simp only at hu2; omega)⟩
        · exact hacc o ho

/-- **§8.2 step 7's own law.**  The sentence above, at the day's own arguments. -/
theorem an_optional_is_placed_in_the_free_day_before_the_wind_down (r : PlanReq) (o : OptPlaced)
    (h : o ∈ r.optionalFold) :
    max r.now.sec r.dayStart ≤ o.start ∧ o.stop ≤ r.windDownSec ∧
      o.stop = o.start + 60 * o.want ∧
      ∀ u, o.start ≤ u → u < o.stop → Look.covered r.optionalOccupied u = false :=
  optionalFold_ok _ _ _ r.optionalCands r.optionalFree []
    (freeIntervals_FreeOk _ _ _) (by simp) o (List.mem_reverse.1 h)

/-- **Its rows.**  No energy: an optional is not on §7's scale and takes no slot's level —
fork `Segment { kind: SegKind::Optional, energy: None, … }` (`planner.rs:1926-1937`).

**`inst` is `none` and that is a gap, not a choice** (README gap **1006**): fork's row carries
`c.instance`, and `Look.Cand` has no instance key on the wire — `RoutineIn` has one and the
candidate record does not.  Deriving it here would be D27 in the kernel (**D34**). -/
def PlanReq.optionalRows (r : PlanReq) : List Seg :=
  r.optionalFold.map (fun o =>
    { start := o.start, stop := o.stop, kind := .optional, energy := none, item := some o.id,
      inst := none, flags := SegFlags.none, planned := some o.want, mult := none,
      note := none })

/-- And the time they took, which the Rest loop flows around (fork's `taken`). -/
def PlanReq.optionalSpans (r : PlanReq) : List (Nat × Nat) :=
  r.optionalFold.map (fun o => (o.start, o.stop))

/-- **An Optional row is an Optional row**, whatever the day holds — the clause every "these
rows cannot reach that set" law below is built on. -/
theorem PlanReq.optionalRows_kinds (r : PlanReq) (s : Seg) (h : s ∈ r.optionalRows) :
    s.kind = SegKind.optional := by
  unfold PlanReq.optionalRows at h
  obtain ⟨o, -, rfl⟩ := List.mem_map.1 h
  rfl

/-! ### Rest -/

/-- **Fork's `taken` at the Rest loop** (`planner.rs:1944`): the optionals just placed, and
the routines **step 6** left placed.  The cut already flowed around the routines step **2**
placed — that is `PlanReq.restsToday`, step 3's own argument — so this is the difference step
6 and step 7 made to it and not a second rest rule. -/
def PlanReq.restTaken (r : PlanReq) : List (Nat × Nat) :=
  r.optionalSpans ++ r.finalRoutines.filterMap (·.placedAt)

/-- **§8.2 step 7's Rest rows** (`planner.rs:1945-1957`): every slot the cursor did not fill,
carved around what step 6 and the optionals took, each piece carrying **the slot's own
energy** — which is what gives `Diagnostics.aCapacityLost` a subject, and is why a Rest row is
the one row of the day besides a Block that has a level at all. -/
def PlanReq.restRows (r : PlanReq) : List Seg :=
  ((r.energisedSlots.zip r.finalAssign.slotOf).filter (fun p => p.2.isNone)).flatMap
    (fun p => (Look.freeIntervals p.1.2.start p.1.2.stop r.restTaken).map (fun iv =>
      { start := iv.1, stop := iv.2, kind := .rest, energy := some p.1.1, item := none,
        inst := none, flags := SegFlags.none, planned := none, mult := none, note := none }))

theorem PlanReq.restRows_kinds (r : PlanReq) (s : Seg) (h : s ∈ r.restRows) :
    s.kind = SegKind.rest := by
  unfold PlanReq.restRows at h
  obtain ⟨p, -, hs⟩ := List.mem_flatMap.1 h
  obtain ⟨iv, -, rfl⟩ := List.mem_map.1 hs
  rfl

/-- **A Rest row is a piece of a slot the cursor left empty, at that slot's level, free of
every optional and of every routine step 6 placed.**  §8.2 step 7's second law, and the one
that says "leftover slots" means the slots and not free time in general: a Rest row cannot
appear where there was no slot, so the evening, the walls and the breaks are not Rest. -/
theorem a_rest_row_is_a_piece_of_an_unfilled_slot (r : PlanReq) (s : Seg)
    (h : s ∈ r.restRows) :
    ∃ (e : Fin 6) (sl : Look.Slot), (e, sl) ∈ r.energisedSlots ∧
      sl.start ≤ s.start ∧ s.start < s.stop ∧ s.stop ≤ sl.stop ∧ s.energy = some e ∧
      ∀ u, s.start ≤ u → u < s.stop → Look.covered r.restTaken u = false := by
  unfold PlanReq.restRows at h
  obtain ⟨p, hp, hs⟩ := List.mem_flatMap.1 h
  obtain ⟨iv, hiv, rfl⟩ := List.mem_map.1 hs
  obtain ⟨g1, g2, g3⟩ := Look.freeIntervals_inside_the_window hiv
  obtain ⟨-, -, hfree⟩ := freeStretch_gives_a_position hiv (Nat.le_refl (iv.2 - iv.1))
  have hfree2 : ∀ u, iv.1 ≤ u → u < iv.2 → Look.covered r.restTaken u = false :=
    fun u hu1 hu2 => hfree u hu1 (by omega)
  refine ⟨p.1.1, p.1.2, ?_, g1, g2, g3, rfl, hfree2⟩
  have hmem := (List.mem_filter.1 hp).1
  have := List.of_mem_zip hmem
  simpa using this.1

/-- **And the slot it is a piece of really is one the cursor left empty** — the `filter`'s own
clause, carried out to the assignment so that a reader does not have to take the `Bool` on
trust. -/
theorem a_rest_row_comes_from_a_slot_no_group_took (r : PlanReq) (p : (Fin 6 × Look.Slot) × Option Nat)
    (h : p ∈ (r.energisedSlots.zip r.finalAssign.slotOf).filter (fun q => q.2.isNone)) :
    p.2 = Option.none := by
  have h2 := (List.mem_filter.1 h).2
  cases hp : p.2 with
  | none => rfl
  | some k => rw [hp] at h2; exact absurd h2 (by simp)

/-! #### Step 7's rows, against every set the day keeps them out of

Ten one-line corollaries of `PlanReq.optionalRows_kinds` and `PlanReq.restRows_kinds`, in the
shape `routineRows_are_not_walls` set at §8.2 step 2: an Optional row and a Rest row are not
work, not a Block, not a Wall, not a Break and not the wind-down, so neither can enter
`assignedOf`, be compared against a wall, answer for a break or be mistaken for the evening.
Every law of the assembled day below takes them through exactly these. -/

theorem PlanReq.optionalRows_are_not_work (r : PlanReq) (t : Seg) (h : t ∈ r.optionalRows) :
    t.kind.isWork = false := by rw [r.optionalRows_kinds t h]; rfl

theorem PlanReq.optionalRows_are_not_blocks (r : PlanReq) (t : Seg) (h : t ∈ r.optionalRows) :
    t.kind ≠ SegKind.block := by rw [r.optionalRows_kinds t h]; intro hc; cases hc

theorem PlanReq.optionalRows_are_not_walls (r : PlanReq) (t : Seg) (h : t ∈ r.optionalRows) :
    t.kind ≠ SegKind.wall := by rw [r.optionalRows_kinds t h]; intro hc; cases hc

theorem PlanReq.optionalRows_are_not_breaks (r : PlanReq) (t : Seg) (h : t ∈ r.optionalRows) :
    t.kind ≠ SegKind.brk := by rw [r.optionalRows_kinds t h]; intro hc; cases hc

theorem PlanReq.optionalRows_are_not_wind_down (r : PlanReq) (t : Seg)
    (h : t ∈ r.optionalRows) : t.kind ≠ SegKind.windDown := by
  rw [r.optionalRows_kinds t h]; intro hc; cases hc

theorem PlanReq.restRows_are_not_work (r : PlanReq) (t : Seg) (h : t ∈ r.restRows) :
    t.kind.isWork = false := by rw [r.restRows_kinds t h]; rfl

theorem PlanReq.restRows_are_not_blocks (r : PlanReq) (t : Seg) (h : t ∈ r.restRows) :
    t.kind ≠ SegKind.block := by rw [r.restRows_kinds t h]; intro hc; cases hc

theorem PlanReq.restRows_are_not_walls (r : PlanReq) (t : Seg) (h : t ∈ r.restRows) :
    t.kind ≠ SegKind.wall := by rw [r.restRows_kinds t h]; intro hc; cases hc

theorem PlanReq.restRows_are_not_breaks (r : PlanReq) (t : Seg) (h : t ∈ r.restRows) :
    t.kind ≠ SegKind.brk := by rw [r.restRows_kinds t h]; intro hc; cases hc

theorem PlanReq.restRows_are_not_wind_down (r : PlanReq) (t : Seg) (h : t ∈ r.restRows) :
    t.kind ≠ SegKind.windDown := by rw [r.restRows_kinds t h]; intro hc; cases hc

/-! ### What step 7 tells §8.2 step 8 -/

/-- **Fork `diagnose`'s high-Rest sum** (`planner.rs:2141-2145`): the Rest minutes at energy
≥ 4.  `Seg.minutes` is `Look.spanMinutes` and not a second arithmetic (AGENTS §5.3). -/
def PlanReq.restHighMin (r : PlanReq) : Nat :=
  (r.restRows.filter (fun s =>
      match s.energy with | some e => decide (4 ≤ e.val) | Option.none => false)).foldl
    (fun a s => a + s.minutes) 0

/-- **Fork `diagnose`'s A-capacity test** (`planner.rs:2146-2152`): those minutes, but only on
a day that also held a `ci = 5` candidate — not a wall, not an optional — the day did not
assign.  Zero otherwise, which is fork `Diagnostics::default()`.

`assigned` is a parameter and not a field read: the caller is `dayDiagnostics`, which is
building the day the set is read off, so taking it as an argument is what keeps the definition
from being circular. -/
def PlanReq.aCapacityLost (r : PlanReq) (assigned : List Id) : Nat :=
  if (decide (0 < r.restHighMin) &&
      (r.cands.val.map Prod.fst).any (fun c =>
        decide (c.ci.val = 5) && !c.wall && !c.optional && !assigned.contains c.id)) = true
  then r.restHighMin else 0

/-- **A day with no high Rest loses no A-capacity** — the `rest_high > 0` guard, stated, so
that "this number is about Rest rows" is a theorem and not a reading of the body. -/
theorem PlanReq.aCapacityLost_needs_rest (r : PlanReq) (assigned : List Id)
    (h : r.restHighMin = 0) : r.aCapacityLost assigned = 0 := by
  unfold PlanReq.aCapacityLost
  rw [if_neg (by simp [h])]

/-- **And what it reports is exactly those minutes when it reports anything.** -/
theorem PlanReq.aCapacityLost_is_the_rest_minutes (r : PlanReq) (assigned : List Id) :
    r.aCapacityLost assigned = 0 ∨ r.aCapacityLost assigned = r.restHighMin := by
  unfold PlanReq.aCapacityLost
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **Fork `diagnose`'s last note** (`planner.rs:2216-2221`): a day whose budget is spent and
that has blocks behind it says so — every slot from here on is about to be Rest, and §8.2 step
7 is the step that makes that true.  `Note.budgetSpent` was written at P0 and nothing
constructed it until now (README gap **904** item 3). -/
def PlanReq.budgetSpentNotes (r : PlanReq) : List Note :=
  if (decide (remainingBudget r = 0) && decide (0 < r.blocksDone)) = true
  then [Note.budgetSpent r.blocksDone] else []

/-- **A day with budget left says nothing** — the note's own guard. -/
theorem PlanReq.no_budget_note_while_the_budget_lasts (r : PlanReq)
    (h : 0 < remainingBudget r) : r.budgetSpentNotes = [] := by
  unfold PlanReq.budgetSpentNotes
  rw [if_neg (by simp; omega)]

/-- **A day that has done nothing says nothing either** — a travel day zeroes the budget
(`a_travel_day_has_no_budget`) and must not therefore claim blocks were done. -/
theorem PlanReq.no_budget_note_without_a_block (r : PlanReq) (h : r.blocksDone = 0) :
    r.budgetSpentNotes = [] := by
  unfold PlanReq.budgetSpentNotes
  rw [if_neg (by simp [h])]

/-- **§8.2 step 6's rows, which are the day's**: the routine instances as **step 6** left them
— fork `emit_segments(…, &routines, …)` is called after `place_deferred` (`planner.rs:1032`),
so a deferred instance step 6 found a position for has a Routine row and one it could not place
still has none (`a_deferred_routine_has_no_row`).  `stepTwoSegs` is the same renderer at step
2's list and stays, because step 2's own laws are about step 2's list. -/
def dayRoutineSegs (r : PlanReq) : List Seg := routineRows r r.finalRoutines

/-! ### §8.2 step 5's rows — the work the day assigns

**Fork `emit_segments`' Block/Batch loop** (`planner.rs:1836-1866`).  Every step up to here had
its rule and its laws and emitted nothing: `assignFold` and `finalAssign` were built, proved and
read seventeen times inside this file, and **their rows reached no day** — D50 and README gap
**1790**.  This is the composition, and it is the only thing between the kernel's day and the
fork's that is not a deletion.

**It reads `finalAssign` and not `assignFold`**, for the reason `restRows` does: fork
`run()` calls `place_deferred` (`planner.rs:1032`) and *then* `emit_segments`
(`planner.rs:1071`) with the same `&assign`, so a slot step 6 freed carries no Block row and a
slot step 6 re-filled does.  `emitKeptBreaks` is the one place the fork keeps step **5**'s
answer, and it says so where it is.

**The four fields that are not the slot's.**  `planned` is the group's commitment and not the
slot's minutes (fork `planned_min: Some(g.commit_min)`); `mult` is the group's exact multiplier
(there is no `Float` here, AGENTS §4); `underused` is fork `gap >= 2` on `slot.energy
.saturating_sub(g.ci)`, which is `Nat` subtraction and needs no `saturating_` spelling; and
`hot` is §7.2's `p = 0` over the **members**, the priority and not the `hot` key.

**`note` is `none` and that is the design, not an omission.**  Fork's row carries
`note: (gap >= 2).then(|| format!("↓ slot {}, item {}", …))`; `Emit.underusedCell` derives
exactly that text from the row's own `energy` and the item's `ci` when `flags.underused` is
set, and `Emit.noteCell` gives an explicit note precedence over it.  A `Note` constructor here
would be a second writer of one sentence (D49's shape, AGENTS §5.3). -/
def Group.ids (g : Group) : List Id := g.members.map (fun m => m.cand.id)

/-- **One assigned row** — fork `emit_segments`' `out.push(Segment { … })` for the slot `i`
that `assign[i]` gave to `groups[gi]`, as a function of the three things the fork reads: the
slot's energy, the slot, and the group.  Named and separate because every law below is a `rfl`
about *this* record, which is what W-28's ten survivors taught: a theorem about the SHAPE of a
row pins nothing about the FIELDS it writes. -/
def assignedSeg (e : Fin 6) (s : Look.Slot) (g : Group) : Seg :=
  { start := s.start, stop := s.stop,
    kind := if 1 < g.ids.length then SegKind.batch (batchIdsOf g.ids) else SegKind.block,
    energy := some e,
    item := match g.ids with | [i] => some i | _ => Option.none,
    inst := Option.none,
    flags := { SegFlags.none with
                 underused := decide (2 ≤ e.val - g.ci.val),
                 hot := g.members.any (fun m => m.key.p == 0) },
    planned := some g.commitMin, mult := some g.mult, note := Option.none }

/-- **§8.2 step 5's rows, at this request's own assignment.** -/
def PlanReq.assignedRows (r : PlanReq) : List Seg :=
  (r.energisedSlots.zip r.finalAssign.slotOf).filterMap (fun p =>
    match p.2 with
    | Option.none => Option.none
    | some gi =>
      match r.finalAssign.groups[gi]? with
      | Option.none => Option.none
      | some g => some (assignedSeg p.1.1 p.1.2 g))

/-! ### What §8.2 step 5's rows say

Eight `rfl`s and two statements.  The `rfl`s are the fields the fork writes, pinned one by one
— `assignedSeg_note` included, because *not* writing a note is a decision `Emit.noteCell`
depends on. -/

theorem assignedSeg_start (e : Fin 6) (s : Look.Slot) (g : Group) :
    (assignedSeg e s g).start = s.start := rfl

theorem assignedSeg_stop (e : Fin 6) (s : Look.Slot) (g : Group) :
    (assignedSeg e s g).stop = s.stop := rfl

theorem assignedSeg_energy (e : Fin 6) (s : Look.Slot) (g : Group) :
    (assignedSeg e s g).energy = some e := rfl

theorem assignedSeg_planned (e : Fin 6) (s : Look.Slot) (g : Group) :
    (assignedSeg e s g).planned = some g.commitMin := rfl

theorem assignedSeg_mult (e : Fin 6) (s : Look.Slot) (g : Group) :
    (assignedSeg e s g).mult = some g.mult := rfl

theorem assignedSeg_inst (e : Fin 6) (s : Look.Slot) (g : Group) :
    (assignedSeg e s g).inst = Option.none := rfl

/-- **The `↓` mark is the slot's gap over the group**, fork `underused: gap >= 2` on
`slot.energy.saturating_sub(g.ci)` — `Nat` subtraction *is* the saturating one, so the fork's
spelling has no counterpart here. -/
theorem assignedSeg_underused (e : Fin 6) (s : Look.Slot) (g : Group) :
    (assignedSeg e s g).flags.underused = decide (2 ≤ e.val - g.ci.val) := rfl

/-- **And the `⚠` is §7.2's `p = 0` over the members** — the priority, not the `hot` key. -/
theorem assignedSeg_hot (e : Fin 6) (s : Look.Slot) (g : Group) :
    (assignedSeg e s g).flags.hot = g.members.any (fun m => m.key.p == 0) := rfl

/-- **The row carries no `Note`, and that is the design.**  Fork's row carries
`note: (gap >= 2).then(|| format!("↓ slot {}, item {}", …))`; `Emit.underusedCell` derives
exactly that text from the row's own `energy` and the item's `ci` whenever `flags.underused`
is set, and `Emit.noteCell` gives an explicit note precedence over it.  A `Note` constructor
here would be a **second writer of one sentence** — D49's shape, AGENTS §5.3. -/
theorem assignedSeg_note (e : Fin 6) (s : Look.Slot) (g : Group) :
    (assignedSeg e s g).note = Option.none := rfl

/-- **An assigned row is a Block or a Batch — never anything else.**  The clause every "these
rows cannot reach that set" law is built on, and the one that makes `dayAssigned` reach
something the planner chose for the first time. -/
theorem assignedSeg_is_work (e : Fin 6) (s : Look.Slot) (g : Group) :
    (assignedSeg e s g).kind.isWork = true := by
  unfold assignedSeg SegKind.isWork
  by_cases h : 1 < g.ids.length
  · simp only [if_pos h]
  · simp only [if_neg h]

/-- A one-or-zero-member list is what the `item` field's `match` is for.  Stated over an
arbitrary list because that is all it is about. -/
theorem shortListIsItsHead (l : List Id) (h : l.length ≤ 1) :
    (match l with | [i] => some i | _ => (Option.none : Option Id)).toList = l := by
  match l, h with
  | [], _ => rfl
  | [i], _ => rfl
  | i :: j :: rest, hl => exact absurd hl (by simp)

/-- **A Batch row names its group's members and a Block row names the one member it has** —
fork `item: (ids.len() == 1).then(|| ids[0].clone())` beside `SegKind::Batch(ids)`, so
`Seg.items` is the group's ids either way and the day's assigned set is the groups' members.

**Stated on the subdomain the bound fits** (AGENTS §3.1 item 4): `batchIdsOf` truncates at
`maxBatch`, and that the truncation never fires on a produced day needs a group chain
`assignFold` and `deferWalk` do not yet carry — README gap **1900**.
`PlanReq.a_group_is_a_bounded_batch` is that fact for `buildGroups`; the missing half is
that a group of `finalAssign` is one of them. -/
theorem assignedSeg_items_when_the_group_fits_the_batch_bound (e : Fin 6) (s : Look.Slot)
    (g : Group) (hb : g.ids.length ≤ maxBatch) : (assignedSeg e s g).items = g.ids := by
  unfold Seg.items assignedSeg
  by_cases hlt : 1 < g.ids.length
  · simp only [if_pos hlt]
    exact batchIdsOf_of_bounded _ hb
  · simp only [if_neg hlt]
    exact shortListIsItsHead g.ids (by omega)

/-- **Every assigned row is `assignedSeg` at a slot of this day and the group that slot went
to** — a `filterMap` over the zip, so a row exists only where `slotOf` says a group holds that
slot, and every law above applies to it. -/
theorem PlanReq.mem_assignedRows {r : PlanReq} {t : Seg} (h : t ∈ r.assignedRows) :
    ∃ (e : Fin 6) (s : Look.Slot) (gi : Nat) (g : Group),
      ((e, s), some gi) ∈ r.energisedSlots.zip r.finalAssign.slotOf ∧
        r.finalAssign.groups[gi]? = some g ∧ t = assignedSeg e s g := by
  unfold PlanReq.assignedRows at h
  obtain ⟨p, hp, hq⟩ := List.mem_filterMap.1 h
  cases hgi : p.2 with
  | none => simp only [hgi] at hq; exact absurd hq (by simp)
  | some gi =>
    cases hg : r.finalAssign.groups[gi]? with
    | none => simp only [hgi, hg] at hq; exact absurd hq (by simp)
    | some g =>
      simp only [hgi, hg, Option.some.injEq] at hq
      refine ⟨p.1.1, p.1.2, gi, g, ?_, hg, hq.symm⟩
      have hpe : ((p.1.1, p.1.2), some gi) = p := by rw [← hgi]
      rw [hpe]; exact hp

/-- **Every assigned row is work.** -/
theorem PlanReq.assignedRows_are_work (r : PlanReq) (t : Seg) (h : t ∈ r.assignedRows) :
    t.kind.isWork = true := by
  obtain ⟨e, s, -, g, -, -, heq⟩ := r.mem_assignedRows h
  rw [heq]; exact assignedSeg_is_work e s g

/-- **A kind that is work is none of the seven that are not** — stated once as the class it is,
rather than four times as a list of names (the shape every widening takes since W-27).  The
four corollaries below are this lemma at the four kinds the day's case analyses ask about. -/
theorem PlanReq.a_work_row_is_not (r : PlanReq) (t : Seg) (h : t ∈ r.assignedRows)
    (k : SegKind) (hk : k.isWork = false) : t.kind ≠ k := by
  intro hc
  have hw := r.assignedRows_are_work t h
  rw [hc, hk] at hw
  exact absurd hw (by simp)

theorem PlanReq.assignedRows_are_not_walls (r : PlanReq) (t : Seg) (h : t ∈ r.assignedRows) :
    t.kind ≠ SegKind.wall := r.a_work_row_is_not t h _ rfl

theorem PlanReq.assignedRows_are_not_breaks (r : PlanReq) (t : Seg) (h : t ∈ r.assignedRows) :
    t.kind ≠ SegKind.brk := r.a_work_row_is_not t h _ rfl

theorem PlanReq.assignedRows_are_not_wind_down (r : PlanReq) (t : Seg)
    (h : t ∈ r.assignedRows) : t.kind ≠ SegKind.windDown := r.a_work_row_is_not t h _ rfl

theorem PlanReq.assignedRows_are_not_rest (r : PlanReq) (t : Seg) (h : t ∈ r.assignedRows) :
    t.kind ≠ SegKind.rest := r.a_work_row_is_not t h _ rfl

/-- **And it spans exactly the slot it was given** — fork `start: slot.start, end: slot.end`,
so §8.2 step 5 invents no interval of its own and `Look`'s cut is the only thing that says
where a Block of this day may be.  This is the hinge every wall, break and overlap obligation
about an assigned row will hang on. -/
theorem PlanReq.an_assigned_row_is_a_slot_of_the_day (r : PlanReq) (t : Seg)
    (h : t ∈ r.assignedRows) :
    ∃ (e : Fin 6) (s : Look.Slot), (e, s) ∈ r.energisedSlots ∧
      t.start = s.start ∧ t.stop = s.stop ∧ t.energy = some e := by
  obtain ⟨e, s, _gi, g, hz, -, heq⟩ := r.mem_assignedRows h
  subst heq
  exact ⟨e, s, (List.of_mem_zip hz).1, assignedSeg_start e s g, assignedSeg_stop e s g,
    assignedSeg_energy e s g⟩

/-- **The row's group is the assignment's own** — the half that lets a law about
`finalAssign.groups` become a law about a row of the day. -/
theorem PlanReq.an_assigned_row_carries_its_group (r : PlanReq) (t : Seg)
    (h : t ∈ r.assignedRows) :
    ∃ (gi : Nat) (g : Group), r.finalAssign.groups[gi]? = some g ∧
      t.planned = some g.commitMin ∧ t.mult = some g.mult ∧ t.note = Option.none := by
  obtain ⟨e, s, gi, g, -, hgp, heq⟩ := r.mem_assignedRows h
  subst heq
  exact ⟨gi, g, hgp, assignedSeg_planned e s g, assignedSeg_mult e s g, assignedSeg_note e s g⟩

/-! ############################################################################
## Fork `open_block_segment` — the worked stretch of the running block (W-34, gaps 554, 2519)

Fork `emit_segments` (`planner.rs:1730-1733`) opens the day with `past_segments()` and then
`open_block_segment(active.is_none() && !interrupted, walls)` — **both, always**, and only then
§8.2 choice 5b's reservation.  **The fork does not choose between this row and the reservation**:
they cover `[since, now)` and `[now, end)`, one behind the cursor and one ahead of it.  What it
chooses is **which of the two carries the `▶`** — the reservation when `active_run` placed one,
this row when it refused (overtime, a wall on `now`, a `d done` what-if), and neither while an
interruption runs, because §9 pauses the block.  `openBlockRows` ports exactly that choice.

**Why it matters.**  `Replay` closes a block's sub-segment only when something interrupts it
(`planner.rs:1994-1997`), so the minutes a running block has worked since its last resume are in
no replayed segment: without this row the kernel's day had a hole where the current block is,
and — wherever no reservation was placed — the running item was missing from the day's
**assigned set**, which is what moved `diagnostics.droppedTail` and `planHonesty` on 42–55 of 273
generated days a run (README gap 2519).

**It is a row of the replayed past.**  It ends at `now`, it comes from the log through D24's seam
(`PlanReq.run`), and nothing about it is the planner's placement — §12.1's "left of the cursor
the timeline renders the log".  So `replayedRows` is the day's one list of the log's rows, and
every law that was about the log's rows is about it: `stepOneSegs`, and `PlanCheck`'s `hnopast`
and `PastPays`, which are finding 1 (README gap 385) and were stated over the closed half only
because the kernel drew no open half.
############################################################################ -/

/-- **Where the worked stretch ends** — fork `open_block_segment`'s `end`: `now`, clipped to the
day's end, and then to the start of whatever paused the block after it began (fork: an ad-hoc
wall, `w.blocked_start > since`; since W-35 `PlanReq.pauseRows`, the running break's and a wall
on `now`'s rows too — P45, P47, so the stretch is never drawn across the meeting that paused it). -/
def PlanReq.openStop (r : PlanReq) (since : Nat) : Nat :=
  r.pauseRows.foldl (fun e w => if since < w.start then min e w.start else e)
    (min r.now.sec r.dayEnd)

/-- **Fork `Planner::open_block_segment`** (`planner.rs:2002-2031`): the stretch of the block the
log holds open, `[since, end)`, a `Block` carrying no slot energy and the running item; `▶`
exactly when §8.2 choice 5b reserved nothing and nothing pauses it; `open`, because the next
replan shows it longer; and the note `"<n>m so far"` at `worked_min_at(now)` (`openWorkedMin`).

The fork's refusals, kept: no open block, or one with no `since` (a paused block); a `since` before
the day or not before `now`; and an `end` the clips left at or before `since`. -/
def openBlockRows (r : PlanReq) : List Seg :=
  match r.run.answer.openBlock with
  | none => []
  | some b =>
    match b.since with
    | none => []
    | some s =>
      if s.1.sec < r.dayStart ∨ r.now.sec ≤ s.1.sec ∨ r.openStop s.1.sec ≤ s.1.sec then []
      else
        [{ start := s.1.sec, stop := r.openStop s.1.sec, kind := .block, energy := none,
           item := some b.id, inst := none,
           flags := { SegFlags.none with
             current := r.activeRun.isNone && !r.interrupted, isOpen := true },
           planned := none, mult := none, note := some (.soFar (r.workedOf b.id (openWorkedMin r.now.sec b))) }]

/-- **The log's rows of the day** — fork `past_segments` and `open_block_segment`, the two
halves §12.1 renders left of the cursor.  Every row here ends at `now`
(`replayedRows_end_at_now`) and none of them is the planner's placement. -/
def replayedRows (r : PlanReq) : List Seg := pastRows r ++ openBlockRows r

/-- **§8.2 step 1's rows.**  The day's own order is `dayRows`, once step 2 has added its own (this
list is step 1's contribution and nothing more).  Written here since W-34 rather than beside
`pastRows`: its replayed half holds `openBlockRows`, which reads §8.2 choice 5b's `activeRun`. -/
def stepOneSegs (r : PlanReq) : List Seg :=
  replayedRows r ++ interruptRows r ++ breakRows r ++
    (wallsToday r).flatMap (fun x => wallRows (r.isTravelDay x.id) x)

/-! ### What the open row is -/

/-- The interruption clip only ever shortens the stretch. -/
theorem openClip_le (lo : Nat) : ∀ (ws : List Seg) (x : Nat),
    ws.foldl (fun e w => if lo < w.start then min e w.start else e) x ≤ x
  | [], _ => Nat.le_refl _
  | w :: ws, x => by
    simp only [List.foldl_cons]
    refine Nat.le_trans (openClip_le lo ws _) ?_
    by_cases h : lo < w.start
    · rw [if_pos h]; exact Nat.min_le_left _ _
    · rw [if_neg h]; exact Nat.le_refl _

/-- And it stops at every interruption that began after `lo`. -/
theorem openClip_le_start (lo : Nat) : ∀ (ws : List Seg) (x : Nat) (w : Seg), w ∈ ws →
    lo < w.start → ws.foldl (fun e w => if lo < w.start then min e w.start else e) x ≤ w.start
  | [], _, _, hw, _ => absurd hw (by simp)
  | v :: ws, x, w, hw, hlt => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hw with rfl | hw
    · refine Nat.le_trans (openClip_le lo ws _) ?_
      rw [if_pos hlt]; exact Nat.min_le_right _ _
    · exact openClip_le_start lo ws _ w hw hlt

/-- **The stretch ends at `now` and at the day's end**, whatever the clip did. -/
theorem PlanReq.openStop_le (r : PlanReq) (since : Nat) :
    r.openStop since ≤ r.now.sec ∧ r.openStop since ≤ r.dayEnd := by
  have h := openClip_le since r.pauseRows (min r.now.sec r.dayEnd)
  unfold PlanReq.openStop
  omega

/-- **Everything the open row is**, read off the one branch that builds it. -/
theorem mem_openBlockRows {r : PlanReq} {t : Seg} (h : t ∈ openBlockRows r) :
    ∃ b s, r.run.answer.openBlock = some b ∧ b.since = some s ∧ t.start = s.1.sec ∧
      t.stop = r.openStop s.1.sec ∧ r.dayStart ≤ t.start ∧ t.start < t.stop ∧
      t.kind = SegKind.block ∧ t.energy = none ∧ t.item = some b.id ∧ t.inst = none ∧
      t.flags = { SegFlags.none with
        current := r.activeRun.isNone && !r.interrupted, isOpen := true } ∧
      t.planned = none ∧ t.mult = none ∧ t.note = some (.soFar (r.workedOf b.id (openWorkedMin r.now.sec b))) := by
  unfold openBlockRows at h
  split at h
  · exact absurd h (by simp)
  · rename_i b hb
    split at h
    · exact absurd h (by simp)
    · rename_i s hs
      split at h
      · exact absurd h (by simp)
      · rename_i hin
        simp only [List.mem_singleton] at h
        subst h
        refine ⟨b, s, hb, hs, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · show r.dayStart ≤ s.1.sec; omega
        · show s.1.sec < r.openStop s.1.sec; omega

/-- **The open row ends at `now` and starts inside the day** — the half of §8.3's stability law
that makes a replan able to leave it alone, as `pastRows_end_at_now` is for the closed half. -/
theorem openBlockRows_end_at_now (r : PlanReq) (t : Seg) (h : t ∈ openBlockRows r) :
    r.dayStart ≤ t.start ∧ t.start < t.stop ∧ t.stop ≤ r.now.sec := by
  obtain ⟨b, s, -, -, -, hstop, h1, h2, -⟩ := mem_openBlockRows h
  exact ⟨h1, h2, by rw [hstop]; exact (r.openStop_le _).1⟩

/-- **The open row is a Block with no slot energy** — a stretch of the log, not a slot
(`energy: None`, fork `planner.rs:2019`). -/
theorem openBlockRows_are_energyless_blocks (r : PlanReq) (t : Seg) (h : t ∈ openBlockRows r) :
    t.kind = SegKind.block ∧ t.energy = none := by
  obtain ⟨-, -, -, -, -, -, -, -, hk, he, -⟩ := mem_openBlockRows h
  exact ⟨hk, he⟩

/-- **The `▶` is the reservation's, the open row's, or nobody's — never both.**  Fork
`mark_current = active.is_none() && !interrupted` (`planner.rs:1733`); W-35 widened the second. -/
theorem the_open_row_is_current_exactly_when_nothing_is_reserved_or_interrupted (r : PlanReq)
    (t : Seg) (h : t ∈ openBlockRows r) :
    t.flags.current = (r.activeRun.isNone && !r.interrupted) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hf, -⟩ := mem_openBlockRows h
  rw [hf]

/-- **The open row stops where a later interruption starts** — §9 pauses the running block, so
the fork clips the worked stretch at the ad-hoc wall's start. -/
theorem the_open_row_stops_where_a_later_interruption_starts (r : PlanReq) (t : Seg)
    (h : t ∈ openBlockRows r) (w : Seg) (hw : w ∈ interruptRows r) (hlt : t.start < w.start) :
    t.stop ≤ w.start := by
  obtain ⟨b, s, -, -, hst, hstop, -⟩ := mem_openBlockRows h
  rw [hstop]
  rw [hst] at hlt
  exact openClip_le_start s.1.sec r.pauseRows _ w (List.mem_append_left _ (List.mem_append_left _ hw)) hlt

/-- **The open row is the item the log holds open**, and it carries its worked minutes. -/
theorem the_open_row_is_the_logs_open_block (r : PlanReq) (t : Seg) (h : t ∈ openBlockRows r) :
    ∃ b, r.run.answer.openBlock = some b ∧ t.item = some b.id ∧
      t.note = some (.soFar (r.workedOf b.id (openWorkedMin r.now.sec b))) ∧ t.flags.isOpen = true := by
  obtain ⟨b, -, hb, -, -, -, -, -, -, -, hi, -, hf, -, -, hn⟩ := mem_openBlockRows h
  exact ⟨b, hb, hi, hn, by rw [hf]⟩

/-- **At most one open row** — the log holds at most one open block. -/
theorem openBlockRows_length_le_one (r : PlanReq) : (openBlockRows r).length ≤ 1 := by
  unfold openBlockRows
  split
  · exact Nat.zero_le _
  · split
    · exact Nat.zero_le _
    · split <;> simp

/-- **And it is drawn whenever the fork draws it**: an open block whose last resume is inside the
day and before `now`, with a stretch the clips left non-empty, is one row, exactly. -/
theorem openBlockRows_of_an_open_block (r : PlanReq) (b : Replay.OpenBlock) (s : Replay.At)
    (hb : r.run.answer.openBlock = some b) (hs : b.since = some s)
    (h1 : r.dayStart ≤ s.1.sec) (h2 : s.1.sec < r.now.sec) (h3 : s.1.sec < r.openStop s.1.sec) :
    openBlockRows r =
      [{ start := s.1.sec, stop := r.openStop s.1.sec, kind := .block, energy := none,
         item := some b.id, inst := none,
         flags := { SegFlags.none with
           current := r.activeRun.isNone && !r.interrupted, isOpen := true },
         planned := none, mult := none, note := some (.soFar (r.workedOf b.id (openWorkedMin r.now.sec b))) }] := by
  unfold openBlockRows
  rw [hb]
  simp only [hs]
  rw [if_neg (by omega)]

/-- **`worked_min_at(now)`, run** (AGENTS §5.2): thirty minutes banked and an hour since the last
resume is ninety; a paused block (no `since`) is its banked minutes alone; and the stretch is
floored to whole minutes, `num_minutes()` of the span. -/
theorem openWorkedMin_is_the_banked_minutes_and_the_running_stretch :
    openWorkedMin 7200 ⟨['m'], (⟨0, 0⟩, ⟨false, 0⟩), 30, some (⟨3600, 0⟩, ⟨false, 0⟩), false⟩ = 90 ∧
      openWorkedMin 7200 ⟨['m'], (⟨0, 0⟩, ⟨false, 0⟩), 30, none, true⟩ = 30 ∧
      openWorkedMin 7259 ⟨['m'], (⟨0, 0⟩, ⟨false, 0⟩), 0, some (⟨3600, 0⟩, ⟨false, 0⟩), false⟩ = 60 := by
  decide

/-! ### The replayed past, whole -/

theorem mem_replayedRows {r : PlanReq} {t : Seg} :
    t ∈ replayedRows r ↔ t ∈ pastRows r ∨ t ∈ openBlockRows r := List.mem_append

/-- **Every row the log contributes ends at `now`** — both halves. -/
theorem replayedRows_end_at_now (r : PlanReq) (t : Seg) (h : t ∈ replayedRows r) :
    r.dayStart ≤ t.start ∧ t.start < t.stop ∧ t.stop ≤ r.now.sec :=
  (mem_replayedRows.1 h).elim (pastRows_end_at_now r t) (openBlockRows_end_at_now r t)

theorem replayedRows_are_not_walls (r : PlanReq) (t : Seg) (h : t ∈ replayedRows r) : t.kind ≠ SegKind.wall :=
  (mem_replayedRows.1 h).elim (pastRows_are_not_walls r t)
    (fun h hc => by rw [(openBlockRows_are_energyless_blocks r t h).1] at hc; cases hc)

theorem replayedRows_are_not_wind_down (r : PlanReq) (t : Seg) (h : t ∈ replayedRows r) : t.kind ≠ SegKind.windDown :=
  (mem_replayedRows.1 h).elim (pastRows_are_not_wind_down r t)
    (fun h hc => by rw [(openBlockRows_are_energyless_blocks r t h).1] at hc; cases hc)

/-- The closed half carries no slot energy: `past_segments` writes `energy: None` on every row. -/
theorem pastRows_carry_no_energy (r : PlanReq) (t : Seg) (h : t ∈ pastRows r) :
    t.energy = none := by
  -- Read through `mem_pastRows` since D65 (a cut piece is a row `pastRowOf` builds, and
  -- `pastRowOf` writes `energy := none` on every row, as fork `past_segments` does); the
  -- lines below keep the check-9 pin sites after this theorem where they were recorded.
  --
  --
  --
  --
  --
  obtain ⟨d, -, g, -, q, -, rfl⟩ := mem_pastRows.1 h
  rfl

/-- The closed half holds no Batch: `pastKind` maps the log's six kinds to none of them. -/
theorem pastRows_are_not_batches (r : PlanReq) (t : Seg) (ids : BatchIds) (h : t ∈ pastRows r) :
    t.kind ≠ SegKind.batch ids := by
  -- Read through `mem_pastRows` since D65: a cut piece keeps its segment's kind, and
  -- `pastKind` maps the log's six kinds to no Batch.  The lines below keep the check-9
  -- pin sites after this theorem where `kernel/mutations.txt` recorded them.
  --
  --
  --
  --
  --
  obtain ⟨d, -, g, -, q, -, rfl⟩ := mem_pastRows.1 h
  cases hg : g.kind <;> simp [pastRowOf, pastKind, hg]

/-- **No row the log contributes carries a slot energy.** -/
theorem replayedRows_carry_no_energy (r : PlanReq) (t : Seg) (h : t ∈ replayedRows r) : t.energy = none :=
  (mem_replayedRows.1 h).elim (pastRows_carry_no_energy r t) (fun h => (openBlockRows_are_energyless_blocks r t h).2)

/-- **No row the log contributes is a Batch** — §7.5's batches are the assign fold's alone. -/
theorem replayedRows_are_not_batches (r : PlanReq) (t : Seg) (ids : BatchIds) (h : t ∈ replayedRows r) :
    t.kind ≠ SegKind.batch ids := (mem_replayedRows.1 h).elim (pastRows_are_not_batches r t ids)
    (fun h hc => by rw [(openBlockRows_are_energyless_blocks r t h).1] at hc; cases hc)

/-- **§8.2 step 1 in fork `emit_segments`' own order** (W-38, README gap 3281): `stepOneSegs` with no running
interruption; with one, its Lost row among the walls where fork `collect_walls`' `(blocked_start, id)` sort puts its
ad-hoc wall, by `wallLe` itself (`sortWalls_snoc`), keyed off the row: its start, and the block it names or `""`. -/
def stepOneOrder (r : PlanReq) : List Seg := match (interruptRows r).head? with
  | none => stepOneSegs r
  | some s => replayedRows r ++ breakRows r ++
      ((wallsToday r).filter (fun y => wallLe y ⟨s.item.getD [], r.today, r.today, s.start, s.start, s.stop⟩)).flatMap (fun x => wallRows (r.isTravelDay x.id) x) ++
      interruptRows r ++ ((wallsToday r).filter (fun y => !wallLe y ⟨s.item.getD [], r.today, r.today, s.start, s.start, s.stop⟩)).flatMap (fun x => wallRows (r.isTravelDay x.id) x)

/-- **Nothing is added and nothing is dropped** — step 1's rows are `stepOneSegs`', in either order. -/
theorem stepOneOrder_perm (r : PlanReq) : (stepOneOrder r).Perm (stepOneSegs r) := by
  unfold stepOneOrder; split
  · exact List.Perm.refl _
  · exact Look.adhoc_walk_perm _ _ _ _ _ _ _

/-- **The day's rows**: steps 1, 2, 6 and **7**, §8.2 choice 5b's reservation and step 5's Block and Batch rows (D50, README
gaps 803/1790), in an order the stable sort leaves as fork `emit_segments` pushes two rows of one start and one end: step 1
(`stepOneOrder`, W-38), the reservation, the work, the kept breaks, the optionals, the Rest slots, and the routines with the
evening LAST -- since W-45 (README gap 4623; the evening came before the reservation, so a block running past bed to midnight
was drawn under its Sleep row).  The routines are pushed by the fork before the work, and no work, break, optional or Rest
row shares a routine's span; a wall, a break or an interruption on `now` pauses the block, so no step-1 row shares its. -/
def dayRows (r : PlanReq) : List WfSeg :=
  sortRows ((stepOneOrder r ++ reservationSegs r ++ r.assignedRows ++ r.keptBreakRows ++
    r.optionalRows ++ r.restRows ++ dayRoutineSegs r).map segOf)

theorem mem_dayRows {r : PlanReq} {s : WfSeg} (h : s ∈ dayRows r) :
    ∃ t ∈ stepOneSegs r ++ dayRoutineSegs r ++ reservationSegs r ++ r.assignedRows ++
      r.keptBreakRows ++ r.optionalRows ++ r.restRows, s = segOf t := by
  have hm := mem_sortRows.1 h
  simpa [eq_comm, (stepOneOrder_perm r).mem_iff, or_comm, or_left_comm, or_assoc] using List.mem_map.1 hm

/-- **A row the planner places is a row of the day** — the converse `dayRows` owes, used to
show the reservation really reaches `dayPlan`. -/
theorem mem_dayRows_of_mem {r : PlanReq} {t : Seg}
    (h : t ∈ stepOneSegs r ++ dayRoutineSegs r ++ reservationSegs r ++ r.assignedRows ++
      r.keptBreakRows ++ r.optionalRows ++ r.restRows) : segOf t ∈ dayRows r :=
  mem_sortRows.2 (List.mem_map.2 ⟨t, by simpa [(stepOneOrder_perm r).mem_iff, or_comm, or_left_comm, or_assoc] using h, rfl⟩)

/-- **The open row reaches the day** (W-34) — `openBlockRows` is not built beside `dayRows`, it
is composed into it, through `stepOneSegs`' replayed half (D50: a row built and not joined is
the defect). -/
theorem the_open_row_is_a_row_of_the_day {r : PlanReq} {t : Seg} (h : t ∈ openBlockRows r) :
    segOf t ∈ dayRows r :=
  mem_dayRows_of_mem (by simp [stepOneSegs, replayedRows, h])

/-- §8.2 step 8's diagnostics, as far as steps 1 and 2 fill them: the overlapping walls step 1
refused to resolve, and the travel-day note.

**Step 2 adds nothing here, and the empty slot is deliberate.**  `Diagnostics.deferred` is
§8.2 step 8's *posterior-downgrade* list — fork `planner.rs:149`, "the candidates a *posterior
downgrade* cost a slot" — and **not** the routines step 2 deferred to step 6.  Writing the
deferred instances into it would give one field two meanings, which is the defect this kernel
is named after (AGENTS §5.3).  A deferred routine is carried on its own `Placed` record with
`deferred := true` and no position, which is exactly the state fork `place_deferred` receives,
and `Note.noPosition` is what names it if step 6 cannot place it either (**P6**). -/
def dayAssigned (r : PlanReq) : List Id :=
  ((dayRows r).filter (fun s => s.val.kind.isWork)).flatMap segItems

/-- **The running item is in the day's assigned set whenever the log draws its open row** — the
fork's `assigned` counts every work row, the worked stretch included, and that set is what
`diagnostics.droppedTail` and `planHonesty` read (README gap 2519: the kernel's set lacked it on
every day with an open block and no reservation, 42–55 of 273 generated days a run). -/
theorem the_open_rows_item_is_assigned (r : PlanReq) (t : Seg) (h : t ∈ openBlockRows r)
    (i : Id) (hi : t.item = some i) : i ∈ dayAssigned r := by
  refine List.mem_flatMap.2 ⟨segOf t, List.mem_filter.2 ⟨the_open_row_is_a_row_of_the_day h, ?_⟩, ?_⟩
  · rw [segOf_kind, (openBlockRows_are_energyless_blocks r t h).1]; rfl
  · show i ∈ (segOf t).val.items
    rw [segOf_items]
    unfold Seg.items
    rw [(openBlockRows_are_energyless_blocks r t h).1, hi]
    exact List.mem_singleton_self i

/-! ### §8.2 step 8: the fields the day fills from what it already computed (W-33, P8's first half)

Fork `Planner::diagnose` (`planner.rs:2105-2222`) fills twelve fields from the candidates, the
answers, the groups and the segments it already holds.  `Diagnostics` has carried all twelve
with the fork's meanings since P0, and `dayDiagnostics` filled three of them until this step
(README gap **2403**, found by driving `--json plan`).  Each definition below is one field, read
off a value the request carried or the day already computed — the capacity op's own answer
(`PlanReq.candAnswers`), the nine facts on the wire (`Look.PlanFacts`), the groups step 5
built, the rows it placed, the day's replayed record — and none derives a fact about a
candidate (D34).

**The comparand is the fork as the shipped binary runs it (D53)**: `planner::plan` fed the
kernel's own grants by `kernel_capacity::rank` (`prio_of` reads each grant's `until`, `bin`
and `shortfall` off the capacity op's JSON, `Boundary`'s `grantJsonF`).  So a field below that
reads §7 reads it exactly where the shipped binary reads it: off the answer, not off a second
test of the grant.  `tm/tests/planner_invariants.rs` compares every field written here with
the kernel-ranked fork's on every generated day (W-33) — `droppedTail` and `planHonesty`
counted instead of compared on a day whose fork draws README gap 554's open-block row, which
this kernel does not port and which changes the assigned set those two read. -/

/-- **`Diagnostics.impossible`** — fork `diagnose`'s `if p.is_impossible() { if let Some(until)
= p.until { d.impossible.push((c.id, p.shortfall_min, until)) } }`, walls skipped, one row per
ANSWER in request order and no de-duplication (the fork pairs by index).

**What `is_impossible` is at the shipped binary, read off the code.**  `Prio::is_impossible` is
`is_hot() && shortfall_min_exact.num > 0`; `kernel_capacity`'s `prio_of` sets `u` only where
the grant has an `until` and is not a wall, and to `≥ 1` only where the grant's `bin` is `null`,
which `Boundary`'s `binJson` writes for a HOT bin; and the `shortfall` it reads is
`Look.FloorOut.shortfall`, which is positive only at a HOT bin.  So the shipped binary's test
is **`0 < o.shortfall`** and nothing else: `until` is present at every such answer (a granted
answer's due date, a floor answer's last day), and a wall carries neither a grant nor a floor.
`shortfall_min` is `capacity::floor_minutes` of the same units — `Arith.floorQ` over
`Look.capDen` here — and the field's "exact" is that floor of the exact value, as the wire's
`shortMin` is (D15).

**Two things this reads that a test of `Grant.impossible` would not** (and the brief this step
was written from suggested that test): a FLOOR answer is listed when its floor is HOT and short
— `Look.FloorOut.shortfall`'s second arm, fork `is_impossible` reading `u` off the floor — and
a granted answer whose need exceeds its availability only through R1's CEILING (`Arith.needMin`)
while §7.1's exact `u` stays below 1 is NOT listed, because its bin is not HOT and the shipped
binary does not call it impossible.  `an_item_the_day_names_with_a_grant_has_impossible_numbers`
and `the_day_names_every_item_whose_numbers_say_impossible_at_a_hot_bin` are the two directions
in `edfNumbers`'s terms, and the second carries the HOT bin because it needs it.

Bounded by the answers: a `filterMap` cannot grow a list and `PlanReq.candAnswers_capped` is
`maxCands` — the wire's bound, reused (R10) — so `Capped.ofListTake` in `dayDiagnostics` drops
nothing (`dayDiagnostics_impossible`). -/
def PlanReq.dayImpossible (r : PlanReq) : List (Id × Nat) :=
  r.candAnswers.filterMap (fun o =>
    if 0 < o.shortfall then
      some (o.out.cand.id, Arith.floorQ (Arith.mkPos o.shortfall Look.capDen Look.capDen_pos))
    else none)

/-- **A row is an answer whose own reported shortfall is positive, with that shortfall floored
to minutes** — both directions, by answer (the fork's pairing). -/
theorem PlanReq.mem_dayImpossible (r : PlanReq) (i : Id) (s : Nat) :
    (i, s) ∈ r.dayImpossible ↔
      ∃ o ∈ r.candAnswers, o.out.cand.id = i ∧ 0 < o.shortfall ∧
        s = Arith.floorQ (Arith.mkPos o.shortfall Look.capDen Look.capDen_pos) := by
  unfold PlanReq.dayImpossible
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨o, ho, h⟩
    by_cases hs : 0 < o.shortfall
    · rw [if_pos hs] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨o, ho, h.1, hs, h.2.symm⟩
    · rw [if_neg hs] at h
      exact absurd h (by simp)
  · rintro ⟨o, ho, hid, hs, rfl⟩
    exact ⟨o, ho, by simp [hs, hid]⟩

/-- The cap.  **Stated AFTER `PlanReq.mem_dayImpossible` on purpose** (W-33 repair, README gap
2567): a length bound is true of the constant `[]`, so the `[]` mutant of the writer breaks this
proof and not this statement, and check 9 records the FIRST error as the pin.  With the
membership law first, the pin check 9 records is a statement the constant falsifies. -/
theorem PlanReq.dayImpossible_capped (r : PlanReq) : r.dayImpossible.length ≤ maxCands :=
  Nat.le_trans (List.length_filterMap_le _ _) r.candAnswers_capped

/-- **The whole IMPOSSIBLE tuple, `until` included** (W-35, README gap 2640): fork `diagnose`'s
`if let Some(until) = p.until { d.impossible.push((c.id, p.shortfall_min, until)) }`.  The
`until` is the one the shipped binary reads off the capacity op's answer (`Boundary.grantJsonF`'s
`until`, `kernel_capacity::prio_of`): a floor answer's last day, else the grant's due date, and an
answer with neither is skipped as the fork skips it.  The walk is `dayImpossible`'s, and
`PlanReq.dayImpossible_is_the_projection` says the pairs are this list's first two components —
the date is never absent where the shortfall is positive. -/
def PlanReq.dayImpossibleUntil (r : PlanReq) : List (Id × Nat × Nat) :=
  r.candAnswers.filterMap (fun o =>
    if 0 < o.shortfall then
      -- the date is `answerUntil`'s, its one reader: D60's key reads the same one (W-36), and the
      -- `match` that stood here inline until then became that definition rather than a second
      -- copy of it (AGENTS §5.3)
      (answerUntil o).map (fun u =>
        (o.out.cand.id, Arith.floorQ (Arith.mkPos o.shortfall Look.capDen Look.capDen_pos), u))
    else none)

/-- A positive shortfall is a floor's or a grant's: `CandOut.shortfall` is `0` without a grant.
Stated over `answerUntil` since W-36, whose `match` it restated inline until then (the date's one
reader, AGENTS §5.3). -/
theorem PlanReq.a_short_answer_has_an_until (o : Look.FloorOut) (h : 0 < o.shortfall) :
    (answerUntil o).isSome = true := by
  unfold answerUntil
  cases hf : o.floor with
  | some g => rfl
  | none =>
    cases hg : o.out.grant with
    | some g => rfl
    | none =>
      exfalso
      have : o.shortfall = 0 := by
        unfold Look.FloorOut.shortfall Look.CandOut.shortfall
        rw [hf, hg]
      omega

/-- **The pairs are the tuple's first two components**: one walk, and no answer the fork lists
loses its date. -/
theorem PlanReq.dayImpossible_is_the_projection (r : PlanReq) :
    r.dayImpossibleUntil.map (fun t => (t.1, t.2.1)) = r.dayImpossible := by
  unfold PlanReq.dayImpossibleUntil PlanReq.dayImpossible
  rw [List.map_filterMap]
  congr 1
  funext o
  by_cases hs : 0 < o.shortfall
  · rw [if_pos hs, if_pos hs]
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (PlanReq.a_short_answer_has_an_until o hs)
    rw [hu]
    rfl
  · rw [if_neg hs, if_neg hs]
    rfl

theorem PlanReq.dayImpossibleUntil_capped (r : PlanReq) :
    r.dayImpossibleUntil.length ≤ maxCands :=
  Nat.le_trans (List.length_filterMap_le _ _) r.candAnswers_capped

/-- **A granted answer is `Look.priorities`' own, unfloored, and its grant is §7.3's** —
`Look.an_answers_grant_reserves_the_min` carried through the floor pass, whose first arm
(`Look.withFloor`) is taken only by an answer WITHOUT a grant. -/
theorem PlanReq.a_granted_answer (r : PlanReq) {o : Look.FloorOut} {g : Grant}
    (ho : o ∈ r.candAnswers) (hg : o.out.grant = some g) :
    o.floor = none ∧ g.reserved = min (g.deadline.need * Look.capDen) g.avail ∧
      o.shortfall = (if o.out.bin = some .hot then g.deadline.need * Look.capDen - g.avail
        else 0) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ho
  unfold PlanReq.candAnswers at hi
  rw [Look.prioritiesWithFloors_getElem?] at hi
  cases hp : (Look.priorities r.prio.bins r.prio.safety r.prio.dflt r.prio.hyst r.edfDays
      (r.cands.val.map Prod.fst))[i]? with
  | none => rw [hp] at hi; simp at hi
  | some oc =>
    rw [hp] at hi
    cases hc : r.cands.val[i]? with
    | none => rw [hc] at hi; simp at hi
    | some cf =>
      rw [hc] at hi
      simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hi
      subst hi
      unfold Look.withFloor at hg ⊢
      cases hog : oc.grant with
      | none =>
        rw [hog] at hg
        cases hf : cf.2 with
        | none => simp [hf, hog] at hg
        | some fl =>
          by_cases hw : oc.cand.wall = true
          · simp [hf, hw, hog] at hg
          · simp [hf, hw] at hg
      | some g' =>
        simp only [hog] at hg ⊢
        have hgg : g' = g := by simpa using hg
        subst hgg
        obtain ⟨hmin, hsh⟩ := Look.an_answers_grant_reserves_the_min r.prio.bins r.prio.safety
          r.prio.dflt r.prio.hyst r.edfDays (r.cands.val.map Prod.fst) hp hog
        refine ⟨by simp, hmin, ?_⟩
        simp only [Look.FloorOut.shortfall]
        exact hsh

/-- **A named answer that carries a grant is IMPOSSIBLE by that grant, at a HOT bin.** -/
theorem PlanReq.a_named_grant_is_impossible_at_a_hot_bin (r : PlanReq) {o : Look.FloorOut}
    {g : Grant} (ho : o ∈ r.candAnswers) (hg : o.out.grant = some g) (hs : 0 < o.shortfall) :
    g.impossible Look.capDenD = true ∧ o.out.bin = some .hot := by
  obtain ⟨-, -, hsh⟩ := r.a_granted_answer ho hg
  by_cases hb : o.out.bin = some .hot
  · rw [if_pos hb] at hsh
    refine ⟨?_, hb⟩
    unfold Grant.impossible
    exact decide_eq_true (show g.avail < g.deadline.need * Look.capDen by omega)
  · rw [if_neg hb] at hsh
    omega

/-- **An IMPOSSIBLE grant at a HOT bin reports a shortfall** — so its answer is named. -/
theorem PlanReq.an_impossible_grant_at_a_hot_bin_is_short (r : PlanReq) {o : Look.FloorOut}
    {g : Grant} (ho : o ∈ r.candAnswers) (hg : o.out.grant = some g)
    (hi : g.impossible Look.capDenD = true) (hb : o.out.bin = some .hot) :
    0 < o.shortfall := by
  obtain ⟨-, -, hsh⟩ := r.a_granted_answer ho hg
  rw [if_pos hb] at hsh
  have hlt : g.avail < g.deadline.need * Look.capDen := of_decide_eq_true hi
  omega

/-- **A named answer without a grant is a HOT floor that falls short** — the floor pass's own
answer (`Look.FloorOut.shortfall`'s second arm), which a test of `Grant.impossible` could not
see because a floor answer carries no `Grant`. -/
theorem PlanReq.a_named_answer_without_a_grant_is_a_short_floor (o : Look.FloorOut)
    (hg : o.out.grant = none) (hs : 0 < o.shortfall) :
    ∃ fg, o.floor = some fg ∧ o.out.bin = some .hot ∧ fg.avail < fg.need * Look.capDen := by
  unfold Look.FloorOut.shortfall at hs
  cases hf : o.floor with
  | none =>
    rw [hf] at hs
    simp only [Look.CandOut.shortfall, hg] at hs
    exact absurd hs (by simp)
  | some fg =>
    rw [hf] at hs
    cases hb : o.out.bin with
    | none => rw [hb] at hs; exact absurd hs (by simp)
    | some b =>
      cases b with
      | hot =>
        rw [hb] at hs
        exact ⟨fg, rfl, rfl, by simp only at hs; omega⟩
      | plus n => rw [hb] at hs; exact absurd hs (by simp)

/-- **The answer an id is answered by, when the answers' ids are distinct, is every answer that
carries the id.** -/
theorem PlanReq.answerFor_of_mem (r : PlanReq)
    (hnodup : (r.candAnswers.map (fun o => o.out.cand.id)).Nodup) {o : Look.FloorOut}
    (ho : o ∈ r.candAnswers) : r.answerFor o.out.cand.id = some o := by
  unfold PlanReq.answerFor
  obtain ⟨as, bs, hl⟩ := List.append_of_mem ho
  refine (List.find?_eq_some_iff_append).2 ⟨by simp, as, bs, hl, fun a hamem => ?_⟩
  rw [hl, List.map_append, List.map_cons, List.nodup_append] at hnodup
  obtain ⟨-, -, hdisj⟩ := hnodup
  have hne : a.out.cand.id ≠ o.out.cand.id := fun heq =>
    hdisj a.out.cand.id (List.mem_map.2 ⟨a, hamem, rfl⟩) o.out.cand.id (by simp) heq
  simp [hne]

/-! ### D67 (P58, README gap 3350): the day SAYS why an item it admitted has no row

The owner's D67 (README gap 3160): §8.2 step 5 stays GREEDY — the fork's `Planner::pick`, which never
reads a grant — so the walk can hand the only unbroken run an atomic impossible item fits to an item
ranked before it, and the item gets no row.  The day names why, and `PlanCheck.impossibleKept` reads
§8.3's "impossible never dropped" as **an owed impossible item is placed or named with its reason**,
the reason checked TRUE of the day (`PlanCheck.whyHolds`).  The fork names none: parity **P58**.

**The reasons are the walk's, found from the walk and not guessed** (`PlanFold`, the W-38 section).
A group that fits a slot before the walk fits it at the walk's own state for as long as it has been
given nothing: `contiguousFits` reads only the slots from the cursor on, and every one of those is
still free when the cursor reaches it; and a group's entry moves only when that group is picked.  So
at every slot where the item's group fits before the walk, step 5 did one of exactly two things
other than place it: gave the slot to a group AHEAD of it (`List.findIdx?`'s first fit) — then the
item found **no run left** (its group is atomic: every unbroken run it fits was taken) or **no slot
left** (splittable) — or passed the slot because the budget was spent (`budget ≤ used`): **budget
spent**.  Nothing else passes a free slot a group fits
(`PlanFold.assignStep_fills_a_free_slot_a_group_fits`), and step 6 never changes step 5's assignment
(`PlanFold.finalAssign_is_assignFold`), so the final slot vector tells the two apart: a slot the item
fits that step 5 left EMPTY was passed for the budget.

The writer names every item §7.3 lists impossible that step 5's filter admits at some slot before
the walk and that the day's rows do not hold, once each, in the list's order — owed today or not:
the check asks the reason of the owed ones (`PlanCheck.owedByItsGrant`), and the reason is as true of
the rest.  It is the WALK's reason and never a second test of the grant.  An item step 5's filter
admits NOWHERE — `[?]`, a `loc:` or a `ci` no slot of the day meets — is named `noSlotAdmits` (the
W-38 repair, README gap 3523: until it such an item was named nothing while its banner said IMPOSSIBLE).  `dayUnplaced`'s laws are at the end of this file, beside the two `dayImpossible`
directions that stood here until W-38 (`the_day_names_every_item_whose_numbers_say_impossible_at_a_hot_bin`,
`an_item_the_day_names_with_a_grant_has_impossible_numbers`, moved whole so no check-9 pin site
below this section moved). -/

/-- **§8.2 step 5's WHOLE filter at one energised slot, BEFORE the walk** (D66): the fork's `pick`
test over the planner's own start groups and its empty cursor (`PlanReq.assignStart`).  Moved from
`PlanCheck` at W-38 so the check and the day's writer read ONE definition (AGENTS §5.3). -/
def fitsBefore (r : PlanReq) (i : Id) (x : (Fin 6 × Look.Slot) × Nat) : Bool := r.startGroups.any (fun g =>
  decide (i ∈ g.ids) && r.groupFitsSlot r.todaySlots r.assignStart.slotOf r.todayBreaks x.2 x.1.1 x.1.2 g)

/-- **`Diagnostics.unplaced`** (D67, P58): each item §7.3 lists impossible (`dayImpossible`, once
each) that `assigned` — the day's `dayAssigned` — does not hold: `noSlotAdmits` when step 5's filter
admits it at no slot before the walk (`fitsBefore`), else the walk's reason — `budgetSpent` when step
5 left a slot it fits EMPTY, else `noRunLeft` when an atomic group holds it and `noSlotLeft` if not.
`slotOf` is read once, outside the per-item walk (README gap 2521's lesson).  Bounded by the listed
items (`PlanReq.dayUnplaced_capped`), whose bound is the wire's `maxCands` (R10), so
`dayDiagnostics` truncates nothing (`dayDiagnostics_unplaced`). -/
def PlanReq.dayUnplaced (r : PlanReq) (assigned : List Id) : List (Id × NoPlace) :=
  let slotOf := r.finalAssign.slotOf
  (r.dayImpossible.map Prod.fst).eraseDups.filterMap (fun i =>
    let xs := r.energisedSlots.zipIdx.filter (fitsBefore r i)
    if assigned.contains i then none else if xs.isEmpty then some (i, .noSlotAdmits)
    else if xs.any (fun x => (slotOf[x.2]?).join.isNone) then some (i, .budgetSpent)
    else some (i, if r.startGroups.any (fun g => decide (i ∈ g.ids) && !g.splittable) then .noRunLeft
      else .noSlotLeft))

/-- `List.eraseDups` (core's, the fork's `!d.xs.contains(&id)` push guard — FIRST occurrence
kept, in push order) never lengthens a list.  Core proves membership (List.mem_eraseDups) and
not this. -/
theorem eraseDups_length_le {α : Type} [BEq α] :
    ∀ (n : Nat) (l : List α), l.length ≤ n → l.eraseDups.length ≤ l.length
  | _, [], _ => by simp
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons]
    have hf := List.length_filter_le (fun b => !b == a) as
    have ih := eraseDups_length_le n (as.filter fun b => !b == a)
      (by simp only [List.length_cons] at h; omega)
    simp only [List.length_cons]
    omega

/-- **`Diagnostics.hot`** — fork `diagnose`: `(p.is_hot() || p.class == HotFlag) &&
!d.hot.contains(&c.id)`, walls skipped.  `is_hot` at the shipped binary is `u ≥ 1`, which
`prio_of` sets exactly where the grant's `bin` is `null` and the grant has an `until`: an answer
whose bin is HOT (a granted answer's `Look.binAt`, a floor answer's `Look.floorBin`).  The
hot-flag class is the one the wire names `hotflag`, `Look.FloorOut.cls`.  One row per id, the
first (`List.eraseDups`). -/
def PlanReq.dayHot (r : PlanReq) : List Id :=
  (r.candAnswers.filterMap (fun o =>
    if !o.out.cand.wall &&
        (decide (o.out.bin = some Arith.Bin.hot) || decide (o.cls = Look.PClass.hotFlag))
    then some o.out.cand.id else none)).eraseDups

/-- **An id is hot exactly when an answer names it, is not a wall, and is HOT by bin or by the
hot flag** (W-33 repair, README gap 2567) — the membership law the `[]` mutant falsifies, stated
before the cap so check 9's first error is a statement and not a proof term. -/
theorem PlanReq.mem_dayHot (r : PlanReq) (i : Id) :
    i ∈ r.dayHot ↔
      ∃ o ∈ r.candAnswers, o.out.cand.id = i ∧ o.out.cand.wall = false ∧
        (o.out.bin = some Arith.Bin.hot ∨ o.cls = Look.PClass.hotFlag) := by
  unfold PlanReq.dayHot
  rw [List.mem_eraseDups, List.mem_filterMap]
  constructor
  · rintro ⟨o, ho, h⟩
    by_cases hc : (!o.out.cand.wall &&
        (decide (o.out.bin = some Arith.Bin.hot) || decide (o.cls = Look.PClass.hotFlag))) = true
    · rw [if_pos hc] at h
      simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, decide_eq_true_eq] at hc
      exact ⟨o, ho, h, hc.1, hc.2⟩
    · rw [if_neg hc] at h
      exact absurd h (by simp)
  · rintro ⟨o, ho, hid, hw, hb⟩
    refine ⟨o, ho, ?_⟩
    have hc : (!o.out.cand.wall &&
        (decide (o.out.bin = some Arith.Bin.hot) || decide (o.cls = Look.PClass.hotFlag))) = true := by
      simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, decide_eq_true_eq]
      exact ⟨hw, hb⟩
    rw [if_pos hc, hid]

theorem PlanReq.dayHot_capped (r : PlanReq) : r.dayHot.length ≤ maxCands :=
  Nat.le_trans (eraseDups_length_le _ _ (Nat.le_refl _))
    (Nat.le_trans (List.length_filterMap_le _ _) r.candAnswers_capped)

/-- **`Diagnostics.droppedTail`** — fork `diagnose`'s "§9: what the tail dropped": every member
of every group `build_groups` built that the day's own assigned set does not hold, once each
(`!d.dropped_tail.contains`).  `PlanReq.buildGroups` is the one `build_groups` (the running
item split out as the fork splits it).  `assigned` is a parameter for `PlanReq.aCapacityLost`'s
reason, and `dayDiagnostics` hands it `dayAssigned` — fork `assigned`, the items of every work
row — computed ONCE: read inside the filter it would be the whole day recomputed per member. -/
def PlanReq.dayDroppedTail (r : PlanReq) (assigned : List Id) : List Id :=
  ((r.buildGroups.flatMap (fun g => g.members.map (fun x => x.cand.id))).filter
    (fun i => !assigned.contains i)).eraseDups

/-- **`Diagnostics.underused`** — fork `diagnose`'s first loop: the items of every work row
whose `flags.underused` §8.2 step 5 set (the slot's energy two or more above the group's `ci`),
one entry per item per row as the fork pushes them.  The fork records `(id, energy, ci)`;
`IdList` carries the id, and the row carries the other two. -/
def PlanReq.dayUnderused (r : PlanReq) : List Id :=
  ((dayRows r).filter (fun s => s.val.flags.underused && s.val.kind.isWork)).flatMap segItems

/-- **An item's `ci` as fork `diagnose` reads it for `underused`**: `cands.iter().find(|c| c.id ==
id).map_or(0, |c| c.ci)` — the first candidate carrying the id, `0` when none does. -/
def PlanReq.candCi (r : PlanReq) (i : Id) : Fin 6 :=
  ((r.cands.val.find? (fun cf => cf.1.id == i)).map (fun cf => cf.1.ci)).getD 0

/-- **The whole UNDERUSED tuple** (W-35, README gap 2743): fork `diagnose`'s first loop,
`d.underused.push((id, seg.energy.unwrap_or(0), ci))`, over the same rows and items as
`PlanReq.dayUnderused` (`PlanReq.dayUnderused_is_the_projection`). -/
def PlanReq.dayUnderusedLevels (r : PlanReq) : List (Id × Fin 6 × Fin 6) :=
  ((dayRows r).filter (fun s => s.val.flags.underused && s.val.kind.isWork)).flatMap
    (fun s => (segItems s).map (fun i => (i, s.val.energy.getD 0, r.candCi i)))

theorem PlanReq.dayUnderused_is_the_projection (r : PlanReq) :
    r.dayUnderusedLevels.map Prod.fst = r.dayUnderused := by
  unfold PlanReq.dayUnderusedLevels PlanReq.dayUnderused
  rw [List.map_flatMap]
  congr 1
  funext s
  rw [List.map_map]
  exact List.map_id' _

/-- **`Diagnostics.planHonesty`** — fork `diagnose`'s §11 ratio, as the pair design §11 asks for
(nothing here divides): Σ `commit_min` over the groups with an assigned member, over
`remaining_budget × block_min`.  The fork's `remaining_budget` is the local `plan()` computes
before the assign loop — travel-day zeroing included, never decremented — which is
`remainingBudget`.  The fork's `Option<f64>` is `None` at a zero budget; the pair is
`Diagnostics.empty`'s `(0, 0)` there.  `assigned` is `PlanReq.dayDroppedTail`'s parameter, for
its reason. -/
def PlanReq.dayPlanHonesty (r : PlanReq) (assigned : List Id) : Nat × Nat :=
  let budgetMin := remainingBudget r * r.blockMin
  if budgetMin = 0 then (0, 0)
  else
    ((r.buildGroups.filter (fun g =>
        g.members.any (fun x => assigned.contains x.cand.id))).foldl
          (fun acc g => acc + g.commitMin) 0,
     budgetMin)

/-- **`Diagnostics.waiting`** — fork `diagnose`'s `if c.waiting && !d.waiting.contains(&c.id)`,
walls skipped: the candidates whose line is `[?]`, read off the wire's own fact
(`Look.PlanFacts.waiting`, fork `priority.rs:718`), once each. -/
def PlanReq.dayWaiting (r : PlanReq) : List Id :=
  (r.cands.val.filterMap (fun cf =>
    if !cf.1.wall && cf.1.plan.val.waiting then some cf.1.id else none)).eraseDups

/-- **An id is waiting exactly when a non-wall candidate carries it with a waiting line** (W-33
repair, README gap 2567) — before the cap, for check 9's pin. -/
theorem PlanReq.mem_dayWaiting (r : PlanReq) (i : Id) :
    i ∈ r.dayWaiting ↔
      ∃ cf ∈ r.cands.val, cf.1.id = i ∧ cf.1.wall = false ∧ cf.1.plan.val.waiting = true := by
  unfold PlanReq.dayWaiting
  rw [List.mem_eraseDups, List.mem_filterMap]
  constructor
  · rintro ⟨cf, hcf, h⟩
    by_cases hc : (!cf.1.wall && cf.1.plan.val.waiting) = true
    · rw [if_pos hc] at h
      simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      exact ⟨cf, hcf, h, hc.1, hc.2⟩
    · rw [if_neg hc] at h
      exact absurd h (by simp)
  · rintro ⟨cf, hcf, hid, hw, hwt⟩
    refine ⟨cf, hcf, ?_⟩
    have hc : (!cf.1.wall && cf.1.plan.val.waiting) = true := by
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨hw, hwt⟩
    rw [if_pos hc, hid]

theorem PlanReq.dayWaiting_capped (r : PlanReq) : r.dayWaiting.length ≤ maxCands :=
  Nat.le_trans (eraseDups_length_le _ _ (Nat.le_refl _))
    (Nat.le_trans (List.length_filterMap_le _ _) r.cands.property)

/-- **`Diagnostics.blocked`** — fork `diagnose`'s `if let Some(Ineligible::Blocked(deps)) =
c.ineligible_reason()`, walls skipped: the `blocked` arm of `Look.PlanFacts.ineligibleReason`,
the kernel's ONE reading of fork `ineligible_reason` (`priority.rs:303-322`), whose `none` case
is `Look.PlanFacts.eligible`.  Until W-34 this re-spelled the rule — `isOpen && !blockedBy.isEmpty`
beside `eligible`'s own conjuncts — and README gap 2573 named the two definitions of one concept
(AGENTS §5.3); the rule has one body now, `mem_dayBlocked` below is re-proved over it and its
statement did not move (D5).  The fork pushes `(id, deps)` with no guard; `IdList` carries the
id. -/
def PlanReq.dayBlocked (r : PlanReq) : List Id :=
  r.cands.val.filterMap (fun cf =>
    match cf.1.wall, cf.1.plan.val.ineligibleReason with
    | false, some (.blocked _) => some cf.1.id | _, _ => none)

/-- **An id is blocked exactly when a non-wall candidate carries it with an open line and a
non-empty `after:` residue** (W-33 repair, README gap 2567) — before the cap, for check 9's
pin. -/
theorem PlanReq.mem_dayBlocked (r : PlanReq) (i : Id) :
    i ∈ r.dayBlocked ↔
      ∃ cf ∈ r.cands.val, cf.1.id = i ∧ cf.1.wall = false ∧ cf.1.plan.val.isOpen = true ∧
        cf.1.plan.val.blockedBy.isEmpty = false := by
  unfold PlanReq.dayBlocked
  rw [List.mem_filterMap]
  -- RE-PROVED at W-34 (D5, README gap 2573): the statement is W-33's, word for word; the
  -- body it is about reads the rule through `Look.PlanFacts.ineligibleReason`, and
  -- `ineligibleReason_blocked_iff` is the bridge from that one reading back to the two facts
  -- this statement names.
  constructor
  · rintro ⟨cf, hcf, h⟩
    split at h
    · rename_i d hw hr
      obtain ⟨ho, hb, -⟩ := (Look.PlanFacts.ineligibleReason_blocked_iff _ d).1 hr
      exact ⟨cf, hcf, Option.some.inj h, hw, ho, hb⟩
    · exact absurd h (by simp)
  · rintro ⟨cf, hcf, hid, hw, ho, hb⟩
    refine ⟨cf, hcf, ?_⟩
    have hr := (Look.PlanFacts.ineligibleReason_blocked_iff _ _).2 ⟨ho, hb, rfl⟩
    simp only [hw, hr, hid]

theorem PlanReq.dayBlocked_capped (r : PlanReq) : r.dayBlocked.length ≤ maxCands :=
  Nat.le_trans (List.length_filterMap_le _ _) r.cands.property

/-- **The whole BLOCKED tuple** (W-35, README gap 2743): fork `diagnose`'s `d.blocked.push((c.id,
deps))`, the deps the `blocked` arm of `Look.PlanFacts.ineligibleReason` carries — the one reading
of fork `ineligible_reason`, as `PlanReq.dayBlocked` reads it
(`PlanReq.dayBlocked_is_the_projection`). -/
def PlanReq.dayBlockedDeps (r : PlanReq) : List (Id × List Field.Dep) :=
  r.cands.val.filterMap (fun cf =>
    match cf.1.wall, cf.1.plan.val.ineligibleReason with
    | false, some (.blocked d) => some (cf.1.id, d) | _, _ => none)

theorem PlanReq.dayBlocked_is_the_projection (r : PlanReq) :
    r.dayBlockedDeps.map Prod.fst = r.dayBlocked := by
  unfold PlanReq.dayBlockedDeps PlanReq.dayBlocked
  rw [List.map_filterMap]
  congr 1
  funext cf
  split <;> rfl

theorem PlanReq.dayBlockedDeps_capped (r : PlanReq) : r.dayBlockedDeps.length ≤ maxCands :=
  Nat.le_trans (List.length_filterMap_le _ _) r.cands.property

/-- **Fork `run()`'s `raw_slots`** (`planner.rs:954-955`): §8.2 step 3's cut energised through
`Posterior::none(cfg)` — today's `EnergyCtx` with no reports, which here is `Look.energizeToday` at a
`today0` whose `reports` are empty, and nothing else (the wake, the sleep debt, the location and
the home cap are the same `today0`'s).  One field of §8.2 step 8 reads it, `deferred`, and README
gap **555** — *"`raw_slots` are not computed"* — closes with it (W-34). -/
def PlanReq.rawSlots (r : PlanReq) : List (Fin 6 × Look.Slot) :=
  Look.energizeToday { r.look with today0 := { r.look.today0 with reports := [] } } r.todaySlots

/-- **`Diagnostics.deferred`** — fork `diagnose`'s "a posterior downgrade cost this item its slot"
(`planner.rs:2172-2183`): walls skipped, a candidate the day's `assigned` does not hold, eligible
(`Look.PlanFacts.eligible`), not an optional, with no placement window, for which SOME slot's raw
energy reached its `ci` while the same slot's energised one did not — once each, the first
(`List.eraseDups`, the fork's `!d.deferred.contains`).  The slot pairs are zipped ONCE, outside the
per-candidate test (README gap 2521's lesson: a recomputation per member is quadratic). -/
def PlanReq.dayDeferred (r : PlanReq) (assigned : List Id) : List Id :=
  let both := r.energisedSlots.zip r.rawSlots
  (r.cands.val.filterMap (fun cf =>
    if !cf.1.wall && !assigned.contains cf.1.id && cf.1.plan.val.eligible && !cf.1.optional &&
        !cf.1.window &&
        both.any (fun p => decide (cf.1.ci ≤ p.2.1) && decide (p.1.1 < cf.1.ci))
    then some cf.1.id else none)).eraseDups

theorem PlanReq.dayDeferred_capped (r : PlanReq) (assigned : List Id) :
    (r.dayDeferred assigned).length ≤ maxCands :=
  Nat.le_trans (eraseDups_length_le _ _ (Nat.le_refl _))
    (Nat.le_trans (List.length_filterMap_le _ _) r.cands.property)

/-- **`Diagnostics.restDebtMin`** — fork `diagnose`'s §11 rest debt (`planner.rs:2206-2212`): Σ
over today's logged breaks of `planned_min.saturating_sub(actual_or_planned())`, where
`BreakRecord::actual_or_planned` is `actual_min.unwrap_or(planned_min)` and `Nat` subtraction is
`saturating_sub`; off the day record `PlanReq.todayRecord` already reads (fork
`self.input.replay.day(self.date)`), `0` with none. -/
def PlanReq.dayRestDebtMin (r : PlanReq) : Nat :=
  ((r.todayRecord.map (·.breaks)).getD []).foldl
    (fun a b => a + (b.plannedMin - b.actualMin.getD b.plannedMin)) 0

/-- **The zip pairs each slot with itself**: the raw and the energised slots are the same slots
of the same cut, in the same order — only their levels differ — so fork `slots.iter().zip(
raw_slots)` compares one slot's two readings and never two slots. -/
theorem PlanReq.the_raw_and_energised_slots_are_the_same_slots (r : PlanReq) :
    r.rawSlots.map Prod.snd = r.todaySlots ∧ r.energisedSlots.map Prod.snd = r.todaySlots := by
  unfold PlanReq.rawSlots PlanReq.energisedSlots Look.energizeToday
  simp [List.map_map, Function.comp_def]

/-- **An id is deferred exactly when** a non-wall candidate carries it, the day does not assign
it, it is eligible, not optional, has no window, and some slot's raw level reaches its `ci` while
the same slot's energised level does not — before the cap, for check 9's pin. -/
theorem PlanReq.mem_dayDeferred (r : PlanReq) (assigned : List Id) (i : Id) :
    i ∈ r.dayDeferred assigned ↔
      ∃ cf ∈ r.cands.val, cf.1.id = i ∧ cf.1.wall = false ∧ assigned.contains cf.1.id = false ∧
        cf.1.plan.val.eligible = true ∧ cf.1.optional = false ∧ cf.1.window = false ∧
        ∃ p ∈ r.energisedSlots.zip r.rawSlots, cf.1.ci ≤ p.2.1 ∧ p.1.1 < cf.1.ci := by
  unfold PlanReq.dayDeferred
  simp only [List.mem_eraseDups, List.mem_filterMap]
  constructor
  · rintro ⟨cf, hcf, h⟩
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨hw, ha⟩, he⟩, ho⟩, hn⟩, p, hp, hle, hlt⟩ := hc
      exact ⟨cf, hcf, h, hw, ha, he, ho, hn, p, hp, hle, hlt⟩
    · exact absurd h (by simp)
  · rintro ⟨cf, hcf, hid, hw, ha, he, ho, hn, p, hp, hle, hlt⟩
    refine ⟨cf, hcf, ?_⟩
    rw [if_pos (by
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨⟨hw, ha⟩, he⟩, ho⟩, hn⟩, p, hp, hle, hlt⟩), hid]

/-- **The rest debt is the sum of the day's shortfalls** — each break's `planned − actual`,
saturating, the fork's `.map(…).sum()` — stated as the sum it is. -/
theorem PlanReq.dayRestDebtMin_is_the_sum_of_the_shortfalls (r : PlanReq) :
    r.dayRestDebtMin = (((r.todayRecord.map (·.breaks)).getD []).map
      (fun b => b.plannedMin - b.actualMin.getD b.plannedMin)).sum := by
  unfold PlanReq.dayRestDebtMin
  generalize ((r.todayRecord.map (·.breaks)).getD []) = l
  suffices h : ∀ a, l.foldl (fun a b => a + (b.plannedMin - b.actualMin.getD b.plannedMin)) a =
      a + (l.map (fun b => b.plannedMin - b.actualMin.getD b.plannedMin)).sum by
    simpa using h 0
  induction l with
  | nil => intro a; simp
  | cons b bs ih => intro a; simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]; omega

/-- §8.2 step 8's diagnostics — **TWELVE of the fork's twelve** since W-34 (three until W-33, ten until W-34; README gaps
**2403** and **2511**), and since W-38 the kernel's thirteenth, `unplaced` (D67, P58).  Each is read off a value the request
carried or the day already computed: `conflicts` (step 1), `notes` (steps 1, 6 and 7), `aCapacityLost` (step 7's Rest against
the ci-5 candidates), W-33's `impossible`, `hot`, `waiting`, `blocked`, `droppedTail`, `underused` and `planHonesty`, W-34's
`deferred` (over `PlanReq.rawSlots`, README gap 555) and `restDebtMin` (the day record's breaks), W-38's `unplaced` (step 5's walk). -/
def dayDiagnostics (r : PlanReq) : Diagnostics :=
  let assigned := dayAssigned r
  { Diagnostics.empty with
    underused := Capped.ofListTake r.dayUnderused
    hot := Capped.ofListTake r.dayHot
    impossible := Capped.ofListTake r.dayImpossible
    conflicts := Capped.ofListTake (wallConflicts (wallsToday r))
    blocked := Capped.ofListTake r.dayBlocked
    deferred := Capped.ofListTake (r.dayDeferred assigned)
    waiting := Capped.ofListTake r.dayWaiting
    aCapacityLost := r.aCapacityLost assigned
    notes := Capped.ofListTake
      ((if travelDay r then [Note.travelDay] else []) ++ r.noPositionNotes ++
        r.budgetSpentNotes)
    droppedTail := Capped.ofListTake (r.dayDroppedTail assigned)
    planHonesty := r.dayPlanHonesty assigned
    restDebtMin := r.dayRestDebtMin
    impossibleUntil := Capped.ofListTake r.dayImpossibleUntil
    underusedLevels := Capped.ofListTake r.dayUnderusedLevels
    blockedDeps := Capped.ofListTake r.dayBlockedDeps, served := Capped.ofListTake r.dayServed
    unplaced := Capped.ofListTake (r.dayUnplaced assigned) }

/-- **The day carries the whole IMPOSSIBLE list**: the cap is the wire's and the list is under
it, so `Capped.ofListTake` truncates nothing. -/
theorem dayDiagnostics_impossible (r : PlanReq) :
    (dayDiagnostics r).impossible.val = r.dayImpossible :=
  Capped.ofListTake_keeps_everything_below_the_cap _ r.dayImpossible_capped

theorem dayDiagnostics_hot (r : PlanReq) : (dayDiagnostics r).hot.val = r.dayHot :=
  Capped.ofListTake_keeps_everything_below_the_cap _ r.dayHot_capped

theorem dayDiagnostics_waiting (r : PlanReq) : (dayDiagnostics r).waiting.val = r.dayWaiting :=
  Capped.ofListTake_keeps_everything_below_the_cap _ r.dayWaiting_capped

theorem dayDiagnostics_blocked (r : PlanReq) : (dayDiagnostics r).blocked.val = r.dayBlocked :=
  Capped.ofListTake_keeps_everything_below_the_cap _ r.dayBlocked_capped

theorem dayDiagnostics_droppedTail (r : PlanReq) :
    (dayDiagnostics r).droppedTail = Capped.ofListTake (r.dayDroppedTail (dayAssigned r)) := rfl

theorem dayDiagnostics_underused (r : PlanReq) :
    (dayDiagnostics r).underused = Capped.ofListTake r.dayUnderused := rfl

theorem dayDiagnostics_planHonesty (r : PlanReq) :
    (dayDiagnostics r).planHonesty = r.dayPlanHonesty (dayAssigned r) := rfl

/-- **The day carries the whole `deferred` list** — the cap is the candidates' and the list is
under it.  W-33's tripwire the_day_leaves_two_diagnostic_fields_empty said these two fields were
`Diagnostics.empty`'s for every request; it FIRED at W-34, is refuted in `PlannerWit`
(`the_day_leaves_two_diagnostic_fields_empty_is_refuted`) and is renamed to these two laws. -/
theorem dayDiagnostics_deferred (r : PlanReq) :
    (dayDiagnostics r).deferred.val = r.dayDeferred (dayAssigned r) :=
  Capped.ofListTake_keeps_everything_below_the_cap _ (r.dayDeferred_capped _)

theorem dayDiagnostics_restDebtMin (r : PlanReq) :
    (dayDiagnostics r).restDebtMin = r.dayRestDebtMin := rfl

/-- **The day carries the whole IMPOSSIBLE tuple**, and the pair list is its projection (W-35,
README gap 2640): the date the fork prints is on every entry the day names. -/
theorem dayDiagnostics_impossibleUntil (r : PlanReq) :
    (dayDiagnostics r).impossibleUntil.val = r.dayImpossibleUntil :=
  Capped.ofListTake_keeps_everything_below_the_cap _ r.dayImpossibleUntil_capped

theorem dayDiagnostics_impossible_is_the_projection (r : PlanReq) :
    (dayDiagnostics r).impossibleUntil.val.map (fun t => (t.1, t.2.1))
      = (dayDiagnostics r).impossible.val := by
  rw [dayDiagnostics_impossibleUntil, dayDiagnostics_impossible]
  exact r.dayImpossible_is_the_projection

theorem dayDiagnostics_blockedDeps (r : PlanReq) :
    (dayDiagnostics r).blockedDeps.val = r.dayBlockedDeps :=
  Capped.ofListTake_keeps_everything_below_the_cap _ r.dayBlockedDeps_capped

theorem dayDiagnostics_blocked_is_the_projection (r : PlanReq) :
    (dayDiagnostics r).blockedDeps.val.map Prod.fst = (dayDiagnostics r).blocked.val := by
  rw [dayDiagnostics_blockedDeps, dayDiagnostics_blocked]
  exact r.dayBlocked_is_the_projection

/-- **The underused tuple and the underused ids are taken alike** — the same cap on the same
rows, so the ids are the tuple's first components whether or not gap 2641's cap bites. -/
theorem dayDiagnostics_underused_is_the_projection (r : PlanReq) :
    (dayDiagnostics r).underusedLevels.val.map Prod.fst = (dayDiagnostics r).underused.val := by
  show (Capped.ofListTake r.dayUnderusedLevels).val.map Prod.fst
    = (Capped.ofListTake r.dayUnderused).val
  unfold Capped.ofListTake
  simp only
  rw [List.map_take, r.dayUnderused_is_the_projection]

/-! ### The two caps W-33 left unproved (README gap 2576)

`dayDroppedTail` and `dayUnderused` reach the day through `Capped.ofListTake`, and W-33 wrote no
law saying the take keeps them whole — gap 322's shape, a silent `take`.  **`droppedTail` truncates
nothing**, proved below by the pigeonhole the gap named.  **`underused` is a different list**: the
fork pushes one `(id, energy, ci)` per item per underused work row, so an item holding two
underused slots is named twice (`PlannerWit.the_underused_list_names_an_item_once_per_slot`), and
the per-candidate cap `IdList` carries is not a bound on it.  What does bound it is the rows and
the batch width, `dayUnderused_length_le`; the cap can bite only past 1,024 (row, item) pairs in
one day, and README gap 2641 records that residue with its cost. -/

/-- **`eraseDups` leaves no duplicate** — the half `eraseDups_length_le` does not state, and the
one the pigeonhole below needs. -/
theorem nodup_eraseDups {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (n : Nat) (l : List α), l.length ≤ n → l.eraseDups.Nodup
  | _, [], _ => by simp
  | 0, _ :: _, h => by simp at h
  | n + 1, a :: as, h => by
    rw [List.eraseDups_cons]
    refine List.nodup_cons.2 ⟨?_, ?_⟩
    · intro ha
      rw [List.mem_eraseDups] at ha
      simp at ha
    · exact nodup_eraseDups n _ (Nat.le_trans (List.length_filter_le _ _)
        (by simp only [List.length_cons] at h; omega))

/-- **`droppedTail` truncates nothing** (README gap 2576, first half): every id it names is an
answer's — a member of a group `buildGroups` built is ranked (`PlanReq.a_group_member_is_ranked`)
and a ranked entry is an answer (`PlanReq.a_ranked_entry_is_an_answer`) — and it names each once
(`nodup_eraseDups`), so core's pigeonhole `List.Nodup.length_le_of_subset` bounds it by the
answers, whose count is the candidates' and is capped. -/
theorem PlanReq.dayDroppedTail_capped (r : PlanReq) (assigned : List Id) :
    (r.dayDroppedTail assigned).length ≤ maxCands := by
  have hsub : r.dayDroppedTail assigned ⊆ r.candAnswers.map (fun o => o.out.cand.id) := by
    intro i hi
    unfold PlanReq.dayDroppedTail at hi
    rw [List.mem_eraseDups] at hi
    obtain ⟨g, hg, hgi⟩ := List.mem_flatMap.1 (List.mem_filter.1 hi).1
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hgi
    exact List.mem_map.2 ⟨y.out, List.mem_of_getElem? (PlanReq.a_ranked_entry_is_an_answer
      (PlanReq.a_group_member_is_ranked hg hy)), rfl⟩
  have hnd : (r.dayDroppedTail assigned).Nodup := nodup_eraseDups _ _ (Nat.le_refl _)
  calc (r.dayDroppedTail assigned).length
      ≤ (r.candAnswers.map (fun o => o.out.cand.id)).length := hnd.length_le_of_subset hsub
    _ = r.candAnswers.length := List.length_map _
    _ ≤ maxCands := r.candAnswers_capped

/-- **So the day carries the whole dropped tail.** -/
theorem dayDiagnostics_droppedTail_whole (r : PlanReq) :
    (dayDiagnostics r).droppedTail.val = r.dayDroppedTail (dayAssigned r) :=
  Capped.ofListTake_keeps_everything_below_the_cap _ (r.dayDroppedTail_capped _)

/-- A list of lists no longer than `k` each flattens to at most `k` per list. -/
theorem length_flatMap_le_mul {α β : Type} (f : α → List β) (k : Nat)
    (h : ∀ x, (f x).length ≤ k) : ∀ l : List α, (l.flatMap f).length ≤ l.length * k
  | [] => by simp
  | x :: xs => by
    rw [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have := length_flatMap_le_mul f k h xs
    have := h x
    omega

/-- **A row names at most `maxBatch` items** — a batch its bounded members, any other row its one
item or none. -/
theorem segItems_length_le (s : WfSeg) : (segItems s).length ≤ maxBatch := by
  unfold segItems Seg.items
  split
  · rename_i ids _; exact ids.property
  · cases s.val.item <;> simp [maxBatch]

/-- **What does bound `underused`** (README gap 2576, second half): its underused work rows times
the batch width — the per-(row, item) list the fork pushes, bounded by what it is made of and not
by the candidates. -/
theorem PlanReq.dayUnderused_length_le (r : PlanReq) :
    r.dayUnderused.length ≤
      ((dayRows r).filter (fun s => s.val.flags.underused && s.val.kind.isWork)).length *
        maxBatch :=
  length_flatMap_le_mul segItems maxBatch segItems_length_le _

/-- **And below the cap the take keeps it whole** — the subdomain named in the theorem (AGENTS
§3.1 item 4): at most 64 underused work rows, which a day whose remaining budget is 64 blocks or
fewer cannot exceed with step 5's rows alone. -/
theorem dayDiagnostics_underused_whole_below_the_cap (r : PlanReq)
    (h : ((dayRows r).filter (fun s => s.val.flags.underused && s.val.kind.isWork)).length *
        maxBatch ≤ maxCands) :
    (dayDiagnostics r).underused.val = r.dayUnderused :=
  Capped.ofListTake_keeps_everything_below_the_cap _
    (Nat.le_trans r.dayUnderused_length_le h)

/-! ### The plan's identity: fork `DayPlan::hash`, byte for byte (W-34 track H, P8's emitter)

Fork `DayPlan::hash` (`planner.rs:577-600`) is FNV-1a/64 over **the UTF-8 bytes of
serde_json::to_string(&Vec<Placement>)**, one `Placement` per segment in the day's order, and
`state.last_plan_hash` stores it as sixteen lowercase hex digits.  What it digests was MEASURED
before anything here was written (README "Stage 6 — W-34, track H", with the probe that
printed each spelling from the fork's own crates):

* a `Placement` is the struct `{start, end, kind, energy, item, instance, planned_min,
  multiplier}` in that order, compact (`serde_json::to_string`), `null` for every `None`;
* `start`/`end` are `DateTime<Tz>`, which chrono 0.4.45 serialises through write_rfc3339(naive,
  offset, SecondsFormat::AutoSi, true): the **local** clock in the zone at that instant, whole
  seconds with no fraction (the kernel's rows are whole seconds), and the offset as `±HH:MM`
  rounded to the minute — or **`Z`** when it is exactly zero (allow_zulu).  The kernel's
  rows are on its own absolute seconds from 0001-01-01 and this converts through the request's
  zone table (`Cal.offsetAt`), never through the Unix epoch;
* `kind` is `SegKind` under #[serde(rename_all = "lowercase")]: `"block"`, `"break"`,
  `"winddown"` (not the wire's `wind-down`) and `{"batch":[ids]}` for a batch;
* `instance` is InstanceKey, externally tagged: `{"Date":"YYYY-MM-DD"}` or `{"Nth":n}`;
* `multiplier` is an `f64`, and serde_json 1.0.151 writes it with **zmij 1.0.23**, not ryu —
  the shortest digits, fixed notation for a first-digit exponent in `-5..=15`, else `1e-6` /
  `1.5e+17` with the exponent's sign ALWAYS written.  The kernel's multiplier is the exact
  decimal the host sent (D17: written_pair of the double's shortest Display), so its
  digits are the double's and only the layout is computed here (`multText`).

The digest is on `Nat` with `% hashBound` for the 64-bit wrap, not `UInt64`: probed at 8G/120 s
the whole of `PlannerWit.theRequest`'s day — planning included — digests by `decide +kernel` in
1.6 s at 1.1 GB, where `Nat.xor`, `Nat.mul` and `Nat.mod` are the kernel's GMP-accelerated
primitives and a `UInt64` step would go through `BitVec` and `Fin` first. -/

/-- **One byte of FNV-1a**: `h ^= byte; h = h.wrapping_mul(FNV_PRIME)`, with the fork's prime
`0x100000001b3` written in place — a named nullary `def` is emitted as a C global the compiled
step never reads, which check 12 would rightly call unreached.  The wrap is `% hashBound`, the
digest's own width (R10) — no second bound is minted. -/
def fnvStep (h : Nat) (b : UInt8) : Nat := (h ^^^ b.toNat) * 1099511628211 % hashBound

/-- **FNV-1a/64** over a byte string, from the fork's offset basis `0xcbf29ce484222325`
(`planner.rs`'s FNV_OFFSET, written in place for the same reason). -/
def fnv1a (bs : List UInt8) : Nat := bs.foldl fnvStep 14695981039346656037

/-- Every step stays under the width, so the digest is a `PlanHash`. -/
theorem fnvFold_lt : ∀ (bs : List UInt8) (h : Nat), h < hashBound →
    bs.foldl fnvStep h < hashBound
  | [], _, hh => hh
  | b :: bs, h, _ => fnvFold_lt bs (fnvStep h b) (Nat.mod_lt _ (by decide))

theorem fnv1a_lt (bs : List UInt8) : fnv1a bs < hashBound := fnvFold_lt bs _ (by decide)

/-- **The published FNV-1a/64 test vectors**, and the digest of the empty day `"[]"`: the empty
string is the offset basis, `"a"` is `af63dc4c8601ec8c`, and `"[]"` is `09612b07b5ecb5a5` —
each printed by the fork's own loop in the W-34 probe. -/
theorem fnv1a_test_vectors :
    fnv1a [] = 0xcbf29ce484222325 ∧
      fnv1a (['a'].flatMap String.utf8EncodeChar) = 0xaf63dc4c8601ec8c ∧
      fnv1a (['[', ']'].flatMap String.utf8EncodeChar) = 0x09612b07b5ecb5a5 := by decide

/-- **Fork `SegKind`'s serde spelling** (#[serde(rename_all = "lowercase")], measured): a unit
variant is its lowercased name — WindDown is `"winddown"`, which is NOT `PlanWire.kindName`'s
wire word — and `Batch(ids)` is the externally tagged `{"batch":[…]}`.  `ghost` is the kernel's
own row kind (the fork's is a `SegFlags` bit) and no row `dayRows` builds has it; it is spelled
`"ghost"`, a word no fork kind serialises to. -/
def serdeKind : SegKind → JVal
  | .block => .str ['b','l','o','c','k']
  | .batch ids => .obj [(['b','a','t','c','h'], .arr (ids.val.map JVal.str))]
  | .brk => .str ['b','r','e','a','k']
  | .routine => .str ['r','o','u','t','i','n','e']
  | .wall => .str ['w','a','l','l']
  | .rest => .str ['r','e','s','t']
  | .optional => .str ['o','p','t','i','o','n','a','l']
  | .windDown => .str ['w','i','n','d','d','o','w','n']
  | .sleep => .str ['s','l','e','e','p']
  | .lost => .str ['l','o','s','t']
  | .ghost => .str ['g','h','o','s','t']

/-- **Fork InstanceKey's serde spelling** — externally tagged, `{"Date":"YYYY-MM-DD"}` or
`{"Nth":n}` (measured).  A row's `inst` carries the key as the text the host (a routine
instance, InstanceKey::to_string) or the log (a replayed routine) wrote, and it is read by
`Recur.parseInstKey` — the kernel's one port of fork parse_instance_key, which is exactly what
fork `past_segments` calls on a logged `inst` — so a key it cannot read is `null` on both sides. -/
def serdeInstance : Option (Id × Id) → JVal
  | none => .null
  | some (_, k) =>
    match Recur.parseInstKey k with
    | none => .null
    | some (.date d) => .obj [(['D','a','t','e'], .str (Field.renderDate d))]
    | some (.nth n) => .obj [(['N','t','h'], .num n)]

/-- **serde_json 1.0.151's spelling of a multiplier** — zmij::Buffer::format_finite of the
double whose shortest digits are this exact decimal (the host sends exactly those digits, D17).
The value at `Look.capDen`'s eighteen places — the most a configured decimal carries (D17), so
the bound is reused, not minted — is `m`; `digitsOf m` has `n` digits and the first digit's
exponent is `n − 19`.  zmij writes fixed notation for an exponent in `-5..=15`
(FIXED_DEC_EXP, `lib.rs:320`: `n ∈ 14..=34` here) — the integer digits, a point, and the
fraction without its trailing zeros, or `0` — and otherwise the first digit, a point and the
rest only when there is a rest, `e`, the exponent's sign ALWAYS (`e+16`, `e-6`) and its digits.
Zero is `0.0`.  A value with more than eighteen places cannot come off the wire (the host
refuses it, kernel_capacity::plan_json); here it is read at its first eighteen. -/
def multText (q : Arith.Pos) : List Char :=
  let m := q.val.num * Look.capDen / q.val.den
  let ds := digitsOf m
  let sig := (ds.reverse.dropWhile (· == '0')).reverse
  if m = 0 then ['0', '.', '0']
  else if 14 ≤ ds.length ∧ ds.length ≤ 34 then
    digitsOf (m / Look.capDen) ++ '.' ::
      (match ((padTo 18 (m % Look.capDen)).reverse.dropWhile (· == '0')).reverse with
       | [] => ['0']
       | fs => fs)
  else
    sig.headD '0' :: ((if 1 < sig.length then '.' :: sig.tail else []) ++
      'e' :: (if 19 ≤ ds.length then '+' :: digitsOf (ds.length - 19)
              else '-' :: digitsOf (19 - ds.length)))

/-- **A row's instant as chrono serialises a `DateTime<Tz>`**: write_rfc3339(naive_local,
offset, SecondsFormat::AutoSi, true).  The pieces are `LogStamp`'s — the same local date and
clock, the same minute-rounded offset `renderStamp` writes — and the two options are the only
difference: whole seconds need no AutoSi fraction here, and allow_zulu writes `Z` for an
offset of exactly zero where `renderStamp` (the log's SecondsFormat::Secs, false) writes
`+00:00`.  `instantText_is_renderStamp_off_utc` says so. -/
def instantText (z : Cal.Tz) (sec : Nat) : List Char :=
  let o := Cal.offsetAt z ⟨sec, 0⟩
  let t := LogStamp.localDateTod ⟨sec, 0⟩ o
  t.1 ++ 'T' :: (Field.renderClock (LogStamp.clockOf t.2) ++ ':' ::
    (padTo 2 (t.2 % 60) ++ (if o.sec = 0 then ['Z'] else LogStamp.renderOffset o)))

/-- **One `Placement`, serialised** — fork Placement::of under serde_json::to_string: the
eight fields in declaration order, compact, `null` for `None`, strings through `jemit` (whose
escaping is serde_json's, `escOf`).  The marks, the note and the diagnostics are not digested
(the fork's docstring: they change with every `tm done`). -/
def placementText (z : Cal.Tz) (s : Seg) : List Char :=
  ['{','"','s','t','a','r','t','"',':'] ++ jemit (.str (instantText z s.start)) ++
  [',','"','e','n','d','"',':'] ++ jemit (.str (instantText z s.stop)) ++
  [',','"','k','i','n','d','"',':'] ++ jemit (serdeKind s.kind) ++
  [',','"','e','n','e','r','g','y','"',':'] ++
    jemit ((s.energy.map fun e => JVal.num e.val).getD .null) ++
  [',','"','i','t','e','m','"',':'] ++ jemit ((s.item.map JVal.str).getD .null) ++
  [',','"','i','n','s','t','a','n','c','e','"',':'] ++ jemit (serdeInstance s.inst) ++
  [',','"','p','l','a','n','n','e','d','_','m','i','n','"',':'] ++
    jemit ((s.planned.map JVal.num).getD .null) ++
  [',','"','m','u','l','t','i','p','l','i','e','r','"',':'] ++
    (s.mult.map multText).getD ['n','u','l','l'] ++ ['}']

/-- **The digested text**: serde_json::to_string(&Vec<Placement>), the rows in the day's
order. -/
def placementsText (z : Cal.Tz) (segs : List Seg) : List Char :=
  '[' :: (List.intercalate [','] (segs.map (placementText z)) ++ [']'])

/-- **Fork `DayPlan::hash`**: FNV-1a/64 of the placement text's UTF-8 bytes (core's
`String.utf8EncodeChar`, the one encoder). -/
def planDigest (z : Cal.Tz) (segs : List Seg) : PlanHash :=
  ⟨fnv1a ((placementsText z segs).flatMap String.utf8EncodeChar), fnv1a_lt _⟩

/-- **D28: this signature is total and stays total.**  There is no `dayPlan?`, no
`PlanRefusal` and no `Except` — the eleven single-run laws of §8.3 are proved over this shape
(G1), not gated behind a refusal.

**What it does today — §8.2 steps 1 to 7, all twelve of step 8's fields, and the hash.**  Its segments
are `dayRows` (`:6138`), the sort of six row lists: step 1's walls (`stepOneSegs`, `:1543`), placed where
the plan's own index puts them, §9's running interruption as an ad-hoc wall, the past half
replayed from this call's own run, and a `travel-day` wall's zeroing of the remaining budget;
step 2's routine instances placed mandatory-first inside their own windows or at a free `pref:`
anchor (`placeStep`, `:2391`; `placedRoutines`, `:2428`), the rest deferred to step 6; step 3's slots,
cut and energised on stage 5's own `Look.cutSlots` and `Look.energizeToday` (`todaySlots`,
`:2826`; `energisedSlots`, `:2835`); step 5's groups walked over the slots (`buildGroups`, `:4238`;
`assignStep`; `assignFold`, `:4577`; `assignedRows`); step 6's placing of what step 2 deferred
(`deferOne`, `:5115`; `deferWalk`, `deferFold`, with `finalRoutines` and `finalAssign` its two
projections and `dayRoutineSegs`, `:5923`, the rows it leaves); and step 7's `optionalRows` and
`restRows`, with the wind-down and sleep rows that close the day.  Its diagnostics are
`dayDiagnostics`, which fills all twelve of `Diagnostics`' fields since W-34 (ten since the W-33
merge of track P's seven writers; README gap 2511 closed, check 13 prints 12 written), and its
`planHash` is `planDigest` of its own rows in the request's zone — fork `DayPlan::hash`, byte for
byte (W-34).  Step 4 is not here by design (D34: no candidate fact is derived in the kernel — the
request carries §7's answers).

*(W-33 track A, README gap 2223, the THIRD time the sentence "steps 3 to 7 are not written
here" stood in this file while false: the module header said it and W-15 repaired it; it said
it again and W-32's track P repaired it; and this docstring, four lines below that repair, said
"Steps 3 to 7 are P3..P7 and none of them is written here" from the day P3 landed until now.
The line numbers above are of this commit and move with the file; re-derive them rather than
copy them, AGENTS §5.11.)* -/
def dayPlan (r : PlanReq) : DayPlan :=
  let rows := dayRows r
  { DayPlan.empty r.today r.window r.blockMin r.budgetBlocks with
    segments := rows
    diagnostics := dayDiagnostics r
    priorities := dayPriorities r
    planHash := planDigest r.tz (rows.map Subtype.val) }

/-! ### The digest the day carries (W-34 track H, P8's emitter)

P0 left the_plan_hash_is_a_placeholder_until_the_emitter_lands — `(dayPlan r).planHash =
PlanHash.zero` for every `r` — as the tripwire that stops compiling the day the emitter lands.
It stopped: that statement is **refuted** by
`PlannerWit.the_plan_hash_is_a_placeholder_until_the_emitter_lands_is_refuted`, on a computed
day whose digest is the fork's own `DayPlan::hash` of the same rows, and it is renamed to what
the day now carries, `dayPlan_planHash` (AGENTS §3.2; `Check.lean`'s W-34 banner records the
deletion).  The value is compared with the fork's on every generated day by
`tm/tests/planner_invariants.rs`' W-34 block, both ways: the kernel's digest of its own rows
against the fork's function over those rows, and against the fork's day ranked by the kernel's
own §7 answer (D53). -/

/-- **The day carries the digest of its own rows in its own zone.** -/
theorem dayPlan_planHash (r : PlanReq) :
    (dayPlan r).planHash = planDigest r.tz ((dayRows r).map Subtype.val) := rfl

/-- **Two requests that place the same rows in the same zone carry the same hash** — the fork's
"two plans that put the same items in the same slots hash the same, so a replan that moves
nothing is not logged as a replan" (`DayPlan::hash`'s docstring), as a law. -/
theorem dayPlan_planHash_is_a_function_of_the_rows (r r' : PlanReq) (hz : r.tz = r'.tz)
    (hrows : (dayRows r).map Subtype.val = (dayRows r').map Subtype.val) :
    (dayPlan r).planHash = (dayPlan r').planHash := by
  rw [dayPlan_planHash, dayPlan_planHash, hz, hrows]

/-- **The marks and the note are not digested** — fork `DayPlan::hash`: "Not hashed: … every
progress or display flag — `done`, `current`, `ghost`, `note`, `underused`, `hot`, `mandatory`,
`deferred`.  Those change with each `tm done` and at every block boundary." -/
theorem placementText_ignores_the_marks_and_the_note (z : Cal.Tz) (s : Seg) (f : SegFlags)
    (n : Option Note) : placementText z { s with flags := f, note := n } = placementText z s := rfl

/-- **Off UTC a row's instant is the log's stamp**: `instantText` and `LogStamp.renderStamp` are
chrono's one write_rfc3339 at two option pairs, and at a whole second and a non-zero offset
the options agree — so the digest adds no third spelling of a local clock. -/
theorem instantText_is_renderStamp_off_utc (z : Cal.Tz) (sec : Nat)
    (hi : Cal.Instant.wf ⟨sec, 0⟩ = true) (ho : (Cal.offsetAt z ⟨sec, 0⟩).wf = true)
    (h0 : (Cal.offsetAt z ⟨sec, 0⟩).sec ≠ 0) :
    instantText z sec = LogStamp.renderStamp ⟨⟨sec, 0⟩, hi⟩ ⟨Cal.offsetAt z ⟨sec, 0⟩, ho⟩ := by
  simp [instantText, LogStamp.renderStamp, h0]

/-- **chrono's spelling, both ways**: a Chicago row at `-05:00`, and the same instant in a zone
whose offset is exactly zero written `Z` — allow_zulu, the one option `renderStamp` does not
take.  Both strings were printed by chrono itself in the W-34 probe. -/
theorem instantText_spells_chrono :
    instantText Cal.chicago (Cal.instantOf Cal.chicago 739867 425).sec
        = "2026-09-09T07:05:00-05:00".toList ∧
      instantText Replay.utcZone (Cal.instantOf Cal.chicago 739867 425).sec
        = "2026-09-09T12:05:00Z".toList := by decide +kernel

/-- **zmij's spellings, value by value** — each right-hand side is serde_json::to_string of the
double, printed by the W-34 probe: the integer layout (`1.0`, `100.0`), the point inside
(`1.6`, `123.456`), the leading zeros (`0.25`, `0.00001`), the exponent below `-5` (`1e-6`,
`1.5e-6`, `1e-18`), the exponent above `15` with its `+` (`1e+16`, `1.5e+17`), zero, and a double
whose shortest digits are seventeen (`0.30000000000000004`). -/
theorem multText_is_zmijs :
    ([(1, 1), (16, 10), (25, 100), (100, 1), (1000, 1), (1, 1000000), (1, 100000),
      (15, 10000000), (0, 1), (10000000000000000, 1), (150000000000000000, 1),
      (1, 1000000000000000000), (123456, 1000), (30000000000000004, 100000000000000000)].map
        (fun p : Nat × Nat => (Arith.ofPair? p.1 p.2).map multText))
      = ["1.0", "1.6", "0.25", "100.0", "1000.0", "1e-6", "0.00001", "1.5e-6", "0.0", "1e+16",
         "1.5e+17", "1e-18", "123.456", "0.30000000000000004"].map (fun t => some t.toList) := by
  decide

/-- **Four rows, the fork's digest**: a furniture routine keyed by DATE, a scheduled routine
keyed by ORDINAL whose id carries a quote, a two-member batch sized at `1.6` and a block sized at
`0.000001`.  `33d70e1eb81d85ba` is fork `DayPlan::hash` of the same four `planner::Segment`s,
printed by the W-34 probe — `{"Date":"2026-09-09"}`, `{"Nth":3}`, `"a\"b"`,
`{"batch":["x1","x2"]}`, `1.6` and `1e-6` are each in the bytes both sides digest. -/
theorem the_placement_bytes_are_the_forks :
    (planDigest Cal.chicago
      [{ start := (Cal.instantOf Cal.chicago 739867 680).sec,
         stop := (Cal.instantOf Cal.chicago 739867 710).sec, kind := .routine, energy := none,
         item := some ['l','u','n','c','h'],
         inst := some (['l','u','n','c','h'], ['2','0','2','6','-','0','9','-','0','9']),
         flags := SegFlags.none, planned := some 30, mult := none, note := none },
       { start := (Cal.instantOf Cal.chicago 739867 720).sec,
         stop := (Cal.instantOf Cal.chicago 739867 740).sec, kind := .routine,
         energy := some 1, item := some ['a','"','b'], inst := some (['a','"','b'], ['#','3']),
         flags := SegFlags.none, planned := some 20, mult := none, note := none },
       { start := (Cal.instantOf Cal.chicago 739867 840).sec,
         stop := (Cal.instantOf Cal.chicago 739867 890).sec,
         kind := .batch ⟨[['x','1'], ['x','2']], by decide⟩, energy := some 4, item := none,
         inst := none, flags := SegFlags.none, planned := some 35,
         mult := some (Arith.mkPos 16 10 (by decide)), note := none },
       { start := (Cal.instantOf Cal.chicago 739867 900).sec,
         stop := (Cal.instantOf Cal.chicago 739867 950).sec, kind := .block, energy := some 3,
         item := some ['m','3'], inst := none, flags := SegFlags.none, planned := some 50,
         mult := some (Arith.mkPos 1 1000000 (by decide)), note := none }]).val
      = 0x33d70e1eb81d85ba := by decide +kernel

theorem dayPlan_day (r : PlanReq) : (dayPlan r).day = r.today := rfl

theorem dayPlan_window (r : PlanReq) : (dayPlan r).window = r.window := rfl

theorem dayPlan_blockMin (r : PlanReq) : (dayPlan r).blockMin = r.look.day.cut.blockMin := rfl

/-- **The day carries §8.1's budget, not the remaining one** — fork
`DayPlan::empty(date, window, budget_blocks)` (`planner.rs:1065`), where `remaining_budget` is a
*local* the assign loop and `diagnose` consume and never a field of the day.  Spec §8.3 words
the overbooking law with `remaining_budget`; the two disagree on a day with blocks already
done, and plan_does_not_overbook is §6.3's to restate at **P5** with that named. -/
theorem dayPlan_budgetBlocks (r : PlanReq) : (dayPlan r).budgetBlocks = r.budgetBlocks := rfl

/-- **The remaining budget is beside the day, not inside it** — what §8.2 step 5 will spend,
already zeroed by a travel day. -/
theorem dayPlan_remaining_budget_is_the_forks_local (r : PlanReq) :
    remainingBudget r ≤ (dayPlan r).budgetBlocks := remainingBudget_le_budget r

theorem dayPlan_segments (r : PlanReq) : (dayPlan r).segments = dayRows r := rfl

/-! ### The running break, as a row (W-35, D57 (1), parity P45)

Fork `planner::plan` reads no `runtime.break_`, and until W-35 neither did this kernel:
`RuntimeIn.brk` was decoded and read by nothing (README gap 2734), so a running break drew no row
and `tm plan` scheduled over it (README gap 2740).  §9 treats a Break as a RUNNING state (§9.2's
idle prompt fires only when *"no Block, Break, Routine, or Wall [is] running"*) and says *"Break
overran → next block starts now"*.  So `breakRows` is a Break row from where the break started to
its planned end — or to `now`, open, once it has overrun, which is what lets the next block start
at `now` — and its span joins `blockedByWalls`, so nothing §8.2 places lies over it; it pauses
the running block (`PlanReq.pauseRows`), so choice 5b reserves nothing while it runs. -/

/-- **The running break's row is a Break that reaches `now`**, from inside the day. -/
theorem breakRows_are_running_breaks (r : PlanReq) (s : Seg) (h : s ∈ breakRows r) :
    s.kind = SegKind.brk ∧ r.now.sec ≤ s.stop ∧ r.dayStart ≤ s.start ∧ s.start < s.stop := by
  unfold breakRows at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · rename_i hne
      simp only [List.mem_singleton] at h
      subst h
      exact ⟨rfl, Nat.le_max_right _ _, Nat.le_max_right _ _, Nat.lt_of_not_le hne⟩

/-- **Its span is blocked**, so everything §8.2 places flows around it: the reservation
(`Look.freeIntervals` over `blockedByWalls`), step 2's routines and step 3's cut. -/
theorem a_running_break_is_blocked (r : PlanReq) (s : Seg) (h : s ∈ breakRows r) :
    (s.start, s.stop) ∈ blockedByWalls r :=
  List.mem_append_right _ (List.mem_map.2 ⟨s, List.mem_append_right _ h, rfl⟩)

/-- **A running break pauses the running block** — `interrupted` reads it, so §8.2 choice 5b
reserves nothing while it runs, and the open row carries no `▶`. -/
theorem a_running_break_pauses_the_block (r : PlanReq) (s : Seg) (h : s ∈ breakRows r) :
    r.interrupted = true ∧ r.activeRun = none := by
  have hi : r.interrupted = true :=
    List.any_eq_true.2 ⟨s, List.mem_append_left _ (List.mem_append_right _ h),
      decide_eq_true (breakRows_are_running_breaks r s h).2.1⟩
  refine ⟨hi, ?_⟩
  unfold PlanReq.activeRun
  split
  · rfl
  · simp [hi]

/-- **The running break is not a Block, not a Batch, not a Wall and not the wind-down.** -/
theorem breakRows_are_not_work (r : PlanReq) (s : Seg) (h : s ∈ breakRows r) :
    s.kind ≠ SegKind.block ∧ (∀ ids, s.kind ≠ SegKind.batch ids) ∧ s.kind ≠ SegKind.wall ∧
      s.kind ≠ SegKind.windDown := by
  rw [(breakRows_are_running_breaks r s h).1]
  refine ⟨?_, fun _ => ?_, ?_, ?_⟩ <;> intro hc <;> cases hc

/-- **The set §8.2 step 8's A-capacity test reads is the day's own.**  `dayDiagnostics` cannot
write `assignedOf (dayPlan r)` — it is building the very day that set is read off — so it takes
`dayAssigned`, and this is the `rfl` that keeps the two from ever drifting apart.

**It exists because check 9 said it had to** (README gap 1001's second half): `dayAssigned`
came back **SURVIVED** from `mutate.py` at `:= default`, because on every witness day the only
day with high Rest assigns nothing, so replacing the set with `[]` changed no answer.
`PlannerWit.the_day_reports_its_lost_capacity_and_its_spent_budget` computes the set as well
as the number. -/
theorem assignedOf_dayPlan_is_dayAssigned (r : PlanReq) :
    assignedOf (dayPlan r) = dayAssigned r := rfl

/-- **The day's assigned set is step 1, the reservation and §8.2 step 5 — and nothing else.**
`assignedOf` keeps the rows `SegKind.isWork` accepts — Block and Batch and nothing else — a
Routine, WindDown, Sleep, Optional or Rest row is none of those, and `sortRows_filter` lets the
filter run *before* the sort.  So the rows §8.2 steps 2, 6 and 7 place can neither enter the
assigned set nor reorder it.

**RESTATED AT P9, and the old form is FALSE** (AGENTS §3.1 item 3, D50).  It read
`= … ((stepOneSegs r ++ reservationSegs r).map segOf) …` and was named
`assignedOf_dayPlan_is_step_one_the_reservation_and_step_five`; the assign fold emits rows now (README gap 803
item 4 closed, gap 1790), and `PlannerWit.the_assigned_set_is_not_the_reservations_alone` is
the computed day on which the two sides of the old equation differ.  The name moved with the
statement (AGENTS §5.2) and `Check.lean` records the deletion. -/
theorem assignedOf_dayPlan_is_step_one_the_reservation_and_step_five (r : PlanReq) :
    assignedOf (dayPlan r)
      = (sortRows (((stepOneSegs r ++ reservationSegs r ++ r.assignedRows).map segOf).filter
          (fun s => s.val.kind.isWork))).flatMap segItems := by
  unfold assignedOf
  rw [dayPlan_segments]
  unfold dayRows
  rw [sortRows_filter]
  have hnil : ((dayRoutineSegs r).map segOf).filter (fun s => s.val.kind.isWork) = [] := by
    refine List.filter_eq_nil_iff.2 (fun s hs => ?_)
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    rw [segOf_kind, routineRows_are_not_work r _ t ht]
    simp
  have hnilo : ((r.optionalRows).map segOf).filter (fun s => s.val.kind.isWork) = [] := by
    refine List.filter_eq_nil_iff.2 (fun s hs => ?_)
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
    rw [segOf_kind, r.optionalRows_are_not_work t ht]
    simp
  have hnilr : ((r.restRows).map segOf).filter (fun s => s.val.kind.isWork) = [] := List.filter_eq_nil_iff.2 (fun s hs => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs; rw [segOf_kind, r.restRows_are_not_work t ht]; simp)
  have hnilb : ((r.keptBreakRows).map segOf).filter (fun s => s.val.kind.isWork) = [] := List.filter_eq_nil_iff.2 (fun s hs => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs; rw [segOf_kind, r.keptBreakRows_are_not_work t ht]; simp)
  -- Step 1's rows reach the day in `emit_segments`' own order since W-38 (gap 3281), and that order moves only the
  -- running interruption, the running break and the walls — none of them work — so the filter sees `stepOneSegs`' rows.
  have hstep : ((stepOneOrder r).map segOf).filter (fun s => s.val.kind.isWork)
      = ((stepOneSegs r).map segOf).filter (fun s => s.val.kind.isWork) := by
    unfold stepOneOrder; split
    · rfl
    · exact Look.adhoc_walk_map_filter _ _ _ _ _ _ _ segOf _
        (fun t ht => by rw [segOf_kind, (interruptRows_are_open_lost_time r t ht).1]; rfl)
        (fun t ht => by rw [segOf_kind, (breakRows_are_running_breaks r t ht).1]; rfl)
        (fun x _ t ht => by rw [segOf_kind, (wallRows_are_walls_of_the_item _ x t ht).1]; rfl)
  -- Every other source the sort reads but step 1, the reservation and step 5 is empty under the filter (`hnil`…).
  simp only [List.map_append, List.filter_append, hstep, hnil, hnilo, hnilr, hnilb, List.append_nil,
    List.nil_append]

/-- **The day carries §8.2 step 4's answer** — fork `planner.rs:1066`, `day.priorities = cands
.zip(&prios)`.  P0 left it `Capped.nil`, which was true of a day with no step 4; it is step 4's
now. -/
theorem dayPlan_priorities (r : PlanReq) : (dayPlan r).priorities = dayPriorities r := rfl

/-- **The day carries §8.2 step 8's IMPOSSIBLE list**, and it is `PlanReq.dayImpossible` whole
(W-33, P8's first half). -/
theorem dayPlan_impossible (r : PlanReq) :
    (dayPlan r).diagnostics.impossible.val = r.dayImpossible :=
  dayDiagnostics_impossible r

theorem dayPlan_hot (r : PlanReq) : (dayPlan r).diagnostics.hot.val = r.dayHot :=
  dayDiagnostics_hot r

/-- **Fork `DayPlan::assigned_from`** (`planner.rs:647`): the items the day assigns at or after
an instant.  §8.3's laws are about *this* set and not about `assigned` — the proptest's own
`assigned_set(day, w.now)` says so (`planner_invariants.rs:470`: "the planner's doing and never
count as 'assigned' for §8.3"), because the replayed past holds Blocks that were worked and
that no replan can move. -/
def assignedFrom (d : DayPlan) (t : Nat) : List Id :=
  (d.segments.filter (fun s => s.val.kind.isWork && decide (t ≤ s.val.start))).flatMap segItems

/-- `assignedFrom`'s membership, in the shape `mem_assignedOf` has. -/
theorem mem_assignedFrom (d : DayPlan) (t : Nat) (i : Id) :
    i ∈ assignedFrom d t ↔
      ∃ s ∈ d.segments, s.val.kind.isWork = true ∧ t ≤ s.val.start ∧ i ∈ segItems s := by
  simp [assignedFrom, List.mem_flatMap, List.mem_filter, and_assoc]

/-- **P5 must delete this.**  Steps 1, 2 and 3 place seven kinds of row and exactly **one** of
them is a future assignment: §8.2 choice 5b's reservation.  The replayed past ends at `now`, the
running interruption ends at `now`, a Wall is not work, and neither is a Routine, a WindDown nor
a Sleep — so the set §8.3's laws are about holds the running block and nothing else, and no goal
that quantifies over an *assigned* Block may be discharged against this body (README gap 347).

**RESTATED AT STEP P3, and the old form is FALSE** (AGENTS §3.1 item 3).  It read
`assignedFrom (dayPlan r) r.now.sec = []` and was named
`the_day_assigns_nothing_after_now_until_the_assign_step_lands`; choice 5b's reservation is a
`SegKind.block` row starting exactly at `now`, so the day now assigns one item after `now` and
the empty-list form has a counterexample —
`PlannerWit.the_reserved_day_assigns_the_running_block` is it, computed.  The name moved with
the statement (AGENTS §5.2) and `Check.lean` records the deletion.

It is stated over `assignedFrom … now` and **not** over `assignedOf`, because a replayed past
Block *is* work and *is* in `assignedOf` — the fork counts it too (`DayPlan::assigned`), and a
tripwire that claimed otherwise would be false the moment the seam had anything to replay. -/
theorem the_day_assigns_after_now_the_running_block_and_what_step_five_chose (r : PlanReq)
    (i : Id) (h : i ∈ assignedFrom (dayPlan r) r.now.sec) :
    r.activeRun.map (·.id) = some i ∨ ∃ t ∈ r.assignedRows, i ∈ t.items := by
  obtain ⟨s, hs, hwk, hge, hi⟩ := (mem_assignedFrom _ _ i).1 h
  rw [dayPlan_segments] at hs
  obtain ⟨t, ht, rfl⟩ := mem_dayRows hs
  simp only [stepOneSegs, List.mem_append] at ht
  rcases ht with ((((((((ht | ht) | ht) | ht) | ht) | ht) | ht) | ht) | ht) | ht
  · obtain ⟨_, h2, h3⟩ := replayedRows_end_at_now r t ht
    have : (segOf t).val.start < r.now.sec := by
      show clampSec t.start < r.now.sec
      simp only [clampSec]; omega
    omega
  · have h2 : (segOf t).val.kind = SegKind.lost := by
      rw [segOf_kind, (interruptRows_are_open_lost_time r t ht).1]
    rw [h2] at hwk; exact absurd hwk (by simp [SegKind.isWork])
  · have h2 : (segOf t).val.kind = SegKind.brk := by
      rw [segOf_kind, (breakRows_are_running_breaks r t ht).1]
    rw [h2] at hwk; exact absurd hwk (by simp [SegKind.isWork])
  · simp only [List.mem_flatMap] at ht
    obtain ⟨x, _, hx⟩ := ht
    have h2 : (segOf t).val.kind = SegKind.wall := by
      rw [segOf_kind, (wallRows_are_walls_of_the_item (r.isTravelDay x.id) x t hx).1]
    rw [h2] at hwk; exact absurd hwk (by simp [SegKind.isWork])
  · rw [segOf_kind, routineRows_are_not_work r _ t ht] at hwk
    exact absurd hwk (by simp)
  · obtain ⟨q, hq, -, -, hkd, -, -, hit⟩ := r.mem_activeRow t ht
    refine Or.inl ?_
    rw [hq]
    unfold segItems Seg.items at hi
    rw [segOf_kind, hkd] at hi
    simp only [segOf_item, hit, Option.toList_some, List.mem_singleton] at hi
    simp [hi]
  · exact Or.inr ⟨t, ht, by unfold segItems at hi; rwa [segOf_items] at hi⟩
  · rw [segOf_kind, r.keptBreakRows_are_not_work t ht] at hwk
    exact absurd hwk (by simp)
  · rw [segOf_kind, r.optionalRows_are_not_work t ht] at hwk
    exact absurd hwk (by simp)
  · rw [segOf_kind, r.restRows_are_not_work t ht] at hwk
    exact absurd hwk (by simp)

/-! ### The two wall goals

`plan_places_no_block_over_a_wall` is **not discharged here** and must not be: steps 1 and 2
place no Block of their own, so the statement is about the replayed past alone and says nothing
about the planner.  The invariant it needs is already stage 5's
(`Look.day0_slots_avoid_the_walls`), and the goal becomes non-vacuous at **P5**; design §6.4's
row gives it to P1, and that row is wrong (README gap 347).

**DISCHARGED at W-17 (track G, `85305f8`) as `PlanCheck.plan_places_no_block_over_a_wall`, over
the Block rows that start at or after `now`; still not by this body, which is what the paragraph
above says.**  The form `Goals.lean` carried is FALSE and
`PlannerWit.plan_places_no_block_over_a_wall_as_stage_6_wrote_it_is_refuted` is the compiled
refutation; **four** of the eleven checkers still range over nothing on **any** day the planner
can produce, which is README gap 650 and is P5's, not this sentence's.  (This read *"five … on
a produced day"* until W-18's repair, and matched no reading of the census under any run: the
two questions the repo keeps apart are *at one request* — `PlannerWit`'s section 14 computes
**seven of eleven** with a subject at `theCensusRequest`, so four without — and *over every
`PlanReq`*, which is gap 650's four and is what this sentence is about.  The four are
`PlanCheck.no_block_row_of_the_day_carries_a_slot_energy_on_an_unassigned_day`,
`no_block_row_of_the_day_reaches_the_wind_down_on_an_unassigned_day`, `the_day_has_no_batch_row_on_an_unassigned_day` and
— until W-33 wrote the field and refuted it — the_day_names_no_impossible_item, whose
positive form is `the_day_names_every_item_whose_numbers_say_impossible_at_a_hot_bin`.)  (Banner owed by
README gap 653, paid at the W-17 land step.)

`plan_never_moves_a_wall` **is** non-vacuous here, and is **false as stage 6 wrote it**. -/

/-- **`plan_never_moves_a_wall` as stage 6 wrote it is REFUTED** (AGENTS §3.1 item 3, D5).

Two shapes break it and neither is an edge case.

1. **`buffer:`**.  Fork `emit_segments` (`planner.rs:1772-1786`) puts a *second* Wall row in
   front of the event, from `start − buffer:` to `start`, carrying the same item.  Its start
   is not the interval's start, so the old statement is false of it.
2. **A wall that crosses local midnight** is clipped to the day (fork `collect_walls`'
   `end.min(self.day_end)`), so its stop is not the interval's end either.

The witness is the rule this step places rows with, applied to a wall the plan can write.  It
is stated over `wallRows` — the function that decides where a row goes — because that is where
the falsity lives: **the request is irrelevant**, every `PlanReq` whose index holds this wall
plans it this way.  A witness that also loaded a plan and a run would say the same thing about
more machinery (README gap 348). -/
theorem plan_never_moves_a_wall_as_stage_6_wrote_it_is_refuted :
    ¬ (∀ (travel : Bool) (x : Look.WallIx) (s : Seg),
        s ∈ wallRows travel x → s.kind = SegKind.wall → s.item = some x.id →
        s.start = x.evLo ∧ s.stop = x.hi) := by
  intro h
  have hx : ({ start := 600, stop := 900, kind := .wall, energy := none,
               item := some (['g','1'] : Id), inst := none, flags := SegFlags.none,
               planned := none, mult := none,
               note := some (.bufferBefore ['g','1']) } : Seg)
      ∈ wallRows false ⟨['g','1'], 0, 0, 600, 900, 1200⟩ := by decide
  exact absurd (h false ⟨['g','1'], 0, 0, 600, 900, 1200⟩ _ hx rfl rfl).1 (by decide)

/-- **`plan_never_moves_a_wall` restated, and proved.**

The law wants: *a wall segment sits where its interval says, not where the planner found
room.*  What is true of **every** wall row is `a_wall_row_comes_from_the_index` below — both
ends come from the index entry and neither comes from the planner.  The exact equation the old
form asserted survives, unchanged in force, for the wall the old form was about: one with no
`buffer:` whose interval lies inside the day it is planned on.  Those two hypotheses are not a
restriction to a case where it happens to hold — they are the two things `buffer:` and the
day-clip do, named. -/
theorem plan_never_moves_a_wall (r : PlanReq) (w : WfSeg) (i : Id) (e : Entity)
    (a b : Field.DT)
    (hagree : r.wallsAgree = true)
    (hw : w ∈ (dayPlan r).segments) (hk : w.val.kind = SegKind.wall)
    (hi : w.val.item = some i)
    (hget : r.plan.val.store.get i = some e) (hsh : e.val.shape = Field.Shape.interval a b)
    (hnb : e.val.buffer = none)
    (hin : r.dayStart ≤ (Cal.instantOf r.tz a.day a.time).sec)
    (hout : (Cal.instantOf r.tz b.day b.time).sec ≤ r.dayEnd)
    (hfwd : (Cal.instantOf r.tz a.day a.time).sec < (Cal.instantOf r.tz b.day b.time).sec)
    (hcal : (Cal.instantOf r.tz b.day b.time).sec < LogStamp.yearEnd) :
    w.val.start = (Cal.instantOf r.tz a.day a.time).sec ∧
      w.val.stop = (Cal.instantOf r.tz b.day b.time).sec := by
  obtain ⟨t, ht, rfl⟩ := mem_dayRows (dayPlan_segments r ▸ hw)
  simp only [stepOneSegs, List.mem_append] at ht
  rcases ht with ((((((((ht | ht) | ht) | ht) | ht) | ht) | ht) | ht) | ht) | ht
  · exact absurd (segOf_kind t ▸ hk) (replayedRows_are_not_walls r t ht)
  · exact absurd (segOf_kind t ▸ hk) (interruptRows_are_not_walls r t ht)
  · exact absurd (segOf_kind t ▸ hk) (breakRows_are_not_work r t ht).2.2.1
  · simp only [List.mem_flatMap] at ht
    obtain ⟨x, hx, hrow⟩ := ht
    have hid : x.id = i := by
      have hit := (wallRows_are_walls_of_the_item (r.isTravelDay x.id) x t hrow).2
      rw [segOf_item, hit] at hi
      exact (Option.some.inj hi)
    obtain ⟨y, hy, hy1, hy2, hyc, hylt⟩ := mem_wallsToday hx
    have hyid : y.id = i := by rw [← hid, hyc, clipWall_id]
    have hwalls : r.look.walls = Look.wallIndex r.tz r.blockMin r.plan.val :=
      of_decide_eq_true hagree
    obtain ⟨j, f, hjf, hwoe⟩ := Look.mem_wallIndex.1 (hwalls ▸ hy)
    have hji : j = i := by
      rw [← hyid]; exact (Look.wallOfEntity_keeps_the_id _ _ _ _ _ _ hwoe).symm
    subst hji
    have hfe : f = e := Option.some.inj (hjf ▸ hget)
    subst hfe
    have hns : f.val.shape ≠ Field.Shape.none := by rw [hsh]; intro hc; cases hc
    have hes : effectiveShape r.plan.val j = Field.Shape.interval a b := by
      rw [effectiveShape_as_written r.plan.val j f hjf hns]; exact hsh
    obtain ⟨hev, hhi⟩ :=
      Look.wallOfEntity_evLo_is_the_written_start _ _ _ _ _ _ _ _ hes hwoe
    have hlo : y.lo = y.evLo :=
      Look.wallOfEntity_lo_is_evLo_without_a_buffer _ _ _ _ _ _ hnb hwoe
    have hclip : Look.clipWall r.dayStart r.dayEnd y = y :=
      clipWall_id_inside _ _ _ (by rw [hlo, hev]; exact hin) (by rw [hhi]; exact hout)
        (by omega) (by rw [hlo, hev, hhi]; omega)
    have hxy : x = y := hyc.trans hclip
    subst hxy
    have honly : t = { start := x.evLo, stop := x.hi, kind := .wall, energy := none,
                       item := some x.id, inst := none, flags := SegFlags.none,
                       planned := none, mult := none,
                       note := (if r.isTravelDay x.id then some Note.travelDayWall
                                else none) } := by
      simp only [wallRows, List.mem_append] at hrow
      rcases hrow with hr | hr
      · rw [if_neg (by omega)] at hr; cases hr
      · simpa using hr
    subst honly
    refine ⟨?_, ?_⟩
    · show clampSec x.evLo = _
      rw [hev]; exact clampSec_id _ (by omega)
    · show max (clampSec x.evLo) (clampSec x.hi) = _
      rw [hev, hhi, clampSec_id _ (by omega), clampSec_id _ hcal]
      omega
  · exact absurd (segOf_kind t ▸ hk) (routineRows_are_not_walls r _ t ht)
  · exact absurd (segOf_kind t ▸ hk) (reservationSegs_are_not_walls r t ht)
  · exact absurd (segOf_kind t ▸ hk) (r.assignedRows_are_not_walls t ht)
  · exact absurd (segOf_kind t ▸ hk) (r.keptBreakRows_are_not_walls t ht)
  · exact absurd (segOf_kind t ▸ hk) (r.optionalRows_are_not_walls t ht)
  · exact absurd (segOf_kind t ▸ hk) (r.restRows_are_not_walls t ht)

/-- **Both ends of every wall row come from the index, and neither comes from the planner** —
the sentence `plan_never_moves_a_wall` was written to protect, true of a buffered wall and of a
clipped one alike. -/
theorem a_wall_row_comes_from_the_index (r : PlanReq) (w : WfSeg)
    (hw : w ∈ (dayPlan r).segments) (hk : w.val.kind = SegKind.wall) :
    ∃ x ∈ r.look.walls, x.fromDay ≤ r.today ∧ r.today ≤ x.toDay ∧
      w.val.item = some x.id ∧
      ((w.val.start = clampSec (Look.clipWall r.dayStart r.dayEnd x).lo ∧
        w.val.stop = max (clampSec (Look.clipWall r.dayStart r.dayEnd x).lo)
          (clampSec (Look.clipWall r.dayStart r.dayEnd x).evLo)) ∨
       (w.val.start = clampSec (Look.clipWall r.dayStart r.dayEnd x).evLo ∧
        w.val.stop = max (clampSec (Look.clipWall r.dayStart r.dayEnd x).evLo)
          (clampSec (Look.clipWall r.dayStart r.dayEnd x).hi))) := by
  obtain ⟨t, ht, rfl⟩ := mem_dayRows (dayPlan_segments r ▸ hw)
  simp only [stepOneSegs, List.mem_append] at ht
  rcases ht with ((((((((ht | ht) | ht) | ht) | ht) | ht) | ht) | ht) | ht) | ht
  · exact absurd (segOf_kind t ▸ hk) (replayedRows_are_not_walls r t ht)
  · exact absurd (segOf_kind t ▸ hk) (interruptRows_are_not_walls r t ht)
  · exact absurd (segOf_kind t ▸ hk) (breakRows_are_not_work r t ht).2.2.1
  · simp only [List.mem_flatMap] at ht
    obtain ⟨c, hc, hrow⟩ := ht
    obtain ⟨x, hx, h1, h2, hxc, _⟩ := mem_wallsToday hc
    refine ⟨x, hx, h1, h2, ?_, ?_⟩
    · rw [segOf_item, (wallRows_are_walls_of_the_item (r.isTravelDay c.id) c t hrow).2, hxc,
        clipWall_id]
    · rw [← hxc]
      simp only [wallRows, List.mem_append] at hrow
      rcases hrow with hr | hr
      · split at hr
        · simp only [List.mem_singleton] at hr; subst hr; exact Or.inl ⟨rfl, rfl⟩
        · cases hr
      · simp only [List.mem_singleton] at hr; subst hr; exact Or.inr ⟨rfl, rfl⟩
  · exact absurd (segOf_kind t ▸ hk) (routineRows_are_not_walls r _ t ht)
  · exact absurd (segOf_kind t ▸ hk) (reservationSegs_are_not_walls r t ht)
  · exact absurd (segOf_kind t ▸ hk) (r.assignedRows_are_not_walls t ht)
  · exact absurd (segOf_kind t ▸ hk) (r.keptBreakRows_are_not_walls t ht)
  · exact absurd (segOf_kind t ▸ hk) (r.optionalRows_are_not_walls t ht)
  · exact absurd (segOf_kind t ▸ hk) (r.restRows_are_not_walls t ht)

/-- **Every Wall row sits inside a span the blocked list holds** — the half of §8.2 step 1 that
step 3 and choice 5b need: `blockedByWalls` really does hold every wall the day draws, run-up
row included (see its own note, README gap 552), and the span is not empty.  Unconditional: no
hypothesis about the plan, because the `max` in `blockedByWalls` is what an inverted `at:` would
otherwise cost.

Stated as a **containment** and not unit-by-unit, because a wall row can legitimately be *empty*
(an event whose start and end coincide) and an empty row covers no unit at all while still
having to be ordered against a Block. -/
theorem a_wall_row_sits_in_a_blocked_span (r : PlanReq) (w : WfSeg)
    (hw : w ∈ dayRows r) (hk : w.val.kind = SegKind.wall) :
    ∃ v ∈ blockedByWalls r, v.1 < v.2 ∧ clampSec v.1 ≤ w.val.start ∧ w.val.stop ≤ v.2 := by
  obtain ⟨t, ht, rfl⟩ := mem_dayRows hw
  have htk : t.kind = SegKind.wall := (segOf_kind t).symm.trans hk
  simp only [stepOneSegs, List.mem_append] at ht
  rcases ht with ((((((((ht | ht) | ht) | ht) | ht) | ht) | ht) | ht) | ht) | ht
  · exact absurd htk (replayedRows_are_not_walls r t ht)
  · exact absurd htk (interruptRows_are_not_walls r t ht)
  · exact absurd htk (breakRows_are_not_work r t ht).2.2.1
  · simp only [List.mem_flatMap] at ht
    obtain ⟨x, hx, hrow⟩ := ht
    have hspan : (x.lo, max x.evLo x.hi) ∈ blockedByWalls r :=
      List.mem_append_left _ (List.mem_map_of_mem hx)
    obtain ⟨y, -, -, -, hyc, hylt⟩ := mem_wallsToday hx
    have hle : x.lo ≤ x.evLo := by rw [hyc]; unfold Look.clipWall; simp only; omega
    refine ⟨(x.lo, max x.evLo x.hi), hspan, by simp only; omega, ?_, ?_⟩ <;>
      simp only [wallRows, List.mem_append] at hrow <;>
      rcases hrow with hr | hr
    · split at hr
      · simp only [List.mem_singleton] at hr; subst hr
        show clampSec x.lo ≤ clampSec x.lo
        exact Nat.le_refl _
      · cases hr
    · simp only [List.mem_singleton] at hr; subst hr
      show clampSec x.lo ≤ clampSec x.evLo
      simp only [clampSec]; omega
    · split at hr
      · simp only [List.mem_singleton] at hr; subst hr
        show max (clampSec x.lo) (clampSec x.evLo) ≤ max x.evLo x.hi
        simp only [clampSec]; omega
      · cases hr
    · simp only [List.mem_singleton] at hr; subst hr
      show max (clampSec x.evLo) (clampSec x.hi) ≤ max x.evLo x.hi
      simp only [clampSec]; omega
  · exact absurd htk (routineRows_are_not_walls r _ t ht)
  · exact absurd htk (reservationSegs_are_not_walls r t ht)
  · exact absurd htk (r.assignedRows_are_not_walls t ht)
  · exact absurd htk (r.keptBreakRows_are_not_walls t ht)
  · exact absurd htk (r.optionalRows_are_not_walls t ht)
  · exact absurd htk (r.restRows_are_not_walls t ht)

/-- **Every Break row of the day is replayed from the log, §9's running break, or a break of the
cut that work touches** — the third since W-37 (README gap **551** closed): fork
`emit_segments` draws `kept_breaks(breaks, slots, assign)` less those a routine took over, and
`PlanReq.keptBreakRows` is that list drawn.

**RESTATED AT W-37, and the old form is FALSE** (AGENTS §3.1 item 3, D5: a theorem that
described the hole is refuted and renamed when the hole closes).  It read
`(∃ t ∈ pastRows r, s = segOf t) ∨ ∃ t ∈ breakRows r, s = segOf t` and was named
a_break_row_is_replayed_or_the_running_break;
`PlannerWit.a_break_row_is_replayed_or_the_running_break_is_refuted` is the computed day holding a
Break row that is neither.  The old form implies the new one.  Its paragraph used to open
*"Steps 1, 2 and 3 place no break of their own … `assign` is **P5**'s"*; P5 landed the assign
fold and left the breaks it made keepable undrawn, and W-37 draws them.

**This paragraph used to end *"so `plan_places_no_block_over_a_break` stays in `Goals.lean`:
the break side of it is still vacuous over what the planner places"*, and both halves are now
false** (W-18 repair; the README copy of the same sentence was corrected by track G and this
one was not).  (a) The goal **left `Goals.lean` at `fc26630`** as a §3.1-item-3 discharge —
PlannerWit.plan_places_no_block_over_a_break_as_stage_6_wrote_it_is_refuted was the refutation (deleted at W-43, back
at W-44, withdrawn at the W-44 repair, README gap 4611); `PlanCheck.plan_places_no_block_over_a_break` stands.
(b) It was never vacuous *in that way*: the goal's Break rows are the **log's**, not the cut's,
so a_break_row_is_a_replayed_row was precisely what made the comparison have a subject — a
log that records a `break` while a block runs gives the day a Break row inside a Block row, and
**neither** row is the planner's doing, which is why the goal as written is false rather than
empty. -/
theorem a_break_row_is_replayed_running_or_kept (r : PlanReq) (s : WfSeg)
    (hs : s ∈ dayRows r) (hk : s.val.kind = SegKind.brk) :
    (∃ t ∈ pastRows r, s = segOf t) ∨ (∃ t ∈ breakRows r, s = segOf t) ∨
      ∃ t ∈ r.keptBreakRows, s = segOf t := by
  obtain ⟨t, ht, rfl⟩ := mem_dayRows hs
  have htk : t.kind = SegKind.brk := (segOf_kind t).symm.trans hk
  simp only [stepOneSegs, List.mem_append] at ht
  rcases ht with ((((((((ht | ht) | ht) | ht) | ht) | ht) | ht) | ht) | ht) | ht
  · -- the open row is a Block, so a Break comes from the closed half (W-34)
    rcases mem_replayedRows.1 ht with ht | ht
    · exact Or.inl ⟨t, ht, rfl⟩
    · rw [(openBlockRows_are_energyless_blocks r t ht).1] at htk; cases htk
  · rw [(interruptRows_are_open_lost_time r t ht).1] at htk; cases htk
  · exact Or.inr (Or.inl ⟨t, ht, rfl⟩)
  · simp only [List.mem_flatMap] at ht
    obtain ⟨x, _, hx⟩ := ht
    rw [(wallRows_are_walls_of_the_item (r.isTravelDay x.id) x t hx).1] at htk
    cases htk
  · rcases routineRows_kinds r _ t ht with h | h | h <;> rw [h] at htk <;> cases htk
  · rw [reservationSegs_are_blocks r t ht] at htk; cases htk
  · exact absurd htk (r.assignedRows_are_not_breaks t ht)
  · exact Or.inr (Or.inr ⟨t, ht, rfl⟩)
  · exact absurd htk (r.optionalRows_are_not_breaks t ht)
  · exact absurd htk (r.restRows_are_not_breaks t ht)

/-- **A WindDown row of the produced day starts at `[day] wind_down`, and only exists while the
wind-down is ahead of `now`.** -/
theorem a_wind_down_row_of_the_day (r : PlanReq) (w : WfSeg) (hw : w ∈ dayRows r)
    (hk : w.val.kind = SegKind.windDown) :
    r.now.sec < r.windDownSec ∧ w.val.start = clampSec r.windDownSec := by
  obtain ⟨t, ht, rfl⟩ := mem_dayRows hw
  have htk : t.kind = SegKind.windDown := (segOf_kind t).symm.trans hk
  simp only [stepOneSegs, List.mem_append] at ht
  rcases ht with ((((((((ht | ht) | ht) | ht) | ht) | ht) | ht) | ht) | ht) | ht
  · exact absurd htk (replayedRows_are_not_wind_down r t ht)
  · rw [(interruptRows_are_open_lost_time r t ht).1] at htk; cases htk
  · exact absurd htk (breakRows_are_not_work r t ht).2.2.2
  · simp only [List.mem_flatMap] at ht
    obtain ⟨x, _, hx⟩ := ht
    rw [(wallRows_are_walls_of_the_item (r.isTravelDay x.id) x t hx).1] at htk; cases htk
  · obtain ⟨h1, -, heq⟩ := a_wind_down_row_is_the_evenings r _ t ht htk
    exact ⟨h1, by show clampSec t.start = _; rw [heq]; rfl⟩
  · rw [reservationSegs_are_blocks r t ht] at htk; cases htk
  · exact absurd htk (r.assignedRows_are_not_wind_down t ht)
  · exact absurd htk (r.keptBreakRows_are_not_wind_down t ht)
  · exact absurd htk (r.optionalRows_are_not_wind_down t ht)
  · exact absurd htk (r.restRows_are_not_wind_down t ht)

/-- **Every Block row of the day is replayed from the log or is §8.2 choice 5b's reservation.**
Steps 1, 2 and 3 place walls, the running interruption, the replayed past, the routines, the
evening and the running block; a Wall is not a Block, an interruption is Lost time, and
`routineRows_are_not_blocks` covers the rest.  `PlanCheck` states the same fact over `dayPlan`
and this is the row-level half of it.

**RESTATED AT STEP P3, and the old form is FALSE** (AGENTS §3.1 item 3).  It read
`∃ t ∈ pastRows r, s = segOf t` and was named `a_block_row_is_a_replayed_row`; choice 5b's
reservation is a Block row the *planner* places, and
`PlannerWit.the_reserved_day_is_the_witness_day_and_the_running_block` exhibits one.  The old name is deleted and `Check.lean` records it.

**RESTATED AGAIN AT W-34, and the P3 form is FALSE** (AGENTS §3.1 item 3): its first disjunct
read `∃ t ∈ pastRows r` — the log's CLOSED half — and `openBlockRows` is a Block row of the log's
OPEN half, which is neither the reservation nor the fold's.
`PlannerWit.a_block_row_is_replayed_reserved_or_assigned_over_the_closed_rows_is_refuted` computes
the day it fails on.  The new disjunct is `replayedRows`, both halves; the old form implies it. -/
theorem a_block_row_is_replayed_reserved_or_assigned (r : PlanReq) (s : WfSeg)
    (hs : s ∈ dayRows r) (hk : s.val.kind = SegKind.block) :
    (∃ t ∈ replayedRows r, s = segOf t) ∨ (∃ t ∈ reservationSegs r, s = segOf t) ∨
      (∃ t ∈ r.assignedRows, s = segOf t) := by
  obtain ⟨t, ht, rfl⟩ := mem_dayRows hs
  have htk : t.kind = SegKind.block := (segOf_kind t).symm.trans hk
  simp only [stepOneSegs, List.mem_append] at ht
  rcases ht with ((((((((ht | ht) | ht) | ht) | ht) | ht) | ht) | ht) | ht) | ht
  · exact Or.inl ⟨t, ht, rfl⟩
  · rw [(interruptRows_are_open_lost_time r t ht).1] at htk; cases htk
  · rw [(breakRows_are_running_breaks r t ht).1] at htk; cases htk
  · simp only [List.mem_flatMap] at ht
    obtain ⟨x, _, hx⟩ := ht
    rw [(wallRows_are_walls_of_the_item (r.isTravelDay x.id) x t hx).1] at htk
    cases htk
  · exact absurd htk (routineRows_are_not_blocks r _ t ht)
  · exact Or.inr (Or.inl ⟨t, ht, rfl⟩)
  · exact Or.inr (Or.inr ⟨t, ht, rfl⟩)
  · exact absurd htk (r.keptBreakRows_are_not_blocks t ht)
  · exact absurd htk (r.optionalRows_are_not_blocks t ht)
  · exact absurd htk (r.restRows_are_not_blocks t ht)

/-! ### §8.3's E1 — `plan_reserves_one_block_at_a_time`, restated and DISCHARGED (step P3)

The goal as `Goals.lean` wrote it quantifies over **every** Block row of the produced day:

```lean
  theorem plan_reserves_one_block_at_a_time (r : PlanReq) (s : WfSeg)
      (hs : s ∈ (dayPlan r).segments) (hk : s.val.kind = SegKind.block) :
      s.val.stop - s.val.start ≤ (dayPlan r).blockMin * 60
```

**It is false**, and the reason is the one `PlanCheck`'s own header records as finding 1 (README
gap 385): the day's Block rows include the ones `Planner.pastRows` replays from the log, and *"a
Block the log holds can run longer than `block_min` … none of it the planner's doing, and none
of it anything a replan may move"*.  Shorten `[day] block_min` after a morning of longer blocks
and the day the planner produces has a Block row twice the length the law allows — which is a
fact about the log, not about the planner.  The witness is
`PlannerWit.plan_reserves_one_block_at_a_time_as_stage_6_wrote_it_is_refuted`, computed on a
request the builder accepts.

**Restated** the way the fork's own proptest restricts §8.3 (`planner_invariants.rs:470`:
`assigned_set(day, w.now)`, *"the planner's doing"*): over the Block rows that start **at or
after `now`**, which is exactly `Planner.assignedFrom`'s restriction and exactly the set
`the_day_assigns_after_now_the_running_block_and_what_step_five_chose` describes.  One R10 hypothesis comes with
it — the `[day]` is one `mkDayCfg?` would have built — and since W-41 (D78) a running block whose logged start is
after `now` adds its lead (its logged start less `now`) to the bound, where until then a hypothesis excluded it.

**It is not vacuous.**  §8.2 choice 5b's reservation is a Block row starting exactly at `now`,
and `PlannerWit.the_reserved_day_assigns_the_running_block` exhibits one. -/

/-- **§8.3's E1, over the rows §8.3 is about** — the goal `Goals.plan_reserves_one_block_at_a
_time` leaves this file for; since W-41 a block's lead past `now` (D78) rides on the reservation, and since the W-41 repair on the reservation ALONE — the row flagged `current` that carries the running item (§8.2 choice 5b's reservation, `PlanReq.activeRow_is_an_energyless_block`): every other Block row from `now` is at most one block (README gap 4136; until then the whole lead rode on EVERY Block row, so no law bounded a step-5 row at one block on a request whose clock is behind the log, though the proof bounded it there directly; `plan_reserves_one_block_at_a_time_off_the_running_row` at the end of this file). -/
theorem plan_reserves_one_block_at_a_time (r : PlanReq)
    (hday : r.dayAgrees = true) (s : WfSeg) (hs : s ∈ (dayPlan r).segments)
    (hk : s.val.kind = SegKind.block) (hnow : r.now.sec ≤ s.val.start) :
    s.val.stop - s.val.start ≤ (dayPlan r).blockMin * 60 + (if s.val.flags.current = true ∧ s.val.item = r.state.activeId then (r.state.active.map (fun a => a.started.sec - r.now.sec)).getD 0 else 0) := by
  rw [dayPlan_segments] at hs
  rcases a_block_row_is_replayed_reserved_or_assigned r s hs hk with
    ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · obtain ⟨-, h2, h3⟩ := replayedRows_end_at_now r t ht
    have hlt : (segOf t).val.start < r.now.sec := by
      show clampSec t.start < r.now.sec
      simp only [clampSec, LogStamp.yearEnd]; omega
    omega
  · obtain ⟨q, hq, hst, hsp, -, -, -, -⟩ := r.mem_activeRow t ht
    obtain ⟨-, -, -, hs0, hlt0, -⟩ := r.activeRun_spec q hq
    have hone := r.the_reservation_reaches_at_most_one_block_past_its_start q (r.blockMin_pos hday) hq
    have hbm : (dayPlan r).blockMin = r.blockMin := rfl
    have hstart : (segOf t).val.start = clampSec q.start := by
      show clampSec t.start = _; rw [hst]
    have hstop : (segOf t).val.stop = max (clampSec q.start) (clampSec q.stop) := by
      show max (clampSec t.start) (clampSec t.stop) = _; rw [hst, hsp]
    rw [hbm, hstart, hstop, if_pos ⟨(r.activeRow_is_an_energyless_block t ht).2.2.1, by rw [segOf_item]; exact (r.activeRow_is_an_energyless_block t ht).2.2.2.1⟩]
    rw [hstart] at hnow
    simp only [clampSec, LogStamp.yearEnd] at hnow ⊢
    omega
  · -- **§8.2 step 5's own rows**: a Block row spans its slot, and no slot is wider than one
    -- block (`PlanReq.a_slot_is_at_most_one_block`).  This case is what P9 added, and E1 is
    -- discharged over it rather than around it.
    obtain ⟨e, sl, hsl, hst, hsp, -⟩ := r.an_assigned_row_is_a_slot_of_the_day t ht
    have hbnd := r.a_slot_is_at_most_one_block sl (r.energised_slot_is_a_slot hsl)
    have hbm : (dayPlan r).blockMin = r.blockMin := rfl
    have hstart : (segOf t).val.start = clampSec t.start := rfl
    have hstop : (segOf t).val.stop = max (clampSec t.start) (clampSec t.stop) := rfl
    rw [hbm, hstart, hstop, hst, hsp]
    simp only [clampSec, LogStamp.yearEnd]
    omega

/-! ### The wind-down goal is NOT discharged here, and the reason is P1's

`Goals.plan_places_no_demanding_block_after_wind_down` quantifies over a **Block** row, and
design §14.2's P2 row says P2 discharges it.  **That row is wrong for the same reason §6.4's P1
row was** (README gap 347): step 2 places the WindDown row the law is *about*, but no Block, so
the statement is still vacuous over `dayPlan` and a discharge would be AGENTS §5.2's theorem
that compiles and means nothing.  What P2 owes it is the other half of its subject, and that is
what landed; the goal becomes real at **P5** (README gap 430).

The tripwire is `the_day_assigns_after_now_the_running_block_and_what_step_five_chose` above, which P5
must delete, plus the theorem below — the WindDown row now *exists*, so the half of the law that
is about the evening can be stated and proved outright. -/

/-- **The day has a wind-down row exactly when the wind-down is still ahead and inside the
day**, and it runs to bed.  Half of §8.2 step 2's "sleep and wind-down define the hard end of the
day", stated over the produced plan. -/
theorem the_wind_down_row_runs_to_bed (r : PlanReq)
    (h1 : r.now.sec < r.windDownSec) (h2 : r.windDownSec < r.dayEnd)
    (h3 : r.windDownSec < LogStamp.yearEnd) (h4 : min r.bedSec r.dayEnd < LogStamp.yearEnd) :
    ∃ w ∈ (dayPlan r).segments, w.val.kind = SegKind.windDown ∧
      w.val.start = r.windDownSec ∧ w.val.stop = min r.bedSec r.dayEnd := by
  have hseg : r.windDownSeg ∈ dayRoutineSegs r := by
    simp only [dayRoutineSegs, routineRows, List.mem_append]
    refine Or.inr ?_
    unfold PlanReq.eveningRows
    simp only [List.mem_append]
    exact Or.inl (by rw [if_pos ⟨h1, h2⟩]; exact List.mem_singleton_self _)
  refine ⟨segOf r.windDownSeg, ?_, segOf_kind _, ?_, ?_⟩
  · rw [dayPlan_segments]
    exact mem_sortRows.2
      (List.mem_map.2 ⟨_, List.mem_append_right _ hseg, rfl⟩)
    -- (the routines and the evening are the list's LAST piece since W-45, README gap 4623: one append on the
    -- right, where their place beside step 1 took five appends on the left.)
  · show clampSec r.windDownSec = _
    exact clampSec_id _ h3
  · show max (clampSec r.windDownSec) (clampSec (min r.bedSec r.dayEnd)) = _
    rw [clampSec_id _ h3, clampSec_id _ h4]
    have := the_night_is_in_order r
    omega

/-! ### The search, run rather than argued (AGENTS §5.2)

Every law above is a ∀ over a request; the witness below is `decide` over the placement's own
engine, so what step 2 does to a real evening is *run*.  It is stated over `earliestFree`, which
is where the decision lives — the request contributes only the blocked list. -/

/-- **`earliestFree`, run.**  A morning blocked 08:00-08:30 and 09:00-10:00 leaves 08:30-09:00
and 10:00-12:00 free: a half-hour routine takes 08:30 (the first stretch that fits), a
forty-five-minute one has to wait for 10:00 (the short stretch is skipped, not squeezed), and a
three-hour one does not fit at all and defers to step 6. -/
theorem the_earliest_free_position_is_run :
    earliestFree 28800 43200 1800 [(28800, 30600), (32400, 36000)] = some 30600 ∧
    earliestFree 28800 43200 2700 [(28800, 30600), (32400, 36000)] = some 36000 ∧
    earliestFree 28800 43200 10800 [(28800, 30600), (32400, 36000)] = none := by decide

/-- **And a stretch the evening closes is not free.**  `night()` is in the blocked list, so a
routine whose window runs past the wind-down is placed before it — the fork's
"before the wind-down if at all possible". -/
theorem the_evening_is_closed_to_a_routine :
    earliestFree 72000 79200 1800 [(75600, 165600)] = some 72000 ∧
    earliestFree 76000 79200 1800 [(75600, 165600)] = none := by decide

/-- **Every assigned row starts at or after `now`** — the clause that lets a row §8.2 step 5
placed join the set all three of §8.3's block-side comparisons are already stated over
(`plan_reserves_one_block_at_a_time`'s `hnow`, and `PlanCheck`'s two).

It is a fact about **step 3's cut** and not about the fold: `PlanReq.cutFrom` is
`min (max now window.1) window.2`, `PlanReq.a_slot_is_inside_the_window` puts every slot at or
after it, and a slot that is not empty cannot begin at the window's own end — so the `min` can
only be the `max`, and the `max` is at least `now`.  W-30, README gap **2021**. -/
theorem PlanReq.an_assigned_row_starts_at_or_after_now (r : PlanReq) (t : Seg)
    (h : t ∈ r.assignedRows) : r.now.sec ≤ t.start := by
  obtain ⟨e, s, hs, hst, -, -⟩ := r.an_assigned_row_is_a_slot_of_the_day t h
  obtain ⟨h1, h2, h3⟩ := r.a_slot_is_inside_the_window s (r.energised_slot_is_a_slot hs)
  unfold PlanReq.cutFrom at h1
  rw [hst]
  omega

/-! ############################################################################
## W-35 (track K): D57 — what the running break, overtime and a wall on `now` owe the day

Three §9 behaviours the fork gets wrong, fixed here before R3 (owner D57, README gap 2740), each a
registered divergence from fork 4748911: the running break is a Break row nothing is scheduled
over (**P45**), the running block keeps its block in overtime (**P46**), and a wall on `now`
pauses the running block (**P47**, the campaign's reading of §9's Interruption row).
############################################################################ -/

/-- **§8.2 choice 5b's reservation clears every span the blocked list holds** — it is placed in
the first free stretch of `[now, limit)` (`Look.freeIntervals` over `blockedByWalls`), so no unit
of it is blocked (`PlanReq.the_reservation_is_free_of_every_wall`), said of the raw span. -/
theorem PlanReq.the_reservation_clears_a_blocked_span (r : PlanReq) (q : ActiveRes)
    (hq : r.activeRun = some q) {v : Nat × Nat} (hv : v ∈ blockedByWalls r) :
    q.stop ≤ v.1 ∨ v.2 ≤ q.start ∨ v.2 ≤ v.1 := by
  obtain ⟨-, -, -, -, hs0, hlt, -⟩ := r.activeRun_spec q hq
  rcases Nat.lt_or_ge v.1 q.stop with h1 | h1
  · rcases Nat.lt_or_ge q.start v.2 with h2 | h2
    · rcases Nat.lt_or_ge v.1 v.2 with h3 | h3
      · exact absurd (⟨Nat.le_max_right _ _, by omega⟩ : v.1 ≤ max q.start v.1 ∧ max q.start v.1 < v.2)
          (r.the_reservation_is_free_of_every_wall q hq hv (Nat.le_max_left _ _) (by omega))
      · exact Or.inr (Or.inr h3)
    · exact Or.inr (Or.inl h2)
  · exact Or.inl h1

/-- **A slot step 3 cut clears every span the blocked list holds** —
`PlanReq.no_slot_touches_a_wall`, said of the raw span. -/
theorem PlanReq.a_slot_clears_a_blocked_span (r : PlanReq) (s : Look.Slot) (h : s ∈ r.todaySlots)
    {v : Nat × Nat} (hv : v ∈ blockedByWalls r) : s.stop ≤ v.1 ∨ v.2 ≤ s.start ∨ v.2 ≤ v.1 := by
  have hne := r.a_slot_is_not_empty s h
  rcases Nat.lt_or_ge v.1 s.stop with h1 | h1
  · rcases Nat.lt_or_ge s.start v.2 with h2 | h2
    · rcases Nat.lt_or_ge v.1 v.2 with h3 | h3
      · exact absurd (⟨Nat.le_max_right _ _, by omega⟩ : v.1 ≤ max s.start v.1 ∧ max s.start v.1 < v.2)
          (r.no_slot_touches_a_wall hv s h (Nat.le_max_left _ _) (by omega))
      · exact Or.inr (Or.inr h3)
    · exact Or.inr (Or.inl h2)
  · exact Or.inl h1

/-- **A Block row of the day clears the running break** (D57 (1), P45: *nothing is scheduled over
it*) — the reservation and every slot step 5 filled clear each span the blocked list holds, and
the running break's span is one (`a_running_break_is_blocked`).  A Block the log replays is the
log's, not the planner's, and owes it `hrep`. -/
theorem a_block_row_clears_the_running_break (r : PlanReq) (b : WfSeg) (hb : b ∈ dayRows r)
    (hbk : b.val.kind = SegKind.block) (u : Seg) (hu : u ∈ breakRows r)
    (hrep : ∀ t ∈ replayedRows r, b = segOf t → t.stop ≤ u.start ∨ u.stop ≤ t.start) :
    b.val.stop ≤ (segOf u).val.start ∨ (segOf u).val.stop ≤ b.val.start := by
  obtain ⟨-, -, -, hfwd⟩ := breakRows_are_running_breaks r u hu
  have hv := a_running_break_is_blocked r u hu
  have eu1 : (segOf u).val.start = clampSec u.start := rfl
  have eu2 : (segOf u).val.stop = max (clampSec u.start) (clampSec u.stop) := rfl
  rcases a_block_row_is_replayed_reserved_or_assigned r b hb hbk with
    ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · obtain ⟨-, h2, -⟩ := replayedRows_end_at_now r t ht
    have e1 : (segOf t).val.start = clampSec t.start := rfl
    have e2 : (segOf t).val.stop = max (clampSec t.start) (clampSec t.stop) := rfl
    rw [e1, e2, eu1, eu2]
    simp only [clampSec, LogStamp.yearEnd]
    rcases hrep t ht rfl with h | h <;> omega
  · obtain ⟨q, hq, hst, hsp, -, -, -, -⟩ := r.mem_activeRow t ht
    obtain ⟨-, -, -, -, hs0, hlt, -⟩ := r.activeRun_spec q hq
    have e1 : (segOf t).val.start = clampSec t.start := rfl
    have e2 : (segOf t).val.stop = max (clampSec t.start) (clampSec t.stop) := rfl
    rw [e1, e2, eu1, eu2, hst, hsp]
    simp only [clampSec, LogStamp.yearEnd]
    rcases r.the_reservation_clears_a_blocked_span q hq hv with h | h | h
    · have h' : q.stop ≤ u.start := h
      omega
    · have h' : u.stop ≤ q.start := h
      omega
    · have h' : u.stop ≤ u.start := h
      omega
  · obtain ⟨e, sl, hsl, hst, hsp, -⟩ := r.an_assigned_row_is_a_slot_of_the_day t ht
    have hslot := r.energised_slot_is_a_slot hsl
    have hne := r.a_slot_is_not_empty sl hslot
    have e1 : (segOf t).val.start = clampSec t.start := rfl
    have e2 : (segOf t).val.stop = max (clampSec t.start) (clampSec t.stop) := rfl
    rw [e1, e2, eu1, eu2, hst, hsp]
    simp only [clampSec, LogStamp.yearEnd]
    rcases r.a_slot_clears_a_blocked_span sl hslot hv with h | h | h
    · have h' : sl.stop ≤ u.start := h
      omega
    · have h' : u.stop ≤ sl.start := h
      omega
    · have h' : u.stop ≤ u.start := h
      omega

/-- **A Block row of the day from `now` clears the running break** — the planner's rows, with no
hypothesis at all: a Block the log replays ends before `now`, so none starts there. -/
theorem a_block_row_from_now_clears_the_running_break (r : PlanReq)
    (hnowcal : r.now.sec + 1 < LogStamp.yearEnd) (b : WfSeg) (hb : b ∈ dayRows r)
    (hbk : b.val.kind = SegKind.block) (hnow : r.now.sec ≤ b.val.start) (u : Seg)
    (hu : u ∈ breakRows r) :
    b.val.stop ≤ (segOf u).val.start ∨ (segOf u).val.stop ≤ b.val.start :=
  a_block_row_clears_the_running_break r b hb hbk u hu (fun t ht hbt => by
    obtain ⟨-, h2, h3⟩ := replayedRows_end_at_now r t ht
    have e1 : b.val.start = clampSec t.start := by rw [hbt]; rfl
    rw [e1] at hnow
    simp only [clampSec, LogStamp.yearEnd] at hnow hnowcal
    omega)

/-- **A Block row of the day clears every break the day keeps** (W-37 track R, README gap 551) —
with no hypothesis at all.  A Block the log replays ends at or before `now` and a kept break
starts at or after it (`PlanReq.a_kept_break_is_after_now`); §8.2 choice 5b's reservation is a
span the cut flowed around (`PlanReq.a_kept_break_clears_the_reservation`); and a Block step 5
filled is a slot of the same cut, which L3 never cuts across one of its own breaks
(`PlanReq.a_slot_clears_a_kept_break`).  `PlanCheck.noBlockOverABreak` reads the day's Break rows
through `a_break_row_is_replayed_running_or_kept`, and this is its third case. -/
theorem a_block_row_clears_a_kept_break (r : PlanReq) (b : WfSeg) (hb : b ∈ dayRows r)
    (hbk : b.val.kind = SegKind.block) (u : Seg) (hu : u ∈ r.keptBreakRows) :
    b.val.stop ≤ (segOf u).val.start ∨ (segOf u).val.stop ≤ b.val.start := by
  obtain ⟨k, hk, hus, hup, -⟩ := r.mem_keptBreakRows u hu
  obtain ⟨hnowk, hkne, -⟩ := r.a_kept_break_is_after_now k hk
  have eu1 : (segOf u).val.start = clampSec k.1 := by rw [← hus]; rfl
  have eu2 : (segOf u).val.stop = max (clampSec k.1) (clampSec k.2) := by rw [← hus, ← hup]; rfl
  rcases a_block_row_is_replayed_reserved_or_assigned r b hb hbk with
    ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · obtain ⟨-, h2, h3⟩ := replayedRows_end_at_now r t ht
    have e1 : (segOf t).val.start = clampSec t.start := rfl
    have e2 : (segOf t).val.stop = max (clampSec t.start) (clampSec t.stop) := rfl
    rw [e1, e2, eu1, eu2]
    simp only [clampSec, LogStamp.yearEnd]
    omega
  · obtain ⟨q, hq, hst, hsp, -, -, -, -⟩ := r.mem_activeRow t ht
    obtain ⟨-, -, -, -, hs0, hlt, -⟩ := r.activeRun_spec q hq
    have e1 : (segOf t).val.start = clampSec t.start := rfl
    have e2 : (segOf t).val.stop = max (clampSec t.start) (clampSec t.stop) := rfl
    rw [e1, e2, eu1, eu2, hst, hsp]
    simp only [clampSec, LogStamp.yearEnd]
    rcases r.a_kept_break_clears_the_reservation q hq k hk with h | h <;> omega
  · obtain ⟨e, sl, hsl, hst, hsp, -⟩ := r.an_assigned_row_is_a_slot_of_the_day t ht
    have hslot := r.energised_slot_is_a_slot hsl
    have hne := r.a_slot_is_not_empty sl hslot
    have e1 : (segOf t).val.start = clampSec t.start := rfl
    have e2 : (segOf t).val.stop = max (clampSec t.start) (clampSec t.stop) := rfl
    rw [e1, e2, eu1, eu2, hst, hsp]
    simp only [clampSec, LogStamp.yearEnd]
    rcases r.a_slot_clears_a_kept_break sl hslot k hk with h | h <;> omega

/-- **The worked stretch stops where the running break starts** (P45) — a break taken while the
log holds the block open pauses it there, as an interruption does. -/
theorem the_open_row_stops_where_the_running_break_starts (r : PlanReq) (t : Seg)
    (h : t ∈ openBlockRows r) (u : Seg) (hu : u ∈ breakRows r) (hlt : t.start < u.start) :
    t.stop ≤ u.start := by
  obtain ⟨b, s, -, -, hst, hstop, -⟩ := mem_openBlockRows h
  rw [hstop]
  rw [hst] at hlt
  exact openClip_le_start s.1.sec r.pauseRows _ u
    (List.mem_append_left _ (List.mem_append_right _ hu)) hlt

/-- **In OVERTIME the run ends at the free stretch's end or the block boundary** (D57 (2), P46):
fork `active_run` returns `None` once `est_min − worked` is zero, so its current row is the next
item's while the header reads *"94m of 60m"*; §8.2 choice 5b reserves the running block and step
5 says *"no preemption mid-block"*, so the kernel keeps the block it is in. -/
theorem PlanReq.activeStop_in_overtime (r : PlanReq) (a : ActiveBlock) (ivStop : Nat)
    (h0 : r.activeLeft a = 0) :
    r.activeStop a ivStop = min ivStop (r.currentBlockEnd a.started.sec) := by
  unfold PlanReq.activeStop
  rw [if_pos h0]

/-- **And outside overtime it is the fork's rule, unchanged.** -/
theorem PlanReq.activeStop_before_overtime (r : PlanReq) (a : ActiveBlock) (ivStop : Nat)
    (h0 : r.activeLeft a ≠ 0) :
    r.activeStop a ivStop =
      min (min (r.now.sec + 60 * r.activeLeft a) ivStop) (r.currentBlockEnd a.started.sec) := by
  unfold PlanReq.activeStop
  rw [if_neg h0]

/-- **A wall on `now` pauses the running block** (D57 (3), P47): `interrupted` reads its rows, so
§8.2 choice 5b reserves nothing — the fork's own `free_from > now` refusal already said so — and
the open row carries no `▶`, which the fork does draw, across the meeting. -/
theorem a_wall_on_now_pauses_the_block (r : PlanReq) (x : Look.WallIx) (hx : x ∈ wallsToday r)
    (hlo : x.lo ≤ r.now.sec) (hhi : r.now.sec < max x.evLo x.hi) : r.interrupted = true := by
  have hmem : ∀ w ∈ wallRows (r.isTravelDay x.id) x, w ∈ r.pauseRows := fun w hw =>
    List.mem_append_right _ (List.mem_flatMap.2
      ⟨x, List.mem_filter.2 ⟨hx, decide_eq_true ⟨hlo, hhi⟩⟩, hw⟩)
  have hev := hmem _ (the_event_row_is_the_event (r.isTravelDay x.id) x)
  unfold PlanReq.interrupted
  rw [List.any_eq_true]
  by_cases hb : x.lo < x.evLo ∧ r.now.sec ≤ x.evLo
  · refine ⟨{ start := x.lo, stop := x.evLo, kind := .wall, energy := none, item := some x.id,
               inst := none, flags := SegFlags.none, planned := none, mult := none,
               note := some (.bufferBefore x.id) }, hmem _ ?_, decide_eq_true hb.2⟩
    simp [wallRows, hb.1]
  · exact ⟨_, hev, decide_eq_true (by simp only; omega)⟩

/-- **The worked stretch stops where a wall on `now` starts** (P47) — the rows of a wall whose
blocked span covers `now` clip it as an interruption's does, so the stretch is not drawn across
the meeting that paused it. -/
theorem the_open_row_stops_where_a_wall_on_now_starts (r : PlanReq) (t : Seg)
    (h : t ∈ openBlockRows r) (x : Look.WallIx) (hx : x ∈ wallsToday r)
    (hlo : x.lo ≤ r.now.sec) (hhi : r.now.sec < max x.evLo x.hi) (w : Seg)
    (hw : w ∈ wallRows (r.isTravelDay x.id) x) (hlt : t.start < w.start) : t.stop ≤ w.start := by
  obtain ⟨b, s, -, -, hst, hstop, -⟩ := mem_openBlockRows h
  rw [hstop]
  rw [hst] at hlt
  exact openClip_le_start s.1.sec r.pauseRows _ w (List.mem_append_right _ (List.mem_flatMap.2
    ⟨x, List.mem_filter.2 ⟨hx, decide_eq_true ⟨hlo, hhi⟩⟩, hw⟩)) hlt

/-- **And the open row is not `▶` while a wall covers `now`** (P47). -/
theorem the_open_row_is_not_current_under_a_wall_on_now (r : PlanReq) (t : Seg)
    (h : t ∈ openBlockRows r) (x : Look.WallIx) (hx : x ∈ wallsToday r)
    (hlo : x.lo ≤ r.now.sec) (hhi : r.now.sec < max x.evLo x.hi) : t.flags.current = false := by
  rw [the_open_row_is_current_exactly_when_nothing_is_reserved_or_interrupted r t h,
    a_wall_on_now_pauses_the_block r x hx hlo hhi]
  simp

/-! ### Relocated at W-35, verbatim (README gap 2136)

Nothing in the package cites these three, and moving them here is what paid, line for line, for
`BreakPlace.word`, `breakRows` and `PlanReq.pauseRows` above the first check-9 pin site. -/

theorem mkActive?_accepts (a : ActiveBlock)
    (h : ActiveBlock.wf a = true) : (mkActive? a).map Subtype.val = some a := by
  unfold mkActive?
  rw [dif_pos h]
  rfl

/-- A request with nothing running agrees trivially. -/
theorem PlanReq.activeAgrees_of_none (r : PlanReq) (h : r.state.active = none) :
    r.activeAgrees = true := by unfold PlanReq.activeAgrees; rw [h]

/-- **A block the smart constructor accepted agrees** — the R10 obligation "a smart constructor
its decoder actually uses", stated so a decoder can discharge it. -/
theorem PlanReq.activeAgrees_of_mkActive? (r : PlanReq) (a : ActiveBlock) (w : WfActive)
    (h : r.state.active = some a) (hw : mkActive? a = some w) : r.activeAgrees = true := by
  unfold PlanReq.activeAgrees
  rw [h]
  unfold mkActive? at hw
  split at hw
  · assumption
  · exact absurd hw (by simp)

/-! ############################################################################
## W-36 (track K): D60 — IMPOSSIBLE ties at `p = 0` go by DUE DATE (parity P51)

The owner's D60 (README gap 2801, 2026-09-27): every IMPOSSIBLE item is HOT (`p = 0`), and §7.4's
key `(p, root line, own line)` ordered them by their place in the file while §7.3's pass computed
their grants by due date — so at `PlannerWit.theReversedTwoImpossibleRequest` the item whose grant
held the day's minutes (`^t1`, due today, lower in the file) was dropped for one whose grant is
tomorrow's (`^t3`).  The key now carries `Ranked.imp` after `p` (`rankedLe`, `GroupKey.nums`):
among `p = 0` answers with a positive shortfall, their `until` (`answerUntil`) and then their
request position, which is `Look.sortDueIx`'s order; those answers before every other `p = 0`
answer; and every pair with no such answer in it exactly where the fork put it
(`rankedLe_is_the_forks_off_the_impossible`).

**The mixed case is a campaign call, revisable.**  An order that sorts the impossible answers by
date and leaves every other `p = 0` answer in line order is not transitive — two impossible
answers and one other can form a cycle — so the impossible ones go FIRST among `p = 0`: of the two
ways to make the order total, the only one under which a `p = 0` item §7.3 served later can never
take a slot that an impossible item's grant was given today.

`PlanReq.a_wall_ranks_before_a_task` and `PlanReq.a_lower_p_ranks_first` are relocated here from
beside `PlanReq.rankedCands_sorted`, their statements unchanged and each proof citing the lemma
over the new order; moving them is what paid, line for line, for D60's three definitions above the
first check-9 pin site (README gap 2136).
############################################################################ -/

/-- **Walls first**, over the order step 5 sorts by — `candKeyLe_notWall` over `rankedLe`. -/
theorem rankedLe_notWall {a b : Ranked} (h : rankedLe a b = true) :
    (if a.key.notWall then 1 else 0) ≤ (if b.key.notWall then (1 : Nat) else 0) :=
  (natsLe_cons_le h).1

/-- **Then `p`**, between two entries of one kind — `candKeyLe_p` over `rankedLe`. -/
theorem rankedLe_p {a b : Ranked} (h : rankedLe a b = true) (hw : a.key.notWall = b.key.notWall) :
    a.key.p ≤ b.key.p :=
  (natsLe_cons_le ((natsLe_cons_le h).2 (by rw [hw]))).1

/-- **A wall is ranked before every task** — §8.2 step 1 places them and step 5 never competes
with one.  Stated the way sortedness gives it: a wall cannot stand after a non-wall. -/
theorem PlanReq.a_wall_ranks_before_a_task (r : PlanReq) (i j : Nat)
    (hi : i < r.rankedCands.length) (hj : j < r.rankedCands.length) (hij : i < j)
    (hw : r.rankedCands[j].out.out.cand.wall = true) :
    r.rankedCands[i].out.out.cand.wall = true := by
  have hp := List.pairwise_iff_getElem.mp (PlanReq.rankedCands_sorted r) i j hi hj hij
  have hki := (PlanReq.a_ranked_entry_carries_its_answers_facts (List.getElem_mem hi)).1
  have hkj := (PlanReq.a_ranked_entry_carries_its_answers_facts (List.getElem_mem hj)).1
  cases hc : r.rankedCands[i].out.out.cand.wall with
  | true => rfl
  | false =>
    have hle := rankedLe_notWall (a := r.rankedCands[i]) (b := r.rankedCands[j]) hp
    rw [hki, hkj, hc, hw] at hle
    exact absurd hle (by simp)

/-- **A lower `p` is ranked first, among candidates of the same kind** — §7.4's first
component, stated over the produced order.  This is the half `plan_is_monotone_in_rank` rests
on and the half a wrong `p` breaks. -/
theorem PlanReq.a_lower_p_ranks_first (r : PlanReq) (i j : Nat)
    (hi : i < r.rankedCands.length) (hj : j < r.rankedCands.length) (hij : i < j)
    (hw : r.rankedCands[i].out.out.cand.wall = r.rankedCands[j].out.out.cand.wall) :
    r.rankedCands[i].out.out.p.getD 7 ≤ r.rankedCands[j].out.out.p.getD 7 := by
  have hp := List.pairwise_iff_getElem.mp (PlanReq.rankedCands_sorted r) i j hi hj hij
  obtain ⟨hwi, hpi, -, -⟩ := PlanReq.a_ranked_entry_carries_its_answers_facts (List.getElem_mem hi)
  obtain ⟨hwj, hpj, -, -⟩ := PlanReq.a_ranked_entry_carries_its_answers_facts (List.getElem_mem hj)
  rw [← hpi, ← hpj]
  exact rankedLe_p (a := r.rankedCands[i]) (b := r.rankedCands[j]) hp
    (by rw [hwi, hwj, hw])

/-- A shared prefix decides nothing. -/
theorem natsLe_append_same : ∀ (c r r' : List Nat), natsLe (c ++ r) (c ++ r') = natsLe r r'
  | [], _, _ => rfl
  | x :: c, r, r' => by
    show natsLe (x :: (c ++ r)) (x :: (c ++ r')) = natsLe r r'
    rw [natsLe_cons, if_neg (Nat.lt_irrefl x), if_neg (Nat.lt_irrefl x)]
    exact natsLe_append_same c r r'

/-- **Two blocks of one length: the first decides first** — if `xs ++ r` is at most `ys ++ r'`
and the blocks have one length, `xs` is at most `ys`. -/
theorem natsLe_of_append : ∀ (xs ys r r' : List Nat), xs.length = ys.length →
    natsLe (xs ++ r) (ys ++ r') = true → natsLe xs ys = true
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => absurd h (by simp)
  | _ :: _, [], _, _, h, _ => absurd h (by simp)
  | x :: xs, y :: ys, r, r', hl, h => by
    have h' : natsLe (x :: (xs ++ r)) (y :: (ys ++ r')) = true := h
    rw [natsLe_cons] at h'
    rw [natsLe_cons]
    by_cases h1 : x < y
    · rw [if_pos h1]
    · rw [if_neg h1] at h' ⊢
      by_cases h2 : y < x
      · rw [if_pos h2] at h'; exact absurd h' (by simp)
      · rw [if_neg h2] at h' ⊢
        exact natsLe_of_append xs ys r r' (by simpa using hl) h'

/-- **`Ranked.imp`, spelled**: an entry carries D60's component exactly when its `p` is `0` and its
shortfall positive, and the component is its `until` and its request position. -/
theorem Ranked.imp_eq_some_iff (x : Ranked) (u i : Nat) :
    x.imp = some (u, i) ↔
      x.key.p = 0 ∧ 0 < x.out.shortfall ∧ answerUntil x.out = some u ∧ i = x.key.ix := by
  unfold Ranked.imp
  by_cases h : x.key.p = 0 ∧ 0 < x.out.shortfall
  · rw [if_pos h]
    cases hu : answerUntil x.out with
    | none => simp
    | some v =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨rfl, rfl⟩; exact ⟨h.1, h.2, rfl, rfl⟩
      · rintro ⟨-, -, rfl, rfl⟩; exact ⟨rfl, rfl⟩
  · rw [if_neg h]
    constructor
    · intro hc; cases hc
    · rintro ⟨h1, h2, -, -⟩; exact absurd ⟨h1, h2⟩ h

/-- **Every `p = 0` entry with a positive shortfall carries the component** — the date is never
absent where the shortfall is positive (`PlanReq.a_short_answer_has_an_until`). -/
theorem Ranked.imp_isSome (x : Ranked) (hp : x.key.p = 0) (hs : 0 < x.out.shortfall) :
    x.imp.isSome = true := by
  unfold Ranked.imp
  rw [if_pos ⟨hp, hs⟩]
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (PlanReq.a_short_answer_has_an_until x.out hs)
  rw [hu]
  rfl

/-- What `impNums` ordering an entry at or before an impossible one says: it is impossible too,
dated no later, and at one date no later in the request. -/
theorem impNums_le_some {x : Option (Nat × Nat)} {u i : Nat}
    (h : natsLe (impNums x) (impNums (some (u, i))) = true) :
    ∃ u' i', x = some (u', i') ∧ (u' < u ∨ (u' = u ∧ i' ≤ i)) := by
  cases x with
  | none => exact absurd h (by simp [impNums, natsLe])
  | some v =>
    obtain ⟨u', i'⟩ := v
    refine ⟨u', i', rfl, ?_⟩
    have h1 := (natsLe_cons_le h).2 rfl
    rcases Nat.lt_or_ge u' u with hl | hl
    · exact Or.inl hl
    · have h2 := natsLe_cons_le h1
      have he : u' = u := by omega
      exact Or.inr ⟨he, (natsLe_cons_le (h2.2 he)).1⟩

/-- **D60's law, over the order**: between two entries of one kind and one `p`, an entry ordered
at or before an IMPOSSIBLE one is impossible too, dated no later, and at one date no later in the
request. -/
theorem rankedLe_impossible_by_until {a b : Ranked} (h : rankedLe a b = true)
    (hw : a.key.notWall = b.key.notWall) (hp : a.key.p = b.key.p) {u i : Nat}
    (hb : b.imp = some (u, i)) :
    ∃ u' i', a.imp = some (u', i') ∧ (u' < u ∨ (u' = u ∧ i' ≤ i)) := by
  have h1 := (natsLe_cons_le h).2 (by rw [hw])
  have h2 := (natsLe_cons_le h1).2 hp
  have h3 : natsLe (impNums a.imp) (impNums b.imp) = true :=
    natsLe_of_append _ _ _ _ (by cases a.imp <;> cases b.imp <;> rfl)
      (by simpa only [List.append_assoc] using h2)
  rw [hb] at h3
  exact impNums_le_some h3

/-- **Everything else is where the fork put it**: between two entries neither of which is a
`p = 0` impossible answer, the order is `candKeyLe` — fork `priority::sorted_candidates`' tuple,
unchanged by D60. -/
theorem rankedLe_is_the_forks_off_the_impossible (a b : Ranked) (ha : a.imp = none)
    (hb : b.imp = none) : rankedLe a b = candKeyLe a.key b.key := by
  unfold rankedLe candKeyLe CandKey.nums
  simp only [ha, hb]
  simp only [List.append_assoc, natsLe_cons, natsLe_append_same]

/-- **D60 over the produced order**: in §7.4's ranking, an entry ranked before an IMPOSSIBLE
entry of its own kind is impossible too, dated no later, and at one date no later in the request
— §7.3's served order among them (`Look.sortDueIx`). -/
theorem PlanReq.an_earlier_due_impossible_item_ranks_first (r : PlanReq) (i j : Nat)
    (hi : i < r.rankedCands.length) (hj : j < r.rankedCands.length) (hij : i < j)
    (hw : r.rankedCands[i].out.out.cand.wall = r.rankedCands[j].out.out.cand.wall) {u ix : Nat}
    (hb : r.rankedCands[j].imp = some (u, ix)) :
    ∃ u' ix', r.rankedCands[i].imp = some (u', ix') ∧ (u' < u ∨ (u' = u ∧ ix' ≤ ix)) := by
  have hs := List.pairwise_iff_getElem.mp (PlanReq.rankedCands_sorted r) i j hi hj hij
  obtain ⟨hwi, -, -, -⟩ := PlanReq.a_ranked_entry_carries_its_answers_facts (List.getElem_mem hi)
  obtain ⟨hwj, -, -, -⟩ := PlanReq.a_ranked_entry_carries_its_answers_facts (List.getElem_mem hj)
  have hwk : r.rankedCands[i].key.notWall = r.rankedCands[j].key.notWall := by rw [hwi, hwj, hw]
  have hpj0 : r.rankedCands[j].key.p = 0 := ((Ranked.imp_eq_some_iff _ u ix).1 hb).1
  have hple := rankedLe_p hs hwk
  exact rankedLe_impossible_by_until hs hwk (by omega) hb

/-- `minGroupKey` answers its seed or one of the members' keys. -/
theorem minGroupKey_mem : ∀ (l : List Ranked) (k : GroupKey),
    minGroupKey k l = k ∨ ∃ y ∈ l, minGroupKey k l = groupKeyOf y
  | [], _ => Or.inl rfl
  | x :: xs, k => by
    unfold minGroupKey
    by_cases h : groupKeyLe (groupKeyOf x) k = true
    · rw [if_pos h]
      rcases minGroupKey_mem xs (groupKeyOf x) with h' | ⟨y, hy, h'⟩
      · exact Or.inr ⟨x, List.mem_cons_self .., h'⟩
      · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, h'⟩
    · rw [if_neg h]
      rcases minGroupKey_mem xs k with h' | ⟨y, hy, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, h'⟩

/-- **A group's key is one of its members' keys** — the minimum is attained, so D60's component
of a group is one member's. -/
theorem PlanReq.a_group_key_is_a_members {r : PlanReq} {g : Group} (hg : g ∈ r.buildGroups) :
    ∃ y ∈ g.members, g.key = groupKeyOf y := by
  obtain ⟨b, hb, e, he, hgo⟩ := PlanReq.mem_rawGroups (PlanReq.mem_buildGroups.1 hg)
  have hm := (groupOf_members hgo).1
  cases hl : e.2 with
  | nil => rw [hl] at hgo; simp [groupOf] at hgo
  | cons z zs =>
    have hk : g.key = minGroupKey (groupKeyOf z) zs := by
      rw [hl] at hgo; simp only [groupOf, Option.some.injEq] at hgo; rw [← hgo]
    rw [hm, hl]
    rcases minGroupKey_mem zs (groupKeyOf z) with h' | ⟨y, hy, h'⟩
    · exact ⟨z, List.mem_cons_self .., hk.trans h'⟩
    · exact ⟨y, List.mem_cons_of_mem _ hy, hk.trans h'⟩

/-- **D60 over the groups the cursor walks**: a group sorted before a group keyed by an IMPOSSIBLE
member is keyed by an impossible member too, dated no later, and at one date no later in the
request — so at a slot both fit, step 5's first-fit gives it to the earlier-dated. -/
theorem PlanReq.an_earlier_due_impossible_group_is_walked_first (r : PlanReq) (i j : Nat)
    (hi : i < r.buildGroups.length) (hj : j < r.buildGroups.length) (hij : i < j) {u ix : Nat}
    (hb : r.buildGroups[j].key.imp = some (u, ix)) :
    ∃ u' ix', r.buildGroups[i].key.imp = some (u', ix') ∧ (u' < u ∨ (u' = u ∧ ix' ≤ ix)) := by
  have hs := List.pairwise_iff_getElem.mp (PlanReq.buildGroups_sorted r) i j hi hj hij
  obtain ⟨y, -, hy⟩ := PlanReq.a_group_key_is_a_members (List.getElem_mem hj)
  generalize r.buildGroups[i] = gi at hs ⊢
  generalize r.buildGroups[j] = gj at hs hb hy
  have hyimp : y.imp = some (u, ix) := by rw [← hb, hy]; rfl
  have hp0 : gj.key.p = 0 := by rw [hy]; exact ((Ranked.imp_eq_some_iff y u ix).1 hyimp).1
  unfold groupLe groupKeyLe GroupKey.nums at hs
  have hpi := (natsLe_cons_le hs).1
  have h2 := (natsLe_cons_le hs).2 (by omega)
  have h3 : natsLe (impNums gi.key.imp) (impNums gj.key.imp) = true :=
    natsLe_of_append _ _ _ _ (by cases gi.key.imp <;> cases gj.key.imp <;> rfl)
      (by simpa only [List.append_assoc] using h2)
  rw [hb] at h3
  exact impNums_le_some h3
/-! ############################################################################
## W-36 (track K): D58's kernel half — the what-if reads the HOST's grown facts (gap 2873)

The owner's D58 (README gap 2680): fork `PlanOverrides::apply` grows the extended candidate's
`remaining_min` and `planned_min` — and `need_min`, which the with-ranking day never reads (W-35's
measurement, README gap 2873) — and the host computes them with the two functions
`collect_candidates` derives the originals with (`planwire::grown`).  The kernel's what-if reads
them: `PlanReq.growing` puts them on every candidate record the extension names, and
`overtimeDiff` plans the grown request.  Nothing here derives a candidate fact (D34): the two
numbers are the host's, as sent, bounded by the width `PlanFacts.wf` already holds them to.
`needMin` is not decoded: no reader of the day reads a need but §7.3's pass, and the pass derives
its own from `remaining` (R1) — README gap 3004 says what that costs and what closes it.
############################################################################ -/

/-- **The host's grown facts for one candidate** (D58): fork `PlanOverrides::apply`'s
`remaining_min` and `planned_min`, as `planwire::grown` computed them. -/
structure GrownFacts where
  remaining  : Nat
  plannedMin : Nat
deriving DecidableEq, Repr

/-- R10: both within the fork's `u32` — `Look.maxPlanMinutes`, the width `PlanFacts.wf` and the
candidate section's `remaining` are already held to, reused and not re-minted. -/
def GrownFacts.wf (g : GrownFacts) : Bool :=
  decide (g.remaining ≤ Look.maxPlanMinutes) && decide (g.plannedMin ≤ Look.maxPlanMinutes)

abbrev WfGrown : Type := { g : GrownFacts // g.wf = true }

/-- The smart constructor the decoder uses (`PlanWire.readGrown`).  Nothing is clamped. -/
def mkGrown? (g : GrownFacts) : Option WfGrown := if h : g.wf = true then some ⟨g, h⟩ else none

theorem mkGrown?_refuses_a_remaining_past_the_width (g : GrownFacts)
    (h : Look.maxPlanMinutes < g.remaining) : mkGrown? g = none := by
  have hn : ¬ g.wf = true := by
    simp only [GrownFacts.wf, Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro h1; omega
  unfold mkGrown?
  rw [dif_neg hn]

theorem mkGrown?_refuses_planned_minutes_past_the_width (g : GrownFacts)
    (h : Look.maxPlanMinutes < g.plannedMin) : mkGrown? g = none := by
  have hn : ¬ g.wf = true := by
    simp only [GrownFacts.wf, Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro _; omega
  unfold mkGrown?
  rw [dif_neg hn]

theorem mkGrown?_accepts (g : GrownFacts) (h : g.wf = true) :
    (mkGrown? g).map Subtype.val = some g := by
  unfold mkGrown?
  rw [dif_pos h]
  rfl

/-- **A candidate's nine facts with the planned minutes replaced stay well-formed** when the new
minutes are within `PlanFacts.wf`'s bound: every other clause reads a field the change keeps. -/
theorem planFacts_wf_with_plannedMin (f : Look.PlanFacts) (hf : f.wf = true) (m : Nat)
    (hm : m ≤ Look.maxPlanMinutes) : Look.PlanFacts.wf { f with plannedMin := m } = true := by
  unfold Look.PlanFacts.wf at hf ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hf ⊢
  exact ⟨⟨⟨⟨hm, hf.1.1.1.2⟩, hf.1.1.2⟩, hf.1.2⟩, hf.2⟩

/-- **One candidate, grown**: its `remaining` and its planned minutes are the host's; every other
fact — id, `ci`, `!k`, due, the flags, and the other eight of the nine — is kept. -/
def growCand (c : Look.Cand) (g : WfGrown) : Look.Cand :=
  { c with remaining := g.val.remaining }.withPlan
    ⟨{ c.plan.val with plannedMin := g.val.plannedMin },
     planFacts_wf_with_plannedMin _ c.plan.property _ (by
       have := g.property
       simp only [GrownFacts.wf, Bool.and_eq_true, decide_eq_true_eq] at this
       exact this.2)⟩

theorem growCand_remaining (c : Look.Cand) (g : WfGrown) :
    (growCand c g).remaining = g.val.remaining := rfl

theorem growCand_plannedMin (c : Look.Cand) (g : WfGrown) :
    (growCand c g).plan.val.plannedMin = g.val.plannedMin := rfl

/-- **The rest of the candidate is kept** — what §7.2's rule table and §8.2 step 5's key read. -/
theorem growCand_keeps (c : Look.Cand) (g : WfGrown) :
    (growCand c g).id = c.id ∧ (growCand c g).ci = c.ci ∧ (growCand c g).rootPrio = c.rootPrio ∧
      (growCand c g).due = c.due ∧ (growCand c g).wall = c.wall ∧
      (growCand c g).optional = c.optional ∧ (growCand c g).window = c.window ∧
      (growCand c g).hot = c.hot ∧ (growCand c g).plan.val.loc = c.plan.val.loc ∧
      (growCand c g).plan.val.splittable = c.plan.val.splittable ∧
      (growCand c g).plan.val.state = c.plan.val.state :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The request with the extended candidate's facts grown** — every candidate record the
extension names (fork `apply` rewrites each), and nothing else of the request. -/
def PlanReq.growing (r : PlanReq) (i : Id) : Option WfGrown → PlanReq
  | none => r
  | some g =>
    { r with cands := ⟨r.cands.val.map (fun p => if p.1.id = i then (growCand p.1 g, p.2) else p),
        by rw [List.length_map]; exact r.cands.property⟩ }

/-- **No grown facts, no change** — the what-if with none is the estimate's. -/
theorem PlanReq.growing_none (r : PlanReq) (i : Id) : r.growing i none = r := rfl

/-- **Growing touches the candidates alone.** -/
theorem PlanReq.growing_touches_only_the_candidates (r : PlanReq) (i : Id) (g : Option WfGrown) :
    (r.growing i g).plan = r.plan ∧ (r.growing i g).run = r.run ∧ (r.growing i g).look = r.look ∧
      (r.growing i g).state = r.state ∧ (r.growing i g).prio = r.prio ∧
      (r.growing i g).routines = r.routines ∧ (r.growing i g).overrides = r.overrides := by
  cases g <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **A named record carries the host's numbers; every other record is as sent.** -/
theorem PlanReq.mem_growing (r : PlanReq) (i : Id) (g : WfGrown) (c : Look.Cand)
    (f : Option Look.Floor) (h : (c, f) ∈ r.cands.val) :
    (if c.id = i then (growCand c g, f) else (c, f)) ∈ (r.growing i (some g)).cands.val := by
  show _ ∈ r.cands.val.map _
  exact List.mem_map.2 ⟨(c, f), h, rfl⟩

/-! ############################################################################
## W-36 track T — ONE reading of worked minutes (parity P55, README gap 2920) and a logged wall
## pause (the owner's D61, parity P53)

**Why the running block's worked minutes are the HOST's.**  Until W-36 there were two readings of
one number.  The host's, `Replay::active_worked_min` (fork `day::worked_min`): the wall clock since
`started` net of the day's pauses, interruptions and breaks, the running break included — what `tm
now`'s header prints and `tm done` LOGS.  And this module's, `openWorkedMin`: the log's open block
(fork `OpenBlock::worked_min_at`), which the reservation's `left` and the open row's `so far` read,
and which never sees a `break` — the replay's machine does not touch a block for one
(`Replay.dayArm`).  On a day with a break inside the running block the two disagreed on one
screen: `tm now` read `· 20m of 30m` over the row's `running · 5m left` (W-35 repair, driven).

**One definition, and the other reads it** (AGENTS §5.3).  The rule has to be evaluable wherever
the host needs it — every tick of the TUI's timer, `tm done`'s `actual_min` — so it is the host's,
and this module READS it: `RuntimeIn.worked`, `state.active.workedMin` on the wire, bounded by a
day (`workedOf?`).  `PlanReq.workedOf` is the one place the planner takes worked minutes from; the
reservation (`activeWorked`) and the open row (`openBlockRows`) both call it, so they print one
number (`the_open_row_reads_the_running_blocks_worked_minutes`).  The log's reading is what a
request that carries no host reading gets — fork `active_run`'s, parity-exact — and every arm of
the proptest that sends none compares against the fork exactly as before.  **R3's planner section
must carry it**: `tm_core::planwire::add_worked_min`, README gap 2920's residue, by name.

**The replay excludes a meeting once D61 has logged it** (`a_logged_wall_pause_is_no_worked_time`):
the pause and unpause the host writes at a wall's start and end are the log's own events, and the
machine banks the stretch before the pause and restarts the block at the unpause, so the fallback
reading, the past half (`pastRows`: a Block row to the pause, and since D65 nothing under the wall)
and the open row (from the unpause, `mem_openBlockRows`) all exclude the meeting.
############################################################################ -/

/-- **R10's smart constructor for `RuntimeIn.worked`**: at most the host's width, `Look.maxPlanMinutes` (the fork's `u32`;
W-41).  It was the day's 1,440, called exact while `active.started` was a clock of the plan's date; since P69 it is the
log's instant, so a block forgotten overnight has run longer than a day (D79) — `ActiveBlock.estMin`'s width is reused. -/
def workedOf? (n : Nat) : Option (Fin (Look.maxPlanMinutes + 1)) :=
  if h : n ≤ Look.maxPlanMinutes then some ⟨n, by omega⟩ else none

/-- **A reading past the width is refused** — nothing is clamped. -/
theorem a_worked_reading_past_the_width_is_refused (n : Nat) (h : Look.maxPlanMinutes < n) :
    workedOf? n = none := by
  unfold workedOf?
  rw [dif_neg (by omega)]

/-- …and every reading within a day is read as itself (so is every one within the width: the bound, run, below). -/
theorem a_worked_reading_within_a_day_is_read (n : Nat) (h : n ≤ Look.maxDayMin) :
    (workedOf? n).map Fin.val = some n := by
  unfold workedOf?
  rw [dif_pos (Nat.le_trans h (by decide))]
  rfl

/-- The bound, run (AGENTS §5.2): 90 and a day's 1,440 are read, and since W-41 so is 1,441 — the day's bound, refuted. -/
theorem the_worked_minutes_bound_is_run_at_the_width :
    (workedOf? 90).map Fin.val = some 90 ∧ (workedOf? 1440).map Fin.val = some 1440 ∧
      (workedOf? 1441).map Fin.val = some 1441 ∧ workedOf? (Look.maxPlanMinutes + 1) = none := by
  decide

/-- **The reservation reads the host's worked minutes** whenever the request carries them for the
running block — its `left` is the estimate less the minutes `tm done` would log. -/
theorem PlanReq.activeWorked_is_the_hosts (r : PlanReq) (a : ActiveBlock)
    (w : Fin (Look.maxPlanMinutes + 1)) (ha : r.state.active = some a) (hw : r.state.worked = some w) :
    r.activeWorked a = w.val := by
  unfold PlanReq.activeWorked PlanReq.workedOf
  rw [ha, hw]
  simp

/-- **…and with none, the log's own reading, exactly as before W-36** (fork `active_run`): the
arms of the proptest that send no host reading compare against the fork unchanged. -/
theorem PlanReq.activeWorked_without_the_hosts (r : PlanReq) (a : ActiveBlock)
    (hw : r.state.worked = none) :
    r.activeWorked a = (match r.run.answer.openBlock with
      | some b => if b.id = a.id then openWorkedMin r.now.sec b
        else Look.spanMinutes a.started.sec r.now.sec
      | none => Look.spanMinutes a.started.sec r.now.sec) := by
  unfold PlanReq.activeWorked PlanReq.workedOf
  rw [hw]
  cases r.state.active <;> rfl

/-- **ONE reading: the open row's `so far` IS the reservation's worked minutes** — whenever the
row is the running block's, whichever reading the request carries.  So the `▶` row, the
reservation and (through the host's reading) `tm now`'s header cannot print two numbers for one
block.  W-34's `the_open_row_is_the_logs_open_block` said the note was the LOG's reading; with the
host's carried that is false (`PlannerWit.the_open_row_carries_the_logs_worked_minutes_is_refuted`)
and its statement now reads `workedOf`. -/
theorem the_open_row_reads_the_running_blocks_worked_minutes (r : PlanReq) (t : Seg)
    (h : t ∈ openBlockRows r) (a : ActiveBlock) (ha : r.state.active = some a)
    (hid : t.item = some a.id) : t.note = some (.soFar (r.activeWorked a)) := by
  obtain ⟨b, s, hb, -, -, -, -, -, -, -, hi, -, -, -, -, hn⟩ := mem_openBlockRows h
  have hba : b.id = a.id := by rw [hi] at hid; exact Option.some.inj hid
  rw [hn]
  simp [PlanReq.activeWorked, hb, hba]

/-- **The open row's `so far` is the host's worked minutes** when the request carries them. -/
theorem the_open_row_reads_the_hosts_worked_minutes (r : PlanReq) (t : Seg)
    (h : t ∈ openBlockRows r) (a : ActiveBlock) (w : Fin (Look.maxPlanMinutes + 1))
    (ha : r.state.active = some a) (hw : r.state.worked = some w) (hid : t.item = some a.id) :
    t.note = some (.soFar w.val) := by
  rw [the_open_row_reads_the_running_blocks_worked_minutes r t h a ha hid,
    PlanReq.activeWorked_is_the_hosts r a w ha hw]

/-- **D61 (parity P53): a logged wall pause is no worked time.**  The two lines D61's housekeeping
writes (`tm/src/cli/day.rs`, `stop_the_timer_at_walls`), replayed: `start a` 09:00, `pause a` at a
wall's 09:10 start, `unpause a` at its 09:50 end.  The open block banks the ten minutes before the
meeting and runs again from its end — at 10:00 it has worked twenty minutes of the sixty on the
clock (`openWorkedMin`) — and the day's segments are the stretch `[09:00, 09:10)` and a Pause
`[09:10, 09:50)`: no Block segment lies across the meeting, which is what `pastRows` and
`openBlockRows` draw from. -/
theorem a_logged_wall_pause_is_no_worked_time :
    let f := Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (Replay.bStart ['a']),
      Replay.bE 2 63924369000 (Log.Event.pause ['a']),
      Replay.bE 3 63924371400 (Log.Event.unpause ['a'])]
    f.openBlock.map (fun b => (b.workedMin, b.since.map (·.1.sec), b.paused,
        openWorkedMin 63924372000 b)) = some (10, some 63924371400, false, 20) ∧
    (f.days.get 739865).map (fun a => a.segments.map (fun s => (s.kind, s.start.1.sec, s.stop.1.sec)))
      = some [(Replay.SegKind.block ['a'], 63924368400, 63924369000),
              (Replay.SegKind.pause ['a'], 63924369000, 63924371400)] := by
  decide

/-- **…and without the pair, the stretch runs across the meeting** — the same hour with nothing
logged at the wall: sixty minutes worked at 10:00 and one open stretch from 09:00, which is what
the log held before D61 and what `tm done` then logged as `actual_min`. -/
theorem an_unlogged_wall_is_worked_time :
    let f := Replay.replay Replay.utcZone [Replay.bE 1 63924368400 (Replay.bStart ['a'])]
    f.openBlock.map (fun b => (b.workedMin, b.since.map (·.1.sec), openWorkedMin 63924372000 b))
      = some (0, some 63924368400, 60) := by
  decide

/-! ############################################################################
## W-37 track T — the owner's D65: a meeting that paused the running block is drawn as the WALL
## ALONE (parity P56, README gaps 3044, 3141 and 3142)

D61 stops a running block's timer at a calendar wall with the log's own `pause`/`unpause` pair,
and until W-37 `pastRows` — like fork `past_segments` — drew the replayed Pause segment as a Lost
row noted `paused`, so the day showed the meeting twice: its Wall row, and a `paused` Lost row over
the same span that `tm review day` counts as no lost time.  One span, two readings (AGENTS §5.3).
`pastRows` now draws each replayed segment over the spans `pastSpans` answers: its clip to
`[day_start, now]`, and for a Pause, with every wall of the day (`wallSpans`, step 1's rows, run-up
included — the span D61 pauses on) cut out of it (`PastCut.lean`).  The laws are below: no paused
row lies under a wall; a pause no wall touches is drawn whole; no other kind is cut.  The shipped
`tm plan` draws the same, because fork `past_segments` (`tm-core/src/planner.rs`) makes the same cut
until R3 deletes it.

The definitions sit where `pastRows` always sat and the laws sit here, so that every check-9 pin
site in this module stays on the line `kernel/mutations.txt` recorded (`PastCut.lean`'s header).
############################################################################ -/

/-- **No kind but a Pause is cut** (D65's rule reaches the paused rows and nothing else): a Block,
a Break, a closed interruption, a routine and an idle mark are drawn over their whole clip. -/
theorem pastSpans_of_not_a_pause (r : PlanReq) (g : Replay.Segment)
    (hk : ∀ i, g.kind ≠ Replay.SegKind.pause i) :
    pastSpans r g = if min g.stop.1.sec r.now.sec ≤ max g.start.1.sec r.dayStart then []
      else [(max g.start.1.sec r.dayStart, min g.stop.1.sec r.now.sec)] := by
  unfold pastSpans
  cases hg : g.kind with
  | pause i => exact absurd hg (hk i)
  | block _ => exact clipCut_nil _ _
  | interrupt _ => exact clipCut_nil _ _
  | brk _ => exact clipCut_nil _ _
  | routine _ _ => exact clipCut_nil _ _
  | idle _ => exact clipCut_nil _ _

/-- **D65 (parity P56): no paused row is drawn under a wall.**  Every row of the replayed past
that carries the `paused` note lies wholly before or wholly after each wall of the day — the
meeting D61's pause covers is drawn as its Wall row and nothing else. -/
theorem a_paused_row_lies_under_no_wall (r : PlanReq) (t : Seg) (h : t ∈ pastRows r)
    (hn : t.note = some Note.paused) (w : Look.WallIx) (hw : w ∈ wallsToday r) :
    t.stop ≤ w.lo ∨ w.hi ≤ t.start := by
  obtain ⟨d, -, g, -, q, hq, rfl⟩ := mem_pastRows.1 h
  obtain ⟨-, -, -, -, -, hlt⟩ := mem_wallsToday hw
  have hwin : (w.lo, w.hi) ∈ wallSpans r := List.mem_map.2 ⟨w, hw, rfl⟩
  unfold pastSpans at hq
  cases hg : g.kind with
  | pause i =>
    rw [hg] at hq
    exact clipCut_apart hq (w.lo, w.hi) hwin hlt
  | block i => simp [pastRowOf, pastKind, hg] at hn
  | interrupt i => simp [pastRowOf, pastKind, hg] at hn
  | brk x => cases x <;> simp [pastRowOf, pastKind, hg] at hn
  | routine a b => simp [pastRowOf, pastKind, hg] at hn
  | idle a => simp [pastRowOf, pastKind, hg] at hn

/-- **…and a pause no wall touches is drawn whole** (AGENTS §5.8: the rule does not over-bite):
where every wall of the day ends by the pause's clipped start or begins at or after its clipped
end, the pause is one row over its whole clip, exactly as fork 4748911 draws it. -/
theorem a_pause_no_wall_touches_is_drawn_whole (r : PlanReq) (g : Replay.Segment) (i : Id)
    (hk : g.kind = Replay.SegKind.pause i)
    (hlt : max g.start.1.sec r.dayStart < min g.stop.1.sec r.now.sec)
    (hw : ∀ w ∈ wallsToday r, w.hi ≤ max g.start.1.sec r.dayStart ∨
      min g.stop.1.sec r.now.sec ≤ w.lo) :
    pastSpans r g = [(max g.start.1.sec r.dayStart, min g.stop.1.sec r.now.sec)] := by
  unfold pastSpans
  rw [hk]
  refine clipCut_untouched hlt (fun s hs => ?_)
  obtain ⟨w, hw', rfl⟩ := List.mem_map.1 hs
  rcases hw w hw' with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-! ## §8.1's window and budget as the fork's PLANNER reads them (W-37 repair and W-38; README gaps 320 and 3341)

`PlanReq.window` was `Look.day0Window` whole until the W-37 repair — fork `Ctx::window`'s reading, day 0's
CAPACITY — and the shipped binary reads the stored window a second way for the day it PLANS: fork
`Planner::window_and_budget` reads `runtime.window` and `runtime.budget` on `planwire::plan_date`'s day
(`state.date`, else `now`'s own date) whatever sits beside them, and ends a window earlier than its start on
the next day.  Gap 320 named the three inputs where the two part.  The W-37 repair took the third (a window
crossing midnight, gap 3341); W-38 takes the other two — a state naming NO day, whose window, budget and
arrival are today's to the planner, and a window with NO budget beside it — through `Look.Today.planWindow`,
`planBudget` and `planArrivalSec`, so `PlanReq.window` and `PlanReq.budgetBlocks` are the fork planner's own
reading of `state.json` and nothing else.  Day 0's capacity keeps `Ctx::window`'s reading, which is where the
binary keeps it (`kernel_lookahead_parity.rs` compares it exactly), so the two readings are the fork's own two,
each where the fork keeps it.  Since W-39 its arrival is `Planner::new`'s whole: the state's, else the day's first
logged `arrive` (`PlanReq.loggedArrival`, README gap 3390), else `now` — where day 0's capacity reads no log.

The view law that equated the planner's window with day 0's capacity window held on every request until the
W-37 repair and on every window not crossing midnight until this one; it holds exactly on the subdomain the
restated name carries (AGENTS §3.1 item 4), and `PlannerWit` refutes each wider form by a computed request. -/

/-- **The planner's window is day 0's capacity window on a state dated today whose stored window carries its budget and
does not cross midnight — unless no window is stored and only the log holds the arrival, or a wall of the day passes its bounds, which the planner clips and the capacity reads whole** (W-39, README gaps 3390 and 3556). -/
theorem PlanReq.window_is_the_lookaheads_on_a_dated_state_with_a_budgeted_window_unless_a_windowless_day_has_only_a_logged_arrival_or_a_wall_passes_its_bounds
    (r : PlanReq) (hd : r.look.today0.date = some r.look.today) (hin : ∀ x ∈ Look.wallIxOn r.look.walls r.look.today, r.dayStart ≤ x.lo ∧ x.lo < x.hi ∧ x.hi ≤ r.dayEnd)
    (ho : r.look.today0.window.isSome = true ∨ r.look.today0.arrival.isSome = true ∨ r.loggedArrival = none)
    (hb : r.look.today0.window.isSome = true → r.look.today0.budget.isSome = true)
    (h : ∀ w, r.look.today0.window = some w → w.1 ≤ w.2) : r.window = Look.day0Window r.look := by
  have hf := r.look.today0.forToday_of_date r.look.today hd
  unfold PlanReq.window Look.day0Window Look.Today.planWindow Look.Today.storedWindow Look.Today.storedBudget
  rw [if_pos hf, if_pos hd]
  cases hw : r.look.today0.window with
  | none =>
    rw [Look.wallsClippedOn_eq_wallsOn (Cal.instantOf r.look.tz r.look.today 0).sec (Cal.instantOf r.look.tz (r.look.today + 1) 0).sec _ _ hin]; simp only [r.look.today0.planArrivalSec_is_arrivalSec_unless_only_the_log_holds_it r.look.today r.look.tz _ hd
      (ho.resolve_left (by simp [hw]))]
  | some w =>
    have hbs := hb (by simp [hw])
    cases hbb : r.look.today0.budget with
    | none => rw [hbb] at hbs; exact absurd hbs (by simp)
    | some b =>
      have hn : ¬ w.2 < w.1 := Nat.not_lt.mpr (h w hw)
      simp [hn]
/-- **A stored window that crosses midnight ends 24 hours after its end clock on the planned day** — the fork planner's
reading (`Planner::window_and_budget`: `end += Duration::days(1)`), which the shipped binary plans a late day with.  RESTATED AT
W-40 (README gap 3782; D5): it read the NEXT day's clock, an hour past the fork's on a fall-back night, which
`PlannerWit.the_window_crossing_midnight_ends_on_the_next_days_clock_is_refuted` refutes. -/
theorem PlanReq.window_crosses_midnight_as_the_forks_planner_reads_it (r : PlanReq)
    (w : Field.Clock × Field.Clock) (hs : r.look.today0.planWindow r.look.today = some w)
    (hlt : w.2 < w.1) :
    r.window = ((Cal.instantOf r.look.tz r.look.today w.1).sec,
      (Cal.instantOf r.look.tz r.look.today w.2).sec + 86400) := by
  unfold PlanReq.window
  rw [hs]
  simp [hlt]

/-- **The window stored for the planned day is the day's window** (gap 320): whatever the state's date says
beside it — none, or today — and whether or not a budget is stored with it. -/
theorem PlanReq.window_is_the_stored_one_on_its_day (r : PlanReq) (w : Field.Clock × Field.Clock)
    (hs : r.look.today0.planWindow r.look.today = some w) (hle : w.1 ≤ w.2) :
    r.window = ((Cal.instantOf r.look.tz r.look.today w.1).sec,
      (Cal.instantOf r.look.tz r.look.today w.2).sec) := by
  have hn : ¬ w.2 < w.1 := Nat.not_lt.mpr hle
  unfold PlanReq.window
  rw [hs]
  simp [hn]

/-- **With no window stored for the planned day, the window is §8.1's formula from the planner's arrival** (`loggedArrival` too). -/
theorem PlanReq.window_is_the_formula_without_a_window_on_its_day (r : PlanReq)
    (hs : r.look.today0.planWindow r.look.today = none) :
    r.window = Look.windowFrom r.look.tz (r.look.today0.planArrivalSec r.look.today r.look.tz r.loggedArrival)
      (Look.windowMinOf r.look.day.windowHours) r.look.day.windowCap (Look.wallsClippedOn r.dayStart r.dayEnd r.look.walls r.look.today) := by
  unfold PlanReq.window
  rw [hs]; rfl

/-- **The day's window is day 0's capacity window on that subdomain** — `dayPlan_window` states the day's
window as `PlanReq.window`. -/
theorem dayPlan_window_is_the_lookaheads_on_a_dated_state_with_a_budgeted_window_unless_a_windowless_day_has_only_a_logged_arrival_or_a_wall_passes_its_bounds
    (r : PlanReq) (hd : r.look.today0.date = some r.look.today) (hin : ∀ x ∈ Look.wallIxOn r.look.walls r.look.today, r.dayStart ≤ x.lo ∧ x.lo < x.hi ∧ x.hi ≤ r.dayEnd)
    (ho : r.look.today0.window.isSome = true ∨ r.look.today0.arrival.isSome = true ∨ r.loggedArrival = none)
    (hb : r.look.today0.window.isSome = true → r.look.today0.budget.isSome = true)
    (h : ∀ w, r.look.today0.window = some w → w.1 ≤ w.2) : (dayPlan r).window = Look.day0Window r.look :=
  PlanReq.window_is_the_lookaheads_on_a_dated_state_with_a_budgeted_window_unless_a_windowless_day_has_only_a_logged_arrival_or_a_wall_passes_its_bounds r hd hin ho hb h

/-! ## §8.2 step 1 in `emit_segments`' own order: the running interruption among the walls (W-38, README gap 3281)

Fork `collect_walls` pushes §9's running interruption after the day's calendar walls — an ad-hoc `WallSeg`
blocked from where it started, keyed by the block it paused or by `""` — and sorts the lot by
`(blocked_start, id)`; `emit_segments` walks the sorted list, a Lost row for the ad-hoc entry and a wall's own
rows for each other, and the final `(start, end)` sort keeps that order for rows that tie.  The kernel drew the
interruption's Lost row before every wall (`stepOneSegs`' order), so a Lost row and a Wall row starting and
ending at one instant were drawn in two orders, and the day's hash with them (README gap 3281, found by
`planner_invariants`' hash arm on seed `ef4f4091…`).  `dayRows` now walks step 1 by `stepOneOrder` over
`wallLe` — the kernel's own `collect_walls` order, reused — and the two laws below say the walk IS the fork's
sort with the ad-hoc wall pushed last, and changes nothing on a day with no interruption. -/

/-- A stable insertion that meets an entry it goes at or before stops there, and the rest follows. -/
theorem insBy_append_cons_of_le {α : Type} (le : α → α → Bool) (a x : α) (hax : le a x = true) :
    ∀ (F G : List α), Replay.insBy le a (F ++ x :: G) = Replay.insBy le a F ++ x :: G
  | [], G => by simp [Replay.insBy, hax]
  | b :: F, G => by
    simp only [List.cons_append, Replay.insBy]
    split
    · rfl
    · rw [insBy_append_cons_of_le le a x hax F G, List.cons_append]

/-- …and passes over every entry it goes after. -/
theorem insBy_append_of_after {α : Type} (le : α → α → Bool) (a : α) :
    ∀ (F R : List α), (∀ b ∈ F, le a b = false) → Replay.insBy le a (F ++ R) = F ++ Replay.insBy le a R
  | [], R, _ => rfl
  | b :: F, R, h => by
    simp only [List.cons_append, Replay.insBy, h b List.mem_cons_self, Bool.false_eq_true, if_false]
    rw [insBy_append_of_after le a F R (fun c hc => h c (List.mem_cons_of_mem _ hc))]

/-- **A stable sort with one entry pushed last places it after every entry at or before it and before the
rest** — fork `collect_walls`' `out.push(..)` then `out.sort_by(..)`, as `Replay.insSort` computes it. -/
theorem insSort_snoc {α : Type} (le : α → α → Bool)
    (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, le a b = true ∨ le b a = true) (x : α) :
    ∀ (l : List α), Replay.insSort le (l ++ [x])
      = (Replay.insSort le l).filter (fun y => le y x) ++ x :: (Replay.insSort le l).filter (fun y => !le y x)
  | [] => by simp [Replay.insSort, Replay.insBy]
  | a :: l => by
    have ih := insSort_snoc le trans total x l
    have hs := Seal.insSort_sorted le trans total l
    rw [List.cons_append, Seal.insSort_cons', ih, Seal.insSort_cons',
      Seal.insBy_filter le trans _ a _ hs, Seal.insBy_filter le trans _ a _ hs]
    cases hax : le a x
    · have hF : ∀ b ∈ (Replay.insSort le l).filter (fun y => le y x), le a b = false := by
        intro b hb
        have hbx : le b x = true := by simpa using (List.mem_filter.1 hb).2
        cases hab : le a b
        · rfl
        · exact absurd (trans a b x hab hbx) (by simp [hax])
      simp only [Bool.false_eq_true, if_false, Bool.not_false, if_true]
      rw [insBy_append_of_after le a _ _ hF]
      simp [Replay.insBy, hax]
    · simp only [if_true, Bool.not_true, Bool.false_eq_true, if_false]
      exact insBy_append_cons_of_le le a x hax _ _

/-- **Fork `collect_walls`' sort with the ad-hoc wall pushed last is the kernel's split**: the calendar walls
`wallLe` puts at or before it, the ad-hoc wall, then the rest — `wallLe` itself, the kernel's one wall order. -/
theorem sortWalls_snoc (C : List Look.WallIx) (i : Look.WallIx) :
    sortWalls (C ++ [i])
      = (sortWalls C).filter (fun y => wallLe y i) ++ i :: (sortWalls C).filter (fun y => !wallLe y i) :=
  insSort_snoc wallLe (fun a b c h₁ h₂ => wallLe_trans a b c h₁ h₂)
    (fun a b => Bool.or_eq_true _ _ |>.mp (wallLe_total a b)) i C

/-- **With no running interruption, step 1 is `stepOneSegs` in its own order** — every day that draws no Lost row
for an interruption is drawn exactly as before W-38. -/
theorem stepOneOrder_without_an_interruption (r : PlanReq) (h : interruptRows r = []) :
    stepOneOrder r = stepOneSegs r := by
  unfold stepOneOrder
  rw [h]
  rfl

/-- **With one, its Lost row is walked where fork `collect_walls`' sort puts its ad-hoc wall**: the key
`(blocked_start, id)` is read off the row itself (its start, and the block it names or `""`), the fork's sort of the
day's clipped calendar walls with that entry pushed last is `wallsToday`' walls at or before it, the entry, and the
rest (`sortWalls_snoc`), and step 1's rows are the log's, the running break's, and then exactly those walls' rows, the
Lost row and the rest's rows, in that order. -/
theorem PlanReq.the_interruption_is_walked_where_collect_walls_sorts_it (r : PlanReq) (s : Seg)
    (hs : (interruptRows r).head? = some s) :
    let i : Look.WallIx := ⟨s.item.getD [], r.today, r.today, s.start, s.start, s.stop⟩
    sortWalls (((Look.wallIxOn r.look.walls r.today).filterMap fun x =>
        if (Look.clipWall r.dayStart r.dayEnd x).lo < (Look.clipWall r.dayStart r.dayEnd x).hi
        then some (Look.clipWall r.dayStart r.dayEnd x) else none) ++ [i])
      = (wallsToday r).filter (fun y => wallLe y i) ++ i :: (wallsToday r).filter (fun y => !wallLe y i) ∧
    stepOneOrder r
      = replayedRows r ++ breakRows r ++
          ((wallsToday r).filter (fun y => wallLe y i)).flatMap (fun x => wallRows (r.isTravelDay x.id) x) ++
          interruptRows r ++
          ((wallsToday r).filter (fun y => !wallLe y i)).flatMap (fun x => wallRows (r.isTravelDay x.id) x) := by
  refine ⟨sortWalls_snoc _ _, ?_⟩
  unfold stepOneOrder
  rw [hs]

/-! ## §8.2 step 5's served order, carried by the day (W-38, README gap 3343)

`planner_invariants`' monotone-rank check asks, of every pair of candidates of one `p` and one `ci`, that the one step
5 serves first is never the one left out — and until W-38 it read "first" off a Rust copy of D63's order
(`forkclass::d60_cands`), pairing by the host's `ci`, because the kernel's order and the `ci` its walk reads were on no
wire (gap 3343).  `PlanReq.dayServed` is that order as the day carries it: the ranked answers in `rankedLe`'s order —
the list `PlanReq.dayBatches` hands §7.5's batching and step 5 walks — each by its request position, its id and the
`ci` the energy filter reads.  Bounded by the candidates' own cap, so `Capped.ofListTake` truncates nothing. -/

theorem PlanReq.dayServed_capped (r : PlanReq) : r.dayServed.length ≤ maxCands := by
  unfold PlanReq.dayServed
  rw [List.length_map]
  exact Nat.le_trans r.rankedCands_length r.cands.property

theorem dayDiagnostics_served (r : PlanReq) : (dayDiagnostics r).served.val = r.dayServed :=
  Capped.ofListTake_keeps_everything_below_the_cap _ r.dayServed_capped

/-- **The day carries step 5's served order whole**: `rankedCands` projected, in `rankedLe`'s order, and it is the
very list step 5's batching reads (`PlanReq.dayBatches`). -/
theorem dayPlan_serves_in_the_walks_order (r : PlanReq) :
    (dayPlan r).diagnostics.served.val
        = r.rankedCands.map (fun x => (x.key.ix, x.out.out.cand.id, x.out.out.cand.ci)) ∧
      r.rankedCands.Pairwise (fun a b => rankedLe a b = true) ∧
      r.dayBatches = batches r.prio.batchMaxMin r.blockMin r.rankedCands :=
  ⟨dayDiagnostics_served r, r.rankedCands_sorted, rfl⟩

/-- **Each served entry names an answer of this request that entered the order, by its position**: the position is
the answer's place in the request's candidate list, the id its candidate's and the `ci` the one the wire sent. -/
theorem PlanReq.mem_dayServed {r : PlanReq} {e : Nat × Id × Fin 6} :
    e ∈ r.dayServed ↔ ∃ p ∈ r.candAnswers.zipIdx, entersTheOrder p.1 = true ∧
      e = (p.2, p.1.out.cand.id, p.1.out.cand.ci) := by
  unfold PlanReq.dayServed
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨p, hp, he, rfl⟩ := PlanReq.mem_rankedCands.1 hx
    exact ⟨p, hp, he, rfl⟩
  · rintro ⟨p, hp, he, rfl⟩
    exact ⟨⟨r.keyOf p.2 p.1, p.1⟩, PlanReq.mem_rankedCands.2 ⟨p, hp, he, rfl⟩, rfl⟩


/-! ### The two `dayImpossible` directions (W-33), moved here whole at W-38

They stood in §8.2 step 8's section until W-38, where `fitsBefore` and `PlanReq.dayUnplaced` now
stand; moving them rather than inserting beside them kept every check-9 pin site of this file on
its line (README gap 2136).  Nothing between their old place and this one used them. -/

/-- **Every item whose EDF numbers say impossible, answered at a HOT bin, is named with its
grant's shortfall** — the direction that makes W-18's `rfl` (the day named no impossible item)
false.  The HOT bin is a real hypothesis and not a convenience: `edfNumbers` is R1's CEILING of
the need against the availability (`Grant.impossible`), §7.1's bin is the EXACT `u`, and an
availability strictly between the exact need and its ceiling makes the first say impossible
and the second say `+n` — the shipped binary then calls the item neither HOT nor impossible,
and so does this field. -/
theorem the_day_names_every_item_whose_numbers_say_impossible_at_a_hot_bin (r : PlanReq)
    (i : Id) {o : Look.FloorOut} (ha : r.answerFor i = some o) (hb : o.out.bin = some .hot)
    (h : Arith.isImpossible (edfNumbers r i).1 (edfNumbers r i).2 = true) :
    ∃ g, r.grantFor i = some g ∧
      (i, Arith.floorQ (g.shortfallQ Look.capDenD)) ∈ r.dayImpossible := by
  have hmem : o ∈ r.candAnswers := by
    unfold PlanReq.answerFor at ha; exact List.mem_of_find?_eq_some ha
  have hid : o.out.cand.id = i := by
    unfold PlanReq.answerFor at ha; simpa using List.find?_some ha
  cases hg : r.grantFor i with
  | none =>
    rw [edfNumbers_without_a_grant r i hg] at h
    exact absurd h (by simp)
  | some g =>
    refine ⟨g, rfl, ?_⟩
    have hog : o.out.grant = some g := by
      unfold PlanReq.grantFor at hg; rw [ha] at hg; simpa using hg
    rw [edfNumbers_is_the_grants_own_impossibility r i g hg] at h
    have hs := r.an_impossible_grant_at_a_hot_bin_is_short hmem hog h hb
    obtain ⟨-, hmin, hsh⟩ := r.a_granted_answer hmem hog
    rw [if_pos hb] at hsh
    have hlt : g.avail < g.deadline.need * Look.capDen := of_decide_eq_true h
    have heq : o.shortfall = g.shortfall Look.capDen := by
      unfold Grant.shortfall; rw [hsh, hmin, Nat.min_eq_right (Nat.le_of_lt hlt)]
    refine (r.mem_dayImpossible i _).2 ⟨o, hmem, hid, hs, ?_⟩
    simp only [Grant.shortfallQ, heq]
    rfl

/-- **An item the day names that entered the pass has impossible EDF numbers** — the converse
by ID, under the one hypothesis it needs: `edfNumbers` answers an id by its FIRST answer
(`PlanReq.answerFor`), so with two candidates of one id (§5.3's carried instance beside today's
fresh one) the named item's numbers could be the other's. -/
theorem an_item_the_day_names_with_a_grant_has_impossible_numbers (r : PlanReq)
    (hnodup : (r.candAnswers.map (fun o => o.out.cand.id)).Nodup) (i : Id) (s : Nat)
    (h : (i, s) ∈ r.dayImpossible) (hg : (r.grantFor i).isSome = true) :
    Arith.isImpossible (edfNumbers r i).1 (edfNumbers r i).2 = true := by
  obtain ⟨o, ho, hid, hs, -⟩ := (r.mem_dayImpossible i s).1 h
  have ha : r.answerFor i = some o := hid ▸ r.answerFor_of_mem hnodup ho
  cases hgi : r.grantFor i with
  | none => rw [hgi] at hg; exact absurd hg (by simp)
  | some g =>
    have hog : o.out.grant = some g := by
      unfold PlanReq.grantFor at hgi; rw [ha] at hgi; simpa using hgi
    rw [edfNumbers_is_the_grants_own_impossibility r i g hgi]
    exact (r.a_named_grant_is_impossible_at_a_hot_bin ho hog hs).1


/-! ### D67 (P58): what `PlanReq.dayUnplaced` names, and that the day carries all of it

The writer stands in §8.2 step 8's section above; its laws are here, at the end of the file, so no
check-9 pin site above moved.  `PlanFold` proves each name TRUE of the day (the W-38 section), and
`PlanCheck.impossibleKept_on_every_day` is the check those proofs buy. -/

/-- **A named item is a listed impossible item that `assigned` does not hold — and its reason is
`noSlotAdmits` when step 5's filter admits it nowhere before the walk, else the walk's**, both
directions.  Restated at the W-38 repair (README gap 3523): it said a named item is one the filter
admits SOMEWHERE, which was the hole — an owed impossible item admitted nowhere had no row and no
name — and `PlanReq.an_item_the_filter_admits_nowhere_is_named` is that hole closed.  Stated before
the cap on purpose (README gap 2567): the `[]` mutant falsifies a membership law, not a length
bound. -/
theorem PlanReq.mem_dayUnplaced (r : PlanReq) (assigned : List Id) (i : Id) (w : NoPlace) :
    (i, w) ∈ r.dayUnplaced assigned ↔
      i ∈ r.dayImpossible.map Prod.fst ∧ assigned.contains i = false ∧
      w = (if (r.energisedSlots.zipIdx.filter (fitsBefore r i)).isEmpty then NoPlace.noSlotAdmits
           else if (r.energisedSlots.zipIdx.filter (fitsBefore r i)).any
              (fun x => (r.finalAssign.slotOf[x.2]?).join.isNone) then NoPlace.budgetSpent
           else if r.startGroups.any (fun g => decide (i ∈ g.ids) && !g.splittable) then .noRunLeft
           else .noSlotLeft) := by
  unfold PlanReq.dayUnplaced
  simp only [List.mem_filterMap, List.mem_eraseDups]
  constructor
  · rintro ⟨j, hj, h⟩
    by_cases h1 : assigned.contains j = true
    · rw [if_pos h1] at h; exact absurd h (by simp)
    · rw [if_neg h1] at h
      simp only [Bool.not_eq_true] at h1
      split at h
      · rename_i h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hj, h1, by rw [if_pos h2]⟩
      · rename_i h2
        split at h
        · rename_i h3
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hj, h1, by rw [if_neg h2, if_pos h3]⟩
        · rename_i h3
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hj, h1, by rw [if_neg h2, if_neg h3]⟩
  · rintro ⟨hi, ha, rfl⟩
    refine ⟨i, hi, ?_⟩
    have ha' : i ∉ assigned := by simpa using ha
    rw [if_neg (by simp [ha'])]
    split
    · rfl
    · split <;> rfl

/-- **The hole D67 left, closed** (README gap 3523): a listed impossible item that `assigned` does
not hold and that step 5's filter admits at no slot before the walk IS named — `noSlotAdmits` — where
until the W-38 repair it had no row and no name while its banner said IMPOSSIBLE (42 owed items on
36 of the 97 frozen class days, the reuse critic's census). -/
theorem PlanReq.an_item_the_filter_admits_nowhere_is_named (r : PlanReq) (assigned : List Id) (i : Id)
    (hi : i ∈ r.dayImpossible.map Prod.fst) (ha : assigned.contains i = false)
    (hx : (r.energisedSlots.zipIdx.filter (fitsBefore r i)).isEmpty = true) :
    (i, NoPlace.noSlotAdmits) ∈ r.dayUnplaced assigned :=
  (r.mem_dayUnplaced assigned i _).2 ⟨hi, ha, by rw [if_pos hx]⟩

/-- **Every listed impossible item the day does not hold is named** — the other direction of the
class: `dayUnplaced` leaves out only what `assigned` holds. -/
theorem PlanReq.every_unassigned_listed_item_is_named (r : PlanReq) (assigned : List Id) (i : Id)
    (hi : i ∈ r.dayImpossible.map Prod.fst) (ha : assigned.contains i = false) :
    ∃ w, (i, w) ∈ r.dayUnplaced assigned :=
  ⟨_, (r.mem_dayUnplaced assigned i _).2 ⟨hi, ha, rfl⟩⟩

/-- The cap: no more names than listed items, and the list is under the wire's `maxCands`. -/
theorem PlanReq.dayUnplaced_capped (r : PlanReq) (assigned : List Id) :
    (r.dayUnplaced assigned).length ≤ maxCands :=
  Nat.le_trans (List.length_filterMap_le _ _)
    (Nat.le_trans (eraseDups_length_le _ _ (Nat.le_refl _))
      (by rw [List.length_map]; exact r.dayImpossible_capped))

/-- **The day carries every name**: the cap is the wire's and the list is under it. -/
theorem dayDiagnostics_unplaced (r : PlanReq) :
    (dayDiagnostics r).unplaced.val = r.dayUnplaced (dayAssigned r) :=
  Capped.ofListTake_keeps_everything_below_the_cap _ (r.dayUnplaced_capped _)

/-! ### §8.1's window flows around the walls step 1 places (W-39 repair, README gap 3556)

Until the W-39 repair the planner's window read the day's walls WHOLE (`Look.wallsOn`, day 0's capacity reading,
fork `Ctx::walls_on`'s quirk (e)), while step 1 placed them clipped to the day (`wallsToday`, fork
`collect_walls`); fork `Planner::window_and_budget` reads the clipped ones.  On a Wednesday inside a
Tuesday-to-Friday conference the kernel's window therefore ran to 14:00 FRIDAY and step 3 cut work into the
small hours inside the wall, where the fork — the shipped binary — plans none.  The window now reads
`Look.wallsClippedOn`, and this is the law that says it is step 1's own clip: one clip, read twice. -/

/-- **The walls §8.1's window flows around ARE the walls step 1 places**, as a multiset: the window reads them in
index order, `wallsToday` in the fork's sorted order. -/
theorem PlanReq.the_windows_walls_are_the_walls_step_one_places (r : PlanReq) :
    (Look.wallsClippedOn r.dayStart r.dayEnd r.look.walls r.look.today).Perm
      ((wallsToday r).map fun w => (w.lo, w.hi)) := by
  unfold wallsToday wallsOfDay sortWalls
  refine List.Perm.symm ((List.Perm.map _ (Replay.insSort_perm wallLe _)).trans ?_)
  rw [List.map_filterMap]
  unfold Look.wallsClippedOn
  have e : ∀ x : Look.WallIx, Option.map (fun w : Look.WallIx => (w.lo, w.hi))
      (if (Look.clipWall r.dayStart r.dayEnd x).lo < (Look.clipWall r.dayStart r.dayEnd x).hi
       then some (Look.clipWall r.dayStart r.dayEnd x) else none) =
      (if (Look.clipWall r.dayStart r.dayEnd x).lo < (Look.clipWall r.dayStart r.dayEnd x).hi
       then some ((Look.clipWall r.dayStart r.dayEnd x).lo, (Look.clipWall r.dayStart r.dayEnd x).hi) else none) := by
    intro x
    by_cases hc : (Look.clipWall r.dayStart r.dayEnd x).lo < (Look.clipWall r.dayStart r.dayEnd x).hi <;> simp [hc]
  simp only [e]
  exact List.Perm.refl _

/-- **So a wall that runs past the day ends the window's extension at the day's end**: every wall the window reads
ends by midnight. -/
theorem PlanReq.the_windows_walls_end_by_the_days_end (r : PlanReq) (w : Nat × Nat)
    (hw : w ∈ Look.wallsClippedOn r.dayStart r.dayEnd r.look.walls r.look.today) : w.2 ≤ r.dayEnd :=
  Look.wallsClippedOn_ends_by _ _ _ _ w hw

/-! ############################################################################
## W-41 (track K): a start after `now` is planned from `now` (D78), the request's two refusals
## (D80), and the running record's widths (D81, README gap 3902)

**D78.**  Fork `Planner::active_run` plans a running block whose logged start is after `now` FROM `now`: its
reservation starts at `now`, its worked minutes are the log's banked minutes plus `(now - since).max(0)` — none for
a block that has not begun — and `current_block_end(started)` ends it `block_min` after the START, `started + bm`,
because `elapsed` is clamped to zero; `open_block_segment` draws no open row (`since >= now`), and `collect_walls`
pushes no interruption wall whose start is not before `now`.  The kernel computed every one of those already
(`PlanReq.activeWorked` through `Look.spanMinutes`' truncation, `blockBoundary`, `openBlockRows`, `interruptRows`);
what refused the request was the decoder (`ActiveBlock.wf`'s and `InterruptState.wf`'s start clause), and the
clause is gone.  §8.3's E1 is restated over the lead (`PlanReq.the_reservation_reaches_at_most_one_block_past_its_start`,
`plan_reserves_one_block_at_a_time`); the form below is E1 as it stood, where the block started by `now`.

**D80.**  The two requests fork 4748911 can never produce are refused by name where the request is assembled
(`PlanWire.planReqOf`): a day whose evening runs past the calendar's last second, and a candidate whose `ci` on the
wire is not the `ci` the plan file gives its item.  Both clauses are defined here, on the request, so the proof
module and the decoder read ONE definition of each (AGENTS §5.3).
############################################################################ -/

/-- **E1's reservation half where the running block started by `now`** — `the_reservation_is_at_most_one_block` as it
stood until W-41, relocated here with `hlead` for the `hok` it carried: `hok` gave it `started ≤ now` until D78 let a
start after `now` through the decoder, and `PlanReq.the_reservation_reaches_at_most_one_block_past_its_start` is the
law over every start, which this is the zero-lead instance of. -/
theorem PlanReq.the_reservation_is_at_most_one_block (r : PlanReq) (q : ActiveRes)
    (hlead : (r.state.active.map (fun a => a.started.sec - r.now.sec)).getD 0 = 0) (hb : r.blockMin ≠ 0) (h : r.activeRun = some q) :
    q.stop - q.start ≤ r.blockMin * 60 := by
  have := r.the_reservation_reaches_at_most_one_block_past_its_start q hb h
  omega

/-- **E1 as it stood until W-41**, on every request whose running block started by `now` (and every request with
nothing running): the restated `plan_reserves_one_block_at_a_time` at a zero lead. -/
theorem plan_reserves_one_block_at_a_time_when_the_block_started_by_now (r : PlanReq)
    (hlead : (r.state.active.map (fun a => a.started.sec - r.now.sec)).getD 0 = 0)
    (hday : r.dayAgrees = true) (s : WfSeg) (hs : s ∈ (dayPlan r).segments)
    (hk : s.val.kind = SegKind.block) (hnow : r.now.sec ≤ s.val.start) :
    s.val.stop - s.val.start ≤ (dayPlan r).blockMin * 60 := by
  have := plan_reserves_one_block_at_a_time r hday s hs hk hnow
  split at this <;> omega

/-- **Nothing running, no lead.** -/
theorem PlanReq.no_lead_without_a_running_block (r : PlanReq) (h : r.state.active = none) :
    (r.state.active.map (fun a => a.started.sec - r.now.sec)).getD 0 = 0 := by rw [h]; rfl

/-- **A block started by `now` has no lead** — every request a clock not behind the log builds. -/
theorem PlanReq.no_lead_for_a_start_by_now (r : PlanReq) (a : ActiveBlock) (h : r.state.active = some a)
    (hst : a.started.sec ≤ r.now.sec) : (r.state.active.map (fun a => a.started.sec - r.now.sec)).getD 0 = 0 := by
  rw [h]; show a.started.sec - r.now.sec = 0; omega

/-- …and every reading within the host's width is read as itself (W-41, D81 gap 3902's width on the worked minutes). -/
theorem a_worked_reading_within_the_width_is_read (n : Nat) (h : n ≤ Look.maxPlanMinutes) :
    (workedOf? n).map Fin.val = some n := by
  unfold workedOf?
  rw [dif_pos h]
  rfl

/-! ### D80 (a): the day's evening inside the calendar (README gaps 3785 and 3780; parity P71) -/

/-- **The last instant the day can place a row at** — the latest of its wind-down, its end (the next local midnight)
and §8.1's window's end, which runs past midnight when the planner arrives after it (the eve, README gap 3790). -/
def PlanReq.eveningEnd (r : PlanReq) : Nat := max r.windDownSec (max r.dayEnd r.window.2)

/-- **D80 (a), the decoder's clause**: the day's evening ends inside the calendar (`LogStamp.yearEnd`, `Cal.Instant.wf`'s
own bound), so the rows' clock (`clampSec`) never squeezes the wind-down, the day's end or the window onto the
calendar's last second.  `PlanWire.planReqOf` refuses a request without it by name (`eveningPastTheCalendar`). -/
def PlanReq.eveningInsideTheCalendar (r : PlanReq) : Bool := decide (r.eveningEnd < LogStamp.yearEnd)

/-- **The wind-down is inside the calendar** on a request the clause accepts — the `hwdcal` every wind-down law reads. -/
theorem PlanReq.windDown_inside_the_calendar (r : PlanReq) (h : r.eveningInsideTheCalendar = true) :
    r.windDownSec < LogStamp.yearEnd := by
  unfold PlanReq.eveningInsideTheCalendar PlanReq.eveningEnd at h
  simp only [decide_eq_true_eq] at h
  omega

/-- **So is the day's end, and the window's.** -/
theorem PlanReq.dayEnd_and_window_inside_the_calendar (r : PlanReq) (h : r.eveningInsideTheCalendar = true) :
    r.dayEnd < LogStamp.yearEnd ∧ r.window.2 < LogStamp.yearEnd := by
  unfold PlanReq.eveningInsideTheCalendar PlanReq.eveningEnd at h
  simp only [decide_eq_true_eq] at h
  omega

/-- **And a WindDown row of such a day is not clamped**: it starts at the wind-down itself, where until D80 a day
past the calendar had it start at the calendar's last second (`PlannerWit`'s W-40 last evening). -/
theorem PlanReq.the_wind_down_row_is_not_clamped (r : PlanReq) (h : r.eveningInsideTheCalendar = true)
    (w : WfSeg) (hw : w ∈ (dayPlan r).segments) (hk : w.val.kind = SegKind.windDown) :
    w.val.start = r.windDownSec := by
  rw [(a_wind_down_row_of_the_day r w (dayPlan_segments r ▸ hw) hk).2,
    clampSec_id _ (r.windDown_inside_the_calendar h)]

/-- **The clause bites** (AGENTS §5.8): a wind-down at or past the calendar's last second fails it. -/
theorem PlanReq.an_evening_past_the_calendar_fails_the_clause (r : PlanReq)
    (h : LogStamp.yearEnd ≤ r.windDownSec) : r.eveningInsideTheCalendar = false := by
  unfold PlanReq.eveningInsideTheCalendar PlanReq.eveningEnd
  simp only [decide_eq_false_iff_not]
  omega

/-! ### D80 (b): the candidate's `ci` on the wire is the plan's (README gap 1984; parity P72) -/

/-- **The `ci` the kernel reads in the plan file for an item**: `effectiveCi` (§3.2 — its own `ci:`, else its
parent's, else its file kind's default), or `none` when the plan does not hold the id at all, so a candidate the plan
does not hold agrees with nothing (`PlanCheck.candPlanView`'s first component, as `PlanCheck` proves). -/
def PlanReq.planCi (r : PlanReq) (i : Id) : Option (Fin 6) :=
  (r.plan.val.store.get i).map (fun _ => effectiveCi r.plan.val i)

/-- **D80 (b), the decoder's clause**: the FIRST candidate, in the request's order, whose `ci` on the wire is not the
plan's — named, with the wire's value and the plan's.  A COMPARISON of two readings of one fact and never a
replacement of one by the other (D34: a candidate's facts stay the host's until D27). -/
def PlanReq.ciDisagreement (r : PlanReq) : Option (Id × Fin 6 × Option (Fin 6)) :=
  (r.cands.val.find? (fun p => r.planCi p.1.id != some p.1.ci)).map (fun p => (p.1.id, p.1.ci, r.planCi p.1.id))

/-- **No disagreement is every candidate agreeing.** -/
theorem PlanReq.ciDisagreement_eq_none_iff (r : PlanReq) :
    r.ciDisagreement = none ↔ ∀ p ∈ r.cands.val, r.planCi p.1.id = some p.1.ci := by
  unfold PlanReq.ciDisagreement
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  constructor
  · intro h p hp
    have := h p hp
    simpa using this
  · intro h p hp
    simp [h p hp]

/-- **Where the wire agrees, a candidate's wire `ci` is its item's `ci` in the plan** — what every law over §8.2
step 5's energy filter and the wind-down needs of the wire, and all it needs. -/
theorem PlanReq.a_candidates_ci_is_its_items_where_the_wire_agrees (r : PlanReq) (h : r.ciDisagreement = none)
    (c : Look.Cand) (f : Option Look.Floor) (hc : (c, f) ∈ r.cands.val) : effectiveCi r.plan.val c.id = c.ci := by
  have hv := (r.ciDisagreement_eq_none_iff.1 h) (c, f) hc
  unfold PlanReq.planCi at hv
  cases hs : r.plan.val.store.get c.id with
  | none => rw [hs] at hv; exact absurd hv (by simp)
  | some e => rw [hs] at hv; simpa using hv

/-- **A disagreement names a candidate the request carries, its wire value and the plan's, and they differ** — the
refusal's text is about a real candidate and a real difference (AGENTS §5.7). -/
theorem PlanReq.a_ci_disagreement_names_a_candidate (r : PlanReq) (i : Id) (w : Fin 6) (p : Option (Fin 6))
    (h : r.ciDisagreement = some (i, w, p)) :
    ∃ c f, (c, f) ∈ r.cands.val ∧ c.id = i ∧ c.ci = w ∧ r.planCi i = p ∧ p ≠ some w := by
  unfold PlanReq.ciDisagreement at h
  obtain ⟨q, hq, he⟩ := Option.map_eq_some_iff.1 h
  have hmem := List.mem_of_find?_eq_some hq
  have hne := List.find?_some hq
  simp only [Prod.mk.injEq] at he
  obtain ⟨h1, h2, h3⟩ := he
  refine ⟨q.1, q.2, hmem, h1, h2, h1 ▸ h3, ?_⟩
  rw [← h3, ← h2]
  simpa using hne


/-- **Every Block row from `now` but the running one is at most one block, whatever the running block's lead** (the
W-41 repair, README gap 4136): the strength the restated E1 had dropped from its statement while its proof kept it. -/
theorem plan_reserves_one_block_at_a_time_off_the_running_row (r : PlanReq)
    (hday : r.dayAgrees = true) (s : WfSeg) (hs : s ∈ (dayPlan r).segments)
    (hk : s.val.kind = SegKind.block) (hnow : r.now.sec ≤ s.val.start)
    (hoff : ¬ (s.val.flags.current = true ∧ s.val.item = r.state.activeId)) :
    s.val.stop - s.val.start ≤ (dayPlan r).blockMin * 60 := by
  have := plan_reserves_one_block_at_a_time r hday s hs hk hnow
  rw [if_neg hoff] at this
  omega

/-- **`dayRows`' list since W-45 is the list it was, reordered** (README gap 4623): fork `emit_segments`
pushes the running block's reservation before the routines and the wind-down and Sleep rows after the
Rest slots, and the stable sort keeps that push order for two rows of one start and one end — a block
running past bed to midnight was drawn under its Sleep row until W-45.  Nothing is added and nothing is
dropped: every law over the day's rows as a multiset reads the old list through this. -/
theorem dayRows_list_perm (r : PlanReq) :
    (stepOneOrder r ++ reservationSegs r ++ r.assignedRows ++ r.keptBreakRows ++
      r.optionalRows ++ r.restRows ++ dayRoutineSegs r).Perm
    (stepOneSegs r ++ dayRoutineSegs r ++ reservationSegs r ++ r.assignedRows ++
      r.keptBreakRows ++ r.optionalRows ++ r.restRows) := by
  rw [List.perm_iff_count]
  intro a
  simp only [List.count_append, (stepOneOrder_perm r).count_eq]
  omega

/-- **Fork `emit_segments`' order where two rows tie, read off `dayRows`' own list**: the reservation is
pushed before the evening (`PlanReq.eveningRows`, the last rows of `dayRoutineSegs`), so the reservation of a
block running past bed to midnight is drawn above the Sleep row it ties with (README gap 4623;
`PlannerWit.the_running_block_precedes_the_sleep_it_ties_with` decides it on a day). -/
theorem the_reservation_precedes_the_evening_in_the_list (r : PlanReq) :
    ∃ pre mid, (stepOneOrder r ++ reservationSegs r ++ r.assignedRows ++ r.keptBreakRows ++
      r.optionalRows ++ r.restRows ++ dayRoutineSegs r) = pre ++ reservationSegs r ++ mid ++ r.eveningRows :=
  ⟨stepOneOrder r, r.assignedRows ++ r.keptBreakRows ++ r.optionalRows ++ r.restRows ++
    r.finalRoutines.flatMap r.routineRow, by simp only [dayRoutineSegs, routineRows, List.append_assoc]⟩

end Planner
end Tm
