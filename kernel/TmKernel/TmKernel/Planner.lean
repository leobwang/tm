import TmKernel.Lookahead
import TmKernel.SealResume
/-!
# The planner's vocabulary — §8's `Segment`, `DayPlan` and `PlanInput`, settled (stage 6, step P0)

Fork-point `tm-core/src/planner.rs` is the oracle, read by type and function name:
`planner::SegKind`, `planner::SegFlags`, `planner::Segment`, `planner::Diagnostics`,
`planner::DayPlan`, `planner::PlanInput`, `planner::PlanOverrides`,
`planner::Planner::window_and_budget`, and `store::RuntimeState` beside them.

This module holds **types and their laws**.  It does not place a wall, cut a slot or assign a
block: §8.2's eight steps are P1..P7, and `dayPlan` here is the fork's own
`DayPlan::empty` — a day with its window and its budget and **no segments at all**.  Two
theorems say so out loud (`the_day_has_no_segments_until_the_first_step_lands`,
`the_plan_hash_is_a_placeholder_until_the_emitter_lands`), and both must be *deleted* by the
step that makes them false.  Nothing in `Goals.lean` is discharged here.

## What is settled, and by which rule

* **`Seg` is on `Look.Slot`'s representation — absolute seconds, not minutes since midnight**
  (README gap 256).  `Goals.lean`'s provisional `Seg` carried `startMin`/`endMin`, which is a
  second representation of an instant beside `Cal.Instant` and `Look.Slot` (AGENTS §5.3), and
  `plan_never_moves_a_wall`'s own doc comment recorded the defect it caused — "says nothing
  about a wall that crosses midnight".  On seconds the caveat is not weakened, it is **gone**.
  `Seg.minutes` is `Look.Slot.minutes`' arithmetic on the same units.
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
`ActiveBlock` (`mkActive?`), `BreakState` (`mkBreak?`), `InterruptState` (`mkInterrupt?`),
yesterday's priorities (`mkYesterday?`) and `PlanOverrides` (`mkOverrides?`).

**Reused rather than re-bounded** (design §9's own "reuse" column): `Look.WakeClock.wf` and
its `badWake`; `Field.Clock` for a stored arrival and a stored window; `Field.parseDate`'s
calendar bound for `state.date`; `Look.maxLocName` for the location name; `yesterdayOf?`
for a stored `p`.  Five of §9's twelve rows are already `Look.Today`'s and are read through it
— re-declaring them would have been the defect this module's header warns about.

## D9-21, the recursion rule

`Capped.ofList?`, `mkYesterday?` and `mkOverrides?` recurse over lists the wire can make
large, and each is a `List.length` test plus core's own `List` operations — no new recursion
is written here.  `Seg.items` is core `Subtype.val`/`Option.toList`.  `dayPlan` folds over
nothing: its segment list is `[]`.
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

/-! ## `Note` — the four things the planner says in prose, named

Fork `Diagnostics::notes` is a `Vec<String>` built at four `notes.push` sites.  A named
constructor per site keeps AGENTS §5.7 (“every diagnostic is named”) and keeps the text where
the terminal is (D30 Q6): `Emit.lean` renders these at P8. -/
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
    (h : 315537897600 ≤ s.stop) : mkSeg? s = .error .pastTheHorizon := by
  unfold mkSeg? Seg.wf Cal.Instant.wf
  rw [dif_neg (by simp; omega), if_pos (by simp [hle])]

theorem mkSeg?_accepts (s : Seg) (h : Seg.wf s = true) :
    (mkSeg? s).map Subtype.val = .ok s := by
  unfold mkSeg?
  rw [dif_pos h]
  rfl

/-- Fork `Segment::minutes`, on `Look.Slot.minutes`' arithmetic. -/
def Seg.minutes (s : Seg) : Nat := (s.stop - s.start) / 60

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

/-- **Fork `planner::Diagnostics`.**  Nine lists, `dropped_tail`, and §11's two ratios.
`planHonesty` is a numerator over a denominator and **nothing here divides** (design §11): the
fork's `None` is denominator `0`, and Rust renders the percentage. -/
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

/-- Nothing wrong with the day yet. -/
def Diagnostics.empty : Diagnostics :=
  ⟨Capped.nil, 0, Capped.nil, Capped.nil, Capped.nil, Capped.nil, Capped.nil, Capped.nil,
   Capped.nil, Capped.nil, (0, 0), 0⟩

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

/-- A running block started at or before `now` and planned for at most a day.  `Look.maxDayMin`
is the day's own bound — this module does not write a second one. -/
def ActiveBlock.wf (now : Cal.Instant) (a : ActiveBlock) : Bool :=
  decide (a.started.sec ≤ now.sec) && decide (a.estMin ≤ Look.maxDayMin)

abbrev WfActive (now : Cal.Instant) := { a : ActiveBlock // ActiveBlock.wf now a = true }

def mkActive? (now : Cal.Instant) (a : ActiveBlock) : Option (WfActive now) :=
  if h : ActiveBlock.wf now a = true then some ⟨a, h⟩ else none

theorem mkActive?_refuses_a_start_after_now (now : Cal.Instant) (a : ActiveBlock)
    (h : now.sec < a.started.sec) : mkActive? now a = none := by
  unfold mkActive? ActiveBlock.wf
  rw [dif_neg (by simp; omega)]

theorem mkActive?_refuses_an_estimate_past_the_day (now : Cal.Instant) (a : ActiveBlock)
    (h : Look.maxDayMin < a.estMin) : mkActive? now a = none := by
  unfold mkActive? ActiveBlock.wf
  rw [dif_neg (by simp; omega)]

theorem mkActive?_accepts (now : Cal.Instant) (a : ActiveBlock)
    (h : ActiveBlock.wf now a = true) : (mkActive? now a).map Subtype.val = some a := by
  unfold mkActive?
  rw [dif_pos h]
  rfl

/-- Fork `state.break.where`, named (AGENTS §5.7) rather than left a free `String`. -/
inductive BreakPlace | walk | seat | bed | phone
deriving DecidableEq, Repr

/-- **Fork `store::BreakState`** — the running break. -/
structure BreakState where
  started    : Option Cal.Instant
  plannedMin : Nat
  place      : Option BreakPlace
deriving DecidableEq, Repr

/-- A break started at or before `now`, planned for at most a day. -/
def BreakState.wf (now : Cal.Instant) (b : BreakState) : Bool :=
  b.started.all (fun t => decide (t.sec ≤ now.sec)) && decide (b.plannedMin ≤ Look.maxDayMin)

abbrev WfBreak (now : Cal.Instant) := { b : BreakState // BreakState.wf now b = true }

def mkBreak? (now : Cal.Instant) (b : BreakState) : Option (WfBreak now) :=
  if h : BreakState.wf now b = true then some ⟨b, h⟩ else none

/-- The design's name for this row is `refuses_a_negative_break`, which **cannot be stated**:
the fork's field is a `u32` and this one is a `Nat`, so there is no negative break to refuse
and a theorem of that name would be a precondition nothing can satisfy (AGENTS §5.2, §9.2's
disguised-gap list).  The real bound is the day. -/
theorem mkBreak?_refuses_a_break_longer_than_a_day (now : Cal.Instant) (b : BreakState)
    (h : Look.maxDayMin < b.plannedMin) : mkBreak? now b = none := by
  unfold mkBreak? BreakState.wf
  rw [dif_neg (by simp; omega)]

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

/-- **Fork `store::InterruptState`** — the running interruption, which §8.2 choice 1 places as
an ad-hoc wall from `t_i` to `now` and which does **not** extend the window. -/
structure InterruptState where
  started : Option Cal.Instant
  id      : Option Id
deriving DecidableEq, Repr

def InterruptState.wf (now : Cal.Instant) (x : InterruptState) : Bool :=
  x.started.all (fun t => decide (t.sec ≤ now.sec))

abbrev WfInterrupt (now : Cal.Instant) := { x : InterruptState // InterruptState.wf now x = true }

def mkInterrupt? (now : Cal.Instant) (x : InterruptState) : Option (WfInterrupt now) :=
  if h : InterruptState.wf now x = true then some ⟨x, h⟩ else none

theorem mkInterrupt?_refuses_a_start_after_now (now : Cal.Instant) (x : InterruptState)
    (t : Cal.Instant) (hs : x.started = some t) (h : now.sec < t.sec) :
    mkInterrupt? now x = none := by
  unfold mkInterrupt? InterruptState.wf
  rw [dif_neg (by rw [hs]; simp; omega)]

theorem mkInterrupt?_accepts (now : Cal.Instant) (x : InterruptState)
    (h : InterruptState.wf now x = true) : (mkInterrupt? now x).map Subtype.val = some x := by
  unfold mkInterrupt?
  rw [dif_pos h]
  rfl

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

/-- Nothing running, nothing planned yet. -/
def RuntimeIn.empty : RuntimeIn := ⟨none, none, none, none, Capped.nil⟩

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

/-- The minutes the day spends on blocks — §8.3's overbooking law counts these.  (Was
`Goals.blockMinutes`; on seconds now, through `Seg.minutes`.) -/
def blockMinutes (d : DayPlan) : Nat :=
  (d.segments.filter (fun s => decide (s.val.kind = SegKind.block))).foldl
    (fun a s => a + s.val.minutes) 0

theorem assignedOf_empty (day : Day) (w : Nat × Nat) (bm bb : Nat) :
    assignedOf (DayPlan.empty day w bm bb) = [] := rfl

theorem blockMinutes_empty (day : Day) (w : Nat × Nat) (bm bb : Nat) :
    blockMinutes (DayPlan.empty day w bm bb) = 0 := rfl

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
  /-- The EDF pass's lookahead, day 0 included since K2. -/
  caps      : Lookahead
  /-- §9's five rows `Look.Today` does not carry. -/
  state     : RuntimeIn
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

/-- §8.1's window, through **the kernel's one reader of it** (`Look.day0Window`, step L9).
The fork's planner computes its own (`Planner::window_and_budget`) and the two disagree on
three inputs — README gap 320.  This module makes the disagreement *unrepresentable in the
request*: there is no window field for a second answer to be carried in. -/
def PlanReq.window (r : PlanReq) : Nat × Nat := Look.day0Window r.look

/-- §8.1's budget: the one `tm arrive` stored for today, else the formula
(`Look.budgetOf`, stage 5 L2).  Never recomputed here. -/
def PlanReq.budgetBlocks (r : PlanReq) : Nat :=
  match r.look.today0.storedBudget r.look.today with
  | some b => b
  | none => Look.budgetOf r.look.day.windowHours r.look.day.cut.blockMin r.look.day.budgetRatio

theorem PlanReq.window_is_the_lookaheads (r : PlanReq) :
    r.window = Look.day0Window r.look := rfl

theorem PlanReq.budget_is_the_stored_one_when_there_is_one (r : PlanReq) (b : Nat)
    (h : r.look.today0.storedBudget r.look.today = some b) : r.budgetBlocks = b := by
  unfold PlanReq.budgetBlocks
  rw [h]

theorem PlanReq.budget_is_the_formula_without_a_stored_one (r : PlanReq)
    (h : r.look.today0.storedBudget r.look.today = none) :
    r.budgetBlocks =
      Look.budgetOf r.look.day.windowHours r.look.day.cut.blockMin r.look.day.budgetRatio := by
  unfold PlanReq.budgetBlocks
  rw [h]

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

/-- `Cal.Instant.wf`'s own horizon, named once.  `Seg.wf` bounds a row by it (P0). -/
def horizonSec : Nat := 315537897600

theorem instant_wf_of_sec (n : Nat) (h : n < horizonSec) : Cal.Instant.wf ⟨n, 0⟩ = true := by
  simp only [Cal.Instant.wf, horizonSec] at *
  simp [h]

theorem Seg.wf_of (s : Seg) (h1 : s.start ≤ s.stop) (h2 : s.stop < horizonSec) :
    Seg.wf s = true := by
  simp [Seg.wf, instant_wf_of_sec _ h2, h1]

/-- A second inside the calendar. -/
def clampSec (n : Nat) : Nat := min n (horizonSec - 1)

theorem clampSec_lt (n : Nat) : clampSec n < horizonSec := by
  simp only [clampSec, horizonSec]; omega

theorem clampSec_id (n : Nat) (h : n < horizonSec) : clampSec n = n := by
  simp only [clampSec, horizonSec] at *; omega

/-- **The total constructor the placement steps use** (D28: `dayPlan` is total, so no step of
it may fail).  A row is forced forwards and into the calendar; `segOf_is_the_row_inside_the
_calendar` says the forcing is the identity on every row a day the boundary accepts can
produce, so this is a bound and not a rewrite. -/
def segOf (s : Seg) : WfSeg :=
  ⟨{ s with start := clampSec s.start, stop := max (clampSec s.start) (clampSec s.stop) },
    Seg.wf_of _ (Nat.le_max_left _ _) (Nat.max_lt.2 ⟨clampSec_lt _, clampSec_lt _⟩)⟩

theorem segOf_is_the_row_inside_the_calendar (s : Seg) (h1 : s.start ≤ s.stop)
    (h2 : s.stop < horizonSec) : (segOf s).val = s := by
  have h3 : s.start < horizonSec := by omega
  simp only [segOf, clampSec_id _ h2, clampSec_id _ h3, Nat.max_eq_right h1]

theorem segOf_kind (s : Seg) : (segOf s).val.kind = s.kind := rfl
theorem segOf_item (s : Seg) : (segOf s).val.item = s.item := rfl

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

/-- Fork `collect_walls`' clip: blocked from `max lo day_start`, ending at `min hi day_end`,
never before it starts; the event's own start moves with the blocked start. -/
def clipWall (lo hi : Nat) (x : Look.WallIx) : Look.WallIx :=
  { x with lo := max x.lo lo,
           evLo := max x.evLo (max x.lo lo),
           hi := max (min x.hi hi) (max x.lo lo) }

/-- Fork `collect_walls`' sort: by blocked start, then by id. -/
def wallLe (a b : Look.WallIx) : Bool :=
  decide (a.lo < b.lo) || (decide (a.lo = b.lo) && Log.charsLe a.id b.id)

/-- **§8.2 step 1's selection, with the request's three numbers as arguments.**  Stage 5's
index, selected for a day (`Look.wallIxOn`), clipped to it, in the fork's order; an empty clip
is dropped (`if e <= s { continue }`).  The request is not a parameter because the rule does
not depend on it — which is also what lets the rule be *run* and checked by `decide`
(`the_spec_days_walls_are_placed_where_they_are_written`; AGENTS §5.2, non-vacuity is a
separate check from correctness). -/
def wallsOfDay (dayLo dayHi d : Nat) (ix : List Look.WallIx) : List Look.WallIx :=
  Replay.insSort wallLe
    ((Look.wallIxOn ix d).filterMap fun x =>
      if (clipWall dayLo dayHi x).lo < (clipWall dayLo dayHi x).hi
      then some (clipWall dayLo dayHi x) else none)

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
      c = clipWall r.dayStart r.dayEnd x ∧ c.lo < c.hi := by
  have hm := (Replay.insSort_perm wallLe _).mem_iff.1 h
  simp only [wallsToday, wallsOfDay, List.mem_filterMap] at hm
  obtain ⟨x, hx, hc⟩ := hm
  obtain ⟨hmem, h1, h2⟩ := Look.mem_wallIxOn.1 hx
  by_cases hlt : (clipWall r.dayStart r.dayEnd x).lo < (clipWall r.dayStart r.dayEnd x).hi
  · rw [if_pos hlt] at hc
    have he : clipWall r.dayStart r.dayEnd x = c := Option.some.inj hc
    exact ⟨x, hmem, h1, h2, he.symm, he ▸ hlt⟩
  · rw [if_neg hlt] at hc; exact absurd hc (by simp)

/-- **A clipped wall keeps its id** — the row can name the item it is written on. -/
theorem clipWall_id (lo hi : Nat) (x : Look.WallIx) : (clipWall lo hi x).id = x.id := rfl

/-- **The clip never widens a wall.** -/
theorem clipWall_within (lo hi : Nat) (x : Look.WallIx) :
    x.lo ≤ (clipWall lo hi x).lo ∧ (clipWall lo hi x).hi ≤ max x.hi (max x.lo lo) := by
  cases x
  simp only [clipWall]
  omega

/-- **A wall wholly inside its day is not moved at all** — the hypothesis the restated
`plan_never_moves_a_wall` runs on. -/
theorem clipWall_id_inside (lo hi : Nat) (x : Look.WallIx) (h1 : lo ≤ x.lo) (h2 : x.hi ≤ hi)
    (h3 : x.lo ≤ x.evLo) (h4 : x.lo ≤ x.hi) : clipWall lo hi x = x := by
  have e1 : max x.lo lo = x.lo := by omega
  have e2 : max x.evLo (max x.lo lo) = x.evLo := by omega
  have e3 : max (min x.hi hi) (max x.lo lo) = x.hi := by omega
  unfold clipWall
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

/-- Today's record inside **this call's own replay** (D24's seam, `PlanReq.run`): the past half
and `blocks_done` both come from here, never from a second read of the log (D9). -/
def PlanReq.todayRecord (r : PlanReq) : Option Replay.DayAcc :=
  (r.run.answer.days.find? (fun d => decide (d.day = r.today))).bind (·.record)

/-- Fork `capacity::remaining_budget(budget, blocks_done)` — `Nat` subtraction *is* the fork's
`saturating_sub` — with §8.2 step 1's travel-day zeroing in front of it. -/
def remainingBudget (r : PlanReq) : Nat :=
  if travelDay r then 0
  else r.budgetBlocks - (r.todayRecord.map (·.blocksDone)).getD 0

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

/-- **§8.3's stability half** (fork `past_segments`): everything that ended before `now` comes
from the log, clipped to `[day_start, now]`, so a replan cannot move it.  The log is read
**once**, through D24's seam (`PlanReq.run`), and never a second time (D9). -/
def pastRows (r : PlanReq) : List Seg :=
  match r.todayRecord with
  | none => []
  | some d =>
    d.segments.filterMap fun g =>
      if min g.stop.1.sec r.now.sec ≤ max g.start.1.sec r.dayStart then none
      else
        some { start := max g.start.1.sec r.dayStart, stop := min g.stop.1.sec r.now.sec,
               kind := (pastKind g.kind).1, energy := none, item := (pastKind g.kind).2.1,
               inst := pastInst g.kind,
               flags := { SegFlags.none with
                 done := ((pastKind g.kind).1 == SegKind.routine) ||
                   (((pastKind g.kind).2.1).map (fun i => decide (i ∈ d.done))).getD false },
               planned := none, mult := none, note := (pastKind g.kind).2.2 }

/-- **The past half ends at `now`** — nothing it holds is in the future, which is the half of
L25 that makes a replan able to leave it alone (design §7.2 item 1). -/
theorem pastRows_end_at_now (r : PlanReq) (s : Seg) (h : s ∈ pastRows r) :
    r.dayStart ≤ s.start ∧ s.start < s.stop ∧ s.stop ≤ r.now.sec := by
  unfold pastRows at h
  split at h
  · cases h
  · simp only [List.mem_filterMap] at h
    obtain ⟨g, _, hg⟩ := h
    by_cases hc : min g.stop.1.sec r.now.sec ≤ max g.start.1.sec r.dayStart
    · rw [if_pos hc] at hg; exact absurd hg (by simp)
    · rw [if_neg hc] at hg
      have he := Option.some.inj hg
      subst he
      exact ⟨Nat.le_max_right _ _, Nat.lt_of_not_le hc, Nat.min_le_right _ _⟩

/-- **The past half is never a wall row.**  A wall is placed from the plan; the past is
replayed from the log, and the two never meet in one row. -/
theorem pastRows_are_not_walls (r : PlanReq) (s : Seg) (h : s ∈ pastRows r) :
    s.kind ≠ SegKind.wall := by
  unfold pastRows at h
  split at h
  · cases h
  · simp only [List.mem_filterMap] at h
    obtain ⟨g, _, hg⟩ := h
    split at hg
    · cases hg
    · have he := Option.some.inj hg
      subst he
      cases g.kind <;> simp [pastKind]

/-! ### The day, assembled -/

/-- Fork `day.segments.sort_by(|a, b| a.start.cmp(&b.start).then(a.end.cmp(&b.end)))`. -/
def rowLe (a b : WfSeg) : Bool :=
  decide (a.val.start < b.val.start) ||
    (decide (a.val.start = b.val.start) && decide (a.val.stop ≤ b.val.stop))

/-- **§8.2 step 1's rows, in the fork's order.** -/
def stepOneRows (r : PlanReq) : List WfSeg :=
  Replay.insSort rowLe
    ((pastRows r ++ interruptRows r ++
      (wallsToday r).flatMap (fun x => wallRows (r.isTravelDay x.id) x)).map segOf)

theorem mem_stepOneRows {r : PlanReq} {s : WfSeg} (h : s ∈ stepOneRows r) :
    ∃ t ∈ pastRows r ++ interruptRows r ++
      (wallsToday r).flatMap (fun x => wallRows (r.isTravelDay x.id) x), s = segOf t := by
  have hm := (Replay.insSort_perm rowLe _).mem_iff.1 h
  simpa [eq_comm] using List.mem_map.1 hm

/-- §8.2 step 8's diagnostics, as far as step 1 fills them: the overlapping walls it refused to
resolve, and the travel-day note. -/
def stepOneDiagnostics (r : PlanReq) : Diagnostics :=
  { Diagnostics.empty with
    conflicts := Capped.ofListTake (wallConflicts (wallsToday r))
    notes := if travelDay r then Capped.ofListTake [Note.travelDay] else Capped.nil }

/-- **D28: this signature is total and stays total.**  There is no `dayPlan?`, no
`PlanRefusal` and no `Except` — the eleven single-run laws of §8.3 are proved over this shape
(G1), not gated behind a refusal.

**What it does today (step P1).**  §8.2 step 1: the day's walls, placed where the plan's own
index puts them; §9's running interruption as an ad-hoc wall; the past half replayed from this
call's own run; the overlapping pairs named and unresolved; and a `travel-day` wall's zeroing
of the remaining budget.  Steps 2 to 7 are P2..P7 and none of them is written here. -/
def dayPlan (r : PlanReq) : DayPlan :=
  { DayPlan.empty r.today r.window r.blockMin r.budgetBlocks with
    segments := stepOneRows r
    diagnostics := stepOneDiagnostics r }

theorem dayPlan_day (r : PlanReq) : (dayPlan r).day = r.today := rfl

theorem dayPlan_window (r : PlanReq) : (dayPlan r).window = Look.day0Window r.look := rfl

theorem dayPlan_blockMin (r : PlanReq) : (dayPlan r).blockMin = r.look.day.cut.blockMin := rfl

/-- **The day carries §8.1's budget, not the remaining one** — fork
`DayPlan::empty(date, window, budget_blocks)` (`planner.rs:1065`), where `remaining_budget` is a
*local* the assign loop and `diagnose` consume and never a field of the day.  Spec §8.3 words
the overbooking law with `remaining_budget`; the two disagree on a day with blocks already
done, and `plan_does_not_overbook` is §6.3's to restate at **P5** with that named. -/
theorem dayPlan_budgetBlocks (r : PlanReq) : (dayPlan r).budgetBlocks = r.budgetBlocks := rfl

/-- **The remaining budget is beside the day, not inside it** — what §8.2 step 5 will spend,
already zeroed by a travel day. -/
theorem dayPlan_remaining_budget_is_the_forks_local (r : PlanReq) :
    remainingBudget r ≤ (dayPlan r).budgetBlocks := remainingBudget_le_budget r

theorem dayPlan_segments (r : PlanReq) : (dayPlan r).segments = stepOneRows r := rfl

/-- **P8 must delete this.**  The FNV-1a digest is the emitter's; until it lands, the identity
`state.last_plan_hash` would compare against is a placeholder and says so. -/
theorem the_plan_hash_is_a_placeholder_until_the_emitter_lands (r : PlanReq) :
    (dayPlan r).planHash = PlanHash.zero := rfl

/-- **Fork `DayPlan::assigned_from`** (`planner.rs:647`): the items the day assigns at or after
an instant.  §8.3's laws are about *this* set and not about `assigned` — the proptest's own
`assigned_set(day, w.now)` says so (`planner_invariants.rs:470`: "the planner's doing and never
count as 'assigned' for §8.3"), because the replayed past holds Blocks that were worked and
that no replan can move. -/
def assignedFrom (d : DayPlan) (t : Nat) : List Id :=
  (d.segments.filter (fun s => s.val.kind.isWork && decide (t ≤ s.val.start))).flatMap segItems

/-- **P5 must delete this.**  Step 1 places three kinds of row and none of them is a *future*
assignment: the replayed past ends at `now`, the running interruption ends at `now`, and a
Wall is not work.  So the set §8.3's laws are about is still empty and no goal that
quantifies over an assigned Block may be discharged against this body (README gap 347).

It is stated over `assignedFrom … now` and **not** over `assignedOf`, because a replayed past
Block *is* work and *is* in `assignedOf` — the fork counts it too (`DayPlan::assigned`), and a
tripwire that claimed otherwise would be false the moment the seam had anything to replay. -/
theorem the_day_assigns_nothing_after_now_until_the_assign_step_lands (r : PlanReq) :
    assignedFrom (dayPlan r) r.now.sec = [] := by
  have hw : ∀ s ∈ stepOneRows r, (s.val.kind.isWork && decide (r.now.sec ≤ s.val.start)) = false := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := mem_stepOneRows hs
    simp only [List.mem_append] at ht
    rcases ht with (ht | ht) | ht
    · obtain ⟨_, h2, h3⟩ := pastRows_end_at_now r t ht
      have : (segOf t).val.start < r.now.sec := by
        show clampSec t.start < r.now.sec
        have := clampSec_lt t.start
        simp only [clampSec]; omega
      simp [Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le, this]
    · have h1 := interruptRows_are_open_lost_time r t ht
      have h2 : (segOf t).val.kind = SegKind.lost := by rw [segOf_kind, h1.1]
      simp [SegKind.isWork, h2]
    · simp only [List.mem_flatMap] at ht
      obtain ⟨x, _, hx⟩ := ht
      have h2 : (segOf t).val.kind = SegKind.wall := by
        rw [segOf_kind, (wallRows_are_walls_of_the_item (r.isTravelDay x.id) x t hx).1]
      simp [SegKind.isWork, h2]
  have hf : (dayPlan r).segments.filter
      (fun s => s.val.kind.isWork && decide (r.now.sec ≤ s.val.start)) = [] := by
    rw [dayPlan_segments]
    exact List.filter_eq_nil_iff.2 (fun s hs => by simp [hw s hs])
  simp [assignedFrom, hf]

/-! ### The two wall goals

`plan_places_no_block_over_a_wall` is **not discharged here** and must not be: step 1 places no
Block of its own, so the statement is about the replayed past alone and says nothing about the
planner.  The invariant it needs is already stage 5's
(`Look.day0_slots_avoid_the_walls`), and the goal becomes non-vacuous at **P5**, where Blocks
are assigned; design §6.4's row gives it to P1, and that row is wrong (README gap 347).

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
    (hcal : (Cal.instantOf r.tz b.day b.time).sec < horizonSec) :
    w.val.start = (Cal.instantOf r.tz a.day a.time).sec ∧
      w.val.stop = (Cal.instantOf r.tz b.day b.time).sec := by
  obtain ⟨t, ht, rfl⟩ := mem_stepOneRows (dayPlan_segments r ▸ hw)
  simp only [List.mem_append] at ht
  rcases ht with (ht | ht) | ht
  · exact absurd (segOf_kind t ▸ hk) (pastRows_are_not_walls r t ht)
  · exact absurd (segOf_kind t ▸ hk) (interruptRows_are_not_walls r t ht)
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
    have hclip : clipWall r.dayStart r.dayEnd y = y :=
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

/-- **Both ends of every wall row come from the index, and neither comes from the planner** —
the sentence `plan_never_moves_a_wall` was written to protect, true of a buffered wall and of a
clipped one alike. -/
theorem a_wall_row_comes_from_the_index (r : PlanReq) (w : WfSeg)
    (hw : w ∈ (dayPlan r).segments) (hk : w.val.kind = SegKind.wall) :
    ∃ x ∈ r.look.walls, x.fromDay ≤ r.today ∧ r.today ≤ x.toDay ∧
      w.val.item = some x.id ∧
      ((w.val.start = clampSec (clipWall r.dayStart r.dayEnd x).lo ∧
        w.val.stop = max (clampSec (clipWall r.dayStart r.dayEnd x).lo)
          (clampSec (clipWall r.dayStart r.dayEnd x).evLo)) ∨
       (w.val.start = clampSec (clipWall r.dayStart r.dayEnd x).evLo ∧
        w.val.stop = max (clampSec (clipWall r.dayStart r.dayEnd x).evLo)
          (clampSec (clipWall r.dayStart r.dayEnd x).hi))) := by
  obtain ⟨t, ht, rfl⟩ := mem_stepOneRows (dayPlan_segments r ▸ hw)
  simp only [List.mem_append] at ht
  rcases ht with (ht | ht) | ht
  · exact absurd (segOf_kind t ▸ hk) (pastRows_are_not_walls r t ht)
  · exact absurd (segOf_kind t ▸ hk) (interruptRows_are_not_walls r t ht)
  · simp only [List.mem_flatMap] at ht
    obtain ⟨c, hc, hrow⟩ := ht
    obtain ⟨x, hx, h1, h2, hxc, _⟩ := mem_wallsToday hc
    refine ⟨x, hx, h1, h2, ?_, ?_⟩
    · rw [segOf_item, (wallRows_are_walls_of_the_item (r.isTravelDay c.id) c t hrow).2, hxc, clipWall_id]
    · rw [← hxc]
      simp only [wallRows, List.mem_append] at hrow
      rcases hrow with hr | hr
      · split at hr
        · simp only [List.mem_singleton] at hr; subst hr; exact Or.inl ⟨rfl, rfl⟩
        · cases hr
      · simp only [List.mem_singleton] at hr; subst hr; exact Or.inr ⟨rfl, rfl⟩

end Planner
end Tm
