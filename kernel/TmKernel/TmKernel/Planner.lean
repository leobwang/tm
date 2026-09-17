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
overrun at all.  That was a silent weakening of `plan_does_not_overbook` and of
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

/-- **§8.2 step 1's rows.**  The day's own order is `dayRows`, once step 2 has added its
own (this list is step 1's contribution and nothing more). -/
def stepOneSegs (r : PlanReq) : List Seg :=
  pastRows r ++ interruptRows r ++
    (wallsToday r).flatMap (fun x => wallRows (r.isTravelDay x.id) x)

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
  restatement `PlanCheck.dayPlan_ok_core`'s own comment assigns to **P5**.  Until it lands a
  routine may be placed over the running block (README gap 434).
* **`diagnostics.notes`' un-placed note** (`planner.rs:1055`) is **P6**'s: a deferred routine is
  only *finally* un-placed once step 6 has tried the lowest-energy position.  `Note.noPosition`
  exists and nothing constructs it yet.
* **A routine row's `hot` mark** is §7.2's `p = 0`, which is **P4**'s pass; the rows carry
  `hot := false` and the flag becomes real there (README gap 435).
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

/-- **What `earliestFree` answers is inside the range it was asked about.** -/
theorem earliestFree_inside {lo hi d : Nat} {ws : List (Nat × Nat)} {s : Nat}
    (h : earliestFree lo hi d ws = some s) : lo ≤ s ∧ s + d ≤ hi := by
  unfold earliestFree at h
  cases hf : (Look.freeIntervals lo hi ws).find? (fun iv => decide (d ≤ iv.2 - iv.1)) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some iv =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have hm : iv ∈ Look.freeIntervals lo hi ws := List.mem_of_find?_eq_some hf
    have hd : d ≤ iv.2 - iv.1 := by
      have := List.find?_some hf
      simpa using this
    obtain ⟨h1, h2, h3⟩ := Look.freeIntervals_inside_the_window hm
    exact ⟨h1, by omega⟩

/-- **And every second of it is free.**  This is the half that makes the placement laws mean
something: a routine placed at `earliestFree` overlaps nothing that was blocked. -/
theorem earliestFree_is_free {lo hi d : Nat} {ws : List (Nat × Nat)} {s u : Nat}
    (h : earliestFree lo hi d ws = some s) (h1 : s ≤ u) (h2 : u < s + d) :
    Look.covered ws u = false := by
  unfold earliestFree at h
  cases hf : (Look.freeIntervals lo hi ws).find? (fun iv => decide (d ≤ iv.2 - iv.1)) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some iv =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have hm : iv ∈ Look.freeIntervals lo hi ws := List.mem_of_find?_eq_some hf
    have hd : d ≤ iv.2 - iv.1 := by
      have := List.find?_some hf
      simpa using this
    obtain ⟨hlo, hlt, hhi⟩ := Look.freeIntervals_inside_the_window hm
    have hin : ∃ w ∈ Look.freeIntervals lo hi ws, w.1 ≤ u ∧ u < w.2 :=
      ⟨iv, hm, h1, by omega⟩
    have hfree := (Look.freeIntervals_are_the_free_units lo hi ws u).1 hin
    cases hc : Look.covered ws u with
    | false => rfl
    | true =>
      obtain ⟨w, hw, hw1, hw2⟩ := Look.covered_eq_true.1 hc
      exact absurd ⟨hw1, hw2⟩ (hfree.2.2 w hw)

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

`Replay.insSort` is the **specification** sort, as `wallsOfDay`'s is; it has no compiled twin for
the same reason that one does not (`Log.charsLe` has no transitivity or totality lemma in the
tree), and it is the same open **gap 394**, not a second one. -/
def routineLe (a b : Placed) : Bool :=
  (decide (a.inst.mandatory = true) && decide (b.inst.mandatory = false)) ||
    (decide (a.inst.mandatory = b.inst.mandatory) &&
      (decide (a.span.2 < b.span.2) ||
        (decide (a.span.2 = b.span.2) && Log.charsLe a.inst.id b.inst.id)))

def sortRoutines (l : List Placed) : List Placed := Replay.insSort routineLe l

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

**The Active reservation is NOT here** (design §2 choice 5b; fork `run()` pushes `active_run`
before `place_mandatory_and_pref`).  It is not a missing input — see this section's header — but
the first Block row the planner places, which `PlanCheck` cannot yet accept.  README gaps 434
and 437. -/
def blockedByWalls (r : PlanReq) : List (Nat × Nat) :=
  (wallsToday r).map (fun x => (x.lo, x.hi)) ++
    (interruptRows r).map (fun s => (s.start, s.stop))

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

/-- **§8.2 step 2, run**: today's window instances, sorted, each placed or deferred.  D9-21: a
`List.foldl` over a list `Capped` bounds at `maxCands`. -/
def PlanReq.placedRoutines (r : PlanReq) : List Placed :=
  (((sortRoutines (splitSleep r r.routineInstances).2).foldl (placeStep r)
    ([], blockedByWalls r)).1).reverse

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
  unfold PlanReq.placedRoutines at hp
  rw [List.mem_reverse] at hp
  exact foldl_placeStep_keeps_PlacedOk r _ _ (by simp) p hp a b hab

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

/-- **Fork `emit_segments`' routine loop** (`planner.rs:1802-1836`): one Routine row per *placed*
instance; a deferred one has no row until step 6 places it (P6).

The `hot` mark is §7.2's `p = 0` and is **P4**'s (README gap 435); it is `false` here, and P4 is
the step that must set it. -/
def PlanReq.routineRow (r : PlanReq) (q : Placed) : List Seg :=
  match q.placedAt with
  | none => []
  | some (a, b) =>
    [{ start := a, stop := b, kind := .routine, energy := r.routineEnergy q.inst.id,
       item := some q.inst.id, inst := q.inst.inst.map (fun k => (q.inst.id, k)),
       flags := { SegFlags.none with mandatory := q.inst.mandatory, deferred := q.deferred },
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

/-- **§8.2 step 2's rows.** -/
def stepTwoSegs (r : PlanReq) : List Seg :=
  r.placedRoutines.flatMap r.routineRow ++ r.eveningRows

/-- **Step 2 places three kinds of row and no other.** -/
theorem stepTwoSegs_kinds (r : PlanReq) (t : Seg) (h : t ∈ stepTwoSegs r) :
    t.kind = SegKind.routine ∨ t.kind = SegKind.windDown ∨ t.kind = SegKind.sleep := by
  simp only [stepTwoSegs, List.mem_append] at h
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

/-- **No row of step 2 is a Wall**, so the two wall laws are untouched by it. -/
theorem stepTwoSegs_are_not_walls (r : PlanReq) (t : Seg) (h : t ∈ stepTwoSegs r) :
    t.kind ≠ SegKind.wall := by
  rcases stepTwoSegs_kinds r t h with h1 | h1 | h1 <;> rw [h1] <;> intro hc <;> cases hc

/-- **No row of step 2 is a Block**, so every block-side check of the battery is still about the
replayed past alone (`PlanCheck.dayPlan_block_rows_come_from_the_log`). -/
theorem stepTwoSegs_are_not_blocks (r : PlanReq) (t : Seg) (h : t ∈ stepTwoSegs r) :
    t.kind ≠ SegKind.block := by
  rcases stepTwoSegs_kinds r t h with h1 | h1 | h1 <;> rw [h1] <;> intro hc <;> cases hc

/-- **And none of them is work**, so §8.3's assigned set is still empty after `now`
(`SegKind.isWork`: `Block` and `Batch`, and nothing else). -/
theorem stepTwoSegs_are_not_work (r : PlanReq) (t : Seg) (h : t ∈ stepTwoSegs r) :
    t.kind.isWork = false := by
  rcases stepTwoSegs_kinds r t h with h1 | h1 | h1 <;> rw [h1] <;> rfl

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

/-! ### The day, assembled -/

/-- **A deferred instance has no row until step 6 places it** — fork `emit_segments`' routine
loop skips an instance with no `placed`, and `place_deferred` (**P6**) is what gives it one. -/
theorem a_deferred_routine_has_no_row (r : PlanReq) (q : Placed) (h : q.placedAt = none) :
    r.routineRow q = [] := by
  unfold PlanReq.routineRow; rw [h]

/-- **The day's rows**, steps 1 and 2, in the fork's order. -/
def dayRows (r : PlanReq) : List WfSeg :=
  sortRows ((stepOneSegs r ++ stepTwoSegs r).map segOf)

theorem mem_dayRows {r : PlanReq} {s : WfSeg} (h : s ∈ dayRows r) :
    ∃ t ∈ stepOneSegs r ++ stepTwoSegs r, s = segOf t := by
  have hm := mem_sortRows.1 h
  simpa [eq_comm] using List.mem_map.1 hm

/-- §8.2 step 8's diagnostics, as far as steps 1 and 2 fill them: the overlapping walls step 1
refused to resolve, and the travel-day note.

**Step 2 adds nothing here, and the empty slot is deliberate.**  `Diagnostics.deferred` is
§8.2 step 8's *posterior-downgrade* list — fork `planner.rs:149`, "the candidates a *posterior
downgrade* cost a slot" — and **not** the routines step 2 deferred to step 6.  Writing the
deferred instances into it would give one field two meanings, which is the defect this kernel
is named after (AGENTS §5.3).  A deferred routine is carried on its own `Placed` record with
`deferred := true` and no position, which is exactly the state fork `place_deferred` receives,
and `Note.noPosition` is what names it if step 6 cannot place it either (**P6**). -/
def dayDiagnostics (r : PlanReq) : Diagnostics :=
  { Diagnostics.empty with
    conflicts := Capped.ofListTake (wallConflicts (wallsToday r))
    notes := if travelDay r then Capped.ofListTake [Note.travelDay] else Capped.nil }

/-- **D28: this signature is total and stays total.**  There is no `dayPlan?`, no
`PlanRefusal` and no `Except` — the eleven single-run laws of §8.3 are proved over this shape
(G1), not gated behind a refusal.

**What it does today (steps P1 and P2).**  §8.2 step 1: the day's walls, placed where the plan's
own index puts them; §9's running interruption as an ad-hoc wall; the past half replayed from
this call's own run; the overlapping pairs named and unresolved; and a `travel-day` wall's
zeroing of the remaining budget.  §8.2 step 2: today's window instances placed mandatory-first
inside their own windows or at a free `pref:` anchor, the rest deferred to step 6, and the
wind-down and sleep rows that close the day.  Steps 3 to 7 are P3..P7 and none of them is
written here. -/
def dayPlan (r : PlanReq) : DayPlan :=
  { DayPlan.empty r.today r.window r.blockMin r.budgetBlocks with
    segments := dayRows r
    diagnostics := dayDiagnostics r }

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

theorem dayPlan_segments (r : PlanReq) : (dayPlan r).segments = dayRows r := rfl

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

/-- **P5 must delete this.**  Steps 1 and 2 place six kinds of row and none of them is a *future*
assignment: the replayed past ends at `now`, the running interruption ends at `now`, a Wall is
not work, and neither is a Routine, a WindDown or a Sleep.  So the set §8.3's laws are about is
still empty and no goal that quantifies over an assigned Block may be discharged against this
body (README gap 347).

It is stated over `assignedFrom … now` and **not** over `assignedOf`, because a replayed past
Block *is* work and *is* in `assignedOf` — the fork counts it too (`DayPlan::assigned`), and a
tripwire that claimed otherwise would be false the moment the seam had anything to replay. -/
theorem the_day_assigns_nothing_after_now_until_the_assign_step_lands (r : PlanReq) :
    assignedFrom (dayPlan r) r.now.sec = [] := by
  have hw : ∀ s ∈ dayRows r, (s.val.kind.isWork && decide (r.now.sec ≤ s.val.start)) = false := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := mem_dayRows hs
    simp only [stepOneSegs, List.mem_append] at ht
    rcases ht with ((ht | ht) | ht) | ht
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
    · have h2 : (segOf t).val.kind.isWork = false := by
        rw [segOf_kind]; exact stepTwoSegs_are_not_work r t ht
      simp [h2]
  have hf : (dayPlan r).segments.filter
      (fun s => s.val.kind.isWork && decide (r.now.sec ≤ s.val.start)) = [] := by
    rw [dayPlan_segments]
    exact List.filter_eq_nil_iff.2 (fun s hs => by simp [hw s hs])
  simp [assignedFrom, hf]

/-! ### The two wall goals

`plan_places_no_block_over_a_wall` is **not discharged here** and must not be: steps 1 and 2
place no Block of their own, so the statement is about the replayed past alone and says nothing
about the planner.  The invariant it needs is already stage 5's
(`Look.day0_slots_avoid_the_walls`), and the goal becomes non-vacuous at **P5**; design §6.4's
row gives it to P1, and that row is wrong (README gap 347).

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
  rcases ht with ((ht | ht) | ht) | ht
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
  · exact absurd (segOf_kind t ▸ hk) (stepTwoSegs_are_not_walls r t ht)

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
  obtain ⟨t, ht, rfl⟩ := mem_dayRows (dayPlan_segments r ▸ hw)
  simp only [stepOneSegs, List.mem_append] at ht
  rcases ht with ((ht | ht) | ht) | ht
  · exact absurd (segOf_kind t ▸ hk) (pastRows_are_not_walls r t ht)
  · exact absurd (segOf_kind t ▸ hk) (interruptRows_are_not_walls r t ht)
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
  · exact absurd (segOf_kind t ▸ hk) (stepTwoSegs_are_not_walls r t ht)

/-- **Every Block row of the day still comes from the log.**  Steps 1 and 2 place walls, the
running interruption, the replayed past, the routines and the evening; a Wall is not a Block, an
interruption is Lost time, and `stepTwoSegs_are_not_blocks` covers the rest.  `PlanCheck` states
the same fact over `dayPlan` and this is the row-level half of it. -/
theorem a_block_row_is_a_replayed_row (r : PlanReq) (s : WfSeg)
    (hs : s ∈ dayRows r) (hk : s.val.kind = SegKind.block) :
    ∃ t ∈ pastRows r, s = segOf t := by
  obtain ⟨t, ht, rfl⟩ := mem_dayRows hs
  have htk : t.kind = SegKind.block := (segOf_kind t).symm.trans hk
  simp only [stepOneSegs, List.mem_append] at ht
  rcases ht with ((ht | ht) | ht) | ht
  · exact ⟨t, ht, rfl⟩
  · rw [(interruptRows_are_open_lost_time r t ht).1] at htk; cases htk
  · simp only [List.mem_flatMap] at ht
    obtain ⟨x, _, hx⟩ := ht
    rw [(wallRows_are_walls_of_the_item (r.isTravelDay x.id) x t hx).1] at htk
    cases htk
  · exact absurd htk (stepTwoSegs_are_not_blocks r t ht)

/-! ### The wind-down goal is NOT discharged here, and the reason is P1's

`Goals.plan_places_no_demanding_block_after_wind_down` quantifies over a **Block** row, and
design §14.2's P2 row says P2 discharges it.  **That row is wrong for the same reason §6.4's P1
row was** (README gap 347): step 2 places the WindDown row the law is *about*, but no Block, so
the statement is still vacuous over `dayPlan` and a discharge would be AGENTS §5.2's theorem
that compiles and means nothing.  What P2 owes it is the other half of its subject, and that is
what landed; the goal becomes real at **P5** (README gap 430).

The tripwire is `the_day_assigns_nothing_after_now_until_the_assign_step_lands` above, which P5
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
  have hseg : r.windDownSeg ∈ stepTwoSegs r := by
    simp only [stepTwoSegs, List.mem_append]
    refine Or.inr ?_
    unfold PlanReq.eveningRows
    simp only [List.mem_append]
    exact Or.inl (by rw [if_pos ⟨h1, h2⟩]; exact List.mem_singleton_self _)
  refine ⟨segOf r.windDownSeg, ?_, segOf_kind _, ?_, ?_⟩
  · rw [dayPlan_segments]
    exact mem_sortRows.2 (List.mem_map.2 ⟨_, List.mem_append_right _ hseg, rfl⟩)
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

end Planner
end Tm
