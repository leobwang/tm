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

/-- Every item the day assigns.  (Was `Goals.assignedOf`.) -/
def assignedOf (d : DayPlan) : List Id := d.segments.flatMap segItems

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

/-! ## `dayPlan`

**D28: this signature is total and stays total.**  There is no `dayPlan?`, no `PlanRefusal`
and no `Except` — the eleven single-run laws of §8.3 are proved over this shape (G1), not
gated behind a refusal.

**What it does today (step P0).**  It returns the fork's `DayPlan::empty` for the request's
day: the window and the budget, and no segments.  §8.2's eight steps are P1..P7 and none of
them is written here — half-building step 1 in the step that settles the vocabulary is how a
representation gets frozen around one caller.  The two theorems below state the emptiness as a
law, so the step that fills the day **cannot leave them standing**. -/
def dayPlan (r : PlanReq) : DayPlan :=
  DayPlan.empty r.today r.window r.blockMin r.budgetBlocks

theorem dayPlan_day (r : PlanReq) : (dayPlan r).day = r.today := rfl

theorem dayPlan_window (r : PlanReq) : (dayPlan r).window = Look.day0Window r.look := rfl

theorem dayPlan_blockMin (r : PlanReq) : (dayPlan r).blockMin = r.look.day.cut.blockMin := rfl

theorem dayPlan_budgetBlocks (r : PlanReq) : (dayPlan r).budgetBlocks = r.budgetBlocks := rfl

theorem dayPlan_diagnostics (r : PlanReq) : (dayPlan r).diagnostics = Diagnostics.empty := rfl

/-- **P1 must delete this.**  Until §8.2 step 1 lands, the day is empty and every §8.3 law is
vacuously true of it; none of the thirteen goals may be discharged against this body. -/
theorem the_day_has_no_segments_until_the_first_step_lands (r : PlanReq) :
    (dayPlan r).segments = [] := rfl

/-- **P8 must delete this.**  The FNV-1a digest is the emitter's; until it lands, the identity
`state.last_plan_hash` would compare against is a placeholder and says so. -/
theorem the_plan_hash_is_a_placeholder_until_the_emitter_lands (r : PlanReq) :
    (dayPlan r).planHash = PlanHash.zero := rfl

theorem dayPlan_assigns_nothing_yet (r : PlanReq) : assignedOf (dayPlan r) = [] := rfl

theorem dayPlan_spends_no_minutes_yet (r : PlanReq) : blockMinutes (dayPlan r) = 0 := rfl

end Planner
end Tm
