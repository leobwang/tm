import TmKernel.Boundary
import TmKernel.Emit
/-!
# `EmitWire.lean` — an `Emit.Row` crosses the wire (stage 6, W-24, README gaps 1105/1318)

`Emit.lean` landed at W-22 with **no caller**.  Nothing on the wire carried a `Row`, the FFI
entry was `callCap`, `emit::render_row` built its cells out of the Rust `Segment`, and the only
machine evidence for the module was its `#print axioms` lines — **21** at `596b56d`, not the
nineteen gap 1318 says (README gap 1331): *the kernel's cells had never been compared to the
shipped bytes by anything but a reader*.  That is what this module ends.

## What crosses, and what does NOT

**The request's new `plan` section carries the day's ROWS, not the day's inputs.**  Design
§10.1's `plan` section (`blockMin`, `day`, `curves`, `allowHome`, `overrides`) is the
*planner's* input and belongs with step R3, where `tm-core/src/planner.rs` dies (D34); the
planner in the shipped binary is still the fork's, so the kernel cannot be asked for the day it
renders.  What it CAN be asked for — and what D30 Q6 (a) actually settles — is the **cells**:
"the kernel emits cells; one Rust function pads".  So the host sends the segments its planner
produced and the kernel answers `Emit.rowOf` for each, reading the item titles, `ci`, estimates
and parents out of **its own** loaded plan and not out of a Rust `Tree`.  A disagreement
between the two readings is exactly what `tm/tests/kernel_row_cells.rs` now fails on.

**`Emit.rowsOf` still has no caller**, and that is stated rather than hidden: it is
`dayPlan`'s rows, and `dayPlan` is the kernel's planner.  This module calls `Emit.rowOf`, which
is every cell function in the module; `rowsOf` is `List.map` of it over a day this kernel did
not plan (README gap 1320).

## Nothing here re-reads a shape the boundary already reads (AGENTS §5.3)

Every value is decoded by a constructor that already exists, and the one this module declares
(`idWithin`) re-uses a bound that does rather than inventing a number: **this sentence was
false when it was written**, and README gap **1415** is the audit that said so — three of the
section's `Id`s reached the kernel with no bound at all, and two more inside `readNote` that
the audit did not name.  The segments' bound is
`Planner.Capped` — **the wire's own candidate cap**.  (`CapWire.maxCandidates` is the same
number under a second name, which is README gap **1330**, found here and not fixed here.) the priorities go through `Priority.yesterdayOf?` (the one reader of a
stored `p`), the multiplier through `CapWire.multiplierOfWire` (the one bounded-rational
reader, `boundedPair` at the multiplier's constants), the batch through `Planner.mkBatch?`, the
energy through `levelOf?`, the clock through `Field.parseClock`, `blockMin` through the
request's own `BlockMin.ofNat?` and the segment itself through `Planner.mkSeg?` — whose two
rejection theorems are the segment's R10 and are not restated here.  The JSON readers are
`CapWire`'s (`need`, `natAt`, `strAt`, `arrAt`, `optNatAt`, `opt`), reached through `asPlan`,
which renames the refusal and nothing else: they are typed to `CapWire.Refusal` and this
section's names are its own, so a **rename** is the whole adapter and `asPlan_keeps_the_value`
says it cannot turn an answer into a refusal.

## R10's table for this section

| wire value | bound | constructor | rejection theorem |
|---|---|---|---|
| a segment | `Seg.wf` — forwards, and inside the calendar | `Planner.mkSeg?` | `readSeg_refuses_an_inverted_segment`, `readSeg_refuses_past_the_horizon` |
| the segment list | `Planner.maxCands` | `Planner.Capped.ofList?` | `readSegs_refuses_past_the_cap` |
| a batch's members, in number | `Planner.maxBatch` | `Planner.mkBatch?` | `readKind_refuses_a_batch_past_the_cap` |
| a batch member's own id | `CapWire.maxCandId` | `idWithin` | `readKind_refuses_a_long_batch_member` |
| a segment's `item` | `CapWire.maxCandId` | `idWithin` | `readSeg_refuses_a_long_item` |
| a priority record's `id` | `CapWire.maxCandId` | `idWithin` | `readPrio_refuses_a_long_id` |
| a replayed note's two ids | `CapWire.maxCandId` | `idWithin` | `readNote_refuses_a_long_no_position_id`, `readNote_refuses_a_long_buffer_before_id` |
| a slot energy | `Fin 6` | `levelOf?` | `readSeg_refuses_an_energy_past_five` |
| `planned` | `CapWire.maxRemaining` (`Look.maxPlanMinutes`) | a guard in `readSeg` | `readSeg_refuses_a_planned_past_the_bound` |
| the multiplier | `maxMultiplier` over `maxPairDen` | `CapWire.multiplierOfWire` | `readSeg_refuses_a_zero_denominator` |
| a priority | `Fin 8` | `Priority.yesterdayOf?` | `readPrio_refuses_a_priority_past_seven` |
| the priority list | `Planner.maxCands` | `Planner.Capped.ofList?` | `readPrios_refuses_past_the_cap` |
| a replayed note's text | `maxNoteText` (the one bound this module declares) | a guard in `readNote` | `readNote_refuses_a_long_text` |
| `bed` | `Fin 1440` | `Field.parseClock` | — the clock grammar's own (`parse_render_clock`) |
| `blockMin` | `BlockMin` | `BlockMin.ofNat?` | — the request clock's own (`badBlockMin`) |

## The FFI entry moved here, and that is the only edit this step makes to `Boundary.lean`

R9 is one export and one shim function, so the export is a single symbol and it now lives at
the end of the pipeline rather than in the middle of it: `Boundary.callExport` keeps its body
and its theorem (`callExport_without_capacity_is_call`) and loses its `@[export]` attribute,
and `EmitWire.callExport` is what `tm_kernel_call` reaches.  A request with no `plan` section
is answered byte for byte as before (`runRows_without_a_plan_section_is_runCap`).
-/

namespace Tm
namespace EmitWire

open Planner (Seg SegKind SegFlags Note WfSeg Capped)
open Emit (Row)

/-! ## The section's names (AGENTS §5.7: every diagnostic is named) -/

/-- A key of the `plan` section, or of one of its segment records. -/
inductive RowKey
  | bed | priorities | segments
  | start | stop | kind | batch | energy | item | planned | mult | flags | note
deriving DecidableEq, Repr

def RowKey.name : RowKey → String
  | .bed => "bed" | .priorities => "priorities" | .segments => "segments"
  | .start => "start" | .stop => "stop" | .kind => "kind" | .batch => "batch"
  | .energy => "energy" | .item => "item" | .planned => "planned" | .mult => "mult"
  | .flags => "flags" | .note => "note"

/-- Fork `planner::SegErr` has no counterpart; this is `Planner.SegErr`'s two names. -/
def segErrName : Planner.SegErr → String
  | .inverted => "inverted" | .pastTheHorizon => "pastTheHorizon"

/-- **The `plan` section's refusals.**  Each names the record it is about by position and the
key by name, exactly as `badCandidate` does.

**Not** named PlanRefusal, which design §10.3 reserves for the *planner* section's family
(badState, badWindow, badBudget, badActive, …) and which four ledger sentences and
`Planner.dayPlan`'s own header cite as a type that **does not exist** — `dayPlan` is total
(D28) and keeps its total signature.  These are the ROWS' refusals, the names are disjoint from
§10.3's list, and the two families will share the one `plan` section's object when R3 brings
the planner's own keys to it. -/
inductive RowRefusal
  /-- The section is not an object, or a key is carried twice. -/
  | shape
  /-- The rows are rendered in a zone and the request carried none. -/
  | tzAbsent
  /-- Every duration cell is counted in blocks and the request carried no `blockMin`. -/
  | blockMinAbsent
  /-- A key of the section itself. -/
  | bad (k : RowKey)
  /-- More segments than the wire's own candidate cap. -/
  | tooManySegments
  /-- More priorities than the wire's own candidate cap. -/
  | tooManyPriorities
  /-- The priority record at this position. -/
  | badPriority (i : Nat)
  /-- A key of the segment record at this position. -/
  | badSegment (i : Nat) (k : RowKey)
  /-- The segment at this position is not one the planner could hold. -/
  | segmentRefused (i : Nat) (e : Planner.SegErr)
  /-- A `plan` section on a request that also edits the documents (gap 109's shape). -/
  | rowsWithCommands
deriving DecidableEq, Repr

def RowRefusal.text : RowRefusal → String
  | .shape => "shape"
  | .tzAbsent => "tzAbsent"
  | .blockMinAbsent => "blockMinAbsent"
  | .bad k => "bad " ++ k.name
  | .tooManySegments => "tooManySegments"
  | .tooManyPriorities => "tooManyPriorities"
  | .badPriority i => "badPriority " ++ String.ofList (digitsOf i)
  | .badSegment i k => "badSegment " ++ String.ofList (digitsOf i) ++ " " ++ k.name
  | .segmentRefused i e =>
      "segmentRefused " ++ String.ofList (digitsOf i) ++ " " ++ segErrName e
  | .rowsWithCommands => "rowsWithCommands"

/-- The refusal on the wire: `{"err": {"plan": "<name> <key>"}}` — `refusalJson`'s shape under
this section's own key. -/
def rowRefusalJson (r : RowRefusal) : JVal := jone "err" (jone "plan" (.str r.text.toList))

/-! ## Reading, through the boundary's own readers

`CapWire`'s readers are typed to `CapWire.Refusal`, and this section's names are its own.  The
adapter renames and does nothing else.  The refusal handed to the `CapWire` reader is a
**placeholder that is thrown away** — `asPlan` replaces it with this section's own name
whatever it is, and `asPlan_renames_a_refusal` says so for every value of it, so the choice of
`nowAbsent` carries no meaning and cannot reach the wire.  Writing the readers again over
`RowRefusal` instead would be a second copy of nine JSON shapes, which is the defect this
kernel is named after (AGENTS §5.3). -/

/-- A `CapWire` reading under this section's names. -/
def asPlan {α : Type} (r : RowRefusal) : Except CapWire.Refusal α → Except RowRefusal α
  | .ok a => .ok a
  | .error _ => .error r

/-- **The adapter renames and nothing else.** -/
theorem asPlan_keeps_the_value {α : Type} (r : RowRefusal) (x : Except CapWire.Refusal α)
    (a : α) (h : x = .ok a) : asPlan r x = .ok a := by
  subst h; rfl

/-- And a refusal stays a refusal, under this section's name. -/
theorem asPlan_renames_a_refusal {α : Type} (r : RowRefusal) (x : Except CapWire.Refusal α)
    (e : CapWire.Refusal) (h : x = .error e) : asPlan r x = .error r := by
  subst h; rfl

/-- A JSON natural at `k`. -/
def natAtP (v : JVal) (k : String) (r : RowRefusal) : Except RowRefusal Nat :=
  asPlan r (CapWire.natAt v k .nowAbsent)

/-- A JSON string at `k`. -/
def strAtP (v : JVal) (k : String) (r : RowRefusal) : Except RowRefusal (List Char) :=
  asPlan r (CapWire.strAt v k .nowAbsent)

/-- A JSON array at `k`. -/
def arrAtP (v : JVal) (k : String) (r : RowRefusal) : Except RowRefusal (List JVal) :=
  asPlan r (CapWire.arrAt v k .nowAbsent)

/-- An optional key: absent or `null` is `none`. -/
def optAtP (v : JVal) (k : String) (r : RowRefusal) : Except RowRefusal (Option JVal) :=
  asPlan r (CapWire.opt v k .nowAbsent)

/-- A mark: **absent is `false`**, which is `SegFlags`' own default, so a host that sends only
the marks it set gets `SegFlags.none` for the rest.  `CapWire.boolAt` is the *required* reading
and is the wrong one here — a `flags` object naming the two marks a row carries is the normal
case, not a malformed one. -/
def flagAtP (v : JVal) (k : String) (r : RowRefusal) : Except RowRefusal Bool :=
  match optAtP v k r with
  | .error e => .error e
  | .ok none => .ok false
  | .ok (some (.bool b)) => .ok b
  | .ok (some _) => .error r

/-- An optional natural at `k`. -/
def optNatAtP (v : JVal) (k : String) (r : RowRefusal) : Except RowRefusal (Option Nat) :=
  asPlan r (CapWire.optNatAt v k .nowAbsent)

/-- An optional string at `k`. -/
def optStrAtP (v : JVal) (k : String) (r : RowRefusal) : Except RowRefusal (Option (List Char)) :=
  match optAtP v k r with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some (.str s)) => .ok (some s)
  | .ok (some _) => .error r

/-- **The bound on an id crossing this section's wire** (R10), and the smart constructor the
five readers of one actually use.

`CapWire.maxCandId` is the number and it is **not a second one**: 1,024 characters is what the
candidate section already puts on a candidate's own id (`Boundary.readCand`'s
`within (decide (id.length ≤ maxCandId))`), `Lookahead.lean` names it as the rule for the same
reason, and two names for one bound is the defect this kernel exists to remove (AGENTS §5.3).

**Five `Id`s cross here and none was bounded** until README gap **1415**: the segment's `item`,
a priority record's `id`, every member of a `batch`, and the two ids `readNote` plays back
(`Note.noPosition`'s and `Note.bufferBefore`'s — the two the audit did not name).  Neither
constructor below them can supply it: `Planner.mkSeg?`'s `Planner.SegErr` has exactly two
constructors (`inverted`, `pastTheHorizon`) so `Seg.wf` says nothing about the item string, and
`Planner.mkBatch?` bounds the batch's **count** at `Planner.maxBatch` and never a member's
length. -/
def idWithin (r : RowRefusal) (id : Id) : Except RowRefusal Id :=
  if id.length ≤ CapWire.maxCandId then .ok id else .error r

/-! ## `Note` — the eleven names, read back

`Planner.Note` carries the *name* and its arguments and `Emit.noteText` holds the words, which
is AGENTS §5.7 paid off at the far end.  The wire therefore carries the name, never the
sentence: a host that sent the rendered text would be a second writer of it and the comparison
this module exists for would compare a string to itself. -/

/-- **The bound on a replayed note's text** (R10).  `Note.breakWhere` and `Note.idleAttributed`
play back the log's own words, which reached the kernel inside a `Replay.Segment` bounded at the
line they were read from; off *this* wire they carry no such provenance, so they carry a bound
of their own.  200 characters is far longer than any `break --where` or idle attribution and far
shorter than a line this kernel will hold. -/
def maxNoteText : Nat := 200

/-- One note, by name.  An unknown name is `badSegment <i> note`, never a silent `none`. -/
def readNote (i : Nat) (v : JVal) : Except RowRefusal Note := do
  let r : RowRefusal := .badSegment i .note
  let nm ← strAtP v "name" r
  if nm = "travelDay".toList then pure .travelDay
  else if nm = "travelDayWall".toList then pure .travelDayWall
  else if nm = "paused".toList then pure .paused
  else if nm = "interruption".toList then pure .interruption
  else if nm = "noPosition".toList then do
    let id ← idWithin r (← strAtP v "id" r)
    let d ← natAtP v "durMin" r
    let lo ← natAtP v "lo" r
    let hi ← natAtP v "hi" r
    pure (.noPosition id d lo hi)
  else if nm = "budgetSpent".toList then do
    let n ← natAtP v "blocksDone" r
    pure (.budgetSpent n)
  else if nm = "plannedOf".toList then do
    let a ← natAtP v "planned" r
    let b ← natAtP v "total" r
    pure (.plannedOf a b)
  else if nm = "bufferBefore".toList then do
    let id ← idWithin r (← strAtP v "id" r)
    pure (.bufferBefore id)
  else if nm = "runningLeft".toList then do
    let n ← natAtP v "leftMin" r
    pure (.runningLeft n)
  else if nm = "breakWhere".toList then do
    let t ← strAtP v "text" r
    if t.length ≤ maxNoteText then pure (.breakWhere t) else throw r
  else if nm = "idleAttributed".toList then do
    let t ← strAtP v "text" r
    if t.length ≤ maxNoteText then pure (.idleAttributed t) else throw r
  else throw r

/-- An absent or `null` note is no note — the row then derives its own (`Emit.noteCell`). -/
def readOptNote (i : Nat) (v : JVal) : Except RowRefusal (Option Note) :=
  match optAtP v "note" (.badSegment i .note) with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some n) => (readNote i n).map some

/-! ## The kind, the flags and the segment -/

/-- **One of the eleven `SegKind`s by its wire word.**  The words are
`tm_core::planner::kind_label`'s — the spelling `tm plan --json` and `.tm/last_plan.json`
already use — and **not** the Lean constructor names, which differ at two of the eleven (`brk`,
because `break` is a keyword here, and `windDown`).  Inventing a second spelling for a kind
that already has one on this repository's wire is AGENTS §5.3's own defect; design §8.2's "the
kernel's `SegKind` name is the wire word" is about `cli/render.rs::kind_name` dying, and it
did.

`ghost` is the eleventh word and the one this host never sends: the fork carries the ghost row
as a `SegFlags` bit and the kernel makes it a kind (`Planner.SegKind`'s own header).

A `batch` reads its members through `Planner.mkBatch?`, at `Planner.maxBatch`. -/
def readKind (i : Nat) (v : JVal) : Except RowRefusal SegKind := do
  let nm ← strAtP v "kind" (.badSegment i .kind)
  if nm = "block".toList then pure .block
  else if nm = "break".toList then pure .brk
  else if nm = "routine".toList then pure .routine
  else if nm = "wall".toList then pure .wall
  else if nm = "rest".toList then pure .rest
  else if nm = "optional".toList then pure .optional
  else if nm = "wind-down".toList then pure .windDown
  else if nm = "sleep".toList then pure .sleep
  else if nm = "lost".toList then pure .lost
  else if nm = "ghost".toList then pure .ghost
  else if nm = "batch".toList then do
    let xs ← arrAtP v "batch" (.badSegment i .batch)
    let ids ← xs.mapM (fun x =>
      match x with
      | .str s => idWithin (.badSegment i .batch) s
      | _ => throw (.badSegment i .batch))
    match Planner.mkBatch? ids with
    | some b => pure (.batch b)
    | none => throw (.badSegment i .batch)
  else throw (.badSegment i .kind)

/-- The seven marks.  Each is absent-is-`false`, which is `SegFlags`' own default, so a host
that sends `{}` gets `SegFlags.none`. -/
def readFlags (i : Nat) (v : JVal) : Except RowRefusal SegFlags := do
  let r : RowRefusal := .badSegment i .flags
  let f ← optAtP v "flags" r
  match f with
  | none => pure {}
  | some o => do
    let done ← flagAtP o "done" r
    let current ← flagAtP o "current" r
    let underused ← flagAtP o "underused" r
    let hot ← flagAtP o "hot" r
    let mandatory ← flagAtP o "mandatory" r
    let deferred ← flagAtP o "deferred" r
    let isOpen ← flagAtP o "open" r
    pure ⟨done, current, underused, hot, mandatory, deferred, isOpen⟩

/-- One segment, every field through the constructor that already bounds it. -/
def readSeg (i : Nat) (v : JVal) : Except RowRefusal WfSeg := do
  let start ← natAtP v "start" (.badSegment i .start)
  let stop ← natAtP v "stop" (.badSegment i .stop)
  let kind ← readKind i v
  let en ← optNatAtP v "energy" (.badSegment i .energy)
  let energy ← match en with
    | none => pure none
    | some n => match levelOf? n with
                | some c => pure (some c)
                | none => throw (.badSegment i .energy)
  let item ← match ← optStrAtP v "item" (.badSegment i .item) with
    | none => pure none
    | some s => (idWithin (.badSegment i .item) s).map some
  let flags ← readFlags i v
  let pl ← optNatAtP v "planned" (.badSegment i .planned)
  let planned ← match pl with
    | none => pure none
    | some n => if n ≤ CapWire.maxRemaining then pure (some n)
                else throw (.badSegment i .planned)
  let mv ← optAtP v "mult" (.badSegment i .mult)
  let mult ← match mv with
    | none => pure none
    | some m =>
      match CapWire.pairWith CapWire.natOf m with
      | none => throw (.badSegment i .mult)
      | some p => match CapWire.multiplierOfWire p with
                  | some q => pure (some q)
                  | none => throw (.badSegment i .mult)
  let note ← readOptNote i v
  match Planner.mkSeg? ⟨start, stop, kind, energy, item, none, flags, planned, mult, note⟩ with
  | .ok s => pure s
  | .error e => throw (.segmentRefused i e)

/-- The segments, read at their positions, refused past the wire's own cap **before** the map
runs (D9-21: the length is measured once and the list is never walked twice). -/
def readSegs (xs : List JVal) : Except RowRefusal (Capped WfSeg) :=
  if Planner.maxCands < xs.length then .error .tooManySegments
  else
    match xs.zipIdx.mapM (fun p => readSeg p.2 p.1) with
    | .error e => .error e
    | .ok ss =>
      match Capped.ofList? ss with
      | some c => .ok c
      | none => .error .tooManySegments

/-- One `{"id": …, "p": …}` pair, the `p` through the one reader of a stored priority. -/
def readPrio (i : Nat) (v : JVal) : Except RowRefusal (Id × Fin 8) :=
  match strAtP v "id" (.badPriority i), natAtP v "p" (.badPriority i) with
  | .error e, _ => .error e
  | _, .error e => .error e
  | .ok id, .ok n =>
    match yesterdayOf? n with
    | none => .error (.badPriority i)
    | some k =>
      match idWithin (.badPriority i) id with
      | .error e => .error e
      | .ok id' => .ok (id', k)

/-- §7's answers for the day's keys, at the same cap. -/
def readPrios (xs : List JVal) : Except RowRefusal (Capped (Id × Fin 8)) :=
  if Planner.maxCands < xs.length then .error .tooManyPriorities
  else
    match xs.zipIdx.mapM (fun p => readPrio p.2 p.1) with
    | .error e => .error e
    | .ok ps =>
      match Capped.ofList? ps with
      | some c => .ok c
      | none => .error .tooManyPriorities

/-! ## The section, and the rows it asks for -/

/-- **The decoded `plan` section.**  `blockMin` is NOT here: the request already carries one
(`ReqClock.blockMin`, `BlockMin.ofNat?`) and a second would be two answers to one question
(AGENTS §5.3).  `tz` likewise. -/
structure RowReq where
  bed   : Field.Clock
  prios : Capped (Id × Fin 8)
  segs  : Capped WfSeg

/-- The section: `bed`, the priorities and the segments. -/
def readRowSection (sec : JVal) : Except RowRefusal RowReq := do
  let bedV ← asPlan (.bad .bed) (CapWire.need sec "bed" .nowAbsent)
  let bed ← match CapWire.clockOf bedV with
    | some c => pure c
    | none => throw (.bad .bed)
  let ps ← match ← optAtP sec "priorities" (.bad .priorities) with
    | none => pure []
    | some (.arr xs) => pure xs
    | some _ => throw (.bad .priorities)
  let prios ← readPrios ps
  let ss ← arrAtP sec "segments" (.bad .segments)
  let segs ← readSegs ss
  pure ⟨bed, prios, segs⟩

/-- **The rows this call answers** — `Emit.rowOf` over the segments the host sent, against the
kernel's **own** loaded plan.  This is the caller `Emit.lean` did not have. -/
def rowsOfReq (p : PlanCore) (z : Cal.Tz) (bm : Nat) (q : RowReq) : List Row :=
  q.segs.val.map (fun s => Emit.rowOf p z bm q.bed q.prios.val s.val)

/-- A batch row's members, whole, for the Rust fitter — `Emit.batchNames`, the one reader of
them (`Emit.batchTitle_is_the_frame_over_batchNames`).  Every other kind answers `[]`. -/
def batchNamesOf (p : PlanCore) (s : Seg) : List (List Char) :=
  match s.kind with
  | .batch ids => Emit.batchNames p ids.val
  | _ => []

/-! ## The response -/

/-- **One row, as §4.3's nine cells in `Row.cells`' order**, plus the batch members the padder
needs and the nine cells do not carry (`emit::fit_batch` shares the title column out between
them; a caller handed only the joined title would have to split it back apart on ` · `). -/
def rowJson (p : PlanCore) (s : Seg) (r : Row) : JVal :=
  .obj [("time".toList, .str r.time), ("ci".toList, .str r.ci), ("p".toList, .str r.p),
    ("mark".toList, .str r.mark), ("title".toList, .str r.title),
    ("parent".toList, .str r.parent), ("est".toList, .str r.est),
    ("actual".toList, .str r.actual), ("note".toList, .str r.note),
    ("batchNames".toList, .arr ((batchNamesOf p s).map JVal.str))]

/-- The day's rows, in the day's order — one per segment sent and no other row.

It goes through `rowsOfReq` rather than mapping `Emit.rowOf` again: the day's row list has one
definition and this is its serializer.  The `zip` is what lets `rowJson` reach the segment as
well as the row, which it needs for the batch members only. -/
def rowsJson (p : PlanCore) (z : Cal.Tz) (bm : Nat) (q : RowReq) : JVal :=
  .arr ((q.segs.val.zip (rowsOfReq p z bm q)).map (fun sr => rowJson p sr.1.val sr.2))

/-- The `plan` key, after `lookahead` (design §10.2's order). -/
def withPlan (r v : JVal) : JVal :=
  match r with
  | .obj [(k, .obj kvs)] => .obj [(k, .obj (kvs ++ [("plan".toList, jone "rows" v)]))]
  | _ => r

/-! ## The entry -/

/-- **The request, with its `plan` section.**  Without one this is `runCap`, byte for byte
(`runRows_without_a_plan_section_is_runCap`).  With one: `runCap` answers first, so every
refusal that stood before this step still comes first and in the same order; then the zone
(`zoneOf`, gap 110's one reading), the request's own `blockMin`, the documents, the section,
and the `plan` key.

**The documents are loaded a second time** on this path (`runLoad` here, and once inside
`runCap`).  It is a cost and not a second reading — one `runLoad`, called twice — and it is
recorded as README gap 1325 with the number it costs.

**A `plan` section on a request that also carries commands is refused by name.**  The rows are
rendered against the plan as `runLoad` read it and the documents come back as the commands left
them, so answering both would put two states in one response.  That is gap 109's stance on
`capacityWithCommands`, applied to the same shape one section along. -/
def runRows (j : JVal) : Except JVal JVal :=
  match jget j "plan" with
  | .error e => .error (jsonErr e)
  | .ok none => runCap j
  | .ok (some sec) =>
    match runCap j with
    | .error e => .error e
    | .ok r =>
      match zoneOf j with
      | .error e => .error e
      | .ok none => .error (rowRefusalJson .tzAbsent)
      | .ok (some z) =>
        match runLoad j with
        | .error e => .error e
        | .ok (p, cmds, clock) =>
          match cmds with
          | _ :: _ => .error (rowRefusalJson .rowsWithCommands)
          | [] =>
          match clock.blockMin with
          | none => .error (rowRefusalJson .blockMinAbsent)
          | some bm =>
            match readRowSection sec with
            | .error x => .error (rowRefusalJson x)
            | .ok q => .ok (withPlan r (rowsJson p.val z bm.val q))

/-- **The response value for a request's bytes**, `respondCap`'s shape over `runRows`. -/
def respondRows (input : List Char) : JVal :=
  match jparse input with
  | .error e => jsonErr s!"bad json: {jerrText e}"
  | .ok j =>
    match runRows j with
    | .error e => e
    | .ok r    => r

/-- What the FFI runs. -/
def callRows (input : String) : String := String.ofList (jemit (respondRows input.toList))

/-- **The one export** (R9), moved here from `Boundary.callExport` so that an `Emit.Row` can
reach it.  The symbol, the shim and the `String → String` signature are unchanged. -/
@[export tm_kernel_call]
def callExport (input : String) : String := callRows input

/-! ## The laws -/

/-- **A request with no `plan` section is answered exactly as before.** -/
theorem runRows_without_a_plan_section_is_runCap (j : JVal) (h : jget j "plan" = .ok none) :
    runRows j = runCap j := by
  simp [runRows, h]

/-- And its bytes are `callCap`'s. -/
theorem callRows_without_a_plan_section_is_callCap (input : String)
    (j : JVal) (hp : jparse input.toList = .ok j) (h : jget j "plan" = .ok none) :
    callRows input = callCap input := by
  simp only [callRows, callCap, respondRows, respondCap, hp,
    runRows_without_a_plan_section_is_runCap j h]
  rfl

/-- **A `plan` section on a request that also edits the documents is refused by name**, so no
response can carry rows read from one state and documents written from another. -/
theorem runRows_refuses_a_plan_section_with_commands (j sec r : JVal) (z : Cal.Tz)
    (pl : WfPlan) (c : ReqCmd) (cs : List ReqCmd) (clock : ReqClock)
    (hp : jget j "plan" = .ok (some sec)) (hcap : runCap j = .ok r)
    (hz : zoneOf j = .ok (some z)) (hl : runLoad j = .ok (pl, c :: cs, clock)) :
    runRows j = .error (rowRefusalJson .rowsWithCommands) := by
  simp only [runRows, hp, hcap, hz, hl]

/-- **The export is `callRows`.** -/
theorem callExport_is_callRows (input : String) : callExport input = callRows input := rfl

/-- The nine keys, in `Row.cells`' order. -/
def rowKeys : List (List Char) :=
  ["time".toList, "ci".toList, "p".toList, "mark".toList, "title".toList,
   "parent".toList, "est".toList, "actual".toList, "note".toList]

/-- **The response's cells are `Row.cells`, in `Row.cells`' order.**  A field reordered in
`Emit.Row` breaks `Emit.cells_are_the_nine_in_order`; a key reordered here breaks this, and the
two together are what makes "the nine cells, in §4.3's order" a fact about the WIRE and not only
about a structure nothing reads. -/
theorem rowJson_is_the_nine_cells_in_order (p : PlanCore) (s : Seg) (r : Row) :
    rowJson p s r = .obj (rowKeys.zip (r.cells.map JVal.str) ++
      [("batchNames".toList, .arr ((batchNamesOf p s).map JVal.str))]) := rfl

/-- **One row per segment sent, and no other row** — the wire half of `Emit.rowsOf_length`. -/
theorem rowsJson_length (p : PlanCore) (z : Cal.Tz) (bm : Nat) (q : RowReq) :
    ∃ xs, rowsJson p z bm q = .arr xs ∧ xs.length = q.segs.val.length := by
  refine ⟨_, rfl, ?_⟩
  simp [rowsOfReq]

/-- And the rows are `Emit.rowOf`'s image of those segments, pointwise. -/
theorem rowsOfReq_eq (p : PlanCore) (z : Cal.Tz) (bm : Nat) (q : RowReq) :
    rowsOfReq p z bm q =
      q.segs.val.map (fun s => Emit.rowOf p z bm q.bed q.prios.val s.val) := rfl

/-! ### The names, the shapes and the two helpers, witnessed

**D40's gate found nine of these missing on this module's first sweep** — `RowKey.name`,
`segErrName`, `RowRefusal.text`, `rowRefusalJson`, `readOptNote`, `batchNamesOf` (twice) and
`withPlan` (twice) all SURVIVED a constant fold, which means nothing in the package could tell
them from `default`.  A definition whose words no theorem reads is a definition that can be
renamed, emptied or reordered with every gate green, and §5.7's "every diagnostic is named" is
worth exactly as much as the theorem that reads the name.  These are those theorems. -/

/-- **The section's keys spell themselves**, so a key renamed here moves a refusal's text and
not only an identifier. -/
theorem rowKey_names_are_the_wire_keys :
    (RowKey.bed.name, RowKey.priorities.name, RowKey.segments.name, RowKey.start.name,
     RowKey.stop.name, RowKey.kind.name, RowKey.batch.name, RowKey.energy.name,
     RowKey.item.name, RowKey.planned.name, RowKey.mult.name, RowKey.flags.name,
     RowKey.note.name)
      = ("bed", "priorities", "segments", "start", "stop", "kind", "batch", "energy",
         "item", "planned", "mult", "flags", "note") := rfl

/-- And `Planner.SegErr`'s two, which reach the wire through `segmentRefused`. -/
theorem segErrName_names_the_two :
    (segErrName .inverted, segErrName .pastTheHorizon) = ("inverted", "pastTheHorizon") := rfl

/-- **Every refusal spells itself, with its position and its key** — the sentence a host reads
off `{"err":{"plan": …}}`. -/
theorem the_refusals_spell_themselves :
    (RowRefusal.shape.text, RowRefusal.tzAbsent.text, RowRefusal.blockMinAbsent.text,
     (RowRefusal.bad .bed).text, RowRefusal.tooManySegments.text,
     RowRefusal.tooManyPriorities.text, (RowRefusal.badPriority 2).text,
     (RowRefusal.badSegment 3 .kind).text, (RowRefusal.segmentRefused 1 .inverted).text,
     RowRefusal.rowsWithCommands.text)
      = ("shape", "tzAbsent", "blockMinAbsent", "bad bed", "tooManySegments",
         "tooManyPriorities", "badPriority 2", "badSegment 3 kind",
         "segmentRefused 1 inverted", "rowsWithCommands") := rfl

/-- **And the shape it goes out in**: `{"err":{"plan":"<name> <key>"}}`, which is
`CapWire.refusalJson`'s shape under this section's own key. -/
theorem rowRefusalJson_is_the_err_plan_shape :
    rowRefusalJson (.badSegment 3 .kind)
      = .obj [("err".toList, .obj [("plan".toList, .str "badSegment 3 kind".toList)])] := rfl

/-- **An absent `note` is no note, and a present one is read.**  The first alone would not
distinguish this reader from `default` — `Except.ok none` **is** `default` here — so the pair
is the witness and the second half is the load-bearing one. -/
theorem readOptNote_of_an_absent_note (i : Nat) : readOptNote i (.obj []) = .ok none := rfl

theorem readOptNote_of_a_present_note (i : Nat) :
    readOptNote i (.obj [("note".toList, .obj [("name".toList, .str "paused".toList)])])
      = .ok (some .paused) := rfl

/-- **A batch row's members are `Emit.batchNames`', whatever the plan says** — the one reader,
reached from the wire.  Stated over every `p` and every `ids`, which is what tells it from the
empty list. -/
theorem batchNamesOf_of_a_batch (p : PlanCore) (s : Seg) (ids : Planner.BatchIds)
    (h : s.kind = .batch ids) : batchNamesOf p s = Emit.batchNames p ids.val := by
  unfold batchNamesOf
  rw [h]

/-- And every other kind answers `[]`, so the `batchNames` key is empty exactly where §7.5's
frame is. -/
theorem batchNamesOf_of_a_block (p : PlanCore) (s : Seg) (h : s.kind = .block) :
    batchNamesOf p s = [] := by
  unfold batchNamesOf
  rw [h]

/-- **The `plan` key goes on the END of the `ok` object**, after `lookahead` (design §10.2's
order), and nothing already there moves. -/
theorem withPlan_appends_the_plan_key (kvs : List (List Char × JVal)) (v : JVal) :
    withPlan (jone "ok" (.obj kvs)) v
      = jone "ok" (.obj (kvs ++ [("plan".toList, jone "rows" v)])) := rfl

/-! ### R10's rejections, one per bounded value

Each names the constructor the bound actually lives in, so nothing is re-bounded here. -/

theorem readSegs_refuses_past_the_cap (xs : List JVal) (h : Planner.maxCands < xs.length) :
    readSegs xs = .error .tooManySegments := by
  unfold readSegs
  rw [if_pos h]

theorem readPrios_refuses_past_the_cap (xs : List JVal) (h : Planner.maxCands < xs.length) :
    readPrios xs = .error .tooManyPriorities := by
  unfold readPrios
  rw [if_pos h]

/-- The empty section is the empty answer, so the two refusals above are not vacuous. -/
theorem readSegs_of_nil : (readSegs []).map (fun c => c.val) = .ok [] := rfl
theorem readPrios_of_nil : (readPrios []).map (fun c => c.val) = .ok [] := rfl

/-- **A stored `p` past seven is refused**, through `Priority.yesterdayOf?` — the one reader.
Stated over *whatever* the two readers return, so it is a fact about the decoder and not about
one JSON object; `readPrio_refuses_eight` is the object that exercises it. -/
theorem readPrio_refuses_a_priority_past_seven (i : Nat) (v : JVal) (id : Id) (n : Nat)
    (hid : strAtP v "id" (.badPriority i) = .ok id)
    (hn : natAtP v "p" (.badPriority i) = .ok n) (h : 8 ≤ n) :
    readPrio i v = .error (.badPriority i) := by
  simp only [readPrio, hid, hn, yesterdayOf?_refuses_eight n h]

/-- The wire object that reaches it. -/
theorem readPrio_refuses_eight :
    readPrio 2 (.obj [("id".toList, .str "a1".toList), ("p".toList, .num 8)])
      = .error (.badPriority 2) := by
  rfl

/-- And seven reads, so the refusal is not the only outcome. -/
theorem readPrio_accepts_seven :
    (readPrio 2 (.obj [("id".toList, .str "a1".toList), ("p".toList, .num 7)])).map
      (fun q => (q.1, q.2.val)) = .ok ("a1".toList, 7) := by
  rfl

set_option maxRecDepth 20000 in
/-- **A replayed note's text past `maxNoteText` is refused.** -/
theorem readNote_refuses_a_long_text :
    readNote 3 (.obj [("name".toList, .str "breakWhere".toList),
      ("text".toList, .str (List.replicate (maxNoteText + 1) 'x'))])
      = .error (.badSegment 3 .note) := by
  rfl

/-- And a short one is accepted, so the refusal is not the only outcome. -/
theorem readNote_accepts_a_short_text (i : Nat) :
    readNote i (.obj [("name".toList, .str "breakWhere".toList),
      ("text".toList, .str "walk".toList)]) = .ok (.breakWhere "walk".toList) := by
  rfl

/-- **An unknown kind word is refused by name**, never defaulted to a block. -/
theorem readKind_refuses_an_unknown_kind (i : Nat) :
    readKind i (.obj [("kind".toList, .str "nosuchkind".toList)])
      = .error (.badSegment i .kind) := by
  rfl

/-- **A batch past `Planner.maxBatch` is refused**, by `mkBatch?` — the one place that bound
lives (`Planner.mkBatch?_refuses_too_many_members`).  Seventeen members, one past the cap. -/
theorem readKind_refuses_a_batch_past_the_cap (i : Nat) :
    readKind i (.obj [("kind".toList, .str "batch".toList),
      ("batch".toList, .arr ((List.range 17).map (fun k => JVal.str (digitsOf k))))])
      = .error (.badSegment i .batch) := by
  rfl

/-- And sixteen are accepted, so the cap is where it says it is. -/
theorem readKind_accepts_a_batch_at_the_cap (i : Nat) :
    (readKind i (.obj [("kind".toList, .str "batch".toList),
      ("batch".toList, .arr ((List.range 16).map (fun k => JVal.str (digitsOf k))))])).isOk
      = true := by
  rfl

/-- **An energy past five is refused**, through `levelOf?`. -/
theorem readSeg_refuses_an_energy_past_five (i : Nat) :
    readSeg i (.obj [("start".toList, .num 0), ("stop".toList, .num 60),
      ("kind".toList, .str "block".toList), ("energy".toList, .num 6)])
      = .error (.badSegment i .energy) := by
  rfl

/-- **An inverted segment is refused**, through `Planner.mkSeg?` — its own rejection theorem is
`mkSeg?_refuses_an_inverted_segment` and this is the wire reaching it. -/
theorem readSeg_refuses_an_inverted_segment (i : Nat) :
    readSeg i (.obj [("start".toList, .num 600), ("stop".toList, .num 60),
      ("kind".toList, .str "block".toList)])
      = .error (.segmentRefused i .inverted) := by
  rfl

/-- **A segment that ends past the calendar is refused** (`mkSeg?_refuses_past_the_horizon`). -/
theorem readSeg_refuses_past_the_horizon (i : Nat) :
    readSeg i (.obj [("start".toList, .num 0), ("stop".toList, .num 400000000000),
      ("kind".toList, .str "block".toList)])
      = .error (.segmentRefused i .pastTheHorizon) := by
  rfl

/-- **A `planned` past the wire's own minutes bound is refused** — `CapWire.maxRemaining` is
`Look.maxPlanMinutes`, the same bound on the same wire (AGENTS §5.3). -/
theorem readSeg_refuses_a_planned_past_the_bound (i : Nat) :
    readSeg i (.obj [("start".toList, .num 0), ("stop".toList, .num 60),
      ("kind".toList, .str "block".toList),
      ("planned".toList, .num (CapWire.maxRemaining + 1))])
      = .error (.badSegment i .planned) := by
  rfl

/-- **A multiplier over a zero denominator is refused**, through `CapWire.multiplierOfWire`. -/
theorem readSeg_refuses_a_zero_denominator (i : Nat) :
    readSeg i (.obj [("start".toList, .num 0), ("stop".toList, .num 60),
      ("kind".toList, .str "block".toList),
      ("mult".toList, .obj [("num".toList, .num 3), ("den".toList, .num 0)])])
      = .error (.badSegment i .mult) := by
  rfl

set_option maxRecDepth 20000 in
/-- And a real segment reads: the refusals above are not the only outcome, and the fields
arrive where they were sent. -/
theorem readSeg_accepts_a_block (i : Nat) :
    (readSeg i (.obj [("start".toList, .num 0), ("stop".toList, .num 3600),
      ("kind".toList, .str "block".toList), ("energy".toList, .num 4),
      ("item".toList, .str "a1".toList), ("planned".toList, .num 60),
      ("flags".toList, .obj [("done".toList, .bool true)])])).map
      (fun s => (s.val.start, s.val.stop, s.val.kind, s.val.energy.map Fin.val, s.val.item,
        s.val.inst.isSome, s.val.flags, s.val.planned, s.val.mult.isSome, s.val.note.isSome))
      = .ok (0, 3600, SegKind.block, some 4, some "a1".toList, false,
        { done := true }, some 60, false, false) := by
  rfl

/-- **`bed` is the only clock this section reads, and it reads it with the clock grammar.** -/
theorem readRowSection_refuses_a_bad_bed :
    readRowSection (.obj [("bed".toList, .str "24:99".toList),
      ("segments".toList, .arr [])]) = .error (.bad .bed) := by
  rfl

/-! ### The five ids, bounded (README gap 1415)

`idWithin` is the constructor and `CapWire.maxCandId` is the bound; each theorem below is the
wire reaching it, and each has an acceptance beside it because a bound nothing can pass is a
trapdoor and a bound nothing can fail is decoration (AGENTS §5.8). -/

/-- **An id past `CapWire.maxCandId` is refused**, whatever the refusal is named. -/
theorem idWithin_refuses_a_long_id (r : RowRefusal) (id : Id)
    (h : CapWire.maxCandId < id.length) : idWithin r id = .error r := by
  unfold idWithin
  rw [if_neg (by omega)]

/-- And an id at the bound is accepted, so the guard is where it says it is. -/
theorem idWithin_accepts_at_the_bound (r : RowRefusal) (id : Id)
    (h : id.length ≤ CapWire.maxCandId) : idWithin r id = .ok id := by
  unfold idWithin
  rw [if_pos h]

/-- **Both are inhabited**: 1,025 characters is over and 1,024 is not, so neither theorem above
is vacuous.  Stated with `List.replicate` and closed by its length lemma rather than by `rfl`,
which would make the kernel walk a thousand cons cells for nothing. -/
theorem idWithin_refuses_1025_and_accepts_1024 (r : RowRefusal) :
    idWithin r (List.replicate (CapWire.maxCandId + 1) 'x') = .error r ∧
    idWithin r (List.replicate CapWire.maxCandId 'x')
      = .ok (List.replicate CapWire.maxCandId 'x') :=
  ⟨idWithin_refuses_a_long_id r _ (by simp), idWithin_accepts_at_the_bound r _ (by simp)⟩

/-- **A segment's `item` past the bound is refused.**  Stated over whatever the reader returns,
so it is a fact about the decoder and not about one JSON object. -/
theorem readSeg_refuses_a_long_item (i : Nat) (v : JVal) (id : Id)
    (hs : natAtP v "start" (.badSegment i .start) = .ok 0)
    (hp : natAtP v "stop" (.badSegment i .stop) = .ok 0)
    (hk : readKind i v = .ok .block)
    (he : optNatAtP v "energy" (.badSegment i .energy) = .ok none)
    (hi : optStrAtP v "item" (.badSegment i .item) = .ok (some id))
    (h : CapWire.maxCandId < id.length) :
    readSeg i v = .error (.badSegment i .item) := by
  simp only [readSeg, hs, hp, hk, he, hi, bind, Except.bind, pure, Except.pure,
    idWithin_refuses_a_long_id (RowRefusal.badSegment i RowKey.item) id h, Except.map]

/-- **A priority record's `id` past the bound is refused**, through the same constructor. -/
theorem readPrio_refuses_a_long_id (i : Nat) (v : JVal) (id : Id) (n : Nat) (k : Fin 8)
    (hid : strAtP v "id" (.badPriority i) = .ok id)
    (hn : natAtP v "p" (.badPriority i) = .ok n) (hk : yesterdayOf? n = some k)
    (h : CapWire.maxCandId < id.length) :
    readPrio i v = .error (.badPriority i) := by
  simp only [readPrio, hid, hn, hk,
    idWithin_refuses_a_long_id (RowRefusal.badPriority i) id h]

/-- **A batch member past the bound is refused**, so `mkBatch?`'s count bound is no longer the
only thing standing between the wire and a `BatchIds`. -/
theorem readKind_refuses_a_long_batch_member (i : Nat) (v : JVal) (id : Id)
    (hk : strAtP v "kind" (.badSegment i .kind) = .ok "batch".toList)
    (hb : arrAtP v "batch" (.badSegment i .batch) = .ok [.str id])
    (h : CapWire.maxCandId < id.length) :
    readKind i v = .error (.badSegment i .batch) := by
  simp only [readKind, hk, hb, bind, Except.bind, pure, Except.pure, List.mapM,
    List.mapM.loop, idWithin_refuses_a_long_id (RowRefusal.badSegment i RowKey.batch) id h]
  rfl

/-- **A replayed `noPosition`'s id past the bound is refused** — the first of the two ids
`readNote` reads back, and neither was named by the audit that opened gap 1415. -/
theorem readNote_refuses_a_long_no_position_id (i : Nat) (v : JVal) (id : Id)
    (hn : strAtP v "name" (.badSegment i .note) = .ok "noPosition".toList)
    (hid : strAtP v "id" (.badSegment i .note) = .ok id)
    (h : CapWire.maxCandId < id.length) :
    readNote i v = .error (.badSegment i .note) := by
  simp only [readNote, hn, hid, bind, Except.bind, pure, Except.pure,
    idWithin_refuses_a_long_id (RowRefusal.badSegment i RowKey.note) id h]
  rfl

/-- **And a `bufferBefore`'s**, which is the id a `buffer:` puts in front of a wall. -/
theorem readNote_refuses_a_long_buffer_before_id (i : Nat) (v : JVal) (id : Id)
    (hn : strAtP v "name" (.badSegment i .note) = .ok "bufferBefore".toList)
    (hid : strAtP v "id" (.badSegment i .note) = .ok id)
    (h : CapWire.maxCandId < id.length) :
    readNote i v = .error (.badSegment i .note) := by
  simp only [readNote, hn, hid, bind, Except.bind, pure, Except.pure,
    idWithin_refuses_a_long_id (RowRefusal.badSegment i RowKey.note) id h]
  rfl

/-- The empty day reads, so the section's own refusals are not the only outcome. -/
theorem readRowSection_accepts_an_empty_day :
    (readRowSection (.obj [("bed".toList, .str "22:00".toList),
      ("segments".toList, .arr [])])).map (fun q => (q.bed.val, q.prios.val.length,
        q.segs.val.length)) = .ok (1320, 0, 0) := by
  rfl

end EmitWire
end Tm
