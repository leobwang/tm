import TmKernel.Planner
/-!
# `Emit.lean` — the day section is CELLS, never padded text (stage 6, step P8)

Fork-point `tm-core/src/emit.rs` is the oracle, read by function name: `render_row`,
`glyph_of`, `shows_scale`, `mark_of`, `est_cell`, `title_cell`, `batch_names`, `parent_cell`,
`key_id`, `note_cell`, `underused_note`, `fmt_dur`, `priority.fmt_blocks` and
`energy.fmt_multiplier`.  `rowsOf` is `emit.plan_rows`; render_segment_row died at W-23.

## D30 Q6, which is the whole shape of this module

The owner's answer is **(a): the kernel emits cells; one Rust function pads.**  `Row` carries
§4.3's nine cells — `time ci p mark title parent est actual note` — as `List Char`, in a fixed
order, and **nothing here measures a column**.  `char_width`'s East-Asian ranges, `pad`,
`truncate` and `fit_batch` stay in Rust where the terminal is, because `Id := List Char` exists
to keep these proofs off UTF-8 (AGENTS §4) and a Unicode width table is the one thing this
kernel must not acquire.  `Row.cells` is the order, as data: a field reordered breaks
`cells_are_the_nine_in_order` and not a snapshot three commits later.

**This module therefore states no theorem about a column's width.**  Two laws come close and
are about a *count of characters*, not a count of terminal columns: `timeCell_length` (the
`HH:MM` cell is five characters, so `TIME_W` is never overrun by the kernel) and
`markCell_length` (the mark is one character, so `MARK_W` is never overrun).  Both are
`List.length` facts, neither knows what a column is, and on the glyphs — which are the
characters that *are* two columns wide — the kernel proves only that they stay out of the mark
column (`the_glyphs_stay_out_of_the_mark_column`), which is G6's rule and not G6's arithmetic.

## What is here, what is not, and why

`Note` was left un-rendered by P0 on purpose — `Planner.Note`'s own header says "Rendering is
P8's" — and `noteText` is that rendering: each of the eleven constructors carries its arguments
and gets the fork's own sentence back.  That is AGENTS §5.7's "every diagnostic is named"
paid off at the far end: the kernel holds the *name*, this module holds the *words*, and
`Diagnostics.notes` never held a `String`.

**NOT here, each named rather than quietly missing:**

* **The plan hash** — it is not text a row prints, and since W-34 it is `Planner.planDigest`
  (the FNV-1a digest `Planner.dayPlan` carries; README gap 1100's P0 placeholder is refuted).
* **`est_cell`'s first choice.**  The fork reads `est_original` before `est:`; this kernel has
  one estimate view, `Core.est` (`Field.viewRemainingDur`), which is `est:` **then** the
  leading estimate — the other order.  `estCell` here reads `Core.est`, and README gap 1101
  records the disagreement rather than inventing a second view of the same field.
* **`hot_note`'s deadline text.**  `note_cell`'s `⚠` branch needs the fork's `effective_due`,
  which this kernel does not have a view of; `noteCell` answers `[]` there where the fork says
  `due today` (README gap 1102).
* **Rounding at an exact half.**  `blocksCell` and `multCell` round with `Arith.halfUpQ`, the
  kernel's one rounding; the fork's `{:.1}` and `{:.2}` round half-to-even on an `f64`, so the
  two disagree exactly at a tie (README gap 1103).  Rounding half-up is *this kernel's*
  arithmetic — `Arith.plannedMin` already rounds that way — and adding a second rounding here
  to chase a formatter would be AGENTS §5.3's own defect.

## AGENTS §5.3 — what is CALLED and not copied

`Field.renderClock` (the `HH:MM` cell), `Field.renderDur` (every duration and every block
count), `digitsOf` (every number), `digitChar` (every single digit), `joinWith` (the title's
words), `Arith.halfUpQ` and `Arith.mkPos`/`Arith.scale` (the two roundings),
`Look.spanMinutes` through `Planner.Seg.minutes` (the `(67m)` cell), `Plan.parentStep` (the
`@parent` cell — the one reader of a record's parent since D6) and `Core.title`/`Core.ci` (the
one reader of each of those fields).  `canonDur` is the only new *shape* of a duration, and it
is a choice of `Field.Dur` constructor, not a second renderer: `durCell` is
`Field.renderDur ∘ canonDur`.

## D9-21, the recursion rule

Nothing here writes a recursion.  `rowsOf` is `List.map` over `DayPlan.segments`; `batchTitle`
is `List.map`, `List.intersperse` and `List.flatten` over a `BatchIds` bounded at
`Planner.maxBatch`; `titleText` is `List.filter` over one record's title words; `pCell` is
`List.lookup` over `Capped` at `Planner.maxCands`.  Every list is core's own and every bound is
one R10 already carries.
-/

namespace Tm
namespace Emit

open Field (Clock renderClock renderDur Dur)
open Planner

/-! ## `Row` — §4.3's nine cells, in order -/

/-- **The day section's row, as cells** (D30 Q6 (a)).  Every field is what the cell *says*;
what the cell is padded to is `emit.render_row`'s and is not representable here. -/
structure Row where
  /-- `HH:MM` — the segment's start in the plan's zone. -/
  time   : List Char
  /-- The slot energy and `↓`, or the kind's glyph. -/
  ci     : List Char
  /-- `p3`, on a row that is on §7's scale. -/
  p      : List Char
  /-- One of `✓ ▶ ⚠` or a space — and never a glyph. -/
  mark   : List Char
  /-- The item's title, or the row's own words. -/
  title  : List Char
  /-- `@m3`. -/
  parent : List Char
  /-- `2b`, `2b×1.6`, `30m`. -/
  est    : List Char
  /-- `(67m)` on a row the log closed. -/
  actual : List Char
  /-- The trailing note column. -/
  note   : List Char
deriving DecidableEq, Repr, Inhabited

/-- **The order, as data.**  `emit.render_row` writes the cells in this order and nothing else
decides it; a field reordered here fails `cells_are_the_nine_in_order` at compile time. -/
def Row.cells (r : Row) : List (List Char) :=
  [r.time, r.ci, r.p, r.mark, r.title, r.parent, r.est, r.actual, r.note]

/-! ## The instant cell -/

/-- Local seconds since the epoch, as a clock.  The bound is arithmetic, not a convention. -/
def clockOfLocal (l : Nat) : Clock := ⟨l % 86400 / 60, by omega⟩

/-- Fork `emit.hhmm` / `planner.fmt_clock`, through `Field.renderClock` — the kernel's one
`HH:MM`, with `parse_render_clock` already proved about it. -/
def timeCell (z : Cal.Tz) (sec : Nat) : List Char :=
  renderClock (clockOfLocal (Cal.localSec z ⟨sec, 0⟩))

/-! ## The `ci` column, the `p` column and the mark -/

/-- Fork `shows_scale`: budgeted work always, and a window *task* the planner gave an energy. -/
def showsScale (s : Seg) : Bool :=
  s.kind.isWork || (s.kind == SegKind.routine && s.energy.isSome)

/-- Fork `glyph_of`: the glyph a row with no scale puts in the `ci` column. -/
def glyphOf : SegKind → Char
  | .wall     => '⏰'
  | .optional => '○'
  | .windDown => '🌙'
  | _         => '·'

/-- Fork `mark_of`: done beats current beats hot, and a row with none carries a space. -/
def markChar (s : Seg) : Char :=
  if s.flags.done then '✓'
  else if s.flags.current then '▶'
  else if s.flags.hot then '⚠'
  else ' '

/-- The mark cell.  One character, always (`markCell_length`). -/
def markCell (s : Seg) : List Char := [markChar s]

/-- Fork `render_row`'s ci cell (a local there, so there is no name to cite): the slot's
energy, else the item's, else a space, with `↓`
beside it on an under-used slot — or the kind's glyph on a row with no scale. -/
def ciCell (s : Seg) (itemCi : Option (Fin 6)) : List Char :=
  if showsScale s then
    (match s.energy.orElse (fun _ => itemCi) with
     | some c => [digitChar c.val]
     | none   => [' ']) ++ (if s.flags.underused then ['↓'] else [])
  else [glyphOf s.kind]

/-- Fork `key_id`: the id a segment is keyed by — its own item, or a batch's first member. -/
def keyId (s : Seg) : Option Id :=
  match s.kind with
  | .batch ids => s.item.orElse (fun _ => ids.val.head?)
  | _          => s.item

/-- Fork `render_row`'s p cell (a local there): §7's answer for the row's key, on a row that
is on §7's scale. -/
def pCell (prios : List (Id × Fin 8)) (s : Seg) : List Char :=
  if showsScale s then
    match (keyId s).bind (fun i => prios.lookup i) with
    | some k => ['p', digitChar k.val]
    | none   => []
  else []

/-- Fork `render_row`'s `actual`: `(67m)` on a row the log closed — never on a Rest row, whose
minutes are not an achievement. -/
def actualCell (s : Seg) : List Char :=
  if s.flags.done && s.kind != SegKind.rest then '(' :: (digitsOf s.minutes ++ ['m', ')'])
  else []

/-! ## Durations and block counts -/

/-- Fork `Dur.canonical`: the shortest natural unit for `n` minutes — `20m`, `1h`, `1h22m`.
A *choice of constructor*, so `Field.renderDur` stays the one renderer (`durCell`). -/
def canonDur (n : Nat) : Dur :=
  if n % 60 = 0 ∧ 0 < n then .simple (n / 60) .hours
  else if 60 < n then .hm (n / 60) (n % 60)
  else .simple n .minutes

/-- Fork `emit.fmt_dur`. -/
def durCell (n : Nat) : List Char := renderDur (canonDur n)

/-- One decimal place, as `{:.1}` writes it: `13` becomes `1.3`. -/
def tenths (k : Nat) : List Char := digitsOf (k / 10) ++ '.' :: [digitChar (k % 10)]

/-- Fork `priority.fmt_blocks`: whole blocks where the minutes divide, one decimal where they
do not and there is at least one block, and bare minutes otherwise. -/
def blocksCell (bm n : Nat) : List Char :=
  if h : 0 < bm then
    if n % bm = 0 then renderDur (.simple (n / bm) .blocks)
    else if bm ≤ n then tenths (Arith.halfUpQ (Arith.mkPos (10 * n) bm h)) ++ ['b']
    else renderDur (.simple n .minutes)
  else renderDur (.simple n .minutes)

/-- Fork `energy.fmt_multiplier`: two decimal places with the trailing zeros dropped. -/
def multCell (m : Arith.Pos) : List Char :=
  let k := Arith.halfUpQ (Arith.scale m 100)
  let whole := digitsOf (k / 100)
  let f := k % 100
  if f = 0 then whole
  else if f % 10 = 0 then whole ++ '.' :: [digitChar (f / 10)]
  else whole ++ '.' :: [digitChar (f / 10), digitChar (f % 10)]

/-- Fork `fmt_planned`'s guard, exact.  `|m − 1| ≥ 1/200` on a rational is
`den ≤ 200 × |num − den|`, and no `f64` is involved. -/
def multShown (m : Arith.Pos) : Bool :=
  decide (m.val.den ≤ 200 * (if m.val.den ≤ m.val.num then m.val.num - m.val.den
                             else m.val.den - m.val.num))

/-! ## The cells that read the plan -/

/-- The item's title, joined, or `none` when the tree does not know it or it has none.
`Core.title` is the one reader of the field (D6). -/
def titleText (p : PlanCore) (i : Id) : Option (List Char) :=
  match p.store.get i with
  | some e =>
      let ws := (Core.title e.val).filter (fun w => !w.isEmpty)
      if ws.isEmpty then none else some (joinWith ' ' ws)
  | none => none

/-- The item's `ci`, through `Core.ci` — the one reader of C2's two slots. -/
def itemCiOf (p : PlanCore) (i : Id) : Option (Fin 6) :=
  (p.store.get i).bind (fun e => Core.ci e.val)

/-- The estimate the item carries, through `Core.est` — `est:` then the leading estimate
(C1).  **The fork's `est_cell` reads `est_original` first**; see the header and gap 1101. -/
def itemEstOf (p : PlanCore) (i : Id) : Option Dur :=
  (p.store.get i).bind (fun e => Core.est e.val)

/-- Fork `title_cell`'s `name(fallback)`. -/
def nameOr (p : PlanCore) (s : Seg) (fallback : List Char) : List Char :=
  (s.item.bind (titleText p)).getD fallback

/-- **Fork `batch_names`**: the titles a batch names, in the order it was assigned (§7.5), each
falling back to the member's own id when the tree does not know it or it has none.

It is a *separate* definition from the frame below because the Rust padder needs the **members**
and not the joined string: `emit::fit_batch` shares the title column out between them and cuts
each one, and a caller handed only `batchTitle`'s output would have to split it back apart on
` · ` — which a title containing that separator would break.  So the members cross the wire
beside the nine cells (`EmitWire.rowJson`'s `batchNames`), and `batchTitle` is this list with
§7.5's frame around it — one reader of the member names, not two. -/
def batchNames (p : PlanCore) (ids : List Id) : List (List Char) :=
  ids.map (fun i => (titleText p i).getD i)

/-- Fork `batch_names` and §7.5's frame: `batch: package · insurance · bank (3)`, whole.
Shortening it to a column is `fit_batch`'s, in Rust, where the widths are. -/
def batchTitle (p : PlanCore) (ids : List Id) : List Char :=
  let names := batchNames p ids
  "batch: ".toList ++ (names.intersperse " · ".toList).flatten ++
    " (".toList ++ digitsOf names.length ++ [')']

/-- **The frame is the only thing `batchTitle` adds to the members** — `fit_batch`'s `full`, on
the Rust side of the wire, is this string with the same members in it. -/
theorem batchTitle_is_the_frame_over_batchNames (p : PlanCore) (ids : List Id) :
    batchTitle p ids =
      "batch: ".toList ++ ((batchNames p ids).intersperse " · ".toList).flatten ++
        " (".toList ++ digitsOf (batchNames p ids).length ++ [')'] := rfl

/-- **D68** (P59): `Planner.pastKind`'s row of a replayed Pause — drawn as a pause, never lost. -/
def pausedRow (s : Seg) : Bool := decide (s.kind = .lost) && s.item.isSome && decide (s.note = some .paused)
/-- Fork `title_cell`, and D68's pause.  `planned` is the minutes the planner set aside, else the
row's own length — the fork's `planned_min.unwrap_or_else(|| seg.minutes())`. -/
def titleCell (p : PlanCore) (bed : Clock) (s : Seg) : List Char :=
  let planned := s.planned.getD s.minutes
  match s.kind with
  | .batch ids => batchTitle p ids.val
  | .brk       => "break ".toList ++ durCell planned
  | .routine   => if showsScale s then nameOr p s ['—']
                  else nameOr p s "routine".toList ++ ' ' :: durCell planned
  | .sleep     => nameOr p s "sleep".toList ++ ' ' :: durCell planned
  | .rest      => "rest ".toList ++ durCell planned
  | .lost      => (if pausedRow s then "paused " else "lost ").toList ++ durCell planned
  | .windDown  => "wind-down · bed ".toList ++ renderClock bed
  | _          => nameOr p s ['—']

/-- Fork `parent_cell`, through `Plan.parentStep` — `@` and the written parent, not the root. -/
def parentCell (p : PlanCore) (s : Seg) : List Char :=
  match s.item.bind (parentStep p) with
  | some j => '@' :: j
  | none   => []

/-- Fork `est_cell`'s gate: which kinds show an estimate at all. -/
def showsEst (s : Seg) : Bool :=
  match s.kind with
  | .block | .batch _ | .wall | .optional => true
  | .routine => showsScale s
  | _ => false

/-- Fork `est_cell`.  The written estimate wins; else `planned_min` un-scaled, in blocks; else,
for the three kinds that carry their own length, the row's minutes. -/
def estCell (p : PlanCore) (bm : Nat) (s : Seg) : List Char :=
  if !showsEst s then []
  else
    let base :=
      match s.item.bind (itemEstOf p) with
      | some d => renderDur d
      | none =>
        match s.planned with
        | some q =>
            let unscaled :=
              match s.mult with
              | some m => if h : 0 < m.val.num then
                            Arith.halfUpQ (Arith.mkPos (q * m.val.den) m.val.num h)
                          else q
              | none => q
            blocksCell bm unscaled
        | none =>
            match s.kind with
            | .wall | .optional => durCell s.minutes
            | .routine          => if showsScale s then durCell s.minutes else []
            | _                 => []
    if base.isEmpty then []
    else match s.mult with
         | some m => if multShown m then base ++ '×' :: multCell m else base
         | none   => base

/-! ## `Note` — §8.2 step 8's eleven sentences -/

/-- **The words `Planner.Note` deliberately does not carry.**  Each constructor is one `notes.push`
or one `note: Some(…)` site of `tm-core/src/planner.rs`, rendered here.  `p` is the plan (one note
names a title), `z` the zone (one names two clocks) and `bm` the block length (one counts blocks). -/
def noteText (p : PlanCore) (z : Cal.Tz) (bm : Nat) : Note → List Char
  | .travelDay =>
      "travel day: no blocks planned (`travel-day` wall today)".toList
  | .noPosition i durMin lo hi =>
      i ++ ": no free ".toList ++ digitsOf durMin ++ "m position in ".toList ++
        timeCell z lo ++ '–' :: timeCell z hi ++ "; not planned today".toList
  | .budgetSpent n =>
      "budget spent: ".toList ++ digitsOf n ++ " blocks done, the rest of the day is rest".toList
  | .plannedOf planned total =>
      let pct := if h : 0 < total then Arith.halfUpQ (Arith.mkPos (100 * planned) total h) else 0
      "planned ".toList ++ blocksCell bm planned ++ " of ".toList ++ blocksCell bm total ++
        " (".toList ++ digitsOf pct ++ "%)".toList
  | .bufferBefore i    => "buffer before ".toList ++ (titleText p i).getD i
  | .travelDayWall     => "travel day".toList
  | .paused            => "paused".toList
  | .interruption      => "interruption".toList
  | .breakWhere t | .idleAttributed t => t
  | .runningLeft n     => "running · ".toList ++ digitsOf n ++ "m left".toList
  | .soFar n           => digitsOf n ++ "m so far".toList

/-- Fork `underused_note`'s fallback pair.  The kernel's `Diagnostics.underused` is the id list
only, so the pair is the segment's own energy and the item's `ci` — which is the branch the
fork reaches when its triple has no entry for the row. -/
def underusedCell (p : PlanCore) (s : Seg) : List Char :=
  match keyId s, s.energy with
  | some i, some slot =>
      match itemCiOf p i with
      | some c => "↓ slot ".toList ++ [digitChar slot.val] ++ ", item ".toList ++ [digitChar c.val]
      | none => []
  | _, _ => []

/-- Fork `note_cell`: an explicit note wins — but D68's pause says it in its title — then the `↓`
derivation.  The `⚠` branch needs `effective_due` and is gap 1102. -/
def noteCell (p : PlanCore) (z : Cal.Tz) (bm : Nat) (s : Seg) : List Char :=
  match s.note with
  | some n => if pausedRow s then [] else noteText p z bm n
  | none   => if s.flags.underused then underusedCell p s else []

/-! ## The row, and the day -/

/-- **One row of §4.3, as cells.**  Everything a surface prints comes from here; what any one
surface does with the nine cells is that surface's layout and not the kernel's.

It takes a `Planner.Seg` and not a `Planner.WfSeg` because **no cell reads the well-formedness bit**: a row
is a projection of a segment's fields and `Seg.wf` bounds when the segment ends, which nothing here asks
about.  The subtype would be a hypothesis the emitter does not use; `rowsOf` supplies the `.val`. -/
def rowOf (p : PlanCore) (z : Cal.Tz) (bm : Nat) (bed : Clock)
    (prios : List (Id × Fin 8)) (s : Seg) : Row :=
  { time   := timeCell z s.start
    ci     := ciCell s (s.item.bind (itemCiOf p))
    p      := pCell prios s
    mark   := markCell s
    title  := titleCell p bed s
    parent := parentCell p s
    est    := estCell p bm s
    actual := actualCell s
    note   := noteCell p z bm s }

/-- **The day's rows, in the day's order.**  One row per segment and no other row: `tm now`
selects a window of this list, `tm plan --json` numbers it, and the day file writes it — which
is D30 Q5 (a)'s "one row renderer, and every surface's rows are its output", stated in the only
half of it the kernel can hold. -/
def rowsOf (r : PlanReq) : List Row :=
  let d := dayPlan r
  d.segments.map (fun s => rowOf r.plan.val r.tz r.blockMin r.look.day.bed d.priorities.val s.val)

/-! ## The laws -/

/-- **The nine cells, in §4.3's order.**  A field reordered breaks this. -/
theorem cells_are_the_nine_in_order (r : Row) :
    r.cells = [r.time, r.ci, r.p, r.mark, r.title, r.parent, r.est, r.actual, r.note] := rfl

theorem cells_length (r : Row) : r.cells.length = 9 := rfl

/-- **The `HH:MM` cell is five characters**, so `TIME_W` is never overrun by the kernel.  A
count of characters, not of terminal columns (the header). -/
theorem timeCell_length (z : Cal.Tz) (sec : Nat) : (timeCell z sec).length = 5 :=
  Field.renderClock_length _

/-- **The mark is one character**, so `MARK_W` is never overrun. -/
theorem markCell_length (s : Seg) : (markCell s).length = 1 := rfl

theorem markChar_mem (s : Seg) : markChar s ∈ ['✓', '▶', '⚠', ' '] := by
  unfold markChar
  split
  · simp
  · split
    · simp
    · split <;> simp

theorem glyphOf_mem (k : SegKind) : glyphOf k ∈ ['⏰', '○', '🌙', '·'] := by
  cases k <;> simp [glyphOf]

/-- **G6's rule, as a theorem.**  `emit.mark_of`'s own comment says the glyphs "belong to the
`ci` column, not here"; nothing but this stops a future arm putting one in the mark column, and
the glyphs are exactly the characters that are two terminal columns wide. -/
theorem the_glyphs_stay_out_of_the_mark_column (s : Seg) (k : SegKind) :
    markChar s ≠ glyphOf k := by
  have h1 := markChar_mem s
  have h2 := glyphOf_mem k
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
  rcases h1 with h1 | h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 | h2 <;>
    rw [h1, h2] <;> decide

/-- **A row with no scale shows the glyph and nothing else** — no energy digit, no `↓`. -/
theorem ciCell_is_the_glyph_off_the_scale (s : Seg) (c : Option (Fin 6))
    (h : showsScale s = false) : ciCell s c = [glyphOf s.kind] := by
  simp [ciCell, h]

/-- **A row with no scale carries no priority**: `p3` is §7's answer and §7 does not rank a
wall. -/
theorem pCell_is_empty_off_the_scale (ps : List (Id × Fin 8)) (s : Seg)
    (h : showsScale s = false) : pCell ps s = [] := by
  simp [pCell, h]

/-- **`(67m)` is a closed row's**: nothing else prints an actual. -/
theorem actualCell_of_not_done (s : Seg) (h : s.flags.done = false) : actualCell s = [] := by
  simp [actualCell, h]

/-- **Rest has no actual** even when the log closed it (fork `!matches!(kind, Rest)`). -/
theorem actualCell_of_rest (s : Seg) (h : s.kind = SegKind.rest) : actualCell s = [] := by
  simp [actualCell, h]

/-- **A wall, an optional and a Rest row show no priority and no scale**, whatever the planner
put on them. -/
theorem the_three_quiet_kinds_are_off_the_scale (s : Seg)
    (h : s.kind = SegKind.wall ∨ s.kind = SegKind.optional ∨ s.kind = SegKind.rest) :
    showsScale s = false := by
  rcases h with h | h | h <;> simp [showsScale, h, SegKind.isWork]

/-- **One row per segment, and no other row.**  This is what makes "`tm now`'s rows are a
contiguous sub-list of the file's" a statement about one list (D30 Q5 (a)). -/
theorem rowsOf_length (r : PlanReq) : (rowsOf r).length = (dayPlan r).segments.length := by
  simp [rowsOf]

/-- And the rows are that list's image, pointwise. -/
theorem rowsOf_eq (r : PlanReq) :
    rowsOf r = (dayPlan r).segments.map
      (fun s => rowOf r.plan.val r.tz r.blockMin r.look.day.bed (dayPlan r).priorities.val s.val)
      := rfl

/-! ### The cells built from numbers hold no newline

The Rust joins rows with `'\n'`, so a cell that could hold one would split a row in two.  The
four cells the kernel builds out of digits and named characters cannot; `title`, `parent`,
`note` and `est` carry the plan's own text and the log's, which R10 bounds at the line they
were read from, and no theorem here claims more than that. -/

theorem digitChar_no_newline (k : Nat) : digitChar k ≠ '\n' := by
  unfold digitChar
  split <;> decide

theorem digitsOf_no_newline (n : Nat) : ∀ c ∈ digitsOf n, c ≠ '\n' := by
  intro c hc h
  have hd := digitsOf_all_digits n c hc
  rw [h] at hd
  exact absurd hd (by decide)

theorem timeCell_no_newline (z : Cal.Tz) (sec : Nat) : ∀ c ∈ timeCell z sec, c ≠ '\n' := by
  intro c hc h
  rcases Field.renderClock_chars _ c hc with hd | hd <;> rw [h] at hd <;>
    exact absurd hd (by decide)

theorem markCell_no_newline (s : Seg) : ∀ c ∈ markCell s, c ≠ '\n' := by
  intro c hc
  have hm := markChar_mem s
  simp only [markCell, List.mem_singleton] at hc
  subst hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hm | hm | hm | hm <;> rw [hm] <;> decide

theorem glyphOf_no_newline (k : SegKind) : glyphOf k ≠ '\n' := by
  have hg := glyphOf_mem k
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with hg | hg | hg | hg <;> rw [hg] <;> decide

theorem ciCell_no_newline (s : Seg) (k : Option (Fin 6)) : ∀ c ∈ ciCell s k, c ≠ '\n' := by
  intro c hc
  unfold ciCell at hc
  split at hc
  · simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · split at hc <;> simp only [List.mem_singleton] at hc <;> subst hc
      · exact digitChar_no_newline _
      · decide
    · split at hc
      · simp only [List.mem_singleton] at hc; subst hc; decide
      · simp at hc
  · simp only [List.mem_singleton] at hc
    subst hc
    exact glyphOf_no_newline _

theorem actualCell_no_newline (s : Seg) : ∀ c ∈ actualCell s, c ≠ '\n' := by
  intro c hc
  unfold actualCell at hc
  split at hc
  · simp only [List.mem_cons, List.mem_append] at hc
    rcases hc with hc | hc | hc
    · rw [hc]; decide
    · exact digitsOf_no_newline _ c hc
    · simp only [List.not_mem_nil, or_false] at hc
      rcases hc with hc | hc <;> rw [hc] <;> decide
  · simp at hc

/-! ## D68 — a typed pause is not lost time (stage 6 W-38 track T, parity P59, README gap 3344)

`tm plan` drew a typed `tm pause` as `lost 10m … paused` while `tm review day` counted none of it
as lost: one span, two readings (AGENTS §5.3).  The spec's "lost" is interruption time — §9's
Interruption row is what logs `lost=`, on `resume` — so the review's reading stands and the
DRAWING moves: the owner's **D68** draws a replayed Pause as a pause, `paused 10m`.

**What moves, and what does not.**  The planner's segment is unchanged: `Planner.pastKind` still
answers the fork's Lost kind with the `paused` note, so the §8.2 day, every law about it, the
planner wire and the fork comparand are what they were.  The drawing is this module's:
`pausedRow` picks the row out, `titleCell` writes `paused <dur>` and `noteCell` nothing, where fork
`title_cell` and `note_cell` wrote `lost <dur>` and `paused`.  A wall-covered pause stays D65's wall
alone (P56): `Planner.a_paused_row_lies_under_no_wall` leaves no row there to draw.

**Both directions** (AGENTS §5.8): a replayed Pause is drawn `paused` and never `lost`
(`a_replayed_pause_is_drawn_as_a_pause`), and every other Lost row the past half draws — an
interruption's or an idle span's — is drawn `lost` as the fork draws it
(`a_lost_row_that_is_not_a_pause_is_drawn_lost`). -/

theorem pausedRow_iff (s : Seg) :
    pausedRow s = true ↔ s.kind = .lost ∧ s.item.isSome = true ∧ s.note = some .paused := by
  simp [pausedRow, and_assoc]

/-- **A paused row's title is `paused <dur>`**, where the fork's was `lost <dur>`. -/
theorem titleCell_of_pausedRow (p : PlanCore) (bed : Clock) (s : Seg) (h : pausedRow s = true) :
    titleCell p bed s = "paused ".toList ++ durCell (s.planned.getD s.minutes) := by
  have hk := ((pausedRow_iff s).1 h).1
  simp [titleCell, hk, h]

/-- **…and its note cell is empty**: the one word is in the title, which the fork wrote twice. -/
theorem noteCell_of_pausedRow (p : PlanCore) (z : Cal.Tz) (bm : Nat) (s : Seg)
    (h : pausedRow s = true) : noteCell p z bm s = [] := by
  have hn := ((pausedRow_iff s).1 h).2.2
  simp [noteCell, hn, h]

/-- **Every other Lost row is drawn `lost`, as the fork draws it.** -/
theorem titleCell_of_a_lost_row_that_is_not_a_pause (p : PlanCore) (bed : Clock) (s : Seg)
    (hk : s.kind = .lost) (h : pausedRow s = false) :
    titleCell p bed s = "lost ".toList ++ durCell (s.planned.getD s.minutes) := by
  simp [titleCell, hk, h]

/-- **A row that is not a pause keeps the fork's note**: the rule moves one row's note, no other. -/
theorem noteCell_of_a_row_that_is_not_a_pause (p : PlanCore) (z : Cal.Tz) (bm : Nat) (s : Seg)
    (h : pausedRow s = false) (n : Note) (hn : s.note = some n) :
    noteCell p z bm s = noteText p z bm n := by
  simp [noteCell, hn, h]

/-- **A row of the past half is a paused row exactly when its segment is a replayed Pause.** -/
theorem pausedRow_pastRowOf (d : Replay.DayAcc) (g : Replay.Segment) (q : Nat × Nat) :
    pausedRow (pastRowOf d g q) = true ↔ ∃ i, g.kind = .pause i := by
  cases hg : g.kind <;> simp [pausedRow, pastRowOf, pastKind, hg]

/-- **D68 on the kernel's day.**  A row of the past half is a paused row exactly when a replayed
Pause drew it, and then it is drawn `paused <dur>` with an empty note — never `lost`. -/
theorem a_replayed_pause_is_drawn_as_a_pause (r : PlanReq) (p : PlanCore) (bed : Clock)
    (z : Cal.Tz) (bm : Nat) (t : Seg) (ht : t ∈ pastRows r) :
    (pausedRow t = true ↔ ∃ d, r.todayRecord = some d ∧ ∃ g ∈ d.segments,
        (∃ i, g.kind = .pause i) ∧ ∃ q ∈ pastSpans r g, t = pastRowOf d g q) ∧
    (pausedRow t = true →
      titleCell p bed t = "paused ".toList ++ durCell (t.planned.getD t.minutes) ∧
      noteCell p z bm t = []) := by
  refine ⟨⟨fun h => ?_, fun ⟨d, _, g, _, hp, q, _, he⟩ => he ▸ (pausedRow_pastRowOf d g q).2 hp⟩,
    fun h => ⟨titleCell_of_pausedRow p bed t h, noteCell_of_pausedRow p z bm t h⟩⟩
  obtain ⟨d, hd, g, hg, q, hq, rfl⟩ := mem_pastRows.1 ht
  exact ⟨d, hd, g, hg, (pausedRow_pastRowOf d g q).1 h, q, hq, rfl⟩

/-- **The past half draws `lost` only an interruption or an idle span** (D68's other direction):
a Lost row that is not a pause is drawn `lost <dur>`, and its segment is an Interrupt or an Idle. -/
theorem a_lost_row_that_is_not_a_pause_is_drawn_lost (r : PlanReq) (p : PlanCore) (bed : Clock)
    (t : Seg) (ht : t ∈ pastRows r) (hk : t.kind = .lost) (h : pausedRow t = false) :
    titleCell p bed t = "lost ".toList ++ durCell (t.planned.getD t.minutes) ∧
    ∃ d, r.todayRecord = some d ∧ ∃ g ∈ d.segments,
      ((∃ i, g.kind = .interrupt i) ∨ ∃ a, g.kind = .idle a) ∧
      ∃ q ∈ pastSpans r g, t = pastRowOf d g q := by
  refine ⟨titleCell_of_a_lost_row_that_is_not_a_pause p bed t hk h, ?_⟩
  obtain ⟨d, hd, g, hg, q, hq, rfl⟩ := mem_pastRows.1 ht
  refine ⟨d, hd, g, hg, ?_, q, hq, rfl⟩
  cases hg' : g.kind <;> simp [pastRowOf, pastKind, pausedRow, hg'] at hk h ⊢

end Emit
end Tm
